import numpy as np
import math
import re
import rstr
import warnings
from utils.debug import trace
from analyzer.func import *
from interval import interval,imath,fpu,inf
from functools import reduce

warnings.simplefilter(action='ignore', category=FutureWarning)

@trace
def eval_logic_op(op,E,T):
    t = "Bool"
    if op == "and":
        e = reduce(lambda res,cur : res&cur, E)
    elif op == "or":
        e = reduce(lambda res,cur : res|cur, E)
    elif op == "xor":
        e = reduce(lambda res,cur : res^cur, E)
    elif op == "not":
        e = not(E[0])
    elif op == "=>":
        e = (False if (E[0]==True and E[1]==False) else True)
    elif op == "ite":
        e = (E[1] if E[0]==True else E[2])
        t = (T[1] if E[0]==True else T[2])
    else:
        e = None
    return e,t

@trace
def eval_cop_op(op,E,T):
    t = "Bool"
    if op == "=":
        if T[0] == "String":
            e = True
            tmp_s = from_uni(E[0][1:-1])
            for i in range(1,len(E)):
                e = e&(tmp_s==from_uni(E[i][1:-1]))
        elif T[0] == "Bool":
            e = True
            tmp_b = E[0]
            for i in range(1,len(E)):
                e = e&(tmp_b==E[i])
        else:
            e =True
            for i in E:
                for j in E:
                    j = j + interval[-1e-10,1e-10]
                    e = e&(not(i&j==interval()))
    elif op == "distinct":
        e_dict = set()
        e = True
        if T[0] =="String":
            tmp_s = from_uni(E[0][1:-1])
            e_dict.add(tmp_s)
            for i in range(1,len(E)):
                e = e&(not(from_uni(E[i][1:-1]) in e_dict))
                e_dict.add(from_uni(E[0][1:-1]))
        elif T[0]=="Bool":
            e = True
            tmp_b = E[0]
            for i in range(1,len(E)):
                e = e&(not(tmp_b==E[i]))
        else:
            e_dict.add(E[0])
            for i in range(len(E)):
                a_i = E[i]+interval[-1e-8,1e-8]
                for j in range(i+1,len(E)):
                    a_j = E[j]+interval[-1e-8,1e-8]
                    e = e&(not(a_i&E[j]==E[j] and a_j&E[i]==E[i]) or (a_i&a_j==interval()))
    elif op == ">=":
        e = True
        _, u = fpu.min(E[0])
        for i in range(1,len(E)):
            l, _ =fpu.min(E[i])
            e = e&(l<=u+1e-7)
            _, u = fpu.max(E[i])
    elif op == ">":
        e = True
        _, u = fpu.min(E[0])
        ca = True
        for i1 in range(len(E)):
            i = E[i1]
            for i2 in range(i1+1,len(E)):
                j = E[i2]
                ca = ca&(not(i&j==interval()))
                
        if ca == False:
            for i in range(1,len(E)):
                l, _ =fpu.min(E[i])
                e = e&(l<u+1e-10)
                _, u = fpu.max(E[i])
        else:
            e = False
    elif op == "<=":
        e = True
        l,_ = fpu.min(E[0])
        for i in range(1,len(E)):
            _, u =fpu.max(E[i])
            e = e&(l<=u+1e-7)
            l, _ = fpu.min(E[i])
    elif op == "<":
        e = True
        ca = True
        for i1 in range(len(E)):
            i = E[i1]
            for i2 in range(i1+1,len(E)):
                j = E[i2]
                ca = ca&(not(i&j==interval()))
        if ca == False:
            l,_ = fpu.min(E[0])
            for i in range(1,len(E)):
                _, u =fpu.max(E[i])
                e = e&(l<u+1e-10)
                l, _ = fpu.min(E[i])
        else:
            e = False
    return e,t

@trace
def eval_real_op(op,E,T,t_dict,m_dict,f_term):
    t = "Real"
    if op == "tanh":
        e = imath.tanh(E[0])
    elif op == "cosh":
        e = imath.cosh(E[0])
    elif op == "sinh":
        e = imath.sinh(E[0])
    elif op in ["arctan","atan"]:
        e = imath.atan(E[0])
    elif op in ["arccos","acos"]:
        e = acos(E[0])
    elif op in ["arcsin","asin"]:
        e = asin(E[0])
    elif op == "tan":
        e = imath.tan(E[0])
    elif op == "cos":
        e = imath.cos(E[0])
    elif op == "sin":
        e = imath.sin(E[0])
    elif op == "log":
        if E[0] <= interval(0.0)+1e-8:
            e = None
        else:
            e = imath.log(E[0])
    elif op == "exp":
        e = imath.exp(E[0])
    elif op == "to_real":
        e = E[0]
    elif op == "/":
        e = E[0]
        if e == interval(0.0):
            return e,t
        t_dict[f_term]-=1
        p = interval(1.0)
        for s in list(t_dict.keys()):
            if t_dict[s]==0:
                continue
            if s == f_term:
                e = interval(1)
                t_dict[s]-=1
            l = pow(m_dict[s],interval(t_dict[s]))
            if 0.0 in l:
                l = l&(interval[-inf,-1e-6]|interval[1e-6,inf])
                if l == interval():
                    l = interval(0.0)
            p *= l
        e = e/p
    elif op in ["arctan2","atan2"]:
        e = arctan2(E[0],E[1])
    elif op == "csc":
        e = None
    elif op == "sec":
        e = None
    elif op == "cot":
        e = None
    elif op =="arccsc":
        e = None
    elif op =="arcsec":
        e = None
    elif op == "arccot":
        e = None
    elif op =="real.pi":
        e = interval(np.arctan(1)*4)
    else:
        e = None
    return e,t

@trace
def eval_int_op(op,E,T,t_dict,m_dict,f_term):
    t = "Int"
    if op == "to_int":
        e = []
        for s in E[0]:
            l,u = s
            l = int(math.floor(float(l)))
            u = int(math.floor(float(u)))
            e.append(interval[l,u])
        e = interval.union(e)
    elif op == "div":
        e = E[0]
        if e == interval():
            return None,None
        t_dict[f_term]-=1
        p = interval(1)
        for s in list(t_dict.keys()):
            if t_dict[s]==0:
                continue
            if s == f_term:
                e = interval(1)
                t_dict[s]-=1
            p*=pow(m_dict[s],interval(t_dict[s]))
        if p<interval(0):
            l1,u1 = e[0]
            if p == interval():
                return None, None
            l2,u2 = p[0]

            l_1 = math.ceil(l1/l2)
            if l2 == 0:
                l2 = min(1,u2)
                if l2 == 0:
                    return None,None
            elif u2 == 0:
                u2 = max(-1,l2)
                if u2 == 0:
                    return None,None
            l_2 = math.ceil(l1/u2)
            l_3 = math.ceil(u1/l2)
            l_4 = math.ceil(u1/u2)
            l = min(l_1,l_2,l_3,l_4)
            u = max(l_1,l_2,l_3,l_4)
            e = interval[l,u]
        else:
            l1,u1 = e[0]
            l2,u2 = p[0]
            if p[0]==interval(0):
                return None,None
            elif l2 == 0:
                l2 = min(1,u2)
                if l2 == 0:
                    return None,None
            elif u2 == 0:
                u2 = max(-1,l2)
                if u2 == 0:
                    return None,None
            
            l_1 = math.floor(l1/l2)
            l_2 = math.floor(l1/u2)
            l_3 = math.floor(u1/l2)
            l_4 = math.floor(u1/u2)
            l = min(l_1,l_2,l_3,l_4)
            u = max(l_1,l_2,l_3,l_4)
            e = interval[l,u]
    elif op == "mod":
        if E[0]==interval():
            return None,None
        l1,u1 = E[0][0]
        if E[1]==interval():
            return None,None
        l2,u2 = E[1][0]
        e = []
        for p in range(int(l1),min(int(l1)+100,int(u1)+1)):
            for s in range(int(l2),min(int(l2)+100,int(u2)+1)):
                if s == 0:
                    continue
                if s<0:
                    e.append(interval(p%(-s)))
                else:
                    e.append(interval(p%s))
        e = interval.union(e)
    elif op == "int.pow2":
        e = []
        for s in E[0]:
            l,u = s
            l = int(math.pow(2,min(512,int(l))))
            u = int(math.pow(2,min(512,int(u))))
            e.append(interval(l,u))
        e = interval.union(e)
    elif op == "iand":
        s1,_ = E[0][0]
        s2,_ = E[1][0]
        s3,_ = E[2][0]
        e = s1%(s2&s3)
    else:
        e = None
    return e,t

@trace   
def eval_arith_op(op,E,T,t_dict,m_dict,f_term):
    if op in ["pow","^"]:
        t = "Real"
        e = pow(E[0],E[1])
    elif op == "sqrt":
        t = "Real"
        e = imath.sqrt(E[0])
    elif op == "max":
        t = T[0]
        e = E[0]
    elif op == "min":
        t = T[0]
        e = E[0]
    elif op == "+":
        e = interval(0)
        for s in list(m_dict.keys()):
            e += m_dict[s]*interval(t_dict[s])
        t = ("Real" if ("Real" in T) else "Int")
    elif op == "-":
        if len(E)==1:
            e = -E[0]
            t = T[0]
        else:
            e = E[0]
            t_dict[f_term]-=1
            for s in list(m_dict.keys()):
                if t_dict[s]==0:
                    continue
                if s == f_term:
                    e = interval(0)
                    t_dict[s]-=1
                e -= m_dict[s]*interval(t_dict[s])
            t = "Real" if "Real" in T else "Int"
    elif op == "*":
        e = interval(1.0)
        mask =interval[-1e-7,1e-7]
        for s in list(t_dict.keys()):
            if t_dict[s]==0:
                continue
            l = pow(m_dict[s],interval(t_dict[s]))
            if e == interval(0.0) or l==interval(0.0) or l&mask==mask:
                e = interval(0.0)
                continue
            e *= l
        t = "Real" if ("Real" in T) else "Int"
    elif op == "abs":
        t = T[0]
        e = abs(E[0])
    else:
        e = None
        t = None
    return e,t

@trace
def from_uni(s):
    if r"\u{" in s:
        d = s.split(r"\u{")
        e = r""
        for c in d:
            if "}" in c:
                l = c.split("}")
                e+=chr(int(l[0],16))
                e+=l[1]
            else:
                e+=c
    else:
        e = s
    return e

@trace
def to_uni(s):
    c = ""
    for d in s:
        i = ord(d)
        if i>=32 and i<=126 and i!=92:
            c +=d
        else:
            c += r'\u{'+str(hex(i))[2:]+'}'
    return c

@trace
def eval_string_op(op,E,T):
    return_b = ["str.in_re","str.<=","str.<","str.suffixof",
            "str.prefixof","str.contains","str.is_digit"]

    return_s = ["str.++","str.at","str.substr","str.replace","str.replace_all",
            "str.replace_re","str.replace_re_all","str.from_code","str.from_int"]+["str.to_upper","str.to_lower","str.rev","str.update"]

    return_i = ["str.len","str.indexof","str.to_code","str.to_int","str.indexof_re"]
    return_r = ["str.to_re"]

    if op in return_b:
        ty = "Bool"
    elif op in return_s:
        ty = "String"
    elif op in return_i:
        ty = "Int"
    elif op in return_r:
        ty = "RegLan"
    else:
        print("String op :",op,"is not supported!!")
        return None,None

    ###### Evaluate #######
    e = None
    if None in E:
        return e,None
    try:
        if op == "str.++":
            e = '"'
            for tmp_e in E:
                tmp_e = tmp_e[1:-1]
                e +=tmp_e
            e+='"'
        elif op == "str.len":
            e = interval(int(len(from_uni(E[0][1:-1]))))
        elif op == "str.<":
            tmp_e1 = from_uni(E[0][1:-1])
            tmp_e2 = from_uni(E[1][1:-1])
            e = (tmp_e1<tmp_e2)
            #("res:",e,E)
        elif op == "str.to_re":
            e = E[0][1:-1]
            e=e.replace('+','\+')
            e=e.replace('*','\*')
        elif op == "str.in_re":
            # (str.in_re w L) => Bool
            # w in L => True else False
            if E[1] is None:
                e = None
            else:
                p = re.compile(from_uni(E[1]),re.DOTALL)
                tmp_e = from_uni(E[0][1:-1])
                e = (True if p.fullmatch(tmp_e) else False)
        elif op == "str.<=":
            tmp_e1 = from_uni(E[0][1:-1])
            tmp_e2 = from_uni(E[1][1:-1])
            e = (tmp_e1<=tmp_e2)
        elif op == "str.at":
            l,_ = E[1][0]
            tmp_e = from_uni(E[0][1:-1])
            if len(tmp_e)<=int(l) or int(l)<0:
                e = '""'
            else:
                e = '"'+to_uni(tmp_e[int(l)])+'"'
        elif op == "str.substr":
            sl,su = E[1][0]
            cl,cu = E[2][0]
            tmp_e = from_uni(E[0][1:-1])
            if int(sl)<0 or int(sl)>=len(tmp_e) or int(cl)<=0:
                e = '""'
            else:
                for s in range(int(sl),int(su)+1):
                    for cnt in range(int(cl),int(cu)+1):
                        if s<0 or s>=len(tmp_e) or cnt<=0:
                            e = '""'
                        else:
                            e = '"'+to_uni(tmp_e[s:s+cnt])+'"'
                        break
                    break
        elif op == "str.prefixof":
            # (str.prefixof s t) : 's' is a prefix of 't' ==> true
            s,t = E
            tmp_s = from_uni(s[1:-1])
            tmp_t = from_uni(t[1:-1])
            e = tmp_t.startswith(tmp_s)
        elif op == "str.suffixof":
            # (str.suffixof s t) : 's' is a suffix of 't' ==> true
            s,t = E
            tmp_s = from_uni(s[1:-1])
            tmp_t = from_uni(t[1:-1])
            e = tmp_t.endswith(tmp_s)
        elif op == "str.contains":
            # (str.contains s t) : 's' contains 't' ==> true
            s,t = E
            tmp_s = from_uni(s[1:-1])
            tmp_t = from_uni(t[1:-1])
            e = (tmp_t in tmp_s)
        elif op == "str.indexof":
            # (str.indexof s t i) : starting position of ocurrence t in s after i
            # not ocurrence --> res : -1
            s,t,i = E
            il,iu = i[0]
            if len(t[1:-1])==0 and il >=0 and il <=len(from_uni(s[1:-1])):
                e = il
            elif len(t[1:-1])==0:
                e = -1
            elif len(s[1:-1]) == 0:
                e = -1
            else:
                s = from_uni(s[1:-1])
                tmp_t = from_uni(t[1:-1])
                if il>len(s) or il < 0:
                    e = -1
                else:
                    tmp_s = s[int(il):]
                    e = tmp_s.find(tmp_t)
                    if e != -1:
                        e += int(il)
            e = interval(e)
        elif op == "str.replace":
            # (str.replace s t t') : replace first occurrence of t in s by any t',
            # Note that t is empty "", prepend t' to s, if t does not occur in s then the result is s.
            s,t,new_t = E
            tmp_s = from_uni(s[1:-1])
            tmp_t = from_uni(t[1:-1])
            tmp_n_t = from_uni(new_t[1:-1])
            if len(tmp_t)==0: # t is empty
                e = '"'+to_uni(tmp_n_t)+to_uni(tmp_s)+'"'
            else:
                if tmp_s.find(tmp_t)==-1: # t does not occur in s
                    e = s
                else:
                    e = '"'+to_uni(tmp_s.replace(tmp_t,tmp_n_t,1))+'"'
        elif op == "str.replace_all":
            # (str.replace_all s t t') : 
            s,t,new_t = E
            tmp_s = from_uni(s[1:-1])
            tmp_t = from_uni(t[1:-1])
            tmp_n_t = from_uni(new_t[1:-1])
            if len(tmp_t)==0 or tmp_s.find(tmp_t)==-1: 
                # t is empty or t does not occur in s
                e = '"'+to_uni(tmp_s)+'"'
            else:
                e = '"'+to_uni(tmp_s.replace(tmp_t,tmp_n_t))+'"'
        elif op == "str.replace_re":
            s,r,t = E
            tmp_s = from_uni(s[1:-1])
            tmp_t = from_uni(t[1:-1])
            if r == '[-]':
                r = ""
            if len(from_uni(r))==0:
                e = '"'+to_uni(tmp_t)+to_uni(tmp_s)+'"'
            else:
                tmp_r = r.split('|')
                if "|" in r:
                    tmp_r[0] = tmp_r[0][1:]
                    tmp_r[-1] = tmp_r[-1][:-1]
                
                bool_t = False
                r = ""
                
                for tr in tmp_r:
                    if ")(" in tr:
                        return None,None

                for tr in tmp_r:
                    if len(tr)==0 or tr[-2:]==")*":
                        e = '"'+to_uni(tmp_t+tmp_s)+'"'
                        bool_t = True
                        break
                
                if bool_t==False:
                    for tr in tmp_r:
                        if ("+" in tr):
                            r += tr+'?'+'|'
                        else:
                            r += tr+'|'
                    r = r[:-1]
                    r=re.sub("(\(\.\)\*)+",'(.)*',r)
                    td = r.split(')*')
                    if len(td)>1 and td[1]!="":
                        r=re.sub("(\(\.\)\*)+",'',r)
                    else:
                        r=re.sub("(\(\.\)\*)+",'(.)',r)
                        r = re.compile('<'+from_uni(r)+'>?',re.DOTALL)
                    e = '"'+to_uni(re.sub(r,tmp_t.replace('\\', r'\\'),tmp_s,1))+'"'
        elif op == "str.replace_re_all":
            s,r,t = E
            tmp_s = from_uni(s[1:-1])
            tmp_t = from_uni(t[1:-1])
            if r == '[-]':
                r = ""
            if len(r)==0 or len(tmp_s)==0:
                e = s
            else:
                r = from_uni(r)
                tmp_r = r.split('|')
                if "|" in r:
                    tmp_r[0] = tmp_r[0][1:]
                    tmp_r[-1] = tmp_r[-1][:-1]
                r = ""
                for tr in tmp_r:
                    if len(tr)==0:
                        pass
                    else:
                        r+=tr+'|'
                r = r[:-1]
                r=re.sub("(\(\.\)\*)+",'(.)*',r)
                td = r.split(')*')
                if len(td)>1 and td[1]!="":
                    r=re.sub("(\(\.\)\*)+",'',r)
                else:
                    r=re.sub("(\(\.\)\*)+",'(.)',r)
                tmp_r = r.replace('*','+')
                tmp_r = tmp_r.replace('+','+?')
                if len(tmp_r)==0:
                    e = '"'+to_uni(tmp_s)+'"'
                else:
                    tmp_r = re.compile(from_uni(tmp_r),re.DOTALL)
                    e = '"'+to_uni(re.sub(tmp_r,tmp_t.replace('\\', r'\\'),tmp_s))+'"'
        elif op == "str.is_digit":
            tmp_s = from_uni(E[0][1:-1])
            e = (tmp_s>="0" and tmp_s<="9" and len(tmp_s)==1)
        elif op == "str.to_code":
            #(str.to_code s) : code point of the only character of s,
            #if s is a singleton string; otherwise, it is -1
            s = E[0]
            tmp_s = s[1:-1]
            if r'\u' in tmp_s:
                first = list(filter(len,tmp_s.split('\\')))
                second = list(filter(len,tmp_s.split('}')))
                if len(re.findall("u{",tmp_s))>1 or len(second)>=2 or len(first)>=2:
                    e = interval(-1)
                else:
                    e = interval(int("0x"+tmp_s[3:-1],16))
            else:
                if len(tmp_s)>1:
                    e = interval(-1)
                elif len(tmp_s)==1:
                    e = interval(ord(tmp_s))
                else:
                    e = interval(-1)
        elif op == "str.from_code":
            nl,nu = E[0][0]
            if int(nl)<0 or int(nu)>196607:
                e = '""'
            else:
                for n in range(int(nl),int(nu)+1):
                    if n<0 or n>196607:
                        e = '""'
                    else:
                        if n>=32 and n<=126:
                            e = '"'+chr(n)+'"'
                        else:
                            e=r'"\u{'+str(hex(ord(chr(n))))[2:]+'}"'
        elif op == "str.to_int":
            # (str.to_int) : 
            e = ""
            if len(E[0])==2:
                e = -1
            else:
                tmp_s = from_uni(E[0][1:-1])
                for s in tmp_s:
                    if not(s>='0' and s<='9'):
                        e = -1
                        break
                    else:
                        e += s
            e = interval(int(e))
        elif op == "str.from_int":
            # (str.from_int n) : n is non-negative integer 
            l,_ = E[0][0]
            '''
            for i in range(int(si),int(ui)+1):
                if i<0:
                    e = '""'
                else:
                    e = '"'+str(i)+'"'
            '''
            if int(l)<0:
                e = '""'
            else:
                e = '"'+to_uni(str(int(l)))+'"'
        elif op =="str.update":
            #(str.update w i)
            sidx,uidx = E[1][0]
            tmp_s = from_uni(E[0][1:-1])
            tmp_t = from_uni(E[2][1:-1])
            e = ""
            for i in range(int(sidx),int(uidx)+1):
                if i<0 or i>=len(tmp_s):
                    e = '"'+to_uni(tmp_s)+'"'
                    break
                else:
                    e = '"'+to_uni(tmp_s[:i]+tmp_t+tmp_s[i+len(tmp_t):])+'"'
                    if i+len(tmp_t)>len(tmp_s):
                        e = '"'+to_uni(tmp_s[:i]+tmp_t[:len(tmp_s)-i])+'"'
                    else:
                        e = '"'+to_uni(tmp_s[:i]+tmp_t+tmp_s[i+len(tmp_t):])+'"'
        elif op == "str.rev":
            tmp_s = from_uni(E[0][1:-1])
            e = '"'+to_uni(tmp_s[::-1])+'"'
        elif op == "str.to_lower":
            tmp_s = from_uni(E[0][1:-1])
            res = ""
            for i in tmp_s:
                if i>="A" and i<="Z":
                    res+=i.lower()
                else:
                    res+=i
            e = '"'+to_uni(res)+'"'
        elif op == "str.to_upper":
            tmp_s = from_uni(E[0][1:-1])
            res = ""
            for i in tmp_s:
                if i>="a" and i<="z":
                    res+=i.upper()
                else:
                    res+=i
            e = '"'+to_uni(res)+'"'
        elif op =="str.indexof_re":
            pass
        else:
            pass
        return e,ty
    except Exception as e:
        #print(e)
        #print(E,op)
        return None,None

@trace
def eval_reg_op(op,E,T):
    return_r = ["re.none","re.all","re.allchar","re.++","re.union",
            "re.inter","re.*","re.comp","re.diff","re.+","re.opt","re.range","re.^","re.loop"]

    t = "RegLan"
    e = None


    if op == "re.none":
        pass
    elif op == "re.all":
        e = "(.)*"
    elif op == "re.allchar":
        e = "(.)"
    elif op == "re.++":
        if (len(E[0])>1 and '|' in E[0] and E[0][-1] in ['*','+']):
            e = E[0]+E[1]
        elif len(E[1])>1 and '|' in E[1] and E[1][-1] in ['*',"+"]:
            e = E[0]+E[1]
        else:
            e = ""
            tmp_r = E[0].split('|')
            if len(tmp_r)>=2 and E[0][0]=='(' and E[0][-1]==')':
                tmp_r[0] = tmp_r[0][1:]
                tmp_r[-1] = tmp_r[-1][:-1]

            tmp_s = E[1].split('|')

            if len(tmp_s)>=2 and E[1][0]=='(' and E[1][-1]==')':
                tmp_s[0] = tmp_s[0][1:]
                tmp_s[-1] = tmp_s[-1][:-1]
            
            for f in tmp_r:
                for s in tmp_s:
                    e += f+s+"|"

            if e[-1]=="|":
                e = e[:-1]
                if len(tmp_r)>=2 or len(tmp_s)>=2:
                    e = "("+e+")"
    elif op == "re.union":
        if E[0]==E[1]:
            e = E[0]
        else:
            if len(E[0])>0 and E[0][-1] in ['*','+']:
                e = "("+E[0]+"|"+E[1]+")"
            else:
                e = ""
                tmp_r = E[0].split('|')
                if len(tmp_r)>=2 and E[0][0]=='(' and E[0][-1]==')':
                    tmp_r[0] = tmp_r[0][1:]
                    tmp_r[-1] = tmp_r[-1][:-1]

                tmp_s = E[1].split('|')

                if len(tmp_s)>=2 and E[1][0]=='(' and E[1][-1]==')':
                    tmp_s[0] = tmp_s[0][1:]
                    tmp_s[-1] = tmp_s[-1][:-1]
                
                for f in tmp_r:
                    e += f+"|"
                for s in tmp_s:
                    e += s+"|"
                
                if e[-1]=='|':
                    e = "("+e[:-1]+")"
                else:
                    e = "("+e+")"
    elif op == "re.inter":
        pass
    elif op == "re.*":
        if len(E[0])==0:
            e = ''
        else:
            e = "("+E[0]+")*"
            if E[0][len(E[0])-1]=='*':
                e = E[0]
            elif E[0][len(E[0])-1]=='+':
                e = E[0][:-1]+'*'
            elif E[0][-1]==')' and '|' in E[0]:
                e = E[0]+'*'
    elif op == "re.comp":
        pass
    elif op == "re.diff":
        pass
    elif op == "re.+":
        if len(E[0])==0:
            e = ''
        else:
            e = "("+E[0]+")+"
            if E[0][len(E[0])-1]=='*':
                e = E[0][-1]+'+'
            elif E[0][len(E[0])-1]=='+':
                e = E[0]
            else:
                tmp_r = E[0].split('|')
                if len(tmp_r)>=2:
                    tmp_r[0] = tmp_r[0][1:]
                    tmp_r[-1] = tmp_r[-1][:-1]
                    e = "("
                    for tr in tmp_r:
                        if len(tr)!=0:
                            e+="("+tr+")+|"
                        else:
                            e+=tr+"|"
                    e = e[:-1]+")"
    elif op == "re.opt":
        e = "("+E[0]+"|)"
    elif op == "re.range":
        tmp_w1 = from_uni(E[0][1:-1])
        tmp_w2 = from_uni(E[1][1:-1])
        if len(tmp_w1)!=1 or len(tmp_w2)!=1 or tmp_w1 > tmp_w2:
            e = None
        else:     
            e = "["+tmp_w1+"-"+tmp_w2+"]"
    elif op == "re.^":
        pass
    elif op == "re.loop":
        pass
    else:
        pass
    return e,t

