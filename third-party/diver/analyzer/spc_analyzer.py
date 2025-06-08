import inspect
import numpy as np
from interval import interval,imath,fpu,inf
from analyzer.evaluate import *
from analyzer.constraint import *

def check(p_op,node_idx,p_state):
    if p_op in ["arctan2","atan2"] and node_idx==1:
        return False
    elif p_op in ["^","pow"] and node_idx == 1:
        return False
    else:
        return p_state

class ConstraintAnalyzer(object):
    def __init__(self,formula,var_type,model,logic):
        self.const = {"Int":set(),"String":set(),"Real":set()}
        self.var = {"Int":set(),"String":set(),"Real":set(),"Bool":set()}
        self.formula = formula
        self.var_type = var_type
        self.model = model
        self.assert_idx = "0"
        self.logic = logic
        self.C = {}
        self.E = {}
        
        self.cnt = 0
        self.terms = {}
        self.tree = {}
        self.parent = {}
        self.term_type = ["Constant","Const_String","RegLan","Bool","Variable",
                        "FOperator","BOperator","SOperator","ROperator","Operator","R_Operator","_Operator"]
        
        self.logic_op = ["and","or","xor","=>","not","ite"]
        self.compare_op = [">=",">","<","<=","=","distinct"]

        self.real_op = ["tanh","cosh","sinh","arctan2","atan2","arctan","atan","arccos","acos","arcsin","asin","tan","cos",
                "sin","log","exp","to_real","/","csc","sec","cot","arccsc","arcsec","arccot","real.pi"]

        self.int_op = ["to_int","div","mod","int.pow2","iand"]

        self.arith_op = ["pow","^","sqrt","max","min","abs","*","-","+"]

        self.string_op = ["str.in_re","str.<=","str.<","str.prefixof","str.suffixof","str.contains","str.is_digit",
                    "str.++","str.at","str.substr","str.replace_all","str.replace_re_all","str.replace_re",
                    "str.replace","str.from_code","str.from_int","str.len","str.to_code","str.to_int","str.to_upper","str.to_lower",
                    "str.rev","str.update","str.indexof_re","str.to_re","str.indexof"]
        
        self.reg_op = ["re.none","re.allchar","re.all","re.++","re.union","re.inter",
                "re.*","re.+","re.opt","re.range","re.comp","re.diff"]

        self.n_op = ["*","/","div","mod"]
        self.parent = {}
    def generateSPC(self):
        try:
            assert_node = []
            for i in range(len(self.formula)):
                cmd = self.formula[i]
                if len(cmd)==0 or (cmd[1]!="assert" and cmd[1]!="assert-soft"):
                    continue
                
                formula = cmd[2]
                self.assert_idx = str(i)
                self.cnt = 0                
                _ = self.term_matching(formula,0)
                self.cnt = 0
                e,_,node = self.evaluate(formula,0)
                assert_node.append(node)
                if e is None or e is False:
                    self.terms = None
                    self.C = None
                    return
                self.cnt = 0
                _ = self.analysis(formula,0)
            return 
        except Exception as e:
            self.terms = None
            self.C = None
            trace = inspect.trace()
            fn = trace[-1].filename
            lineno = trace[-1].lineno
            return

    def term_matching(self,term,depth,parent=None):
        self.cnt+=1
        t_type = term.__class__.__name__
        term = [i for i in term if i not in ['(',')','_']]
        node = self.term_labeling(t_type,term[0],depth)
        self.parent[node] = parent
        
        if t_type == "_Operator":
            expr = "("+"(_"+" "+term[0]+" "+self.term_matching(term[1],depth+1)+")"
            expr += " "+self.term_matching(term[2],depth+1)
            expr += " "+self.term_matching(term[3],depth+1)+")"
        elif t_type == "R_Operator":
            pass
        elif len(term)>1:
            expr = "("+term[0]
            t = term[1:]
            for s in t:
                expr += " "+self.term_matching(s,depth+1,node)
            expr+=")"
        elif len(term)==1:
            expr = term[0]
        self.terms[node] = expr
        return expr

    def term_labeling(self,t_type,term,depth):
        node = term+"_"+str(self.cnt)+"_"+str(depth)
        if t_type in ["Constant","Const_String","RegLan","Bool"]:
            node = "const_"+node
        node = self.assert_idx+"_"+node
        return node

    #========================================
    @trace
    def evaluate(self,term,depth):
        self.cnt += 1
        t_type = term.__class__.__name__

        term = [i for i in term if i not in ['(',')','_']]
        node = self.term_labeling(t_type,term[0],depth)
        self.tree[node] = []
        op = term[0]
        c_terms = term[1:]
        E = []
        T = []
        N = []
        t_dict = {}
        m_dict = {}
        idx = 0
        e = None
        t = None
        for c_term in c_terms:
            e,c_type,c_node = self.evaluate(c_term,depth+1)
            self.tree[node].append([c_node,idx])
            self.parent[c_node] = node
            if e is None:
                return None,None,None
            
            E.append(e)
            T.append(c_type)
            N.append(c_node)

            if self.terms[c_node] in t_dict:
                t_dict[self.terms[c_node]] += 1
            else:
                t_dict[self.terms[c_node]] = 1
            m_dict[self.terms[c_node]] = e
            idx+=1

        if len(E) == 0:
            try:
                if t_type == "Variable":
                    if self.var_type[op]=="String":
                        self.var[self.var_type[op]].add(op)
                        self.const[self.var_type[op]].add(self.model[op])
                        for i in range(len(self.model[op][1:-1])+1):
                            self.const["Int"].add(str(i))
                    elif self.var_type[op] == "Bool":
                        self.var[self.var_type[op]].add(op)
                    elif self.var_type[op] in ["Int","Real"]:
                        self.var[self.var_type[op]].add(op)
                        self.const["Real"].add(str(float(int(float(self.model[op][0][0])))))
                        self.const["Int"].add(str(int(float(self.model[op][0][0]))))
                    e = self.model[op]
                    t = self.var_type[op]
                elif t_type == "Bool":
                    e = (op=="true")
                    t = "Bool"
                elif t_type == "Const_String":
                    self.const["String"].add(op)
                    for i in range(len(op[1:-1])+1):
                        self.const["Int"].add(str(i))
                    e = op
                    t = "String"
                elif t_type == "Constant":
                    if (self.logic&1)!=0 and (self.logic&2)!=0:
                        self.const["Real"].add(str(float(op)))
                        self.const["Int"].add(str(int(float(op))))
                        t = ("Real" if "." in term else "Int")
                    elif (self.logic&1)!=0:
                        self.const["Int"].add(str(int(float(op))))
                        t = "Real"
                    else:
                        self.const["Int"].add(str(int(float(op))))
                        t = "Int"
                    e = interval(float(op))
                elif t_type == "RegLan":
                    e,t = self.eval(op,t_type,E,T)
            except Exception as e:
                return None,None,None
        else:
            if None in E or interval() in E:
                return None,None,None
            e,t = self.eval(op,t_type,E,T,t_dict,m_dict,self.terms[N[0]])
            if e is None or (t in ["Real", "Int"] and interval()==e):
                return None,None,None
        self.E[node] = [e,t,N]
        return e,t,node

    def eval(self,op,t_type,E,T,t_dict=None,m_dict=None,f_term=None):
        if op in self.logic_op:
            e,t = eval_logic_op(op,E,T)
        elif op in self.compare_op:
            e,t = eval_cop_op(op,E,T)
        elif op in self.real_op:
            e,t = eval_real_op(op,E,T,t_dict,m_dict,f_term)
        elif op in self.int_op:
            e,t = eval_int_op(op,E,T,t_dict,m_dict,f_term)
        elif op in self.arith_op:
            e,t = eval_arith_op(op,E,T,t_dict,m_dict,f_term)
        elif op in self.string_op:
            e,t = eval_string_op(op,E,T)
        elif op in self.reg_op:
            e,t = eval_reg_op(op,E,T)
        else:
            e,t = (None,None)
        return e,t

    #========================================
    #
    # 
    #========================================
    def analysis(self,term,depth,p_node=None):
        self.cnt += 1
        t_type = term.__class__.__name__
        terms = [i for i in term if i not in ['(',')','_']]
        sterms = terms[1:]
        node = self.term_labeling(t_type,terms[0],depth)
        e,t,_ = self.E[node]

        if p_node is None:
            self.C[node] = [e,t,True]
            res = True
            for sterm in sterms:
                res = self.analysis(sterm,depth+1,node)
            return res

        p_op = p_node.split('_')[1]
        _,_,siblings = self.E[p_node]
        p_cond,_,state = self.C[p_node]

        siblings_eval = []
        midx = -1

        t_dict = {}
        e_dict = {}
        for idx in range(len(siblings)):
            snode = siblings[idx]
            if self.terms[snode] in t_dict:
                t_dict[self.terms[snode]] += 1
            else:
                t_dict[self.terms[snode]] = 1
            e_dict[self.terms[snode]] = self.E[snode][0]
            if snode == node:
                midx = idx
                continue
            siblings_eval.append(self.E[snode][0])
    
        cond = self.get_spc(t,p_op,p_cond,node,siblings_eval,e,midx,e_dict,t_dict)


        if self.logic&8!=0 and p_op in self.n_op:
            state = False

        self.C[node] = [cond,t,state] 
        res = True
        for sterm in sterms:
            res = (res&self.analysis(sterm,depth+1,node))
        return res
        
    def get_spc(self,t,p_op,p_cond,node,siblings_eval,e,midx,e_dict,t_dict):
        try:
            if p_op in self.logic_op:
                cond = analyze_logic_op(p_op,p_cond,siblings_eval,e,midx)
            elif p_op in self.compare_op:
                cond = analyze_cop_op(t,p_op,p_cond,siblings_eval,e,midx)
            elif p_op in self.real_op:
                cond = analyze_real_op(t,p_op,p_cond,self.terms[node],siblings_eval,e,midx,e_dict,t_dict)
            elif p_op in self.int_op:
                cond = analyze_int_op(t,p_op,p_cond,siblings_eval,e,midx)
            elif p_op in self.arith_op:
                cond = analyze_arith_op(t,p_op,p_cond,self.terms[node],siblings_eval,e,midx,e_dict,t_dict)
            elif p_op in self.string_op:
                cond = analyze_string_op(t,p_op,p_cond,self.terms[node],siblings_eval,e,midx,e_dict,t_dict)
            elif p_op in self.reg_op:
                cond = analyze_reg_op(t,p_op,p_cond,self.terms[node],siblings_eval,e,midx,e_dict,t_dict)
            else:
                cond = e
        except Exception as e:
            trace = inspect.trace()
            fn = trace[-1].filename
            lineno = trace[-1].lineno
            return e
        return cond

    #####
    def validate(self):
        try:
            formula = self.formula
            self.assert_idx = "0"
            self.cnt = 0                
            _ = self.term_matching(formula[0],0)
            self.cnt = 0
            e,_,_ = self.evaluate(formula[0],0)
            return e
        except Exception as e:
            trace = inspect.trace()
            fn = trace[-1].filename
            lineno = trace[-1].lineno
            return None
