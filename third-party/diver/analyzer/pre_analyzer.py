import inspect
from parser.smt_parser import *
from analyzer.constraintRule import *
from utils.solver import *
from utils.z3Interface import *
from utils.cvc5Interface import *


class PreAnalyzer(object):
    def __init__(self, seed, ast, var_dict, model, logic, data, solver):
        self.seed = seed
        self.solver = solver
        self.s_data = data
        self.model = model

        self.const = {"Int":set(),"String":set(),"Real":set()}
        self.var = {"Int":set(),"String":set(),"Real":set(),"Bool":set()}
        self.ast = ast
        self.var_dict = var_dict
        #self.model = model
        self.logic = get_logic(logic)
        self.line = "0"
        self.constraints = {} # node to sat-preserving constraint
        self.evaluations = {} # node to evaluation results 
        self.api_terms = {}

        self.cnt = 0
        self.terms = {}
        self.tree = {}
        self.parent = {}
        
        self.term_type = ["Constant","Const_String","RegLan","Bool","Variable",
                        "FOperator","BOperator","SOperator","ROperator","Operator","R_Operator","_Operator"]
        
        self.logic_op = ["and","or","xor","=>","not","ite"]
        self.eq_op = ["=","distinct"]
        self.compare_op = [">=",">","<","<="]

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

        self.return_re_op = ["str.to_re","re.none","re.all","re.allchar","re.++","re.union","re.inter","re.*","re.comp",
            "re.diff","re.+","re.range", "re.^","re.loop","re.opt"]

        self.n_op = ["re.range"]

    def pre_analysis(self):
        
        res = False
        formula_node = []   
        for i in range(len(self.ast)):
            cmd = self.ast[i]
            if len(cmd) == 0 or ("assert" not in cmd[1]):
                continue
            
            formula = cmd[2]
            self.line = str(i)
            self.cnt = 0
            _ = self.matching(formula,0)
            self.cnt = 0
            node, cur_eval, _, _ = self.evaluate(formula,0)
            if cur_eval is None:
                return "Fail",None
            self.cnt = 0
            succ = self.get_constraint(formula,0)
            res = True
            if not(succ):
                return "Fail",None

        seed_info = {"var": self.var, "const":self.const, "term": self.terms, "evaluation" : self.evaluations, "constraints": self.constraints, }
        if res:
            return "Succ",seed_info
        else:
            return "Fail", seed_info

    def get_constraint(self, term, depth, p_node = "root-node"):
        self.cnt += 1
        ty = term.__class__.__name__
        tmp_term = [i for i in term if i not in ['(',')','_']]
        node = self.labeling(ty, tmp_term[0],depth)
        op = tmp_term[0]
        sub_terms = tmp_term[1:]
        res = True
        cur_eval, cur_ty = self.evaluations[node]
        if p_node == "root-node":
            self.constraints[node] = [is_true(cur_eval),cur_ty, cur_eval, True] # constraint, type, evaluation, possibility for mutation
        else:
            parent_op = '_'.join(p_node.split('_')[1:-2])
            p_sub_nodes = self.tree[p_node]
            idx = -1
            state = True
            sub_evaluations = []
            sub_api_terms = []
            sub_asts = []
            for i in range(len(p_sub_nodes)):
                sub_node = p_sub_nodes[i]
                if sub_node == node:
                    idx = i
                    continue
                sub_evaluations.append(self.evaluations[sub_node][0])
                sub_api_terms.append(self.api_terms[sub_node])

            if parent_op in self.n_op:
                state = False
            
            parent_cond = self.constraints[p_node][0]
            #print(self.constraints[p_node][1],parent_cond)
            cond = self.sat_preserving_constraint(parent_op, parent_cond, cur_eval, cur_ty, idx, sub_evaluations, sub_api_terms)
            self.constraints[node] = [cond, cur_ty, cur_eval, state]

        for sub in sub_terms:
            res = (res&self.get_constraint(sub, depth+1, node))
        return res

    def evaluate(self,term,depth):
        self.cnt += 1
        ty = term.__class__.__name__
        tmp_term = [i for i in term if i not in ['(',')','_']]
        node = self.labeling(ty,tmp_term[0],depth)
        self.tree[node] = []
        op = tmp_term[0]
        sub_terms = tmp_term[1:]
        nodes = [] # nodes of sub terms
        evaluations = [] # evaluation results of sub terms
        types = [] # types of sub terms
        solver_terms = [] # solver asts of sub terms


        for sub in sub_terms:
            sub_node, evaluation, sub_type, sub_solver_ast = self.evaluate(sub,depth+1)
            self.tree[node].append(sub_node)
            self.parent[sub_node] = node

            nodes.append(sub_node)
            evaluations.append(evaluation)
            types.append(sub_type)
            solver_terms.append(sub_solver_ast)
        

        cur_eval, cur_ty, cur_ast = self.get_evaluation(term, solver_terms)
        if ty == "Variable":
            self.var[cur_ty].add(op)
            
            if cur_ty == "Real":
                if (self.solver == "z3" and not(is_algebraic_value(cur_eval))):
                    if "/" in str(cur_eval):
                        tmp = str(cur_eval).split("/")
                        if "e" in str(float(tmp[0])/float(tmp[1])):
                            pass
                        else:
                            self.const["Real"].add(str(float(tmp[0])/float(tmp[1])))
                    else:
                        if str(cur_eval)==op:
                            pass
                        else:
                            self.const["Real"].add(str(float(str(cur_eval))))
                #elif (self.solver == "cvc" and not()):
            elif cur_ty == "Int":
                tmp_eval = str(cur_eval)
                self.const["Int"].add(str(tmp_eval))
            elif cur_ty == "String":
                if self.solver == "z3":
                    self.const["String"].add(cur_eval.sexpr())
                else:
                    self.const["String"].add(str(cur_eval))
                for i in range(len(str(cur_eval))):
                    self.const["Int"].add(str(i+1))
        elif ty == "Const_String":
            self.const["String"].add(op)
            for i in range(len(op[1:-1])+1):
                self.const["Int"].add(str(i))
        elif ty == "Constant":                
            if (self.logic&1)!=0 and (self.logic&2)!=0:
                self.const["Real"].add(str(float(op)))
                self.const["Int"].add(str(int(float(op))))
            elif (self.logic&1)!=0:
                self.const["Real"].add(str(int(float(op))))
            else:
                self.const["Int"].add(str(int(float(op))))
            
        self.evaluations[node] = [cur_eval, cur_ty] # evaluation * type pair
        self.api_terms[node] = cur_ast

        return node, cur_eval, cur_ty, cur_ast

        
    def sat_preserving_constraint(self,parent_op,parent_cond,cur_eval,cur_type,node_idx,sub_evaluations, sub_api_terms):
        try:
            cond = cur_eval
            if parent_op in self.logic_op and parent_op != "ite":
                if self.solver == "z3":
                    cur_eval = is_true(cur_eval)
                    for idx in range(len(sub_evaluations)):
                        sub_evaluations[idx] = is_true(sub_evaluations[idx])
                elif self.solver == "cvc":
                    cur_eval = (str(cur_eval)=="true")
                    for idx in range(len(sub_evaluations)):
                        sub_evaluations[idx] = (str(sub_evaluations[idx])=="true")
                cond = get_logic_constraint(parent_op, parent_cond, cur_eval, cur_type,node_idx, sub_evaluations)
            elif parent_op == "ite":
                if cur_type == "Bool":
                    if self.solver == "z3":
                        cur_eval = is_true(cur_eval)
                    elif self.solver =="cvc":
                        cur_eval = (str(cur_eval)=="true")
                cond = get_logic_constraint(parent_op, parent_cond, cur_eval, cur_type, node_idx, sub_evaluations)
            elif parent_op in self.eq_op:
                if self.solver == "z3":
                    if cur_type == "Bool":
                        cur_eval = is_true(cur_eval)
                        for idx in range(len(sub_evaluations)):
                            sub_evaluations[idx] = is_true(sub_evaluations[idx])
                    elif cur_type == "String":
                        cur_eval = str(cur_eval)
                        for idx in range(len(sub_evaluations)):
                            sub_evaluations[idx] = str(sub_evaluations[idx])
                elif self.solver == "cvc":
                    if cur_type == "Bool":
                        cur_eval = (str(cur_eval)=="true")
                        for idx in range(len(sub_evaluations)):
                            sub_evaluations[idx] = (str(sub_evaluations[idx])=="true")
                    elif cur_type == "String":
                        cur_eval = str(cur_eval)
                        for idx in range(len(sub_evaluations)):
                            sub_evaluations[idx] = str(sub_evaluations[idx])
                cond = get_eq_constraint(parent_op, parent_cond, cur_eval, cur_type, node_idx, sub_evaluations)    
            elif parent_op in self.compare_op:
                cond = get_compare_constraint(parent_op,parent_cond, cur_eval, cur_type, node_idx, sub_evaluations, sub_api_terms, self.solver, self.model)
            elif parent_op in self.real_op:
                cond = get_real_constraint(parent_op,parent_cond, cur_eval, cur_type, node_idx, sub_evaluations, sub_api_terms, self.solver, self.model)
            elif parent_op in self.int_op:
                cond = get_int_constraint(parent_op,parent_cond, cur_eval, cur_type, node_idx, sub_evaluations, sub_api_terms, self.solver, self.model)
            elif parent_op in self.arith_op:
                cond = get_arith_constraint(parent_op,parent_cond, cur_eval, cur_type, node_idx, sub_evaluations, sub_api_terms, self.solver, self.model)
            elif parent_op in self.string_op:
                cond = get_string_constraint(parent_op,parent_cond, cur_eval, cur_type, node_idx, sub_evaluations, sub_api_terms, self.solver, self.model)
            elif parent_op in self.reg_op:
                cond = get_regp_constraint(parent_op,parent_cond, cur_eval, cur_type, node_idx, sub_evaluations, sub_api_terms, self.solver, self.model)
            return cond
        except Exception as e:
            print("During obtaining sat-preserving constraint: file {} - {}".format(self.seed,parent_op))
            trace = inspect.trace()
            fn = trace[-1].filename
            lineno = trace[-1].lineno 
            print("line : {}, function {}, error message {}".format(lineno,fn,e))
            return cur_eval


    def get_evaluation(self,term, subs):
        if self.solver == "z3":
            z3_ast = ast_to_z3(term,self.s_data,self.logic, subs)
            if z3_ast is None:
                return None, None, None

            evaluation = self.model.eval(z3_ast)
            ty = None
            if is_bool(evaluation):
                ty = "Bool"
            elif is_int(evaluation):
                ty = "Int"
            elif is_real(evaluation):
                ty = "Real"
            elif is_string(evaluation):
                ty = "String"
            elif is_re(evaluation):
                ty = "RegLan"

            return evaluation, ty, z3_ast
        elif self.solver == "cvc":
            cvc5_ast = ast_to_cvc5(term, self.model, self.s_data, self.logic, subs)
            if cvc5.Sort.isBoolean(cvc5.Term.getSort(cvc5_ast)):
                ty = "Bool"
            elif cvc5.Sort.isInteger(cvc5.Term.getSort(cvc5_ast)):
                ty = "Int"
            elif cvc5.Sort.isReal(cvc5.Term.getSort(cvc5_ast)):
                ty = "Real"
            elif cvc5.Sort.isString(cvc5.Term.getSort(cvc5_ast)):
                ty = "String"
            elif cvc5.Sort.isRegExp(cvc5.Term.getSort(cvc5_ast)):
                ty = "RegLan"
                return cvc5_ast, ty, cvc5_ast
            evaluation = self.model.getValue(cvc5_ast)
            return evaluation, ty, cvc5_ast
        else:
            return None, None, None

    def matching(self, term, depth, parent = None):
        self.cnt += 1
        ty = term.__class__.__name__
        tmp_term = [i for i in term if i not in ['(',')','_']]
        node = self.labeling(ty, tmp_term[0], depth)
        self.parent[node] = parent
        
        if ty == "_Operator":
            expr = "("+"(_"+" "+term[0]+" "+self.matching(tmp_term[1],depth+1, node)+")"
            expr +=" "+self.matching(tmp_term[2],depth+1, node)
            expr +=" "+self.matching(tmp_term[3],depth+1, node)+")"
        elif ty == "R_Operator":
            if term[0] == "re.^":
                expr = "("+"(_"+" "+term[0]+" "+self.matching(tmp_term[1],depth+1, node)+")"
                expr +=" "+self.matching(tmp_term[2],depth+1, node)+")"
            elif term[0] == "re.loop":
                expr = "("+"(_"+" "+term[0]+" "+self.matching(tmp_term[1],depth+1, node)
                expr +=" "+self.matching(tmp_term[2],depth+1, node)+")"
                expr +=" "+self.matching(tmp_term[3],depth+1, node)+")"
            else:
                return "None"
        elif len(tmp_term)>1:
            expr = "("+tmp_term[0]
            t = tmp_term[1:]
            for s in t:
                expr += " "+self.matching(s,depth+1,node)
            expr+=")"
        elif len(tmp_term) == 1:
            expr = tmp_term[0]
        else:
            return "None"

        if "None" in expr:
            return "None"
        
        self.terms[node] = expr
        return expr

    def labeling(self,ty,term, depth):
        node = term+"_"+str(self.cnt)+"_"+str(depth)
        if ty in ["Constant","Const_String","RegLan","Bool"]:
            node = "const_"+node
        node = self.line+"_"+node
        return node