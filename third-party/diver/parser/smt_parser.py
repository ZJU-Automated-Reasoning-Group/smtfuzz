# -*- coding: utf-8 -*-

from pyparsing import *
import unittest

class AST(list):
    def __eq__(self,other):
        return list.__eq__(self, other) and self.__class__ == other.__class__
    def __repr__(self):
        return '%s(%s)' % (self.__class__.__name__, list.__repr__(self))

    @classmethod
    def group(cls, expr):
        def group_action(s, l, t):
            try:
                lst = t[0].asList()
            except (IndexError, AttributeError):
                lst = t
            return [cls(lst)]

        return Group(expr).setParseAction(group_action)

    def get_query(self):
        raise NotImplementedError()

class Variable(AST) : pass
class Bool(AST) : pass
class Constant(AST) : pass
class RegLan(AST) : pass 
class Const_String(AST) : pass

class FOperator(AST) : pass
class BOperator(AST) : pass
class SOperator(AST) : pass
class ROperator(AST) : pass
class R_Operator(AST) : pass
class Operator(AST) : pass 
class _Operator(AST) : pass

class Letstmt(AST) : pass
class Bind_Var(AST) : pass
class Bind_List(AST) : pass

ASSERT_ = Keyword('assert')
ASSERT_SOFT_ = Keyword('assert-soft')
CHECK_SAT_ = Keyword('check-sat')
SET_LOGIC_ = Keyword('set-logic')
ECHO_ = Keyword('echo')
EXIT_ = Keyword('exit')
GET_ASSERTIONS_ = Keyword('get-assertions')
GET_INFO_ = Keyword('get-info')
GET_MODEL_ = Keyword('get-model')
GET_OPTION_ = Keyword('get-option')
GET_PROOF_ = Keyword('get-proof')
GET_UNSAT_ASSUMPTIONS_ = Keyword('get-unsat-assumptions')
GET_UNSAT_CORE_ = Keyword('get-unsat-core')
POP_ = Keyword('pop')
PUSH_ = Keyword('push')
RESET_ = Keyword('reset')
RESET_ASSERTIONS_ = Keyword('reset-assertions')
SET_INFO_ = Keyword('set-info')
SET_LOGIC_ = Keyword('set-logic')
SET_OPTION_ = Keyword('set-option')
DECLARE_FUN = Keyword('declare-fun')
DECLARE_CONST = Keyword('declare-const')
DEFINE_FUN = Keyword('define-fun')
GET_VALUE_ = Keyword('get-value')
MAXIMIZE_ = Keyword('maximize')
MINIMIZE_ = Keyword('minimize')

NL = Suppress(LineEnd())
TAP = Suppress(Literal('\t'))
Logic_ = (Keyword('QF_LIA') | Keyword('QF_NIA') | Keyword('QF_NRA') | Keyword('QF_NIRA') | Keyword('QF_NRA_ODE') | Keyword('QF_LRA') | Keyword('QF_RDL') | Keyword('ALL') | Keyword('QF_S') | Keyword('QF_SLIA') | Keyword('QF_IDL') | Keyword('QF_LIRA'))
 
TRUE_ = Keyword('true')
FALSE_ = Keyword('false')


Type_ = (Keyword('Real') | Keyword('Int') | Keyword('Bool') | Keyword('Binary') | Keyword('String') | Keyword('RegLan') | Keyword('(RegEx String)'))
lp = Literal('(')
rp = Literal(')')
lbr = Suppress(Literal('['))
rbr = Suppress(Literal(']'))


INT_TOKEN = Regex(r'[-+]?(0|[1-9][0-9]*)') 
HEXADECIMAL_TOKEN = Regex(r'#x[0-9A-Fa-f]+') 
DOUBLE_TOKEN = Regex(r'[-+]?[0-9]+(\.[0-9]*)([eE][-+]?[0-9]+)?')
BINARY_TOKEN = Regex(r'#b[01]+') 
STRING_TOKEN = Regex(r'"([0-9a-zA-Z]|[\\_:+%&\?\-*/=\.,<>@{}^`\[\]\(\)\|#$%^;&!\'~]| )*"') | Keyword('" "') | Keyword('""')

SIMPLE_SYMBOL_TOKEN = Regex(r'[a-zA-Z~!@$%\^&*_+=<>\.?/\#-][0-9a-zA-Z~!@$%\^&*_+=<>\.?/\#-]*')
QUOTED_SYMBOL_TOKEN = Regex(r'\|[0-9a-zA-Z~!@$%\^&*_+=<>\.?/\-#]*\|')
SYMBOL_TOKEN = (SIMPLE_SYMBOL_TOKEN | QUOTED_SYMBOL_TOKEN)
STRING = Regex(r'"?([0-9a-zA-Z]|[_:+\-*/=\.\\,<>@{}\[\]\|#$%^&\'~])+"?')

SET_INFO_SYMBOL = Regex(r'("|\|)*([0-9a-zA-Z]|[_":+\-*/=\.,<>@{}\[\]\(\)#$%^&\'~])+([0-9a-zA-Z]|[_":+\-*/=\.,<>@{}\[\]#$%^&\'~])("|\|)*')
SET_INFO_SYMBOL_LIST = Forward()
SET_INFO_SYMBOL_LIST << (SET_INFO_SYMBOL+SET_INFO_SYMBOL_LIST | SET_INFO_SYMBOL)
#=============================================================

restOfLineNL = restOfLine + NL
COMMENT = (Literal(';')+restOfLineNL)
#=============================================================

VAR_BINDING = lp+SYMBOL_TOKEN

FORMULA = Forward()
VAR_BINDING_TOKEN = lp+Bind_Var.group(SYMBOL_TOKEN)+FORMULA+rp
VAR_BINDING_LIST_TOKEN = OneOrMore(VAR_BINDING_TOKEN)
LET_BINDING_LIST_TOKEN = Bind_List.group(lp+VAR_BINDING_LIST_TOKEN+rp)

FROMULA_LIST = OneOrMore(FORMULA)

FORMULA<<(COMMENT | Bool.group(FALSE_) | Bool.group(TRUE_) |
        Constant.group(HEXADECIMAL_TOKEN) | Constant.group(DOUBLE_TOKEN) | Constant.group(INT_TOKEN) |
        Const_String.group(STRING_TOKEN) | 
        #=============================dReal==========================
        Operator.group(lp+Keyword('pow')+FORMULA+FORMULA+rp) |
        Operator.group(lp+Literal('^')+FORMULA+FORMULA+rp) |
        Operator.group(lp+Keyword('sqrt')+FORMULA+rp) |
        Operator.group(lp+Keyword('max')+FORMULA+FORMULA+rp) |
        Operator.group(lp+Keyword('min')+FORMULA+FORMULA+rp) |
        Operator.group(lp+Keyword('tanh')+FORMULA+rp) |
        Operator.group(lp+Keyword('cosh')+FORMULA+rp) |
        Operator.group(lp+Keyword('sinh')+FORMULA+rp) |
        Operator.group(lp+Keyword('arctan2')+FORMULA+FORMULA+rp) |
        Operator.group(lp+Keyword('atan2')+FORMULA+FORMULA+rp) |
        Operator.group(lp+Keyword('arctan')+FORMULA+rp) |
        Operator.group(lp+Keyword('atan')+FORMULA+rp) |
        Operator.group(lp+Keyword('arccos')+FORMULA+rp) |
        Operator.group(lp+Keyword('acos')+FORMULA+rp) |
        Operator.group(lp+Keyword('arcsin')+FORMULA+rp) |
        Operator.group(lp+Keyword('asin')+FORMULA+rp) |
        Operator.group(lp+Keyword('csc')+FORMULA+rp) |
        Operator.group(lp+Keyword('sec')+FORMULA+rp) |
        Operator.group(lp+Keyword('cot')+FORMULA+rp) |
        Operator.group(lp+Keyword('arccsc')+FORMULA+rp) |
        Operator.group(lp+Keyword('arcsec')+FORMULA+rp) |
        Operator.group(lp+Keyword('arccot')+FORMULA+rp) |
        Operator.group(lp+Keyword('tan')+FORMULA+rp) |
        Operator.group(lp+Keyword('cos')+FORMULA+rp) |
        Operator.group(lp+Keyword('sin')+FORMULA+rp) |
        Operator.group(lp+Keyword('abs')+FORMULA+rp) |
        Operator.group(lp+Keyword('log')+FORMULA+rp) |
        Operator.group(lp+Keyword('exp')+FORMULA+rp) |
        Operator.group(Keyword('real.pi')) |
        Operator.group(lp+Keyword('/')+FORMULA+FROMULA_LIST+rp) |
        Operator.group(lp+Keyword('*')+FORMULA+FROMULA_LIST+rp) |
        Operator.group(lp+Keyword('-')+FORMULA+FROMULA_LIST+rp) |
        Operator.group(lp+Keyword('-')+FORMULA+rp) |
        Operator.group(lp+Keyword('+')+FORMULA+FROMULA_LIST+rp) |
        Operator.group(lp+Keyword('+')+FORMULA+rp) |
        Letstmt.group(lp+Keyword('let')+LET_BINDING_LIST_TOKEN+FORMULA+rp) | 
        Operator.group(lp+Keyword('div')+FORMULA+FORMULA+rp) |
        Operator.group(lp+Keyword('mod')+FORMULA+FORMULA+rp) |
        Operator.group(lp+Keyword('to_real')+FORMULA+rp) |
        Operator.group(lp+Keyword('to_int')+FORMULA+rp) |
        #==============Formula operator===============================
        FOperator.group(lp+Keyword('ite')+FORMULA+FORMULA+FORMULA+rp) |
        FOperator.group(lp+Keyword('=>')+FORMULA+FORMULA+rp) |
        FOperator.group(lp+Keyword('not')+FORMULA+rp) |
        FOperator.group(lp+Keyword('xor')+FROMULA_LIST+rp) |
        FOperator.group(lp+Keyword('or')+FROMULA_LIST+rp) |
        FOperator.group(lp+Keyword('and')+FROMULA_LIST+rp) |
        ##========Int Operator cvc5 =========================
        Operator.group(lp+Keyword('int.pow2')+FORMULA+rp) |
        _Operator.group(lp+lp+Literal('_')+Keyword('iand')+FORMULA+rp+FORMULA+FORMULA+rp) |
        ##=====String Operator Return Int or Real============================
        Operator.group(lp+Keyword('str.len')+FORMULA+rp) |
        Operator.group(lp+Keyword('str.indexof')+FORMULA+FORMULA+FORMULA+rp) |
        Operator.group(lp+Keyword('str.to_code')+FORMULA+rp) |
        Operator.group(lp+Keyword('str.to_int')+FORMULA+rp) |
        #==============return type Boolean============================
        BOperator.group(lp+Keyword('is_int')+FORMULA+rp) |
        BOperator.group(lp+Keyword('>=')+FORMULA+FROMULA_LIST+rp) |
        BOperator.group(lp+Keyword('>')+FORMULA+FROMULA_LIST+rp) |
        BOperator.group(lp+Keyword('<=')+FORMULA+FROMULA_LIST+rp) |
        BOperator.group(lp+Keyword('<')+FORMULA+FROMULA_LIST+rp) |
        BOperator.group(lp+Literal('distinct')+FORMULA+FROMULA_LIST+rp) |
        BOperator.group(lp+Literal('=')+FORMULA+FROMULA_LIST+rp) |
        ##=====String Operator Return Bool============================
        BOperator.group(lp+Keyword('str.in_re')+FORMULA+FORMULA+rp) |
        BOperator.group(lp+Keyword('str.<=')+FORMULA+FORMULA+rp) |
        BOperator.group(lp+Keyword('str.<')+FORMULA+FORMULA+rp) |
        BOperator.group(lp+Keyword('str.prefixof')+FORMULA+FORMULA+rp) |
        BOperator.group(lp+Keyword('str.suffixof')+FORMULA+FORMULA+rp) |
        BOperator.group(lp+Keyword('str.contains')+FORMULA+FORMULA+rp) |
        BOperator.group(lp+Keyword('str.is_digit')+FORMULA+rp) |
        #==============Return String Operator================================
        SOperator.group(lp+Keyword('str.++')+FORMULA+FROMULA_LIST+rp) |
        SOperator.group(lp+Keyword('str.at')+FORMULA+FORMULA+rp) |
        SOperator.group(lp+Keyword('str.substr')+FORMULA+FORMULA+FORMULA+rp) |
        SOperator.group(lp+Keyword('str.replace_all')+FORMULA+FORMULA+FORMULA+rp) |
        SOperator.group(lp+Keyword('str.replace_re_all')+FORMULA+FORMULA+FORMULA+rp) |
        SOperator.group(lp+Keyword('str.replace_re')+FORMULA+FORMULA+FORMULA+rp) |
        SOperator.group(lp+Keyword('str.replace')+FORMULA+FORMULA+FORMULA+rp) |
        SOperator.group(lp+Keyword('str.from_code')+FORMULA+rp) |
        SOperator.group(lp+Keyword('str.from_int')+FORMULA+rp) |
        SOperator.group(lp+Keyword('str.update')+FORMULA+FORMULA+FORMULA+rp) |
        SOperator.group(lp+Keyword('str.rev')+FORMULA+rp) | 
        SOperator.group(lp+Keyword('str.to_lower')+FORMULA+rp) | 
        SOperator.group(lp+Keyword('str.to_upper')+FORMULA+rp) |
        SOperator.group(lp+Keyword('str.indexof_re')+FORMULA+FORMULA+FORMULA+rp) |
        #==============Return Reglan Operator================================
        ROperator.group(lp+Keyword('str.to_re')+FORMULA+rp) |
        RegLan.group(Keyword('re.none')) |
        RegLan.group(Keyword('re.allchar')) |
        RegLan.group(Keyword('re.all')) |
        ROperator.group(lp+Keyword('re.++')+FORMULA+FROMULA_LIST+rp) |
        ROperator.group(lp+Keyword('re.union')+FORMULA+FORMULA+rp) |
        ROperator.group(lp+Keyword('re.inter')+FORMULA+FORMULA+rp) |
        ROperator.group(lp+Keyword('re.*')+FORMULA+rp) |
        ROperator.group(lp+Keyword('re.+')+FORMULA+rp) |
        ROperator.group(lp+Keyword('re.opt')+FORMULA+rp) |
        ROperator.group(lp+Keyword('re.range')+FORMULA+FORMULA+rp) |
        ROperator.group(lp+Keyword('re.comp')+FORMULA+rp) |
        ROperator.group(lp+Keyword('re.diff')+FORMULA+FORMULA+rp) |
        R_Operator.group(lp+lp+Literal('_')+Keyword('re.^')+FORMULA+rp+FORMULA+rp) |
        R_Operator.group(lp+lp+Literal('_')+Keyword('re.loop')+INT_TOKEN+INT_TOKEN+rp+FORMULA+rp) |
        Variable.group(SYMBOL_TOKEN)
        )



COMMAND_ASSERT = (lp+ASSERT_+FORMULA+rp) 
COMMAND_CHECK_SAT = (lp+CHECK_SAT_+rp)
COMMAND_DECLARE_FUN = ( (lp+DECLARE_FUN+SYMBOL_TOKEN+lp+rp+Type_+rp) | 
                        (lp+DECLARE_FUN+SYMBOL_TOKEN+Type_+lp+rp+FORMULA+rp) |
                        (lp+DECLARE_FUN+SYMBOL_TOKEN+lp+rp+Type_+lbr+FORMULA+','+FORMULA+rbr+rp) |
                        (lp+DECLARE_CONST+SYMBOL_TOKEN+Type_+rp) |
                        (lp+DECLARE_CONST+SYMBOL_TOKEN+Type_+lbr+FORMULA+','+FORMULA+rbr+rp)
                    )

COMMAND_DEFINE_FUN = (lp+DEFINE_FUN+SYMBOL_TOKEN+lp+rp+Type_+FORMULA+rp) 
COMMAND_EXIT = (lp+EXIT_+rp)
COMMAND_GET_MODEL = (lp+GET_MODEL_+rp)
COMMAND_GET_VALUE = (lp+GET_VALUE_+lp+FORMULA+rp+rp)
COMMAND_MAXIMIZE = (lp+MAXIMIZE_+FORMULA+rp)
COMMAND_MINIMIZE = (lp+MINIMIZE_+FORMULA+rp)
COMMAND_SET_INFO = ((lp+SET_INFO_+SET_INFO_SYMBOL+DOUBLE_TOKEN+rp ) |
                    (lp+SET_INFO_+SET_INFO_SYMBOL+SET_INFO_SYMBOL+rp ) |
                    (lp+SET_INFO_+SET_INFO_SYMBOL+SET_INFO_SYMBOL_LIST+rp)
                )
COMMAND_SET_LOGIC = (lp+SET_LOGIC_+Logic_+rp)
COMMAND_SET_OPTION = ((lp+SET_OPTION_+SET_INFO_SYMBOL+SET_INFO_SYMBOL+rp) |
                    (lp+SET_OPTION_+SET_INFO_SYMBOL+DOUBLE_TOKEN+rp) |
                    (lp+SET_OPTION_+SET_INFO_SYMBOL+TRUE_+rp) |
                    (lp+SET_OPTION_+SET_INFO_SYMBOL+FALSE_+rp)
                )
COMMAND_GET_OPTION = (lp+GET_OPTION_+SET_INFO_SYMBOL+rp)
COMMAND_PUSH = (lp+PUSH_+INT_TOKEN+rp)
COMMAND_POP = (lp+POP_+INT_TOKEN+rp)

COMMAND = ( COMMENT | COMMAND_ASSERT | COMMAND_CHECK_SAT | COMMAND_DECLARE_FUN | COMMAND_DEFINE_FUN |
            COMMAND_EXIT | COMMAND_GET_MODEL | COMMAND_GET_VALUE | COMMAND_MAXIMIZE | COMMAND_MINIMIZE |
            COMMAND_POP | COMMAND_PUSH | COMMAND_SET_LOGIC | COMMAND_SET_INFO | COMMAND_SET_OPTION | COMMAND_GET_OPTION    
        )

COMMAND_LIST = Forward()
COMMAND_LIST << COMMAND
listoftype = COMMAND_LIST

def transform_smt_to_ast(file):
    f = open(file,mode='r',encoding='utf-8')
    file_line = f.readlines()
    str_file = ""
    
    for line in file_line:
        str_file+=line
    
    constraint_cmd = []

    r = listoftype.scanString(str_file)
    for cmd,_,_ in r:
        if cmd == []:
            continue
        constraint_cmd.append(cmd)
    return constraint_cmd

def getTermAST(term):
    formula_token = []
    r = FROMULA_LIST.scanString(term)
    for token,_,_ in r:
        if token==[]:
            continue
        formula_token.append(token)
    
    return formula_token[0]
