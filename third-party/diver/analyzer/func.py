import inspect
import numpy as np
import math
from interval import interval,imath,fpu,inf



class Function(object):
    def __init__(self,fun_name,*args):
        self.fun_name = fun_name

    def real_function(self, x=None, y=None):
        fun_name = self.fun_name
        pi = interval(np.arctan(1)*4)

        if isinstance(x,(int,float)):
            return fun_name(x)

        evaluation = []
        if fun_name == np.arcsin:
            for si in x:
                xl,xu = si
                xl=np.arcsin(xl)
                xu=np.arcsin(xu)
                evaluation.append(interval[xl,xu])
            evaluation = interval.union(evaluation)

        return evaluation

def asin(x):
    interval_mask = interval[-1.0,1.0]
    x = interval_mask&x
    fcn = Function(np.arcsin)
    return fcn.real_function(x)

def acos(x):
    return 0.5*np.pi-asin(x)

def pow(x,y):
    try:
        evaluation = []
        for pi in x:
            pl,pu = pi
            for ei in y:
                el,eu = ei
                t1 = math.pow(pl,el)
                t2 = math.pow(pu,el)
                t3 = math.pow(pl,eu)
                t4 = math.pow(pu,eu)
                low = min(t1,t2,t3,t4)
                upp = max(t1,t2,t3,t4)
                evaluation.append(interval[low,upp])
        evaluation = interval.union(evaluation)
        return evaluation
    except Exception as e:
        return None

def arctan2(y,x):
    try:
        phi = interval(np.arctan(1)*4)
        evaluation = []
        if x > interval(0.0):
            evaluation.append(imath.atan(y/x))
        elif x < interval(0.0):
            if y>=interval(0.0):
                evaluation.append(imath.atan(y/x)+interval(phi))
            elif y<interval(0.0):
                evaluation.append(imath.atan(y/x)-interval(phi))
            else:
                return None
        elif x in interval[-1e-5,1e+5]:
            if y > interval(0.0):
                evaluation.append(interval(phi)/2.0)
            elif y < interval(0.0):
                evaluation.append(-interval(phi)/2.0)
            else:
                return None
        evaluation = interval.union(evaluation)
        return evaluation
    except Exception as e:
        return None

