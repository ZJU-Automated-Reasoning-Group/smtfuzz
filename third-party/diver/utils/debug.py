import inspect
from logging.config import dictConfig
from functools import wraps
import errno
import os
import signal


def trace(func):
    def wrapper(*args, **kwargs):
        try:
            x = func(*args, **kwargs)
            return x
        except Exception as e:
            trace = inspect.trace()
            fn = trace[-1].filename
            lineno = trace[-1].lineno
            print("Runtime error at %s,  Line : %s, Error Message : %s" % (fn, lineno, e), flush=True)
            # print(f"Args are: {args}")

    return wrapper


class TimeoutError(Exception):
    pass


def timeout(seconds=10, error_message=os.strerror(errno.ETIME)):
    def decorator(func):
        def _handle_timeout(signum, frame):
            raise TimeoutError(error_message)

        def wrapper(*args, **kwargs):
            signal.signal(signal.SIGALRM, _handle_timeout)
            signal.setitimer(signal.ITIMER_REAL, seconds)  # used timer instead of alarm
            try:
                result = func(*args, **kwargs)
            finally:
                signal.alarm(0)
            return result

        return wraps(func)(wrapper)

    return decorator
