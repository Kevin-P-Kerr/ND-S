### this is a non-deterministic scheme intereperter  ###
import sys

rl = sys.getrecursionlimit()

sys.setrecursionlimit(10*rl)


from numbers import Number


def evaluate(exprs, env, succeed, fail):
	if len(exprs) > 1:
		tmp =	analyze_seq(exprs)
		tmp(env, succeed, fail)
	else:
		analyze_exp(exprs[0])(env, succeed, fail)

def analyze_seq(exprs):
	def sequentially(a, b):
		def exec_seq(env, succeed, fail):
			def seq_cont(a_val, fail2):
				b(env, succeed, fail2)
			a(env, seq_cont, fail)
		return exec_seq
	def loop(first, rest):
		if len(rest) == 0: return first
		return loop(sequentially(first, rest[0]), rest[1:])
	procs = map(analyze_exp, exprs)
	return loop(procs[0], procs[1:])

def analyze_exp(expr):
	if self_evaluating(expr): return self_eval(expr)
	if quoted(expr): return quote(expr)
	if amb(expr): return analyze_amb(expr)
	if variable(expr): return var(expr)
	if assignment(expr): return assign(expr)
	if definition(expr): return define(expr)
	if sif(expr): return analyze_if(expr)
	if lamb(expr): return analyze_lambda(expr)
	if begin(expr): return analyze_begin(expr)
	if cond(expr): return analyze_cond(expr)
	if null(expr): return analyze_null(expr)
	if application(expr): return analyze_application(expr)
	return "ERROR UNKNOWN EXPRESSION"

def self_evaluating(var):
	return isinstance(var, Number)

def self_eval(expr):
	def exec_self(env, succeed, fail):
		succeed(expr, fail)
	return exec_self

def quoted(expr):
	return expr[0] == 'quote'

def quote(expr):
	qval = expr[1]
	def exec_quote(env, succeed, fail):
		succeed(qval, fail)
	return exec_quote
		
def variable(expr):
	return (not isinstance(expr, Number) and not isinstance(expr, list))

def var(expr):
	def var_cont(env, succeed, fail):
		if expr in env: succeed(env[expr], fail)
		elif 'link' in env: var_cont(env['link'], succeed, fail)
		else: succeed("Error: Unknown Val", fail)
	return var_cont

def assignment(expr):
	return expr[0] == 'set!'

def assign(expr):
	def exec_assign(env, succeed, fail):
		val = analyze_exp(expr[2])
		var = expr[1]
		def aux(val, fail2):
			tmp = env[var]
			def new_fail():
				env[var] = tmp
				fail2()
			env[var] = val
			succeed("'OK", new_fail)
		val(env, aux, fail)
	return exec_assign

def definition(expr):
	return expr[0] == 'define'

def define(expr):
	def exec_define(env, succeed, fail):
		if isinstance(expr[1], list): name = expr[1][0]
		else: name = expr[1]
		def aux(val, fail2):
			env[name] = val
			succeed('Ok', fail2)
		if not isinstance(expr[1], list):
			val = analyze_exp(expr[2])
		else: 
			proc = []
			proc.append(expr[1][1:])
			bod = []
			for var in expr[2:]:
				bod.append(var)
			proc.append(bod)
			val = make_define_procedure(proc)
		val(env, aux, fail)
	return exec_define

def make_define_procedure(proc): # There is nothing to do
	def exec_define(env, succeed, fail):
		succeed(proc, fail)
	return exec_define

def make_procedure(exp):
	def exec_make_proc(env, succeed, fail):
		params = []
		for param in exp[0]:
			params.append(param)
		procedure = []
		procedure.append(params)
		procedure.append(exp[1:]) # may contain multiple expressions
		succeed(procedure, fail)
	return exec_make_proc	

def sif(expr):
	return expr[0] == 'if'

def analyze_if(expr):
	pred = analyze_exp(expr[1])
	consq = analyze_exp(expr[2])
	alt = analyze_exp(expr[3])
	def exec_if(env, succeed, fail):
		def if_cont(predicate, fail2):
			if predicate: consq(env, succeed, fail2)
			else: alt(env, succeed, fail2)
		pred(env, if_cont, fail)
	return exec_if

def lamb(expr):
	return expr[0] == 'lambda'

def analyze_lambda(expr):
	def exec_lambda(env, succeed, fail):
		proc = expr[1:]
		make_procedure(proc)(env, succeed, fail)
	return exec_lambda

def begin(expr):
	return expr[0] == 'begin'

def analyze_begin(expr):
	exps = expr[1:]
	def sequentially(a, b):
		def exec_begin(env, succeed, fail):
			def seqcont(a_value, fail2):
				b(env, succeed, fail2)
			a(env, seqcont, fail)
		return exec_begin
	def loop(first, rest):
		if len(rest) == 0: return first
		loop(sequentially(first, rest[0]), rest[1:])
	procs = map(analyze_expr, exps)
	if len(procs) == 0: raise Exception ("ERROR ON BEGIN")
	return loop(procs[0], procs[1:])

def cond(expr):
	return expr[0] == 'cond'

def analyze_cond(expr):
	return "stub"

def null(expr):
	return expr[0] == 'null?'

def analyze_null(expr):
	cdr = analyze_exp(expr[1])
	def exec_null(env, succeed, fail):
		def null_cont(val, fail2):
			ret = val == []
			succeed(ret, fail2)
		cdr(env, null_cont, fail)
	return exec_null

def application(expr):
	return isinstance(expr, list)

def analyze_application(expr):
	operator = analyze_exp(expr[0])
	operands = map(analyze_exp, expr[1:])
	def appl(env, succeed, fail):
		def appl_cont(proc, fail2):
			def appl_cont2(args, fail3):
				execute_application(proc, args, env, succeed, fail3)
			get_args(operands, env, appl_cont2, fail2)
		operator(env, appl_cont, fail)
	return appl

def get_args(operands, env, succeed, fail):
	def gac(arg, fail2):
		def regac(args, fail3):
			succeed(list((arg, args)), fail3)
		get_args(operands[1:], env, regac, fail2)
	if len(operands) == 0: succeed([], fail)
	else:
		operands[0](env, gac, fail)

def execute_application(proc, args, env, succeed, fail):
	def gargs(arg_list, nargs):
		if len(arg_list) == 0: return None
		else:
			for arg in arg_list:
				if isinstance(arg, list): gargs(arg, nargs)
				else: nargs.append(arg)

	new_args = []
	gargs(args, new_args)
	args = new_args
	if primitive_procedure(proc): succeed(apply_prim(proc, args), fail)
	elif compound_procedure(proc):
		procedure_body(proc) (extend_env(procedure_param(proc), args, env), succeed, fail)
	else: 
		raise Exception ("Unknown Procedure Type")

def primitive_procedure(proc):
	return callable(proc)

def apply_prim(proc, args):
	return proc(args)

def compound_procedure(proc):
	return isinstance(proc, list)

def get_procedure_body(proc):
	return proc[1]

def procedure_body(proc):
	body = get_procedure_body(proc)
	def exec_proc(env, succeed, fail):
		evaluate(body, env, succeed, fail)
	return exec_proc

def procedure_param(proc):
	return proc[0]

def extend_env(param_list, args, env):
	new_env = {}
	i = 0
	for param in param_list:
		new_env[param] = args[i]
		i += 1
	new_env['link'] = env
	return new_env

def add(e_list):
	z = 0
	for x in e_list:
		z+=x
	return z

def minus(e_list):
	z = e_list[0]
	for x in e_list[1:]:
		z-=x
	return z

def times(e_list):
	z = 1
	for x in e_list:
		z*=x
	return z

def divide(e_list):
	new_list = []
	for x in e_list:
		new_list.append(float(x))
	start = new_list[0]
	for y in new_list[1:]:
		start /= y
	return start

def modulo(e_list):
	if len(e_list) != 2: return "MODULO ERRRO"
	return e_list[0] % e_list[1]

def gt(e_list):
	if len(e_list) != 2: raise Exception ("K-NDS: >: 2 ARGS EXACTLY")
	return (e_list[0] > e_list[1])

def gte(e_list):
	if len(e_list) != 2: raise Exception ("K-NDS: >: 2 ARGS EXACTLY")
	return (e_list[0] >= e_list[1])

def lt(e_list):
	if len(e_list) != 2: ret  = "K-NDS: >: 2 ARGS EXACTLY"
	else: ret = e_list[0] < e_list[1]
	return ret

def lte(e_list):
	if len(e_list) != 2: ret =  "K-NDS: >: 2 ARGS EXACTLY"
	else: ret = e_list[0] <= e_list[1]
	return ret

def eq(e_list):
	if len(e_list) != 2: 
		ret = "K-NDS: >: 2 ARGS EXACTLY"
	else: ret = e_list[0] == e_list[1]
	return ret

def let(expr):
	return expr[0] == 'let'

def analyze_let(expr):
	assignments = expr[1]
	body = analyze_exp(expr[2])
	def exec_let(env, succeed, fail):
		def let_cont2(val, fail3):
			body(env, succeed, fail3)
		get_assignments(assignments, env, let_cont2, fail)
	return exec_let

def get_assignments(assignments, env, succeed, fail):
	return "stub"	

def amb(expr):
	return expr[0] == 'amb'
		
def analyze_amb(expr):
	e_list = expr[1:]
	def amb_exec(env, succeed, fail):
		if len(e_list) == 0: fail()
		else:
			def try_next(choices):
					if len(choices) == 0: fail()
					else:
						next_choices = choices[1:]
					succeed(choices[0], lambda: try_next(next_choices))
			try_next(e_list)
	return amb_exec

def require(e_list, env, succeed, fail):
	evaluated_list = []
	retcon = make_eval_cont(evaluated_list)
	evaluate([0], env, retcon, fail)
	if evaluated_list[0]: evaluate(e_list[1], env, succeed, fail)
	else:
		fail()

def conj(e_list, env, succeed, fail):
	if len(e_list) != 2: ret = "AND: 2 ARGS EXACTLY"
	else:
		evaluated_list = []
		retcont = make_eval_cont(evaluated_list)
		for exp in e_list:
			evaluate([exp], env, retcont, fail)
		ret = (evaluated_list[0] and evaluated_list[1])
	succeed(ret, fail)

def disj(e_list, env, succeed, fail):
	if len(e_list) != 2: ret = "OR: 2 ARGS EXACTLY"
	else:
		evaluated_list = []
		retcont = make_eval_cont(evaluated_list)
		for exp in e_list:
			evaluate([exp], env, retcont, fail)
		ret = (evaluated_list[0] or evaluated_list[1])
	succeed(ret, fail)

def no(e_list):
	if len(e_list) != 1: ret = "NOT: Takes One Argument"
	else: ret = not e_list[0]
	return ret

def make_list(e_list, env, succeed, fail):
	evaluated_list = []
	retcon = make_eval_cont(evaluated_list)
	for exp in e_list:
		evaluate([exp], env, retcon, fail)
	ret_list = []
	hold = ret_list
	mark = len(e_list)-1
	i = 1
	ret_list.append(evaluated_list[0])
	ret_list.append([])
	for var in evaluated_list[1:mark]:
		ret_list[i].append(var)
		ret_list[i].append([])
		ret_list = ret_list[i]
	ret_list[i].append(evaluated_list[len(evaluated_list)-1])
	ret_list[i].append([])

	succeed(hold, fail)

def cons(e_list, env, succeed, fail):
	if len(e_list) != 2: ret = "CONS ERROR"
	else:
		evaluated_list = []
		retcon = make_eval_cont(evaluated_list)
		evaluate([e_list[0]], env, retcon, fail)
		evaluate([e_list[1]], env, retcon, fail)
		ret = [evaluated_list[0], evaluated_list[1]]
		succeed(ret, fail)

def car(e_list, env, succeed, fail):
	evaluated_list = []
	retcon = make_eval_cont(evaluated_list)
	evaluate([e_list[0]], env, retcon, fail)
	succeed(evaluated_list[0][0], fail)

def cdr(e_list, env, succeed, fail):
	evaluated_list = []
	retcon = make_eval_cont(evaluated_list)
	evaluate([e_list[0]], env, retcon, fail)
	succeed(evaluated_list[0][1], fail)

def lex(string):
	prev = ''
	for char in string:
		if char == '(':
			char = '( '
			prev = prev + char
		elif char == ')':
			char = ' )'
			prev = prev + char
		else:  prev = prev + char
	string = prev.split()
	return string

def parse(string):
	index = 0
	p_list = lex(string)
	in_list = []
	while len(p_list):
		index = process(in_list, p_list, True)
		p_list = p_list[index:]
	return in_list

def process(inlis, plis, flag):
	counter = 0
	while counter < len(plis):	
		if plis[counter][0] in ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']: 
			inlis.append(int(plis[counter]))
			counter += 1
		elif plis[counter][0] != '(' and plis[counter][0] != ')': 
			inlis.append(plis[counter])
			counter += 1
		elif plis[counter][0] == '(':
			inlis.append([])
			counter += 1
			counter += process(inlis[len(inlis)-1], plis[counter:], False)
		elif plis[counter][0] == ')':
			counter+=1
			return counter
	return counter
		
global_env = {'+' : add, '-' : minus, '*' :  times, '/' : divide, '<': lt, '<=': lte, '>' : gt, '>=' : gte, '=': eq, 'inc' : [['x'], ['+', 'x', 1]], 'null?' : null, 'modulo' : modulo, 'not': no}
"""
plus_test = ['+', 1, ['+', 2, 3]]
minus_test = ['-', 9, ['+', 3, 3]]
times_test = ['*', plus_test, minus_test]
division_test = ['/', times_test, 6]
assert evaluate(plus_test, global_env) == 6
assert evaluate(minus_test, global_env) == 3
assert evaluate(times_test, global_env) == 18
assert evaluate(division_test, global_env) == 3
assert evaluate(['/', 3, 2], global_env) == 1.5
assert evaluate(['<', division_test, 2], global_env) == False
assert evaluate(['<=', 3, 2], global_env) == False
assert evaluate(['>=', 3, 2], global_env) == True
assert evaluate(['>', 3, 3], global_env) == False
assert evaluate(['=', 3, 3], global_env) == True
"""
#def intsuc(val, fail):
#	return None
#def intfail():
#	print "fail"
#
#m = parse("(define (map proc alist) (if (null? alist) (quote ()) (cons (proc (car alist)) (map proc (cdr alist)))))")
#evaluate(m, global_env, intsuc, intfail)
#n = parse("(define (filter pred alist) (cond ((null? alist) (quote ())) ((pred (car alist)) (cons (car alist) (filter pred (cdr alist)))) (else (filter pred (cdr alist)))))")
#evaluate(n, global_env, intsuc, intfail)

def driver():
	def succeed(val, alt):
		print val
		internal_loop(alt)
	def fail():
		print ";;; There are no more values ;;;"
		driver()
	def internal_loop(try_again):
		ip = raw_input('ND-S => ')
		if ip == "try-again": try_again()
		else:
			print ";;; Starting a new problem ;;;"
			feed = parse(ip)
			evaluate(feed, global_env, succeed, fail)
	def init():
		print ";;; There is no problem to solve ;;;"
		driver()

	internal_loop(init)

driver()


#while True:
#	try:
#		s = raw_input('ND-S => ')
#	except EOFError: break
#	if not s: continue
#	result = parse(s)
#	print evaluate(result, global_env)

#test = [['if', ['<', 2, 3], ['+', 2, 3], ['-', 2, 3]]]
#print evaluate(test, global_env)
#print evaluate(parse("(adder 3)"), global_env)
#print parse("((lambda (x) (+ x 1)) 2)")
#print evaluate([[['lambda', ['x'], ['+', 'x', 1]], 2]], global_env)

#evaluate ([['or', 2, 3]], global_env)

#print(evaluate(parse("(+ 2 2)"), global_env))
#print(evaluate(parse("(+ 2 (/ 3 2))"), global_env))
