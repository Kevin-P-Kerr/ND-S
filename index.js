// A Non-Deterministic Scheme Interpreter //

evaluate = function(exprs, env, succeed, fail) {
	if (exprs.length > 1:) {
		analyze_seq(exprs)(env, succeed, fail);
	} else {
		analyze_exp(exprs[0])(env, succeed, fail);
	}
};

analyze_seq = function(exprs) {
	sequentially = function(a, b) {
		return function (env, succeed, fail) {
			a(env, function(a_val, fail2) { b(env, succeed, fail2) }, fail);
		}
	};
	loop = function(first, rest) {
		if rest.length === 0: return first
		return loop (sequentially(first, rest[0]), rest.slice(1))
	};
	procs = exprs.map(analyze_exp);
	return loop(procs[0], procs.slice(1));
};

analyze_exp = function(expr) {
	if (self_evaluating(expr)) { return self_eval(expr) }
	if (quoted(expr)) { return quote(expr) }
	if (amb(expr)) { return analyze_amb(expr) }
	if (variable(expr)) { return analyze_var(expr) }
	if (assignment(expr)) { return assign(expr) }
	if (definition(expr)) { return  define(expr) }
	if (sif(expr)) { return analyze_if(expr) }
	if (lamb(expr)) { return analyze_lambda(expr) }
	if (begin(expr)) { return analyze_begin(expr) }
	if (cond(expr)) { return analyze_cond(expr) }
	if (nil(expr)) { return analyze_null(expr) }
	if (application(expr)) { return analyze_application(expr) }
	return ("ERROR UNKNOWN EXPRESSION");
};

isNumber = function (n) {
	return !isNan(parseFloat(n)) && isFinite(n);
};

self_evaluating = function(expr) {
	return isNumber(expr);
};

self_eval = function(expr) {
	return function(env, succeed, fail) {
		succeed(expr, fail);
	};
};

quoted = function(expr) {
	return (expr[0] === 'quoted');
};

quote = function(expr) {
	qval = expr[1];
	return function(env, succeed, fail) {
		succeed(qval, fail);
	};
};

variable = function(expr) {
	return ((! (expr instanceof Array)) && (!isNumber(expr)));
};

analyze_var = function(expr) {
	var_cont = function(env, succeed, fail) {
		if (expr in env) {
			succeed(env[expr], fail);
		} else if ('link' in env) {
			var_cont(env['link'], succeed, fail);
		} else {
			succeed("ERROR: UNKNOWN VAL", fail);
		}
	};
	return var_cont;
};

assignment = function(expr) {
	return expr[0] == 'set!';
};

assign = function(expr) {
	return function(env, succeed, fail) {
		val = analyze_exp(expr[2]);
		variable = expr[1];
		val(env, function(value, fail2) {
				tmp = env[variable];
				env[variable] = value;
				succeed("'OK", function() {
							env[variable] = tmp;
							fail2();
						});}, fail); 
		};
};

definition = function(expr) {
	return expr[0] === 'define';
};

define = function(expr) {
	return function(env, succeed, fail) {
		if (expr[1] instanceof Array) {
			name = expr[1][0];
		} else {
			name = expr[1];
		} if !(expr[1] instanceof Array) {
			val = analyze_exp(expr[2])
		} else {
			proc = [];
			proc.append(expr[1].slice(1));
			bod = [];
			bodexp = expr.slice(2);
			bodlen = (bodexp.length)-1;
			for (i=0; i<=bodlen; i++) {
				bod.append(bodexp[i]);
			} proc.append(bod);
			val = make_define_procedure(proc);
		} val(env, function(val, fail2) {
			env[name] = val;
			succeed("'OK", fail2);
			}, fail);
	};
};

make_define_procedure = function(proc) {
	return function(env, succeed, fail) {
		succeed(proc, fail);
	};
};

make_procedure = function(exp) {
	return function(env, succeed, fail) {
		params = [];
		for (i=0; i<exp[0].length; i++) {
			params.append(exp[0][i]);
		} procedure = []
		procedure.append(params)
		procedure.append(exp.slice(1)) // may contain multiple expressions
		succeed(procedure, fail);
	};
};

sif = function(expr) {
	return expr[0] === 'if';
};

analyze_if = function(expr) {
	pred = analyze_exp(expr[1]);
	consq = analyze_exp(expr[2]);
	alt = analyze_exp(expr[3]);
	return function(env, succeed, fail) {
		pred(env, function(bool, fail2) {
			if (bool) {
				consq(env, succeed, fail2);
			} else {
				alt(env, succeed, fail2);
			}
		}, fail);
	};
};

lamb = function(expr) {
	return expr[0] === 'lambda';
};

analyze_lambda = function(expr) {
	return function(env, succeed, fail) {
		proc = expr.slice(1);
		make_procedure(proc)(env, succeed, fail);
	};
};

begin = function(expr) {
	return expr[0] === 'begin';
};

analyze_begin = function(expr) {
	exps = expr.slice(1);
	sequentially = function(a, b) {
		return function(env, succeed, fail) {
			a(env, function(a_value, fail2) {
				b(env, succeed, fail2);
			}, fail);
		};
	};
	loop = function(first, rest) {
		if (rest.length === 0) {
			return first;
		} else {
			return loop(squentially(first, rest[0]), rest.slice(1));
		}
	};
	procs = exps.map(analyze_exp);
	return loop(procs[0], procs.slice(1));
};

cond = function(expr) {
	return expr[0] === 'cond'
};

analyze_cond = function(expr) {
	return "this is a stub";
};

nil = function(expr) {
	return expr[0] === 'null?';
};

analyze_null = function(expr) {
	cdr = analyze_exp(expr[1]);
	return function(env, succeed, fail) {
		cdr(env, function(bool, fail2) {
			ret = (val === []);
			succeed(ret, fail2);
		}, fail);
	};
};

application = function(expr) {
	return (expr instanceof Array);
};

analyze_application = function(expr) {
	operator = analyze_exp(expr[0]);
	operands = expr.slice(1).map(analyze_exp);
	return function(env, succeed, fail) {
		operator(env, function(proc, fail2) {
			get_args(operands, env, function(args, fail3) {
				execute_application(proc, args, env, succeed, fail3);
			}, fail2);
		}, fail);
	};
};

get_args = function(operands, env, succeed, fail) {
	len = operands.length;
	if (len === 0) {
		succeed([], fail);
	} else {
		operands[0](env, function(arg, fail2) {
			get_args(operands.slice(1), env, function(args, fail3) {
				succeed([arg, args], fail3);
			}, fail2);
		}, fail);
	}
};

execute_application = function(proc, args, env, succeed, fail){
	g = function(arg_list, nargs) {
		if arg_list.length === 0 { return null; }
		else {
			for (i=0, i<arg_list.length; i++) {
				nargs.append(arg_list[i])
			} 
		}
	};
	new_args = []
	g(args, new_args)
	args = new_args;
	if (primitive_procedure(proc)) {
		succeed(apply_prim(proc, args), fail);
	} else if (compound_procedure(proc)) {
		procedure_body(proc)(extend_env(procedure_param(proc), args, env), succeed, fail);
	} else {
		new Error ("Uknown Procedure Type");
	}
};

primitive_procedure = function(proc) {
	return (proc instanceof Function);
};

apply_prim = function(proc, args) {
	return proc(args);
};

compound_procedure = function(proc) {
	return (proc instanceof Array);
};

get_procedure_body = function(proc) {
	return proc[1];
};

procedure_body = function(proc) {
	body = get_procedure_body(proc);
	return function(env, succeed, fail) {
		evaluate(body, env, succeed, fail)
	};
};

procedure_param = function(proc) {
	return proc[0];
};

extend_env = function(param_list, args, env) {
	new_env = {};
	i = 0;
	for (n=0; n<param_list.length; n++) {
		new_env[param_list[n]] = args[i];
		i++
	} new_env['link'] = env;
	return new_env;
};

add = function(e_list) {
	z = 0;
	for (i=0; i<e_list.length; i++) {
		z += e_list[i];
	} return z;
};

minus = function(e_list) {
	z = e_list[0];
	for (i=0; i<e_list.slice(1).length; i++) {
		z -= e_list[i];
	} return z;
};

times = function(e_list) {
	z = 1;
	for (i=0; i<e_list.length; i++) {
		z *= e_list[i];
	} return z;
};

divide = function(e_list) {
	start = e_list[0];
	for (i=0; i<e_list.length; i++) {
		start /= e_list[i];
	} return start;
};

modulo = function(e_list) {
	if (e_list.length != 2) {
		return "MODULO ERROR";
	} return e_list[0] % e_list[1];
};

gt = function(e_list) {
	if (e_list.length != 2) {
		return "GT ERROR";
	} return (e_list[0] > e_list[1]);
};

gte = function(e_list) {
	if (e_list.length != 2) {
		return "GTE ERROR";
	} return (e_list[0] >= e_list[1]);
};

lt = function(e_list) {
	if (e_list.length != 2) {
		return "LT ERROR";
	} return (e_list[0] < e_list[1]);
};
	
lte = function(e_list) {
	if (e_list.length != 2) {
		return "LTE ERROR";
	} return (e_list[0] <= e_list[1]);
};
	
eq = function(e_list) {
	if (e_list.lengt != 2) {
		return "EQ ERROR";
	} return (e_list[0] === e_list[1]);
};

amb = function(expr) {
	return expr[0] === 'amb';
};

analyze_amb = function(expr) {
	e_list = expr.slice(1);
	return function(env, succeed, fail) {
		if (e_list.length === 0) {
			fail();
		} else {
			try_next = function(choices) {
				if (choices.length == 0) {
					fail();
				} else {
					next_choices = choices.slice(1);
					succeed(choices[0], function() { try_next(next_choices); });
				}
			} try_next(e_list);
		}
	};
};

no = function(e_list) {
	if (e_list.length != 1) { 
		ret = "NOT: TAKES ONE ARGUMENT";
	} else {
		ret = !e_list[0];
	} return ret;
};

lex = function(string) {
	prev = '';
	for (i=0; i<string.length; i++) {
		if (string[i] === '(') {
			charc = '( ';
			prev = prev + charc;
		} else if (string[i] === ')') {
			charc = ' )';
			prev = prev + charc;
		} else {
			prev = prev + charc;
		}
	} string = prev.split();
	return string;
};

parse = function(string) {
	index = 0;
	p_list = lex(string);
	in_list = [];
	while (p_list.length)	{
		index = process(in_list, p_list, true);
		p_list = p_list.slice(index);
	} return in_list;
};

process = function(inlis, plis, flag) {
	counter = 0;
	while (counter < plis.length) {
		if plis[counter][0] in ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'] {
			inlis.append(parseFloat(plis[counter]));
			counter++
		} else if (plis[counter][0] != '(' && plis[counter][0] != ')') {
			inlis.append(plis[counter]);
			counter++
		} else if (plis[counter][0] === '(') {
			inlis.append([]);
			counter++
			counter += process(inlis[inlis.length-1], plis.slice(counter), false);
		} else if (plis[counter][0] === ')') {
			counter++;
			return counter;
		} return counter;
	}
};

global_env = {'+': add, '-': minus, '*': times, '/': divide, '<': lt, '<=': lte, '>': gt, '>=': gte, '=': eq, 'null?': nil, 'modulo': modulo, 'not': no};
