/* ND-S: A Non-Deterministic Scheme Interpreter, JS Version.
Copyright (C) 2012 Kevin Kerr
This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>. */

evaluate = function(exprs, env, succeed, fail) {
	if (exprs.length > 1) {
		analyze_seq(exprs)(env, succeed, fail);
	} else {
		analyze_exp(exprs[0])(env, succeed, fail);
	}
};

analyze_seq = function(exprs) {
	var sequentially = function(a, b) {
		return function (env, succeed, fail) {
			a(env, function(a_val, fail2) { b(env, succeed, fail2) }, fail);
		}
	};
	var loop = function(first, rest) {
		if (rest.length === 0) { return first }
		return loop (sequentially(first, rest[0]), rest.slice(1))
	};
	var procs = exprs.map(analyze_exp);
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
	if (s_car(expr)) { return analyze_car(expr) }
	if (s_cdr(expr)) { return analyze_cdr(expr) }
	if (cons(expr)) { return analyze_cons(expr) }
	if (list(expr)) { return analyze_list(expr) }
	if (application(expr)) { return analyze_application(expr) }
	return ("ERROR UNKNOWN EXPRESSION\n");
};

isNumber = function (n) {
	return n===+n
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
	return (expr[0] === 'quote');
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
	var tmp = '';
	var var_cont = function(env, succeed, fail) {
		if (expr in env) {
			tmp = env[expr]; 
			succeed(tmp, fail);
		} else if ('link' in env) {
			var_cont(env['link'], succeed, fail);
		} else {
			succeed("ERROR: UNKNOWN VAL\n", fail);
		}
	};
	return var_cont;
};

assignment = function(expr) {
	return expr[0] == 'set!';
};

assign = function(expr) {
	return function(env, succeed, fail) {
		var val = analyze_exp(expr[2]);
		var variable = expr[1];
		val(env, function(value, fail2) {
				var tmp = env[variable];
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
		var val = '';
		if (expr[1] instanceof Array) {
			var name = expr[1][0];
		} else {
			name = expr[1];
		} if (!(expr[1] instanceof Array)) {
			val = analyze_exp(expr[2])
		} else {
			var proc = [];
			proc.push(expr[1].slice(1));
			var bod = [];
			var bodexp = expr.slice(2);
			var bodlen = (bodexp.length)-1;
			for (i=0; i<=bodlen; i++) {
				bod.push(bodexp[i]);
			} proc.push(bod);
			var val = make_define_procedure(proc);
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
		var params = [];
		for (i=0; i<exp[0].length; i++) {
			params.push(exp[0][i]);
		} procedure = []
		procedure.push(params)
		procedure.push(exp.slice(1)) // may contain multiple expressions
		succeed(procedure, fail);
	};
};

sif = function(expr) {
	return expr[0] === 'if';
};

analyze_if = function(expr) {
	var pred = analyze_exp(expr[1]);
	var consq = analyze_exp(expr[2]);
	var alt = analyze_exp(expr[3]);
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
		var proc = expr.slice(1);
		make_procedure(proc)(env, succeed, fail);
	};
};

begin = function(expr) {
	return expr[0] === 'begin';
};

analyze_begin = function(expr) {
	var exps = expr.slice(1);
	var sequentially = function(a, b) {
		return function(env, succeed, fail) {
			a(env, function(a_value, fail2) {
				b(env, succeed, fail2);
			}, fail);
		};
	};
	var loop = function(first, rest) {
		if (rest.length === 0) {
			return first;
		} else {
			return loop(squentially(first, rest[0]), rest.slice(1));
		}
	};
	var procs = exps.map(analyze_exp);
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
	var cdr = analyze_exp(expr[1]);
	return function(env, succeed, fail) {
		cdr(env, function(val, fail2) {
			ret = (val[0] === '');
			succeed(ret, fail2);
		}, fail);
	};
};

analyze_cdr = function(expr) {
	var body = analyze_exp(expr[1]);

	return function(env, succeed, fail) {
		body(env, function(val, fail2) {
			succeed(val.slice(1)[0], fail2);
		}, fail);
	};
};

s_cdr = function(expr) {
	return expr[0] === 'cdr';
};

s_car = function(expr) {
	return expr[0] === 'car';
};

analyze_car = function(expr) {
	var body = analyze_exp(expr[1]);
	
	return function(env, succeed, fail) {
		body(env, function(val, fail2) {
			succeed(val[0], fail2);
		}, fail);
	};
};

cons = function(expr) {
	return expr[0] === 'cons';
};

analyze_cons = function(expr) {
	var body = expr.slice(1).map(analyze_exp);
	return function(env, succeed, fail) {
		body[0](env, function(val, fail2) {
			body[1](env, function(val1, fail3) {
				ret_list = [];
				ret_list.push(val);
				ret_list.push(val1);
				succeed(ret_list, fail3);
			}, fail2);
		}, fail);
	};
};

list = function(expr) {
	return expr[0] === 'list';
};

analyze_list = function(expr) {
	var body = expr.slice(1).map(analyze_exp);
	var ret_list = [];
	var list_cont = function(val, fail2) {
		body = body.slice(1);
		ret_list.push(val);
		if (body.length) {
			body[0](env, list_cont, fail2);
		} else { // all the values have been pushed to ret_list
			make_list(succeed, fail2, ret_list);
		}
	};
	return function(env, succeed, fail) {
		body[0](env, function list_cont (val, fail2) {
			body = body.slice(1);
			ret_list.push(val);
			if (body.length) {
				body[0](env, list_cont, fail2);
			} else { // all the values have been pushed to ret_list
				make_list(succeed, fail2, ret_list);
			}
		}, fail)
	};
};

make_list = function(succeed, fail, pre_list) {
	var helper = function(prep_list, final_list) {
		if (prep_list.length) {
			final_list.push(prep_list[0]);
			final_list.push([]);
			helper(prep_list.slice(1), final_list[final_list.length-1]);
		} else {
			final_list.push(''); // this makes the representation of null consistent with the value produced when (quote ()) is evaluated
		}
	};
	var ret_list = [];
	helper(pre_list, ret_list);
	succeed(ret_list, fail);
};

application = function(expr) {
	return (expr instanceof Array);
};

analyze_application = function(expr) {
	var operator = analyze_exp(expr[0]);
	var operands = expr.slice(1).map(analyze_exp);
	return function(env, succeed, fail) {
		operator(env, function(proc, fail2) {
			get_args(operands, env, function(args, fail3) {
				execute_application(proc, args, env, succeed, fail3);
			}, fail2);
		}, fail);
	};
};

get_args = function(operands, env, succeed, fail) {
	var len = operands.length;
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
	var g = function(arg_list, nargs) {
		if (arg_list.length === 0) { return null; }
		else {
			for (i=0; i<arg_list.length; i++) {
				if (arg_list[i] instanceof Array) {
					g(arg_list[i], nargs);
				} else {
				nargs.push(arg_list[i])
				}
			} 
		}
	};
	var new_args = []
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
	var body = get_procedure_body(proc);
	return function(env, succeed, fail) {
		evaluate(body, env, succeed, fail)
	};
};

procedure_param = function(proc) {
	return proc[0];
};

extend_env = function(param_list, args, env) {
	var new_env = {};
	var i = 0;
	for (n=0; n<param_list.length; n++) {
		new_env[param_list[n]] = args[i];
		i++
	} new_env['link'] = env;
	return new_env;
};

add = function(e_list) {
	var z = 0;
	for (i=0; i<e_list.length; i++) {
		z += e_list[i];
	} return z;
};

minus = function(e_list) {
	var z = e_list[0];
	for (i=0; i<e_list.slice(1).length; i++) {
		z -= e_list.slice(1)[i];
	} return z;
};

times = function(e_list) {
	var z = 1;
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
	if (e_list.length != 2) {
		return "EQ ERROR";
	} return (e_list[0] === e_list[1]);
};

amb = function(expr) {
	return expr[0] === 'amb';
};

analyze_amb = function(expr) {
	var e_list = expr.slice(1);
	return function(env, succeed, fail) {
		if (e_list.length === 0) {
			fail();
		} else {
			var try_next = function(choices) {
				if (choices.length == 0) {
					fail();
				} else {
					var next_choices = choices.slice(1);
					succeed(choices[0], function() { try_next(next_choices); });
				}
			} 
			try_next(e_list);
		}
	};
};

no = function(e_list) {
	if (e_list.length != 1) { 
		var ret = "NOT: TAKES ONE ARGUMENT";
	} else {
		ret = !e_list[0];
	} return ret;
};

partition = function(string) {
	var retarr = [];
	var tmp = string.split(' ');
	for (i=0; i<tmp.length; i++) {
		if (tmp[i] === ' ') {
			continue;
		} else {
			retarr.push(tmp[i]);
		}
	}
	return retarr;
};

lex = function(string) {
	var prev = '', charc = '';
	for (i=0; i<string.length; i++) {
		if (string[i] === '(') {
			charc = '( ';
			prev = prev + charc;
		} else if (string[i] === ')') {
			charc = ' )';
			prev = prev + charc;
		} else {
			prev = prev + string[i];
		}
	} string = partition(prev);
	return string;
};

parse = function(string) {
	var index = 0,
	p_list = lex(string),
	in_list = [];
	while (p_list.length)	{
		index = proceed(in_list, p_list, true);
		p_list = p_list.slice(index);
	} return in_list;
};

proceed = function(inlis, plis, flag) {
	var counter = 0;
	while (counter < plis.length) {
		if (plis[counter][0] in ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) {
			inlis.push(parseFloat(plis[counter]));
			counter++
		} else if (plis[counter][0] != '(' && plis[counter][0] != ')') {
			inlis.push(plis[counter]);
			counter++
		} else if (plis[counter][0] === '(') {
			inlis.push([]);
			counter++
			counter += proceed(inlis[inlis.length-1], plis.slice(counter), false);
		} else if (plis[counter][0] === ')') {
			counter++;
			return counter;
		}
	} return counter;
};

global_env = {'+': add, '-': minus, '*': times, '/': divide, '<': lt, '<=': lte, '>': gt, '>=': gte, '=': eq, 'null?': nil, 'modulo': modulo, 'not': no};

driver = function() {
	var stdin = process.stdin, stdout = process.stdout;
	var succeed = function(val, alt) {
		val = String(val);
		val = val + '\n';
		stdout.write(val);
		internal_loop(alt);
	};
	var fail = function() {
		stdout.write(";;; There are no more values ;;;\n");
		driver();
	};
	var internal_loop = function(try_again) {
		stdin.resume();
		stdin.write("ND_S => ");
		stdin.once('data', function(data) {
			data = data.toString().trim();
			if (data === 'try-again') { try_again(); }
			else {
				stdout.write(";;; Starting A New Problem ;;;\n");
				feed = parse(data);
				evaluate(feed, global_env, succeed, fail);
			}
		});
	}; 
	var init = function() {
		stdout.write(";;; There is no problem to solve ;;;\n");
		driver();
	};
	internal_loop(init);
};

driver();
