/**
 * @fileOverview small lisp implementation written in javascript
 * @name mispli
 * @author mooz <stillpedant@gmail.com>
 * @license The MIT License
 */

var Mispli =
    (function () {
         // ====================================================================== //
         // Class variables (private)
         // ====================================================================== //

         var globalEnv = {};
         var localEnvs = [];
         var builtins  = {};
         var specials  = {};
         var macros    = {};

         const ATOM_SYMBOL = 1;
         const ATOM_STRING = 2;
         const ATOM_NUMBER = 3;

         const SYM_VARIABLE = 1;
         const SYM_FUNCTION = 2;
         const SYM_CONSTANT = 3;

         var symTrue = intern("t");
         setSymbolValue(symTrue, SYM_CONSTANT, symTrue);

         var symNil = intern("nil");
         setSymbolValue(symNil, SYM_CONSTANT, symNil);

         var boxBool = {
             "true"  : symTrue,
             "false" : symNil
         };

         // often used symbols (not interned)
         var symLambda   = createSymbol('lambda');
         var symProgn    = createSymbol('progn');
         var symQuote    = createSymbol('quote');
         var symFunction = createSymbol('function');
         var symRest     = createSymbol('&rest');
         var symOptional = createSymbol('&optional');
         var symKey      = createSymbol('&key');

         // ====================================================================== //
         // Atom
         // ====================================================================== //

         function createAtom(type, name, value) {
             return {
                 type  : type,
                 name  : name,
                 value : value
             };
         }

         function createString(value) { return createAtom(ATOM_STRING, null, value); }
         function createNumber(value) { return createAtom(ATOM_NUMBER, null, value); }
         function createSymbol(name)  { return createAtom(ATOM_SYMBOL, name); }

         // ====================================================================== //
         // Symbol
         // ====================================================================== //

         function intern(name, context) {
             context = context || globalEnv;
             if (!(name in context))
             {
                 context[name] = createSymbol(name);
                 context[name].value = {};
             }
             return context[name];
         }

         function unIntern(name, context) {
             context = context || globalEnv;
             delete context[name];
         }

         function setSymbolValue(symbol, type, value) {
             if (symbol.type !== ATOM_SYMBOL)
                 throw "Wrong assignment";

             switch (type)
             {
             case SYM_VARIABLE:
                 symbol.value.v = value;
                 break;
             case SYM_FUNCTION:
                 symbol.value.f = value;
                 break;
             case SYM_CONSTANT:
                 symbol.value.c = value;
                 break;
             }
         }

         function set(sym, value, constant, context) {
             if (!isSymbol(sym))
                 throw "wrong type symbolp " + sexpToStr(sym);

             var sym = intern(sym.name, context);

             if (isConstantSymbol(sym))
                 throw "setting value to the constant";

             setSymbolValue(sym, constant ? SYM_CONSTANT : SYM_VARIABLE, value);

             return value;
         }

         function setSymbolFunction(atom, func) {
             if (!isSymbol(atom))
                 throw "wrong type symbolp" + sexpToStr(atom);

             var sym = intern(atom.name);
             setSymbolValue(sym, SYM_FUNCTION, func);

             return func;
         }

         function getSymbolValue(symbol, type) {
             if (symbol.type !== ATOM_SYMBOL)
                 throw "Non symbol value passed";

             switch (type)
             {
             case SYM_VARIABLE:
                 return symbol.value.v;
             case SYM_FUNCTION:
                 return symbol.value.f;
             case SYM_CONSTANT:
                 return symbol.value.c;
             }
         }

         function hasSymbolType(symbol, type) {
             if (symbol.type !== ATOM_SYMBOL)
                 throw "Non symbol value passed";

             if (!symbol.value)
                 return false;

             switch (type)
             {
             case SYM_VARIABLE:
                 return !!symbol.value.v;
             case SYM_FUNCTION:
                 return !!symbol.value.f;
             case SYM_CONSTANT:
                 return !!symbol.value.c;
             }

             return false;
         }

         function isConstantSymbol(symbol) {
             return hasSymbolType(symbol, SYM_CONSTANT) || symbol.name[0] === ":";
         }

         // ====================================================================== //
         // Symbol / Env
         // ====================================================================== //

         function findSymbolInEnv(name, type, env) {
             if (name in env && (!type || hasSymbolType(env[name], type)))
                 return env[name];
         }

         function findSymbol(name, type) {
             var sym;
             for (var i = localEnvs.length - 1; i >= 0; --i)
                 if ((sym = findSymbolInEnv(name, type, localEnvs[i])))
                     return sym;
             return findSymbolInEnv(name, type, globalEnv);
         }

         // ====================================================================== //
         // Atom, Symbol / Utils
         // ====================================================================== //

         function sexpToStr(elem, omitParen) {
             if (elem instanceof Array)
             {
                 var a    = sexpToStr(car(elem));
                 var rest = cdr(elem);
                 var b    = sexpToStr(rest, isList(rest));

                 var center = isNil(rest) ? a : a + (isList(rest) ? " " : " . ") + b;

                 return omitParen ? center : "(" + center + ")";
             }

             if (elem && elem.type)
             {
                 switch (elem.type)
                 {
                 case ATOM_SYMBOL:
                     return elem.name;
                 case ATOM_STRING:
                     return "\"" + elem.value + "\"";
                 case ATOM_NUMBER:
                     return elem.value;
                 }
             }

             return "sexpToStr : Non LISP object passed. It's value is `" + elem + "'";
         }

         function listToArray(lst) {
             if (isNil(lst))
                 return [];

             for (var array = []; isTrue(cdr(lst)); lst = cdr(lst))
             {
                 if (!isList(cdr(lst)))
                     throw "not a pure list given";
                 array.push(car(lst));
             }
             array.push(car(lst));

             return array;
         }

         function arrayToList(array) {
             var lst = symNil;

             for (var i = array.length - 1; i >= 0; --i)
                 lst = cons(array[i], lst);

             return lst;
         }

         // ====================================================================== //
         // Predicatives
         // ====================================================================== //

         function equal(a, b) {
             if (a instanceof Array && b instanceof Array)
             {
                 while (isTrue(a) && isTrue(b))
                 {
                     if (!equal(car(a), car(b)))
                         return false;
                     a = cdr(a);
                     b = cdr(b);
                 }

                 return true;
             }

             if (a.type !== b.type)
                 return false;

             switch (a.type)
             {
             case ATOM_SYMBOL:
                 return a.name === b.name;
             case ATOM_STRING:
                 return a.value === b.value;
             case ATOM_NUMBER:
                 return a.value === b.value;
             }
         }

         function eq(a, b) {
             if (a instanceof Array && b instanceof Array)
                 return a === b;

             return equal(a, b);
         }

         function isNil(x)    { return x === symNil; }
         function isTrue (x)  { return !isNil(x); }
         function isSymbol(x) { return x.type === ATOM_SYMBOL || isNil(x); }
         function isNumber(x) { return x.type === ATOM_NUMBER; }
         function isString(x) { return x.type === ATOM_STRING; }
         function isList(x)   { return isNil(x) || x instanceof Array; }
         function isAtom(x)   { return isNil(x) || isSymbol(x) || isNumber(x) || isString(x); }
         function isCons(x)   { return isList(x) && !isNil(x); }

         // ====================================================================== //
         // Basic functions for list processing
         // ====================================================================== //

         function setCar(cell, val)  { return cell[0] = val; }
         function setCdr(cell, val)  { return cell[1] = val; }

         function car(lst)  {
             if (!isList(lst))
                 throw "wrong type argument listp " + sexpToStr(lst);
             return isNil(lst) ? symNil : lst[0];
         }
         function cdr(lst)  {
             if (!isList(lst))
                 throw "wrong type argument listp " + sexpToStr(lst);
             return isNil(lst) ? symNil : lst[1];
         }

         function caar(lst) { return car(car(lst)); }
         function cadr(lst) { return car(cdr(lst)); }
         function cdar(lst) { return cdr(car(lst)); }
         function cddr(lst) { return cdr(cdr(lst)); }

         function cons(a, b) { return [a, b]; };

         function tail(lst) {
             while (!isNil(cdr(lst)))
                 lst = cdr(lst);
             return lst;
         }

         function list() {
             var lst = symNil;
             for (var i = arguments.length - 1; i >= 0; --i)
                 lst = cons(arguments[i], lst);
             return lst;
         }

         function append() {
             var newList = [];
             var lst;

             if (!arguments.length)
                 return symNil;

             for (var i = 0; i < arguments.length - 1; ++i)
             {
                 if (!isList(arguments[i]))
                     throw "append : wrong type argument " + sexpToStr(arguments[i]);

                 lst = arguments[i];

                 while (isTrue(cdr(lst)))
                 {
                     newList.push(car(lst));
                     lst = cdr(lst);
                 }

                 if (isTrue(car(lst)))
                     newList.push(car(lst));
             }

             newList = arrayToList(newList);

             if (isCons(newList))
                 return setCdr(tail(newList), arguments[i]), newList;
             return arguments[0];
         };

         // ====================================================================== //
         // Parser
         // ====================================================================== //

         function Parser() {}

         Parser.prototype = {
             parse: function (str, multi) {
                 this.i    = 0;
                 this.str  = str;
                 this.slen = str.length;

                 if (multi)
                 {
                     var forms = [];
                     while (!this.eos())
                     {
                         this.skip();
                         forms.push(this.parseElement());
                     }

                     return forms;
                 }

                 this.skip();
                 var form = this.parseElement();
                 if (!this.eos())
                     throw "Parse Error";
                 return form;
             },

             eos: function () {
                 return this.i >= this.slen;
             },

             isSpace: function (c) {
                 return " \t\n".indexOf(c) !== -1;
             },

             skip: function () {
                 while (this.isSpace(this.peekCurrent()) && !this.eos())
                     this.i++;
             },

             getCurrent: function () {
                 return this.str.charAt(this.i++);
             },

             peekCurrent: function () {
                 return this.str.charAt(this.i);
             },

             peekNext: function () {
                 return this.str.charAt(this.i + 1);
             },

             parseElement: function () {
                 var current = this.peekCurrent();

                 if (current === "#" && this.peekNext() === "'")
                 {
                     this.getCurrent();
                     this.getCurrent();
                     return cons(symFunction, cons(this.parseElement(), symNil));
                 }

                 if (current === "'")
                 {
                     this.getCurrent();
                     return cons(symQuote, cons(this.parseElement(), symNil));
                 }

                 if (current === "(")
                     return this.parseList();
                 else if (current === "\"")
                     return this.parseString();
                 else
                     return this.parseSymbolOrNumber(); // or number
             },

             parseList: function parseList() {
                 var lst = [];

                 if (this.getCurrent() !== "(")
                     throw "parseList : ParseError";

                 this.skip();

                 while (this.peekCurrent() !== ")" && !this.eos())
                 {
                     lst.push(this.parseElement());
                     this.skip();
                 }

                 if (this.getCurrent() !== ")")
                     throw "parseList : Unclosed Parenthesis";

                 var slst = symNil;

                 while (lst.length)
                     slst = [lst.pop(), slst];

                 return slst;
             },

             parseString: function () {
                 if (this.getCurrent() !== "\"")
                     throw "parseString : Not a String";

                 var buffer = [];
                 var escaped = false;

                 while ((escaped || this.peekCurrent() !== "\"") && !this.eos())
                 {
                     escaped = false;
                     var current = this.getCurrent();
                     if (current === "\\")
                         escaped = true;
                     buffer.push(current);
                 }

                 if (this.getCurrent() !== "\"")
                     throw "parseList : Unterminated String";

                 return createString(buffer.join(""));
             },

             parseSymbolOrNumber: function parseSymbolOrNumber() {
                 const symbolChars = /[a-zA-Z0-9*&^%$@!~_+=<>:./-]/;

                 var buffer = [];

                 while (symbolChars.test(this.peekCurrent()) && !this.eos())
                     buffer.push(this.getCurrent());

                 if (!buffer.length)
                     throw "parseSymbol : Parse error";

                 var symbolName = buffer.join("");

                 if (/^-?[0-9]+([.][0-9]*|e-?[0-9]+)?$/.test(symbolName))
                     return createNumber(parseFloat(symbolName));

                 return createSymbol(symbolName);
             }
         };

         var parser = new Parser();

         // ====================================================================== //
         // Evaluation
         // ====================================================================== //

         function processArgKeywords(args, vals) {
             var pArgs = [];
             var pVals = [];

             for (var i = 0, j = 0; i < args.length; ++i, ++j)
             {
                 if (equal(args[i], symOptional))
                 {
                     if (!args[i + 1])
                         throw "missing argument name for &optional";
                     pArgs.push(args[i + 1]);
                     pVals.push(vals[j] || symNil);
                     i++;
                     continue;
                 }
                 else if (equal(args[i], symRest))
                 {
                     // where function (foo (x &rest r) ...) given,
                     // (foo :a)       ; r <= nil
                     // (foo :a :b)    ; r <= (:b)
                     // (foo :a :b :c) ; r <= (:b :c)

                     if (!args[i + 1])
                         throw "missing argument name for &rest";
                     pArgs.push(args[i + 1]);
                     pVals.push(list.apply(null, vals.slice(j)));
                     j = vals.length;
                     break;
                 }
                 else
                 {
                     if (!vals[j])
                         throw "wrong number of arguments";

                     pArgs.push(args[i]);
                     pVals.push(vals[j]);
                 }
             }

             // for assertArgCountA
             while (j < vals.length)
                 pVals.push(vals[j++]);

             return { args: pArgs, vals: pVals };
         }

         function validateFunction(func) {
             if (!equal(car(func), symLambda) || !listToArray(cadr(func)).every(isSymbol))
                 throw "invalid function " + sexpToStr(func);
         }

         function evalFunction(func, vals) {
             if (isSymbol(func))
             {
                 // macro
                 if (func.name in macros)
                 {
                     var expanded = evalFunction(macros[func.name], vals);
                     return Eval(expanded);
                 }

                 // built-in function
                 if (func.name in builtins)
                     return builtins[func.name].apply(null, vals.map(Eval));

                 // lisp function
                 var symInEnv;
                 if ((symInEnv = findSymbol(func.name, SYM_FUNCTION)))
                     func = getSymbolValue(symInEnv, SYM_FUNCTION);
                 else
                     throw "void function " + sexpToStr(func);

                 vals = vals.map(Eval);
             }

             validateFunction(func);

             var body = cddr(func);
             var args = listToArray(cadr(func));
             var processed = processArgKeywords(args, vals);

             args = processed.args;
             vals = processed.vals;

             if (args.length !== vals.length)
                 throw "wrong number of arguments";

             var env = {};

             for (var i = 0; i < args.length; ++i)
             {
                 var sym = intern(args[i].name, env);
                 setSymbolValue(sym, SYM_VARIABLE, vals[i]);
             }

             var error;
             localEnvs.push(env);
             try {
                 var val = Eval(cons(symProgn, body));
             } catch (x) {
                 error = x;
             }
             localEnvs.pop();

             if (error)
                 throw error;
             return val;
         }

         var evalDepth    = 0;
         var maxEvalDepth = 100000;

         function Eval(form) {
             if (++evalDepth > maxEvalDepth)
                 throw "eval depth exceeds maxEvalDepth (" + maxEvalDepth + ")";

             if (isCons(form))
             {
                 var sym  = car(form);
                 var args = cdr(form);

                 if (isSymbol(sym))
                 {
                     if (sym.name in specials)
                         return specials[sym.name](args, form);
                     else
                         return evalFunction(sym, listToArray(args));
                 }

                 // (lambda () ...)
                 if (isCons(sym) && equal(car(sym), symLambda))
                     return evalFunction(form, listToArray(args).map(Eval));

                 throw "invalid function " + sexpToStr(sym);
             }
             else
             {
                 var atom = form;

                 switch (atom.type)
                 {
                 case ATOM_SYMBOL:
                     var name = atom.name;

                     if (name && name[0] === ":") // keyword
                         return atom;

                     var sym = findSymbol(name);

                     if (!sym)
                         throw "void variable " + name;

                     if (hasSymbolType(sym, SYM_CONSTANT))
                         return getSymbolValue(sym, SYM_CONSTANT);
                     else if (hasSymbolType(sym, SYM_VARIABLE))
                         return getSymbolValue(sym, SYM_VARIABLE);
                     else
                         throw "void variable " + name;
                     break;
                 case ATOM_STRING:
                 case ATOM_NUMBER:
                     return atom;
                     break;
                 }
             }
         }

         // ====================================================================== //
         // Arguments
         // ====================================================================== //

         function argCount(args) {
             var count = 0;
             while (isList(args) && !isNil(args))
                 count++, args = cdr(args);
             return count;
         }

         // List
         function assertArgCountL(count, op, args) {
             if (!op(argCount(args), count))
                 throw "wrong number of arguments";
         }

         // Array
         function assertArgCountA(count, op, args) {
             if (!op(args.length, count))
                 throw "wrong number of arguments";
         }

         function argEq(a, b) { return a === b; }
         function argGt(a, /* than */ b)  { return a > b; }
         function argLt(a, /* than */ b)  { return a < b; }
         function argGte(a, /* than */ b) { return a >= b; }
         function argLte(a, /* than */ b) { return a <= b; }

         // ====================================================================== //
         // Special forms
         // ====================================================================== //

         function special(names, func) {
             if (!(names instanceof Array))
                 names = [names];

             for (var i in names)
                 specials[names[i]] = func;
         }

         // ====================================================================== //
         // Special forms / Basics
         // ====================================================================== //

         special(['quote', 'function'], function (lst) {
                     assertArgCountL(1, argEq, lst);

                     return car(lst);
                 });

         special('set', function (lst) {
                     assertArgCountL(2, argEq, lst);

                     var sym = Eval(car(lst));
                     var val = Eval(cadr(lst));
                     set(sym, val);

                     return val;
                 });

         special('setq', function (lst) {
                     var args = listToArray(lst);

                     for (var i = 0; i < args.length; i += 2)
                     {
                         var sym = args[i];
                         var val = Eval(args[i + 1] || symNil);
                         findSymbol
                         set(sym, val);
                     }

                     return val;
                 });

         special('defun', function (lst) {
                     // (defun NAME ARGLIST [BODY ...])
                     assertArgCountL(2, argGte, lst);

                     var name  = car(lst);
                     var pargs = cadr(lst);
                     var body  = cddr(lst);

                     var func = cons(symLambda, cons(pargs, body));
                     setSymbolFunction(name, func);

                     return symNil;
                 });

         special('let', function (lst) {
                     // (let VARLIST BODY...)
                     assertArgCountL(1, argGte, lst);

                     var body  = cdr(lst);
                     var vlist = listToArray(car(lst));

                     var vars = vlist.map(function (pair) { return isList(pair) ? car(pair) : pair; });
                     var vals = vlist.map(function (pair) { return isList(pair) ? cadr(pair) : symNil; }).map(Eval);

                     return evalFunction(cons(symLambda, cons(arrayToList(vars), body)), vals);
                 });

         special('let*', function (lst) {
                     // (let* VARLIST BODY...)
                     assertArgCountL(1, argGte, lst);

                     var vlist = listToArray(car(lst));
                     var body  = cdr(lst);

                     var vars = vlist.map(function (pair) { return isList(pair) ? car(pair)  : pair; });
                     var vals = vlist.map(function (pair) { return isList(pair) ? cadr(pair) : symNil; });

                     var env = {};
                     localEnvs.push(env);

                     for (var i = 0; i < vars.length; ++i)
                         setSymbolValue(intern(vars[i].name, env), SYM_VARIABLE, Eval(vals[i]));

                     var error;
                     try {
                         var val = Eval(cons(symProgn, body));
                     } catch (x) {
                         error = x;
                     }
                     localEnvs.pop();

                     if (error)
                         throw error;
                     return val;
                 });

         special('lambda', function (lst, form) { return form; });

         // ====================================================================== //
         // Special forms / Control Structures
         // ====================================================================== //

         special('cond', function (lst) {
                     do
                     {
                         var clause = car(lst);

                         if (isList(clause))
                         {
                             var condResult;
                             if (isTrue(condResult = Eval(car(clause))))
                             {
                                 return isNil(cdr(clause)) ? condResult : Eval(cadr(clause));
                             }
                         }
                         else
                             throw "wrong type argument listp";

                         lst = cdr(lst);
                     } while (isTrue(clause));

                     return symNil;
                 });

         special('if', function (lst) {
                     assertArgCountL(2, argGte, lst);

                     var test  = car(lst);
                     var tform = cadr(lst);
                     var fform = cddr(lst);

                     if (isTrue(Eval(test)))
                         return Eval(tform);

                     fform = listToArray(fform);

                     var val = symNil;
                     for (var i = 0; i < fform.length; ++i)
                         val = Eval(fform[i]);
                     return val;
                 });

         special('while', function (lst) {
                     assertArgCountL(1, argGte, lst);

                     var test = car(lst);
                     var body = cdr(lst);
                     body = listToArray(body);
                     while (isTrue(Eval(test)))
                         for (var i = 0; i < body.length; ++i)
                             Eval(body[i]);
                     return symNil;
                 });

         function progn(lst) {
             var body = listToArray(lst);
             var val = symNil;
             for (var i = 0; i < body.length; ++i)
                 val = Eval(body[i]);
             return val;
         }

         special('progn', progn);

         special('prog1', function (lst) {
                     assertArgCountL(1, argGte, lst);
                     var first = Eval(car(lst));
                     progn(cdr(lst));
                     return first;
                 });

         special('prog2', function (lst) {
                     assertArgCountL(2, argGte, lst);
                     var first  = Eval(car(lst));
                     var second = Eval(cadr(lst));
                     progn(cddr(lst));
                     return second;
                 });

         special('and', function (lst) {
                     var conditions = listToArray(lst);
                     var v = t;
                     for (var i = 0; i < conditions.length; ++i)
                         if (isNil(v = Eval(conditions[i])))
                             return symNil;
                     return v;
                 });

         special('or', function (lst) {
                     var conditions = listToArray(lst);
                     var v = t;
                     for (var i = 0; i < conditions.length; ++i)
                         if (isTrue(v = Eval(conditions[i])))
                             return v;
                     return v;
                 });

         // ====================================================================== //
         // Macros
         // ====================================================================== //

         function setMacro(atom, macro) {
             if (!isSymbol(atom))
                 throw "wrong type symbolp" + sexpToStr(atom);
             macros[atom.name] = macro;
             return macro;
         }

         special('defmacro', function (lst) {
                     var name  = car(lst);
                     var pargs = cadr(lst);
                     var body  = cddr(lst);

                     setMacro(name, cons(symLambda, cons(pargs, body)));

                     return symNil;
                 });

         // ====================================================================== //
         // Builtin functions
         // ====================================================================== //

         function builtin(names, func) {
             if (!(names instanceof Array))
                 names = [names];

             for (var i in names)
                 builtins[names[i]] = func;
         }

         // ====================================================================== //
         // Builtin functions / Predicatives
         // ====================================================================== //

         builtin(['eq', 'eql'], function (a, b) { assertArgCountA(2, argEq, arguments); return boxBool[eq(a, b)]; });
         builtin('equal', function (a, b) { assertArgCountA(2, argEq, arguments); return boxBool[equal(a, b)]; });

         builtin(['null', 'not'], function (x) { assertArgCountA(1, argEq, arguments); return boxBool[isNil(x)]; });
         builtin('symbolp', function (x) { assertArgCountA(1, argEq, arguments); return boxBool[isSymbol(x)]; });
         builtin('atom', function (x) { assertArgCountA(1, argEq, arguments); return boxBool[isAtom(x)]; });
         builtin('consp', function (x) { assertArgCountA(1, argEq, arguments); return boxBool[isCons(x)]; });
         builtin('listp', function (x) { assertArgCountA(1, argEq, arguments); return boxBool[isList(x)]; });
         builtin('numberp', function (x) { assertArgCountA(1, argEq, arguments); return boxBool[isNumber(x)]; });
         builtin('stringp', function (x) { assertArgCountA(1, argEq, arguments); return boxBool[isString(x)]; });
         builtin('boundp', function (x) {
                     assertArgCountA(1, argEq, arguments);
                     return boxBool[isSymbol(x) && (hasSymbolType(x, SYM_CONSTANT || hasSymbolType(x, SYM_VARIABLE)))];
                 });
         builtin('fboundp', function (x) {
                     assertArgCountA(1, argEq, arguments);
                     return boxBool[isSymbol(x) &&
                                    ((x.name in builtins)
                                     || (x.name in specials)
                                     || (x.name in macros)
                                     || isSymbol(x) && hasSymbolType(x, SYM_FUNCTION))];
                 });

         builtin('funcall', function (func) {
                     assertArgCountA(1, argGte, arguments);
                     return evalFunction(func, Array.prototype.slice.call(arguments, 1));
                 });

         builtin('apply', function (func) {
                     assertArgCountA(1, argGte, arguments);
                     var vals = Array.prototype.slice.call(arguments, 1, arguments.length - 1);
                     vals = vals.concat(listToArray(arguments[arguments.length - 1]));
                     return evalFunction(func, vals);
                 });

         // ====================================================================== //
         // Builtin functions / List processing
         // ====================================================================== //

         builtin('cons', function (x, y) { assertArgCountA(2, argEq, arguments); return cons(x, y); });
         builtin('car',  function (x, y) { assertArgCountA(2, argEq, arguments); return car(x, y);  });
         builtin('cdr',  function (x, y) { assertArgCountA(2, argEq, arguments); return cdr(x, y);  });
         builtin('caar', function (x, y) { assertArgCountA(2, argEq, arguments); return caar(x, y); });
         builtin('cadr', function (x, y) { assertArgCountA(2, argEq, arguments); return cadr(x, y); });
         builtin('cdar', function (x, y) { assertArgCountA(2, argEq, arguments); return cdar(x, y); });
         builtin('cddr', function (x, y) { assertArgCountA(2, argEq, arguments); return cddr(x, y); });

         builtin('list', list);
         builtin('tail', function (seq) { assertArgCountA(1, argEq, arguments); return tail(seq); });
         builtin('append', append);

         function mapList(func, seq) {
             if (!isList(seq))
                 throw "wrong type listp " + sexpToStr(seq);

             return arrayToList(listToArray(seq).map(func));
         }

         builtin('mapc', function (func, seq) {
                     assertArgCountA(2, argGte, arguments);
                     mapList(function (elem) { return evalFunction(func, [elem]); }, seq);
                     return seq;
                 });

         builtin('mapcar', function (func, seq) {
                     assertArgCountA(2, argGte, arguments);
                     return mapList(function (elem) { return evalFunction(func, [elem]); }, seq);
                 });

         // ====================================================================== //
         // Builtin functions / Operators
         // ====================================================================== //

         builtin('+', function (numbers) {
                     for (var i = 0, v = 0; i < arguments.length; ++i)
                         v += arguments[i].value;
                     return createNumber(v);
                 });
         builtin('-', function (x, numbers) {
                     if (!arguments.length)
                         return createNumber(0);

                     if (arguments.length === 1)
                         return createNumber(-x.value);

                     for (var i = 1, v = x.value; i < arguments.length; ++i)
                         v -= arguments[i].value;
                     return createNumber(v);
                 });
         builtin('*', function (numbers) {
                     for (var i = 0, v = 1; i < arguments.length; ++i)
                         v *= arguments[i].value;
                     return createNumber(v);
                 });
         builtin('/', function (x, divisors) {
                     assertArgCountA(2, argGte, arguments);
                     for (var i = 1, v = x.value; i < arguments.length; ++i)
                         v /= arguments[i].value;
                     return createNumber(v);
                 });
         builtin('%', function (x, y) {
                     assertArgCountA(2, argEq, arguments);
                     return createNumber(x.value % y.value);
                 });

         builtin('1-', function (x) { assertArgCountA(1, argEq, arguments); return createNumber(x.value - 1); });
         builtin('1+', function (x) { assertArgCountA(1, argEq, arguments); return createNumber(x.value + 1); });

         // ====================================================================== //
         // Builtin functions / Operators
         // ====================================================================== //

         builtin('=',  function (x, y) { assertArgCountA(2, argEq, arguments); return boxBool[x.value == y.value]; });
         builtin('<',  function (x, y) { assertArgCountA(2, argEq, arguments); return boxBool[x.value <  y.value]; });
         builtin('<=', function (x, y) { assertArgCountA(2, argEq, arguments); return boxBool[x.value <= y.value]; });
         builtin('>',  function (x, y) { assertArgCountA(2, argEq, arguments); return boxBool[x.value >  y.value]; });
         builtin('>=', function (x, y) { assertArgCountA(2, argEq, arguments); return boxBool[x.value >= y.value]; });

         // ====================================================================== //
         // Builtin functions / IO
         // ====================================================================== //

         builtin('print', function (v) { assertArgCountA(1, argEq, arguments); print(sexpToStr(v)); return v; });

         // ====================================================================== //
         // Builtin functions / Math
         // ====================================================================== //

         builtin('abs', function (x) { assertArgCountA(1, argEq, arguments); return createNumber(Math.abs(x.value)); });
         builtin('exp', function (x) { assertArgCountA(1, argEq, arguments); return createNumber(Math.exp(x.value)); });
         builtin('log', function (x) { assertArgCountA(1, argEq, arguments); return createNumber(Math.log(x.value)); });
         builtin('pow', function (x) { assertArgCountA(1, argEq, arguments); return createNumber(Math.pow(x.value)); });
         builtin('round', function (x) { assertArgCountA(1, argEq, arguments); return createNumber(Math.round(x.value)); });
         builtin('ceil', function (x) { assertArgCountA(1, argEq, arguments); return createNumber(Math.ceil(x.value)); });
         builtin('sin', function (x) { assertArgCountA(1, argEq, arguments); return createNumber(Math.sin(x.value)); });
         builtin('cos', function (x) { assertArgCountA(1, argEq, arguments); return createNumber(Math.cos(x.value)); });
         builtin('tan', function (x) { assertArgCountA(1, argEq, arguments); return createNumber(Math.tan(x.value)); });
         builtin('sqrt', function (x) { assertArgCountA(1, argEq, arguments); return createNumber(Math.sqrt(x.value)); });
         builtin('random', function (limit) {
                     assertArgCountA(1, argLte, arguments);
                     var rand = Math.random();
                     return createNumber(!arguments.length ? rand : rand * limit.value);
                 });

         // ====================================================================== //
         // Builtin functions / Misc
         // ====================================================================== //

         builtin('iota', function (count, from, delta) {
                     assertArgCountA(1, argGte, arguments);

                     count = count.value;

                     if (count < 0)
                         throw "negative count";

                     from  = (typeof from  === "undefined") ? 0 : from.value;
                     delta = (typeof delta === "undefined") ? 1 : delta.value;

                     var array = [createNumber(from)];
                     for (var i = 1; i < count; ++i)
                         array.push(createNumber(from += delta));

                     return arrayToList(array);
                 });

         // ====================================================================== //
         // LISP Codes
         // ====================================================================== //

         function evalLisp(str) {
             return parser.parse(str, true).map(
                 function (lst) {
                     evalDepth = 0;
                     return Eval(lst);
                 });
         }

         function evalLispString(str) {
             return evalLisp(str).map(function (str) { return sexpToStr(str); }).join("\n");
         }

         function syntaxChecker (str) {
             try { parser.parse(str, true); return true; } catch (x) { return false; }
         };

         // ====================================================================== //
         // Utils
         // ====================================================================== //

         function dir(obj) {
             for (k in obj)
                 print(k + " : " + obj[k]);
         }

         function printa(atom) { print(sexpToStr(atom)); }

         // ====================================================================== //
         // Define misc codes
         // ====================================================================== //

         evalLisp("(defmacro when (cond &rest body) (list 'if cond (cons 'progn body)))");
         evalLisp("(defmacro unless (cond &rest body) (cons 'if (cons cond (cons nil body))))");

         // ====================================================================== //
         // Public
         // ====================================================================== //

         var self = {
             // constans
             SYM_FUNCTION   : SYM_FUNCTION,
             SYM_VARIABLE   : SYM_VARIABLE,
             SYM_CONSTANT   : SYM_CONSTANT,
             // Envs
             globalEnv      : globalEnv,
             localEnvs      : localEnvs,
             builtins       : builtins,
             specials       : specials,
             macros         : macros,
             // inspection
             hasSymbolType  : hasSymbolType,
             getSymbolValue : getSymbolValue,
             setSymbolValue : setSymbolValue,
             // methods
             defSpecial     : special,
             defBuiltin     : builtin,
             evalLisp       : evalLisp,
             sexpToStr      : sexpToStr,
             syntaxChecker  : syntaxChecker
         };

         return self;
     })();
