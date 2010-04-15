/**
 * @fileOverview small lisp implementation written in javascript
 * @name mispli
 * @author mooz <stillpedant@gmail.com>
 * @license The MIT License
 */

// ====================================================================== //
// Envs
// ====================================================================== //

var genv     = {};
var envs     = [];
var builtins = {};
var specials = {};

// ====================================================================== //
// Atom, Symbol
// ====================================================================== //

const ATOM_SYMBOL = 1;
const ATOM_STRING = 2;
const ATOM_NUMBER = 3;

function createAtom(type, name, value) {
    return {
        type  : type,
        name  : name,
        value : value
    };
}

function createString(value) { return createAtom(ATOM_STRING, null, value); }
function createNumber(value) { return createAtom(ATOM_NUMBER, null, value); }

// ====================================================================== //
// Atom, Symbol / Symbol
// ====================================================================== //

const SYM_VARIABLE = 1;
const SYM_FUNCTION = 2;
const SYM_CONSTANT = 3;

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

function hasSymbolType(symbol, type) {
    if (symbol.type !== ATOM_SYMBOL)
    {
        dir(symbol);
        throw "Non symbol value passed";
    }

    if (!symbol.type)
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

function findSymbolInEnv(name, type, env) {
    if (name in env && (!type || hasSymbolType(env[name], type)))
        return env[name];
}

function findSymbol(name, type) {
    var sym;
    for (var i = envs.length - 1; i >= 0; --i)
        if ((sym = findSymbolInEnv(name, type, envs[i])))
            return sym;
    return findSymbolInEnv(name, type, genv);
}

function isSymConstant(symbol) {
    return hasSymbolType(symbol, SYM_CONSTANT) || symbol.name[0] === ":";
}

function createSymbol(name) {
    return createAtom(ATOM_SYMBOL, name);
}

function intern(name, context) {
    context = context || genv;
    if (!(name in context))
    {
        context[name] = createSymbol(name);
        context[name].value = {};
    }
    return context[name];
}

function unintern(name, context) {
    context = context || genv;
    delete context[name];
}

function set(atom, value, constant, context) {
    if (!symbolp(atom))
        throw "wrong type symbolp" + tos(atom);

    var sym = intern(atom.name, context);

    if (isSymConstant(sym))
        throw "setting value to the constant";

    setSymbolValue(sym, constant ? SYM_CONSTANT : SYM_VARIABLE, value);

    return value;
}

function setFunc(atom, func) {
    if (!symbolp(atom))
        throw "wrong type symbolp" + tos(atom);

    var sym = intern(atom.name);

    setSymbolValue(sym, SYM_FUNCTION, func);

    return func;
}

var t = intern("t");
setSymbolValue(t, SYM_CONSTANT, t);

var nil = intern("nil");
setSymbolValue(nil, SYM_CONSTANT, nil);

// often used symbols (not interned)
var lambda = createSymbol('lambda');
var progn  = createSymbol('progn');
var quote  = createSymbol('quote');

// ====================================================================== //
// Atom, Symbol / Utils
// ====================================================================== //

function tos(elem) {
    if (elem instanceof Array)
    {
        var a = tos(car(elem));
        var b = tos(cdr(elem));
        return "(" + a + " . " + b + ")";
        // return "(" + a + (listp(cdr(elem)) ? " " : " . ") + b + ")";
    }

    switch (elem.type)
    {
    case ATOM_SYMBOL:
        return elem.name;
        break;
    case ATOM_STRING:
        return "\"" + elem.value + "\"";
        break;
    case ATOM_NUMBER:
        return elem.value;
        break;
    }
}

function listToArray(lst) {
    for (var array = []; isTrue(cdr(lst)); lst = cdr(lst))
    {
        if (!listp(cdr(lst)))
            throw "not a pure list given";
        array.push(car(lst));
    }
    array.push(car(lst));

    return array;
}

function arrayToList(array) {
    var lst = nil;

    for (var i = array.length - 1; i >= 0; --i)
        lst = cons(array[i], lst);

    return lst;
}

// ====================================================================== //
// Predicatives (returns boolean value in js)
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

function isNil(x)   { return x === nil; }
function isTrue (x) { return !isNil(x); }

function symbolp(x) { return x.type === ATOM_SYMBOL || isNil(x); }
function numberp(x) { return x.type === ATOM_NUMBER; }
function stringp(x) { return x.type === ATOM_STRING; }
function listp(x)   { return isNil(x) || x instanceof Array; }

function atom(x)    { return isNil(x) || symbolp(x) || numberp(x) || stringp(x); }
function consp(x)   { return listp(x) && !isNil(x); }

// ====================================================================== //
// Basic functions for list processing
// ====================================================================== //

function setCar(lst, val)  { return lst[0] = val; }
function setCdr(lst, val)  { return lst[1] = val; }

function car(lst)  { return isNil(lst) ? nil : lst[0]; }
function cdr(lst)  { return isNil(lst) ? nil : lst[1]; }

function caar(lst) { return car(car(lst)); }
function cadr(lst) { return car(cdr(lst)); }
function cdar(lst) { return cdr(car(lst)); }
function cddr(lst) { return cdr(cdr(lst)); }

function cons(a, b) { return [a, b]; };

function append() {
    for (var i = 0; i < arguments.length; ++i)
    {
        if (!listp(arguments[i]))
            throw "append : wrong type argument";

        var lst = arguments[i];

        while (isTrue(cdr(lst)))
            lst = cdr(lst);

        setCdr(lst, arguments[i + 1] || nil);
    }

    return arguments[0];
};

// ====================================================================== //
// Parser
// ====================================================================== //

function Parser() {}

Parser.prototype = {
    parse: function (str) {
        this.i    = 0;
        this.str  = str;
        this.slen = str.length;

        var val;
        while (!this.eos())
        {
            this.skip();
            val = this.parseElement();
        }

        return val;
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
        return this.str[this.i++];
    },

    peekCurrent: function () {
        return this.str[this.i];
    },

    peekNext: function () {
        return this.str[this.i + 1];
    },

    parseElement: function () {
        var current = this.peekCurrent();

        if (current === "'")
        {
            this.getCurrent();
            return cons(quote, cons(this.parseElement(), nil));
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

        while (this.peekCurrent() !== ")" && !this.eos())
        {
            this.skip();
            lst.push(this.parseElement());
        }

        if (this.getCurrent() !== ")")
            throw "parseList : Unclosed Parenthethis";

        var slst = nil;

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
        const symbolp = /[a-zA-Z0-9*&^%$@!~_+=<>:./-]/;

        var buffer = [];

        while (symbolp.test(this.peekCurrent()) && !this.eos())
            buffer.push(this.getCurrent());

        if (!buffer.length)
            throw "parseSymbol : Parse error";

        var symbolName = buffer.join("");

        if (/^-?[0-9]+([.][0-9]*|e-?[0-9]+)?$/.test(symbolName))
            return createNumber(parseFloat(symbolName));

        return createSymbol(symbolName);
    }
};

// ====================================================================== //
// Evaluation
// ====================================================================== //

function evalFunction(func, args) {
    // func => [lambda, [  [arg1, [arg2, nil]], [body]]]
    var body = cddr(func);
    var pargs = listToArray(cadr(func));

    if (args.length !== pargs.length)
        throw "wrong number of arguments";

    var env = {};

    for (var i = 0; i < pargs.length; ++i)
    {
        var sym = intern(pargs[i].name, env);
        setSymbolValue(sym, SYM_VARIABLE, args[i]);
    }

    envs.push(env);
    var val = Eval(cons(progn, body));
    envs.pop();

    return val;
}

function validateFunction(func) {
    if (!equal(car(func), lambda) || !listToArray(cadr(func)).every(function (e) {
                                                                        print("checking [" + tos(e) + "] => " + symbolp(e));
                                                                        return symbolp(e);
                                                                    }))
        throw "invalid function " + tos(sym);
}

function Eval(form) {
    if (consp(form))
    {
        var sym  = car(form);
        var args = cdr(form);

        if (consp(sym) && equal(car(sym), lambda))
        {
            print(tos(sym));
            validateFunction(sym);
            return evalFunction(sym, listToArray(args).map(Eval));
        }

        if (sym.type !== ATOM_SYMBOL)
            throw tos(sym) + " is not a function";

        if (sym.name in specials)
        {
            // special form
            return specials[sym.name](args, form);
        }
        else
        {
            var symInEnv;

            if (sym.name in builtins)
            {
                // built-in function
                return builtins[sym.name].apply(null, listToArray(args).map(Eval));
            }
            else if ((symInEnv = findSymbol(sym.name, SYM_FUNCTION)))
            {
                // lisp function
                var func = getSymbolValue(symInEnv, SYM_FUNCTION);
                validateFunction(func);
                return evalFunction(func, listToArray(args).map(Eval));
            }
            else
                throw "void function " + tos(sym);
        }
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
    while (listp(cdr(args)) && !isNil(cdr(args)))
        count++, args = cdr(args);
    return count;
}

function assertArgCount(args, count) {
    if (argCount(args) !== count)
        throw "Wrong number of arguments";
}

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

special('quote', function (lst) { return car(lst); });

special('set', function (lst) {
            var args = listToArray(lst);
            for (var i = 0; i < args.length; i += 2)
            {
                var sym = Eval(args[i]);
                var val = Eval(args[i + 1]) || nil;
                set(sym, val);
            }

            return val;
        });

special('setq', function (lst) {
            var args = listToArray(lst);
            for (var i = 0; i < args.length; i += 2)
            {
                var sym = args[i];
                var val = Eval(args[i + 1]) || nil;
                set(sym, val);
            }

            return val;
        });

special('defun', function (lst) {
            var name  = car(lst);
            var pargs = cadr(lst);
            var body  = cddr(lst);

            var func = cons(lambda, cons(pargs, body));
            setFunc(name, func);

            return nil;
        });

special('let', function (lst) {
    // func => [lambda, [  [arg1, [arg2, nil]], [body]]]
    var body = cddr(func);
    var pargs = listToArray(cadr(func));

    if (args.length !== pargs.length)
        throw "wrong number of arguments";

    var env = {};

    for (var i = 0; i < pargs.length; ++i)
    {
        var sym = intern(pargs[i].name, env);
        setSymbolValue(sym, SYM_VARIABLE, args[i]);
    }

    envs.push(env);
    var val = Eval(cons(progn, body));
    envs.pop();

    return val;
});

special('let', function (lst) {
            var vlist = listToArray(car(lst));
            var body  = cdr(lst);

            var vars = vlist.map(car);
            var vals = vlist.map(cadr).map(Eval);

            return evalFunction(cons(lambda, cons(arrayToList(vars), body)), vals);
        });

special('lambda', function (lst, form) { return form; });

// ====================================================================== //
// Special forms / Control Structures
// ====================================================================== //

special('if', function (lst) {
            var test  = car(lst);
            var tform = cadr(lst);
            var fform = cddr(lst);

            if (isTrue(Eval(test)))
                return Eval(tform);

            fform = listToArray(fform);

            var val = nil;
            for (var i = 0; i < fform.length; ++i)
                val = Eval(fform[i]);
            return val;
        });

special('while', function (lst) {
            var test = car(lst);
            var body = cdr(lst);
            body = listToArray(body);
            while (isTrue(Eval(test)))
                for (var i = 0; i < body.length; ++i)
                    Eval(body[i]);
            return nil;
        });

special('progn', function (lst) {
            var body = listToArray(lst);
            var val = nil;
            for (var i = 0; i < body.length; ++i)
                val = Eval(body[i]);
            return val;
        });

special('and', function (lst) {
            var conditions = listToArray(lst);
            var v;
            for (var i = 0; i < conditions.length; ++i)
                if (isNil(v = Eval(conditions[i])))
                    return nil;
            return v;
        });

special('or', function (lst) {
            var conditions = listToArray(lst);
            var v;
            for (var i = 0; i < conditions.length; ++i)
                if (isTrue(v = Eval(conditions[i])))
                    return v;
            return nil;
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

// boolean => boolean
var b2b = {
    true  : t,
    false : nil
};

builtin(['eq', 'eql'], function (a, b) { return eq(a, b); });
builtin('equal', function (a, b) { return equal(a, b); });

builtin(['null', 'not'], function (x) { return b2b[isNil(x)]; });
builtin('symbolp', function (x) { return b2b[symbolp(x)]; });
builtin('atom', function (x) { return b2b[atom(x)]; });
builtin('consp', function (x) { return b2b[consp(x)]; });
builtin('listp', function (x) { return b2b[listp(x)]; });
builtin('numberp', function (x) { return b2b[numberp(x)]; });
builtin('stringp', function (x) { return b2b[stringp(x)]; });

// ====================================================================== //
// Builtin functions / List processing
// ====================================================================== //

builtin('cons', cons);
builtin('car',  car);
builtin('cdr',  cdr);
builtin('caar', caar);
builtin('cadr', cadr);
builtin('cdar', cdar);
builtin('cddr', cddr);

// ====================================================================== //
// Builtin functions / Operators
// ====================================================================== //

builtin('+', function (numbers) {
            for (var i = 0, v = 0; i < arguments.length; ++i)
                v += arguments[i].value;
            return createNumber(v);
        });
builtin('-', function (x, numbers) {
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
            for (var i = 1, v = x.value; i < arguments.length; ++i)
                v /= arguments[i].value;
            return createNumber(v);
        });
builtin('%', function (x, y) {
            return createNumber(x.value % y.value);
        });

builtin('1-', function (x) { return createNumber(x.value - 1); });
builtin('1+', function (x) { return createNumber(x.value + 1); });

// ====================================================================== //
// Builtin functions / Operators
// ====================================================================== //

builtin('=',  function (x, y) { return b2b[x.value == y.value]; });
builtin('<',  function (x, y) { return b2b[x.value <  y.value]; });
builtin('<=', function (x, y) { return b2b[x.value <= y.value]; });
builtin('>',  function (x, y) { return b2b[x.value >  y.value]; });
builtin('>=', function (x, y) { return b2b[x.value >= y.value]; });

// ====================================================================== //
// Builtin functions / IO
// ====================================================================== //

builtin('print', function (v) { print(tos(v)); return v; });

// ====================================================================== //
// Utils
// ====================================================================== //

if (typeof window !== "undefined")
{
    window.print = function (str) {
        Application.console.log(str);
    };
}

function dir(obj) {
    for (k in obj)
        print(k + " : " + obj[k]);
}

// ====================================================================== //
// Test
// ====================================================================== //

var ev = (function () {
              var p = new Parser();

              return function (str) {
                  return Eval(p.parse(str));
              };
          })();

function checker (str) { return tos(ev(str)); }

function assert(result, exp) {
    if (equal(exp, result))
        print("=> Test passed");
    else
        print("=> expects " + tos(exp) + " but got " + tos(result));
}

// assert(ev("()"), nil);
// assert(ev("1"), createNumber(1));

// checker("(progn (setq i 10) (while (> i 0) (print i) (setq i (1- i))))");

// checker("(progn (let ((a 1) (c 2)) (print a) (print c)) (print a))");

// ====================================================================== //
// REPL (For spidermonkey)
// ====================================================================== //

if (typeof readline === "function")
{
    var input;
    while ((input = readline()) !== null)
    {
        try {
            print("=> " + checker(input));
        } catch (x) {
            print("error :: " + x);
        }
    }
}
