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
var macros   = {};

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
        throw "Non symbol value passed";

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
        throw "wrong type symbolp " + tos(atom);

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
var symLambda   = createSymbol('lambda');
var symProgn    = createSymbol('progn');
var symQuote    = createSymbol('quote');
var symFunction = createSymbol('function');
var symRest     = createSymbol('&rest');
var symOptional = createSymbol('&optional');
var symKey      = createSymbol('&key');

// ====================================================================== //
// Atom, Symbol / Utils
// ====================================================================== //

function tos(elem, omitParen) {
    if (elem instanceof Array)
    {
        var a    = tos(car(elem));
        var rest = cdr(elem);
        var b    = tos(rest, listp(rest));

        var center = isNil(rest) ? a : a + (listp(rest) ? " " : " . ") + b;

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

    return "tos : Non LISP object passed. It's value is `" + elem + "'";
}

function listToArray(lst) {
    if (isNil(lst))
        return [];

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

function setCar(cell, val)  { return cell[0] = val; }
function setCdr(cell, val)  { return cell[1] = val; }

function car(lst)  {
    if (!listp(lst))
        throw "wrong type argument listp " + tos(lst);
    return isNil(lst) ? nil : lst[0];
}
function cdr(lst)  {
    if (!listp(lst))
        throw "wrong type argument listp " + tos(lst);
    return isNil(lst) ? nil : lst[1];
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
    var lst = nil;
    for (var i = arguments.length - 1; i >= 0; --i)
        lst = cons(arguments[i], lst);
    return lst;
}

function append() {
    var newList = [];
    var lst;

    if (!arguments.length)
        return nil;

    for (var i = 0; i < arguments.length - 1; ++i)
    {
        if (!listp(arguments[i]))
            throw "append : wrong type argument " + tos(arguments[i]);

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

    if (consp(newList))
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
            return cons(symFunction, cons(this.parseElement(), nil));
        }

        if (current === "'")
        {
            this.getCurrent();
            return cons(symQuote, cons(this.parseElement(), nil));
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
            pVals.push(vals[j] || nil);
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
    if (!equal(car(func), symLambda) || !listToArray(cadr(func)).every(symbolp))
        throw "invalid function " + tos(func);
}

function evalFunction(func, vals) {
    if (symbolp(func))
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
            throw "void function " + tos(func);

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
    envs.push(env);
    try {
        var val = Eval(cons(symProgn, body));
    } catch (x) {
        error = x;
    }
    envs.pop();

    if (error)
        throw error;
    return val;
}

var evalDepth    = 0;
var maxEvalDepth = 100000;

function Eval(form) {
    if (++evalDepth > maxEvalDepth)
        throw "eval depth exceeds maxEvalDepth (" + maxEvalDepth + ")";

    if (consp(form))
    {
        var sym  = car(form);
        var args = cdr(form);

        if (symbolp(sym))
        {
            if (sym.name in specials)
                return specials[sym.name](args, form);
            else
                return evalFunction(sym, listToArray(args));
        }

        // (lambda () ...)
        if (consp(sym) && equal(car(sym), symLambda))
            return evalFunction(form, listToArray(args).map(Eval));

        throw "invalid function " + tos(sym);
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
    while (listp(args) && !isNil(args))
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
                var val = Eval(args[i + 1] || nil);
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
            setFunc(name, func);

            return nil;
        });

special('let', function (lst) {
            // (let VARLIST BODY...)
            assertArgCountL(1, argGte, lst);

            var body  = cdr(lst);
            var vlist = listToArray(car(lst));

            var vars = vlist.map(function (pair) { return listp(pair) ? car(pair) : pair; });
            var vals = vlist.map(function (pair) { return listp(pair) ? cadr(pair) : nil; }).map(Eval);

            return evalFunction(cons(symLambda, cons(arrayToList(vars), body)), vals);
        });

special('let*', function (lst) {
            // (let* VARLIST BODY...)
            assertArgCountL(1, argGte, lst);

            var vlist = listToArray(car(lst));
            var body  = cdr(lst);

            var vars = vlist.map(function (pair) { return listp(pair) ? car(pair)  : pair; });
            var vals = vlist.map(function (pair) { return listp(pair) ? cadr(pair) : nil; });

            var env = {};
            envs.push(env);

            for (var i = 0; i < vars.length; ++i)
                setSymbolValue(intern(vars[i].name, env), SYM_VARIABLE, Eval(vals[i]));

            var error;
            try {
                var val = Eval(cons(symProgn, body));
            } catch (x) {
                error = x;
            }
            envs.pop();

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

                if (listp(clause))
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

            return nil;
        });

special('if', function (lst) {
            assertArgCountL(2, argGte, lst);

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
            assertArgCountL(1, argGte, lst);

            var test = car(lst);
            var body = cdr(lst);
            body = listToArray(body);
            while (isTrue(Eval(test)))
                for (var i = 0; i < body.length; ++i)
                    Eval(body[i]);
            return nil;
        });

function progn(lst) {
    var body = listToArray(lst);
    var val = nil;
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
                    return nil;
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
    if (!symbolp(atom))
        throw "wrong type symbolp" + tos(atom);
    macros[atom.name] = macro;
    return macro;
}

special('defmacro', function (lst) {
            var name  = car(lst);
            var pargs = cadr(lst);
            var body  = cddr(lst);

            setMacro(name, cons(symLambda, cons(pargs, body)));

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
    "true"  : t,
    "false" : nil
};

builtin(['eq', 'eql'], function (a, b) { assertArgCountA(2, argEq, arguments); return b2b[eq(a, b)]; });
builtin('equal', function (a, b) { assertArgCountA(2, argEq, arguments); return b2b[equal(a, b)]; });

builtin(['null', 'not'], function (x) { assertArgCountA(1, argEq, arguments); return b2b[isNil(x)]; });
builtin('symbolp', function (x) { assertArgCountA(1, argEq, arguments); return b2b[symbolp(x)]; });
builtin('atom', function (x) { assertArgCountA(1, argEq, arguments); return b2b[atom(x)]; });
builtin('consp', function (x) { assertArgCountA(1, argEq, arguments); return b2b[consp(x)]; });
builtin('listp', function (x) { assertArgCountA(1, argEq, arguments); return b2b[listp(x)]; });
builtin('numberp', function (x) { assertArgCountA(1, argEq, arguments); return b2b[numberp(x)]; });
builtin('stringp', function (x) { assertArgCountA(1, argEq, arguments); return b2b[stringp(x)]; });

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
    if (!listp(seq))
        throw "wrong type listp " + tos(seq);

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

builtin('=',  function (x, y) { assertArgCountA(2, argEq, arguments); return b2b[x.value == y.value]; });
builtin('<',  function (x, y) { assertArgCountA(2, argEq, arguments); return b2b[x.value <  y.value]; });
builtin('<=', function (x, y) { assertArgCountA(2, argEq, arguments); return b2b[x.value <= y.value]; });
builtin('>',  function (x, y) { assertArgCountA(2, argEq, arguments); return b2b[x.value >  y.value]; });
builtin('>=', function (x, y) { assertArgCountA(2, argEq, arguments); return b2b[x.value >= y.value]; });

// ====================================================================== //
// Builtin functions / IO
// ====================================================================== //

builtin('print', function (v) { assertArgCountA(1, argEq, arguments); print(tos(v)); return v; });

// ====================================================================== //
// Misc
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
// Utils
// ====================================================================== //

if (typeof Application !== "undefined")
    window.print = Application.console.log;

function dir(obj) {
    for (k in obj)
        print(k + " : " + obj[k]);
}

function printa(atom) { print(tos(atom)); }

// ====================================================================== //
// LISP Codes
// ====================================================================== //

var evalLisp = (function () {
                    var p = new Parser();
                    return function (str) {
                        return p.parse(str, true).map(
                            function (lst) {
                                evalDepth = 0;
                                return Eval(lst);
                            });
                    };
                }());

function evalLispString(str) {
    return evalLisp(str).map(function (str) { return tos(str); }).join("\n");
}

evalLisp("(defmacro when (cond &rest body) (list 'if cond (cons 'progn body)))");
evalLisp("(defmacro unless (cond &rest body) (cons 'if (cons cond (cons nil body))))");

// ====================================================================== //
// Test
// ====================================================================== //

function assert(result, exp) {
    if (equal(exp, result))
        print("=> Test passed");
    else
        print("=> expects " + tos(exp) + " but got " + tos(result));
}

var syntaxChecker =
    (function () {
         var p = new Parser();

         return function (str) {
             try { p.parse(str, true); return true; } catch (x) { return false; }
         };
     })();

// ====================================================================== //
// REPL (For spidermonkey)
// ====================================================================== //

if (typeof readline === "function")
{
    print("MispLi 0.0.1");
    print("Input Lisp codes and press Enter to evaluate.");
    print("Type \\? to see available commands.");

    var input;
    while ((input = readline()) !== null)
    {
        if (input[0] === "\\" && input.length <= 2)
        {
            var commands = {
                "?" : ["Display this help", function () {
                           print("<<< COMMANDS >>>");
                           for (var k in commands)
                               print("\\" + k + "\t" + commands[k][0]);
                       }],
                "b" : ["Show builtin functions", function () { for (var k in builtins) print(k); }],
                "m" : ["Show macros", function () { for (var k in macros) print(k); }],
                "s" : ["Show special forms", function () { for (var k in specials) print(k); }],
                "f" : ["Show global functions", function () {
                           for (var k in genv)
                           {
                               var sym = genv[k];
                               if (hasSymbolType(sym, SYM_FUNCTION))
                                   print(sym.name + "\t" + tos(getSymbolValue(sym, SYM_FUNCTION)));
                           }
                       }],
                "v" : ["Show global variables", function () {
                           for (var k in genv)
                           {
                               var sym = genv[k];
                               if (hasSymbolType(sym, SYM_VARIABLE))
                                   print(sym.name + "\t" + tos(getSymbolValue(sym, SYM_VARIABLE)));
                           }
                       }],
                "j" : ["Evaluate JavaScript Code", function () {
                           print("Input JavaScript Code");
                           try {
                               print(">> " + eval(readline()));
                           } catch (x) {
                               print(x);
                           }
                       }]
            };

            print("------------------------------------------------------------");

            (commands[input[1]] || commands["?"])[1]();

            print("------------------------------------------------------------");

            continue;
        }

        try {
            evalLisp(input).map(function (result) { return tos(result); }).forEach(
                function (str) { print("=> " + str); }
            );
        } catch (x) {
            if (x.stack)
                print("js error ::\n" + x + "\n" + x.stack);
            else
                print("error :: " + x);
        }
    }
}

