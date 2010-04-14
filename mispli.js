#!/usr/bin/js

/**
 * @fileOverview LISP like
 * @name mispli
 * @author mooz <stillpedant@gmail.com>
 * @license The MIT License
 */

// Envs

var genv     = {};
var builtins = {};
var specials = {};

// ====================================================================== //

const T_ATOM_UISYMBOL = 1;
const T_ATOM_SYMBOL   = 2;
const T_ATOM_STRING   = 3;
const T_ATOM_NUMBER   = 4;

const T_ATOM_T        = 5;
const T_ATOM_NIL      = 6;

function createAtom(type, name, value) {
    return {
        type  : type,
        name  : name,
        value : value
    };
}

function createUISymbol(name) { return createAtom(T_ATOM_UISYMBOL, name); } // uninterned symbol
function createString(value) { return createAtom(T_ATOM_STRING, null, value); }
function createNumber(value) { return createAtom(T_ATOM_NUMBER, null, value); }

function atomToString(atom) {
    // list is not an atom...
    if (atom instanceof Array)
        return "(" + atom.map(atomToString).join(" . ") + ")";

    switch (atom.type)
    {
    case T_ATOM_UISYMBOL:
    case T_ATOM_SYMBOL:
        return atom.name;
        break;
    case T_ATOM_STRING:
        return "\"" + atom.value + "\"";
        break;
    case T_ATOM_NUMBER:
        return atom.value;
        break;
    case T_ATOM_T:
        return "t";
        break;
    case T_ATOM_NIL:
        return "nil";
        break;
    }
}

// ====================================================================== //

const TYPE_VARIABLE = 1;
const TYPE_FUNCTION = 2;
const TYPE_CONSTANT = 3;

function Symbol(type, val) {
    switch (type)
    {
    case TYPE_CONSTANT:
        this.constant = true;
        this.value    = (arguments.length < 2) ? this : val;
        this.cbound   = true;
        break;
    case TYPE_VARIABLE:
        this.value  = val;
        this.vbound = true;
        break;
    case TYPE_FUNCTION:
        this.func   = val;
        this.fbound = true;
        break;
    }

    this.attributes = {};
}

var t   = createAtom(T_ATOM_T);
var nil = createAtom(T_ATOM_NIL);

function isNil (exp) exp === nil;
function isTrue (exp) !isNil(exp);

function car(list) isNil(list) ? nil : list[0];
function cdr(list) isNil(list) ? nil : list[1];
function cadr(list) isNil(list) ? nil : list[1][0];
function cddr(list) isNil(list) ? nil : list[1][1];

function cons(a, b) [a, b];

function processSpecial(op, form) { /* ^^ */ }

function dir(obj) {
    for (k in obj)
        print(k + " : " + obj[k]);
}

function Eval(form) {
    if (form instanceof Array)
    {
        // list

        var op = car(form);

        if (op.type !== T_ATOM_UISYMBOL && op.type !== T_ATOM_SYMBOL)
            throw atomToString(op) + " is not a function";

        if (op.name in specials)
            return processSpecial(op.name, form); // special form
        else
        {
            if (op.name in builtins)
            {
                var args = cdr(form);
                return builtins[op.name].call(null, args);
            }
            else if (op in genv && genv[op.name].fbound)
            {
                // Not implemented yet
                // var lambda = genv[op];
                // cdr(lambda);
            }
            else
                throw "void function " + atomToString(op);
        }
    }
    else
    {
        // atom

        var atom = form;

        switch (atom.type)
        {
        case T_ATOM_UISYMBOL:
        case T_ATOM_SYMBOL:
            var name     = atom.name;
            var variable = genv[name];

            if (variable && variable.vbound)
                return variable.value;
            else
                throw "void variable " + atomToString(atom);
            break;
        case T_ATOM_STRING:
        case T_ATOM_NUMBER:
        case T_ATOM_T:
        case T_ATOM_NIL:
            return atom;
            break;
        }
    }
}

function argCount(args) {
    var count = 0;
    while (isTrue(cdr(args)))
        count++, args = cdr(args);
    return count;
}

function builtin(name, func) { builtins[name] = func; }

builtin(
    'if',
    function ([pred, form]) {
        var tform = car(form);
        var fform = cdr(form);

        if (isTrue(Eval(pred)))
            return Eval(tform);
        else if (fform)
            return Eval(['progn', fform]);
        return nil;
    }
);

builtin(
    'while',
    function (pred, form) {
        while (isTrue(Eval(pred)))
            Eval(form);
        return t;
    });

builtin(
    'progn',
    function (lst) {
        var val = nil;
        for (var i = 0; i < lst.length; ++i)
            val = Eval(lst[i]);
        return val;
    });

builtin('quote', function (lst) { return car(lst); });
builtin('cons', function (lst) { return [Eval(car(lst)), Eval(cadr(lst))]; });
builtin('car', function (lst) { return Eval(car(lst)); });
builtin('cdr', function (lst) { return Eval(cdr(lst)); });
builtin('cadr', function (lst) { return Eval(cadr(lst)); });
builtin('cddr', function (lst) { return Eval(cddr(lst)); });

builtin('+', function (lst) {
            for (var v = 0; isTrue(car(lst)); lst = cdr(lst))
                v += Eval(car(lst)).value;
            return createNumber(v);
        });
builtin('-', function (lst) {
            for (var v = 0; isTrue(car(lst)); lst = cdr(lst))
                v -= Eval(car(lst)).value;
            return createNumber(v);
        });
builtin('*', function (lst) {
            for (var v = 1; isTrue(car(lst)); lst = cdr(lst))
                v *= Eval(car(lst)).value;
            return createNumber(v);
        });
builtin('/', function (lst) {
            for (var v = Eval(car(lst)).value; isTrue(cdr(lst)); v /= Eval(car(lst)).value)
                lst = cdr(lst);
            return createNumber(v);
        });
builtin('%', function (lst) {

            for (var v = Eval(car(lst)).value; isTrue(cdr(lst)); v %= Eval(car(lst)).value)
                lst = cdr(lst);
            return createNumber(v);
        });

builtin('=',  function ([a, b]) Eval(a) == Eval(car(b)) ? t : nil);
builtin('<',  function ([a, b]) Eval(a) <  Eval(car(b)) ? t : nil);
builtin('<=', function ([a, b]) Eval(a) <= Eval(car(b)) ? t : nil);
builtin('>',  function ([a, b]) Eval(a) >  Eval(car(b)) ? t : nil);
builtin('>=', function ([a, b]) Eval(a) >= Eval(car(b)) ? t : nil);

builtin('print', function (lst) { var v = Eval(car(lst)); print(atomToString(v)); return v; });

builtin('1-', function (lst) Eval(car(lst)) - 1);
builtin('1+', function (lst) Eval(car(lst)) + 1);

// ====================================================================== //

function Parser() {
}

Parser.prototype = {
    parse: function (str) {
        this.i    = 0;
        this.str  = str;
        this.slen = str.length;

        this.skip();

        return this.parseElement();
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

        if (current === "(")
            return this.parseList();
        else if (current === "\"")
            return this.parseString();
        else
            return this.parseSymbolOrNumber(); // or number
    },

    parseList: function parseList() {
        var list = [];

        if (this.getCurrent() !== "(")
            throw "parseList : ParseError";

        while (this.peekCurrent() !== ")" && !this.eos())
        {
            this.skip();
            list.push(this.parseElement());
        }

        if (this.getCurrent() !== ")")
            throw "parseList : Unclosed Parenthethis";

        var slist = nil;

        while (list.length)
            slist = [list.pop(), slist];

        return slist;
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
        const symbolp = /[a-zA-Z0-9*&^%$@!~_+=./-]/;

        var buffer = [];

        while (symbolp.test(this.peekCurrent()) && !this.eos())
            buffer.push(this.getCurrent());

        if (!buffer.length)
            throw "parseSymbol : Parse error";

        var symbolName = buffer.join("");

        if (/^[0-9.e-]+$/.test(symbolName))
        {
            // var dotMatch = symbolName.match(/[.]/g);
            // var dotCount = dotMatch ? dotMatch.length : 0;

            // /([.]|e[0-9]+)/;

            return createNumber(parseFloat(symbolName));
        }

        return createUISymbol(symbolName);
    }
};

// ====================================================================== //
// Test
// ====================================================================== //

var checker = (function () {
                   var p = new Parser();

                   return function (str) {
                       return atomToString(Eval(p.parse(str)));
                   };
               })();

// ;; (equal
// ;;  '(:a (:b :c))
// ;;  '(:a . ((:b :c) . nil)))
// ;; => t

function assert(exp, result) {
    if (exp === result)
        print("=> Test passed");
    else
        print("=> expects " + exp + " but got " + result);
}

var evs = (function () {
               var parser = new Parser();

               return function evs(str) {
                   return Eval(parser.parse(str));
               };
           })();

assert(evs("()"), nil);
assert(evs("1"), 1);
