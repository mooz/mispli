/**
 * @fileOverview small lisp implementation written in javascript
 * @name mispli
 * @author mooz <stillpedant@gmail.com>
 * @license The MIT License
 */

var Mispli = (function () {
  // ====================================================================== //
  // Class variables (private)
  // ====================================================================== //

  var globalEnv   = {};
  var currentEnvs = [];
  var builtins    = {};
  var specials    = {};
  var macros      = {};

  const ATOM_SYMBOL  = 1;
  const ATOM_STRING  = 2;
  const ATOM_NUMBER  = 3;
  const SP_CLOSURE   = 4;

  const SYM_VARIABLE = 1;
  const SYM_FUNCTION = 2;
  const SYM_CONSTANT = 3;

  const ENV_TRANSPARENT = 1;
  const ENV_BARRIER     = 2;

  const EVAL_INNER_ENV = 1;
  const EVAL_OUTER_ENV = 2;
  const EVAL_NOTHING   = 3;

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
  var symDeclare  = createSymbol('declare');
  var symSpecial  = createSymbol('special');
  var symRest     = createSymbol('&rest');
  var symOptional = createSymbol('&optional');
  var symKey      = createSymbol('&key');
  var symDot      = createSymbol('.');

  // ====================================================================== //
  // Public
  // ====================================================================== //

  var self = {
    // constants
    SYM_FUNCTION   : SYM_FUNCTION,
    SYM_VARIABLE   : SYM_VARIABLE,
    SYM_CONSTANT   : SYM_CONSTANT,
    // Envs
    globalEnv      : globalEnv,
    currentEnvs    : currentEnvs,
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
    parse          : function () { return parser.parse.apply(parser, arguments); },
    evalBlock      : Eval,
    evalLisp       : evalLisp,
    sexpToStr      : sexpToStr,
    syntaxChecker  : syntaxChecker,
    // customize this (ex: Mispli.print = window.alert;)
    print          : function (msg) { if (typeof console !== "undefined") console.log(msg); }
  };

  // ====================================================================== //
  // Env
  // ====================================================================== //

  function createEnv(type) {
    return {
      type     : type,
      locals   : {},
      dynamics : {}
    };
  }

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

  function intern(name, env) {
    env = env || globalEnv;
    if (!(name in env))
    {
      env[name] = createSymbol(name);
      env[name].value = {};
    }
    return env[name];
  }

  function unIntern(name, env) {
    env = env || globalEnv;
    delete env[name];
  }

  function setSymbolValue(symbol, type, value) {
    if (symbol.type !== ATOM_SYMBOL)
      throw "invalid assignment";

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

  // uiSym :=> un interned symbol
  function setVariable(uiSym, value, constant, envs) {
    if (!isSymbol(uiSym))
      throw "wrong type symbolp " + sexpToStr(uiSym);

    if (isKeyword(uiSym))
      throw "setting value to the keyword";

    var sym = findSymbol(uiSym.name, SYM_VARIABLE, envs);

    if (!sym && findSymbol(uiSym.name, SYM_CONSTANT, envs))
      throw "setting value to the constant";

    if (!sym)
      sym = intern(uiSym.name); // create the global variable

    setSymbolValue(sym, constant ? SYM_CONSTANT : SYM_VARIABLE, value);

    return value;
  }

  function setFunction(uiSym, func) {
    if (!isSymbol(uiSym))
      throw "wrong type symbolp" + sexpToStr(uiSym);

    // functions becomes automatically global
    var sym = intern(uiSym.name);
    setSymbolValue(sym, SYM_FUNCTION, func);

    return func;
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

  function isKeyword(symbol) {
    return symbol.name && symbol.name[0] === ":";
  }

  function isConstantSymbol(symbol) {
    return hasSymbolType(symbol, SYM_CONSTANT) || isKeyword(symbol);
  }

  // ====================================================================== //
  // Symbol / Env
  // ====================================================================== //

  function findSymbolInEnv(name, type, env) {
    if ((name in env) && (!type || hasSymbolType(env[name], type)))
      return env[name];
  }

  function findSymbol(name, type, envs) {
    var env, sym, i;
    envs = envs || currentEnvs;

    if (envs.length)
    {
      // local variable (in current scope created by function)
      if ((sym = findSymbolInEnv(name, type, envs[envs.length - 1].locals)))
        return sym;

      // local variable or variables in closure (in current outer scope created by `let')
      for (i = envs.length - 2; i >= 0; --i)
      {
        if (envs[i].type !== ENV_TRANSPARENT)
          break;
        if ((sym = findSymbolInEnv(name, type, envs[i].locals)))
          return sym;
      }

      // dynamic variable
      for (i = 0; i >= 0; --i)
        if ((sym = findSymbolInEnv(name, type, envs[i].dynamics)))
          return sym;
    }

    // global variable
    return findSymbolInEnv(name, type, globalEnv);
  }

  // ====================================================================== //
  // Closure
  // ====================================================================== //

  function copyAccessibleEnvs(envs) {
    var copied = [];

    for (var i = envs.length - 1; i >= 0; --i)
    {
      if (envs[i].type !== ENV_TRANSPARENT)
      {
        // copy last accessible env by changing its type
        var last = {};
        for (var k in envs[i])
          last[k] = envs[i][k];
        last.type = ENV_TRANSPARENT; // this is important
        copied.unshift(last);
        break;
      }
      copied.unshift(envs[i]);
    }

    return copied;
  }

  function createClosure(lambda, envs) {
    return {
      type   : SP_CLOSURE,
      lambda : lambda,
      envs   : copyAccessibleEnvs(envs)
    };
  }

  // ====================================================================== //
  // List <=> Array Transformation
  // ====================================================================== //

  function listToArray(lst) {
    if (isNil(lst))
      return [];

    for (var array = []; isTrue(cdr(lst)); lst = cdr(lst))
    {
      if (!isList(cdr(lst)))
        throw "non-pure list is given";
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

  function eachL(func, lst) {
    var i = 0;
    while (isList(lst) && isTrue(lst))
    {
      func(car(lst), cdr(lst), i++);
      lst = cdr(lst);
    }
  }

  function everyL(func, lst) {
    var i = 0;
    while (isList(lst) && isTrue(lst))
    {
      if (!func(car(lst), cdr(lst), i++))
        return false;
      lst = cdr(lst);
    }
    return true;
  }

  function someL(func, lst) {
    var i = 0;
    while (isList(lst) && isTrue(lst))
    {
      if (func(car(lst), cdr(lst), i++))
        return true;
      lst = cdr(lst);
    }
    return false;
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

  function isNil(x)    { return x.name && x.name === "nil"; }
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
        throw "wrong type argument listp " + sexpToStr(arguments[i]);

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

        if (isCons(args[i + 1]))
        {
          // with defalut value e.g. (&optional (x 10))
          pArgs.push(car(args[i + 1]));
          pVals.push(vals[j] || cadr(args[i + 1]));
        }
        else
        {
          pArgs.push(args[i + 1]);
          pVals.push(vals[j] || symNil);
        }

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
          throw argErrorMessage(j + 1, j);

        pArgs.push(args[i]);
        pVals.push(vals[j]);
      }
    }

    while (j < vals.length)
      pVals.push(vals[j++]);

    return { args: pArgs, vals: pVals };
  }

  function validateFunction(func) {
    var optional;

    if (!equal(car(func), symLambda) ||
        !everyL(function (elem) {
          if (isSymbol(elem))
          {
            optional = equal(elem, symOptional);
            return true;
          }
          else if (isList(elem))
          {
            if (!optional)
              return false;
            return isSymbol(car(elem)) && isNil(cddr(elem));
          }
          optional = false;
          return false;
        }, cadr(func)))
      throw "invalid function " + sexpToStr(func);
  }

  function evalFunctionBody(body, args, vals, envs, envType, evalType) {
    if (args.length !== vals.length)
      throw argErrorMessage(args.length, vals.length);

    var specialVars = {};

    // special variables
    if (isList(car(body)) && equal(caar(body), symDeclare))
    {
      var declarations = cdar(body);
      body = cdr(body);

      eachL(function (pair) {
        var type = car(pair), sym = cadr(pair);

        if (!isSymbol(type) || !isSymbol(sym))
          throw "wrong type symbolp";

        if (equal(type, symSpecial) && !isNil(sym))
          specialVars[sym.name] = true;
      }, declarations);
    }

    var env = createEnv(envType);

    if (evalType === EVAL_INNER_ENV)
      envs.push(env);

    for (var i = 0; i < args.length; ++i)
    {
      var sym = intern(args[i].name, env.locals);
      var val = (evalType === EVAL_NOTHING) ? vals[i] : Eval(vals[i], envs);
      setSymbolValue(sym, SYM_VARIABLE, val);

      // special variable
      if (specialVars[sym.name])
        env.dynamics[sym.name] = sym;
    }

    if (evalType !== EVAL_INNER_ENV)
      envs.push(env);

    var error;
    try {
      var val = Eval(cons(symProgn, body), envs);
    } catch (x) {
      error = x;
    }
    envs.pop();

    if (error)
      throw error;
    return val;
  }

  function evalFunction(func, vals, envs, envType) {
    envType = envType || ENV_BARRIER;

    if (isSymbol(func))
    {
      // macro
      if (func.name in macros)
      {
        var expanded = evalFunction(macros[func.name], vals, envs);
        return Eval(expanded, envs);
      }

      // built-in function
      if (func.name in builtins)
        return builtins[func.name](arrayToList(vals.map(curry2(Eval, envs))), envs);

      // lisp global function. find function from globalEnv
      var symFunc;
      if ((symFunc = findSymbol(func.name, SYM_FUNCTION)))
        func = getSymbolValue(symFunc, SYM_FUNCTION);
      else
        throw "void function " + sexpToStr(func);

      vals = vals.map(curry2(Eval, envs));
    }
    else
    {
      // law closure like (lambda () ...)
      envType = ENV_TRANSPARENT; // important
    }

    if (func && func.type && func.type === SP_CLOSURE)
    {
      // lexical closure
      var closure = func;
      func = closure.lambda;
      envs = (envs || []).concat(closure.envs);
    }

    validateFunction(func);

    var body = cddr(func);
    var args = listToArray(cadr(func));
    var processed = processArgKeywords(args, vals);

    args = processed.args;
    vals = processed.vals;

    return evalFunctionBody(body, args, vals, envs, envType, EVAL_NOTHING);
  }

  var evalDepth    = 0;
  var maxEvalDepth = 1000000;
  // maxEvalDepth = -1;

  function Eval(form, envs) {
    // [...].map(Eval) => env becomes the index (number)
    if (!(envs instanceof Array))
      envs = currentEnvs;

    if (maxEvalDepth > 0 && ++evalDepth > maxEvalDepth)
      throw "eval depth exceeds maxEvalDepth (" + maxEvalDepth + ")";

    if (isCons(form))
    {
      var sym  = car(form);
      var args = cdr(form);

      if (isSymbol(sym))
      {
        try
        {
          if (sym.name in specials)
            return specials[sym.name](args, envs);
          else
            return evalFunction(sym, listToArray(args), envs);
        } catch (x) { throw sym.name + " : " + x; }
      }

      // ((lambda () ...) ...)
      // We does not need to create the closure
      if (isCons(sym) && equal(car(sym), symLambda))
        return evalFunction(car(form), listToArray(args).map(curry2(Eval)), envs, ENV_TRANSPARENT);

      throw "invalid function " + sexpToStr(sym);
    }
    else
    {
      var atom = form;

      switch (atom.type)
      {
      case ATOM_SYMBOL:
        if (isKeyword(atom)) // keyword
          return atom;

        var sym;

        if ((sym = findSymbol(atom.name, SYM_CONSTANT, envs)))
          return getSymbolValue(sym, SYM_CONSTANT);

        if ((sym = findSymbol(atom.name, SYM_VARIABLE, envs)))
          return getSymbolValue(sym, SYM_VARIABLE);

        throw "void variable " + sexpToStr(atom);
      case ATOM_STRING:
      case ATOM_NUMBER:
      case SP_CLOSURE:
        return atom;
      default:
        throw "unknown atom passed";
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
  function assertArgCountL(expects, op, args) {
    var count;
    if (!op(count = argCount(args), expects))
      throw argErrorMessage(expects, count);
  }

  // Array
  function assertArgCountA(expects, op, args) {
    if (!op(args.length, expects))
      throw argErrorMessage(expects, args.length);
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

  special('defvar', function (lst, envs) {
    assertArgCountL(1, argGte, lst);
    assertArgCountL(2, argLte, lst);

    var uiSym = car(lst);

    if (!isSymbol(uiSym))
      throw "wrong type argument listp " + sexpToStr(uiSym);

    var sym = intern(uiSym.name, globalEnv);

    if (hasSymbolType(sym, SYM_CONSTANT))
      throw "setting value to the constant " + sexpToStr(uiSym);

    if (!hasSymbolType(sym, SYM_VARIABLE))
      setSymbolValue(sym, SYM_VARIABLE, cadr(lst));

    return sym;
  });

  special(['quote', 'function'], function (lst, envs) {
    assertArgCountL(1, argEq, lst);

    return car(lst);
  });

  special('set', function (lst, envs) {
    assertArgCountL(2, argEq, lst);

    var sym = Eval(car(lst));
    var val = Eval(cadr(lst));
    setVariable(sym, val, false, envs);

    return val;
  });

  special('setq', function (lst, envs) {
    var args = listToArray(lst);

    for (var i = 0; i < args.length; i += 2)
    {
      var sym = args[i];
      var val = Eval(args[i + 1] || symNil, envs);
      setVariable(sym, val, false, envs);
    }

    return val;
  });

  special('defun', function (lst, envs) {
    // (defun NAME ARGLIST [BODY ...])
    assertArgCountL(2, argGte, lst);

    var name  = car(lst);
    var pargs = cadr(lst);
    var body  = cddr(lst);

    var func = cons(symLambda, cons(pargs, body));
    setFunction(name, createClosure(func, envs));

    return symNil;
  });

  function doLet(lst, evalType, envs) {
    // (let VARLIST BODY...)
    assertArgCountL(1, argGte, lst);

    var vlist = listToArray(car(lst));
    var body  = cdr(lst);

    var args = vlist.map(function (pair) { return isList(pair) ? car(pair)  : pair; });
    var vals = vlist.map(function (pair) { return isList(pair) ? cadr(pair) : symNil; });

    return evalFunctionBody(body, args, vals, envs, ENV_TRANSPARENT, evalType);
  }

  special('let', function (lst, envs) { return doLet(lst, EVAL_OUTER_ENV, envs); });
  special('let*', function (lst, envs) { return doLet(lst, EVAL_INNER_ENV, envs); });

  special('lambda', function (lst, envs) {
    return createClosure(cons(symLambda, lst), envs);
  });

  special('time', function (lst, envs) {
    assertArgCountL(1, argEq, lst);

    var begin = +new Date();
    Eval(car(lst), envs);
    var end = +new Date();

    return createNumber((end - begin) / 1000);
  });

  // ====================================================================== //
  // Special forms / Control Structures
  // ====================================================================== //

  special('cond', function (lst, envs) {
    do
    {
      var clause = car(lst);

      if (isList(clause))
      {
        var condResult;
        if (isTrue(condResult = Eval(car(clause), envs)))
        {
          return isNil(cdr(clause)) ? condResult : Eval(cadr(clause), envs);
        }
      }
      else
        throw "wrong type argument listp " + sexpToStr(lst);

      lst = cdr(lst);
    } while (isTrue(clause));

    return symNil;
  });

  special('if', function (lst, envs) {
    assertArgCountL(2, argGte, lst);

    var test  = car(lst);
    var tform = cadr(lst);
    var fform = cddr(lst);

    if (isTrue(Eval(test, envs)))
      return Eval(tform, envs);

    fform = listToArray(fform);

    var val = symNil;
    for (var i = 0; i < fform.length; ++i)
      val = Eval(fform[i], envs);
    return val;
  });

  special('while', function (lst, envs) {
    assertArgCountL(1, argGte, lst);

    var test = car(lst);
    var body = cdr(lst);
    body = listToArray(body);
    while (isTrue(Eval(test, envs)))
      for (var i = 0; i < body.length; ++i)
        Eval(body[i], envs);
    return symNil;
  });

  function progn(lst, envs) {
    var body = listToArray(lst);
    var val = symNil;
    for (var i = 0; i < body.length; ++i)
      val = Eval(body[i], envs);
    return val;
  }

  special('progn', progn);

  special('prog1', function (lst, envs) {
    assertArgCountL(1, argGte, lst);
    var first = Eval(car(lst, envs));
    progn(cdr(lst), envs);
    return first;
  });

  special('prog2', function (lst, envs) {
    assertArgCountL(2, argGte, lst);
    var first  = Eval(car(lst), envs);
    var second = Eval(cadr(lst), envs);
    progn(cddr(lst), envs);
    return second;
  });

  special('and', function (lst, envs) {
    var conditions = listToArray(lst);
    var v = symTrue;
    for (var i = 0; i < conditions.length; ++i)
      if (isNil(v = Eval(conditions[i], envs)))
        return symNil;
    return v;
  });

  special('or', function (lst, envs) {
    var conditions = listToArray(lst);
    var v = symTrue;
    for (var i = 0; i < conditions.length; ++i)
      if (isTrue(v = Eval(conditions[i], envs)))
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

  special('defmacro', function (lst, envs) {
    assertArgCountL(2, argGte, lst);

    var name  = car(lst);
    var pargs = cadr(lst);
    var body  = cddr(lst);

    setMacro(name, cons(symLambda, cons(pargs, body)));

    return symNil;
  });

  special('macroexpand', function (lst, envs) {
    assertArgCountL(1, argGte, lst);

    var form = Eval(car(lst), envs);

    var sym  = car(form);
    var args = cdr(form);

    if (!isSymbol(sym) || !(sym.name in macros))
      return form;

    var expanded = evalFunction(macros[sym.name], listToArray(args), envs);

    return expanded;
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

  builtin(['eq', 'eql'], function (lst, envs) {
    assertArgCountL(2, argEq, lst);
    return boxBool[eq(car(lst), cadr(lst))];
  });
  builtin('equal', function (lst, envs) {
    assertArgCountL(2, argEq, lst);
    return boxBool[equal(car(lst), cadr(lst))];
  });
  builtin(['null', 'not'], function (lst, envs) {
    assertArgCountL(1, argEq, lst);
    return boxBool[isNil(car(lst))];
  });
  builtin('symbolp', function (lst, envs) {
    assertArgCountL(1, argEq, lst);
    return boxBool[isSymbol(car(lst))];
  });
  builtin('atom', function (lst, envs) {
    assertArgCountL(1, argEq, lst);
    return boxBool[isAtom(car(lst))];
  });
  builtin('consp', function (lst, envs) {
    assertArgCountL(1, argEq, lst);
    return boxBool[isCons(car(lst))];
  });
  builtin('listp', function (lst, envs) {
    assertArgCountL(1, argEq, lst);
    return boxBool[isList(car(lst))];
  });
  builtin('numberp', function (lst, envs) {
    assertArgCountL(1, argEq, lst);
    return boxBool[isNumber(car(lst))];
  });
  builtin('stringp', function (lst, envs) {
    assertArgCountL(1, argEq, lst);
    return boxBool[isString(car(lst))];
  });
  builtin('boundp', function (lst, envs) {
    assertArgCountL(1, argEq, lst);
    var uiSym = car(lst);

    var sym = findSymbolInEnv(uiSym.name, SYM_CONSTANT, globalEnv)
          || findSymbolInEnv(uiSym.name, SYM_VARIABLE, globalEnv);

    return boxBool[!!sym];
  });
  builtin('fboundp', function (lst, envs) {
    assertArgCountL(1, argEq, lst);

    var uiSym = car(lst);

    return boxBool[((uiSym.name in builtins) ||
                    (uiSym.name in specials) ||
                    (uiSym.name in macros)   ||
                    !!findSymbolInEnv(uiSym.name, SYM_FUNCTION, globalEnv))];
  });

  // ====================================================================== //
  // Builtin functions / Evaluation
  // ====================================================================== //

  builtin('eval', function (lst, envs) {
    assertArgCountL(1, argEq, lst);
    return Eval(car(lst), envs);
  });

  builtin('funcall', function (lst, envs) {
    assertArgCountL(1, argGte, lst);
    return evalFunction(car(lst), listToArray(cdr(lst)), envs);
  });

  builtin('apply', function (lst, envs) {
    assertArgCountL(1, argGte, lst);

    var args = listToArray(lst);
    var vals = Array.prototype.slice.call(args, 1, args.length - 1);
    vals = vals.concat(listToArray(args[args.length - 1]));

    return evalFunction(car(lst), vals, envs);
  });

  // ====================================================================== //
  // Builtin functions / List processing
  // ====================================================================== //

  builtin('cons', function (lst) { assertArgCountL(2, argEq, lst); return cons(car(lst), cadr(lst)); });
  builtin('car',  function (lst) { assertArgCountL(1, argEq, lst); return car(car(lst)); });
  builtin('cdr',  function (lst) { assertArgCountL(1, argEq, lst); return cdr(car(lst)); });
  builtin('caar', function (lst) { assertArgCountL(1, argEq, lst); return caar(car(lst)); });
  builtin('cadr', function (lst) { assertArgCountL(1, argEq, lst); return cadr(car(lst)); });
  builtin('cdar', function (lst) { assertArgCountL(1, argEq, lst); return cdar(car(lst)); });
  builtin('cddr', function (lst) { assertArgCountL(1, argEq, lst); return cddr(car(lst)); });

  builtin(['setcar', 'rplaca'], function (lst) {
    assertArgCountL(2, argEq, lst);
    if (!isCons(car(lst)))
      throw "wrong type argument consp " + sexpToStr(car(lst));
    return setCar(car(lst), cadr(lst));
  });
  builtin(['setcdr', 'rplacd'], function (lst) {
    assertArgCountL(2, argEq, lst);
    if (!isCons(car(lst)))
      throw "wrong type argument consp " + sexpToStr(car(lst));
    return setCdr(car(lst), cadr(lst));
  });

  builtin('list', function (lst) { return lst; });
  builtin('tail', function (lst) { assertArgCountL(1, argEq, lst); return tail(car(lst)); });
  builtin('append', function (lst) { return append.apply(null, listToArray(lst)); });

  function mapList(func, seq) {
    if (!isList(seq))
      throw "wrong type listp " + sexpToStr(seq);

    return arrayToList(listToArray(seq).map(func));
  }

  builtin('mapc', function (lst, envs) {
    assertArgCountL(2, argGte, lst);

    var func = car(lst), seq = cadr(lst);

    mapList(function (elem) { return evalFunction(func, [elem], envs); }, seq);

    return seq;
  });

  builtin('mapcar', function (lst, envs) {
    assertArgCountL(2, argGte, lst);

    var func = car(lst), seq = cadr(lst);

    return mapList(function (elem) { return evalFunction(func, [elem], envs); }, seq);
  });

  builtin('some', function (lst, envs) {
    assertArgCountL(2, argEq, lst);

    var func = car(lst), seq = cadr(lst);

    return boxBool[
      someL(function (elem, rest, i) {
        return isTrue(evalFunction(func, [elem], envs));
      }, seq)];
  });

  builtin('every', function (lst, envs) {
    assertArgCountL(2, argEq, lst);

    var func = car(lst), seq = cadr(lst);

    return boxBool[
      everyL(function (elem, rest, i) {
        return isTrue(evalFunction(func, [elem], envs));
      }, seq)];
  });

  builtin('assoc', function (lst, envs) {
    assertArgCountL(2, argEq, lst);

    var key = car(lst), alist = cadr(lst);
    var found = symNil;

    someL(function (pair) {
      if (equal(key, car(pair)))
        return found = pair;
    }, alist);

    return found;
  });

  builtin('rassoc', function (lst, envs) {
    assertArgCountL(2, argEq, lst);

    var key = car(lst), alist = cadr(lst);
    var found = symNil;

    someL(function (pair) {
      if (equal(key, cdr(pair)))
        return found = pair;
    }, alist);

    return found;
  });

  // ====================================================================== //
  // Builtin functions / Operators
  // ====================================================================== //

  builtin('+', function (lst) {
    var args = listToArray(lst);

    for (var i = 0, v = 0; i < args.length; ++i)
      v += args[i].value;

    return createNumber(v);
  });
  builtin('-', function (lst) {
    var args = listToArray(lst);

    if (!args.length)
      return createNumber(0);

    var x = args[0];

    if (args.length === 1)
      return createNumber(-x.value);

    for (var i = 1, v = x.value; i < args.length; ++i)
      v -= args[i].value;

    return createNumber(v);
  });
  builtin('*', function (lst) {
    var args = listToArray(lst);

    for (var i = 0, v = 1; i < args.length; ++i)
      v *= args[i].value;

    return createNumber(v);
  });
  builtin('/', function (lst) {
    assertArgCountL(2, argGte, lst);

    var args = listToArray(lst);
    var x    = args[0];

    for (var i = 1, v = x.value; i < args.length; ++i)
      v /= args[i].value;

    return createNumber(v);
  });
  builtin('%', function (lst) {
    assertArgCountL(2, argEq, lst);

    return createNumber(car(lst).value % cadr(lst).value);
  });

  builtin('1-', function (lst) { assertArgCountL(1, argEq, lst); return createNumber(car(lst).value - 1); });
  builtin('1+', function (lst) { assertArgCountL(1, argEq, lst); return createNumber(car(lst).value + 1); });

  // ====================================================================== //
  // Builtin functions / Operators
  // ====================================================================== //

  builtin('=',  function (lst) { assertArgCountL(2, argEq, lst); return boxBool[car(lst).value == cadr(lst).value]; });
  builtin('<',  function (lst) { assertArgCountL(2, argEq, lst); return boxBool[car(lst).value <  cadr(lst).value]; });
  builtin('<=', function (lst) { assertArgCountL(2, argEq, lst); return boxBool[car(lst).value <= cadr(lst).value]; });
  builtin('>',  function (lst) { assertArgCountL(2, argEq, lst); return boxBool[car(lst).value >  cadr(lst).value]; });
  builtin('>=', function (lst) { assertArgCountL(2, argEq, lst); return boxBool[car(lst).value >= cadr(lst).value]; });

  // ====================================================================== //
  // Builtin functions / IO
  // ====================================================================== //

  builtin('print', function (lst) { assertArgCountL(1, argEq, lst); self.print(sexpToStr(car(lst))); return car(lst); });

  // ====================================================================== //
  // Builtin functions / Math
  // ====================================================================== //

  builtin('abs', function (lst) { assertArgCountL(1, argEq, lst); return createNumber(Math.abs(car(lst).value)); });
  builtin('exp', function (lst) { assertArgCountL(1, argEq, lst); return createNumber(Math.exp(car(lst).value)); });
  builtin('log', function (lst) { assertArgCountL(1, argEq, lst); return createNumber(Math.log(car(lst).value)); });
  builtin('pow', function (lst) { assertArgCountL(1, argEq, lst); return createNumber(Math.pow(car(lst).value)); });
  builtin('round', function (lst) { assertArgCountL(1, argEq, lst); return createNumber(Math.round(car(lst).value)); });
  builtin('ceil', function (lst) { assertArgCountL(1, argEq, lst); return createNumber(Math.ceil(car(lst).value)); });
  builtin('sin', function (lst) { assertArgCountL(1, argEq, lst); return createNumber(Math.sin(car(lst).value)); });
  builtin('cos', function (lst) { assertArgCountL(1, argEq, lst); return createNumber(Math.cos(car(lst).value)); });
  builtin('tan', function (lst) { assertArgCountL(1, argEq, lst); return createNumber(Math.tan(car(lst).value)); });
  builtin('sqrt', function (lst) { assertArgCountL(1, argEq, lst); return createNumber(Math.sqrt(car(lst).value)); });
  builtin('random', function (lst) {
    assertArgCountL(1, argLte, lst);
    var rand = Math.random();
    return createNumber(isNil(lst) ? rand : rand * car(lst).value);
  });

  // ====================================================================== //
  // Builtin functions / Misc
  // ====================================================================== //

  builtin('iota', function (lst, env) {
    assertArgCountL(1, argGte, lst);

    var count = car(lst);
    var from  = cadr(lst);
    var delta = car(cddr(lst));

    count = count.value;

    if (count < 0)
      throw "negative count";

    from  = isNil(from) ? 0 : from.value;
    delta = isNil(delta) ? 1 : delta.value;

    var array = [createNumber(from)];
    for (var i = 1; i < count; ++i)
      array.push(createNumber(from += delta));

    return arrayToList(array);
  });

  // ====================================================================== //
  // Parser
  // ====================================================================== //

  function SexParser() {}

  SexParser.prototype = {
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

          if (this.eos())
            return forms;

          forms.push(this.parseElement());
        }

        return forms;
      }

      this.skip();

      if (this.eos()) // when blank line is given
        return null;

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
        var elem = this.parseElement();

        if (equal(elem, symDot))
        {
          if (lst.length !== 1)
            throw "parseList : . in wrong context";

          this.skip();
          var pair = [lst[0], this.parseElement()];
          this.skip();

          if (this.getCurrent() !== ")")
            throw "parseList : . in wrong context";

          return pair;
        }

        lst.push(elem);

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
      const numberPat   = /^-?[0-9]+([.][0-9]*|e-?[0-9]+)?$/;

      var buffer = [];

      while (symbolChars.test(this.peekCurrent()) && !this.eos())
        buffer.push(this.getCurrent());

      if (!buffer.length)
        throw "parseSymbolOrNumber : Parse error";

      var symbolName = buffer.join("");

      if (numberPat.test(symbolName))
        return createNumber(parseFloat(symbolName));

      return createSymbol(symbolName);
    }
  };

  var parser = new SexParser();

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

  function argErrorMessage(expects, given, name) {
    return (name ? name + " : " : "") +
      "wrong number of arguments. required " + expects + " but got " + given;
  }

  function curry2(func, arg2) {
    return function (arg1) {
      return func(arg1, arg2);
    };
  }

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
      case SP_CLOSURE:
        return "#<" + (elem.envs.length ? "lexical-closure" : "lambda") + " : " + sexpToStr(elem.lambda) + ">";
      }
    }

    return "sexpToStr : Non LISP object passed. It's value is `" + elem + "'";
  }

  function dir(obj) {
    for (k in obj)
      self.print(k + " : " + obj[k]);
  }

  function printa(atom) { self.print(sexpToStr(atom)); }

  // ====================================================================== //
  // Define misc codes
  // ====================================================================== //

  evalLisp("(defmacro when (cond &rest body) (list 'if cond (cons 'progn body)))");
  evalLisp("(defmacro unless (cond &rest body) (cons 'if (cons cond (cons nil body))))");
  evalLisp("(defmacro incf (place &optional x) (list 'setq place (list '+ place (list 'or x 1))))");
  evalLisp("(defmacro decf (place &optional x) (list 'setq place (list '- place (list 'or x 1))))");

  return self;
})();

if (typeof exports !== "undefined")
  exports.Mispli = Mispli;