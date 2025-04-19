"use strict";
var __haste_prog_id = '5bc5883e0498adfc63a0512333316a5e1f8313c9ac905fd0cede90f5b4814931';
var __haste_script_elem = typeof document == 'object' ? document.currentScript : null;
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined' && typeof global !== 'undefined') window = global;
window['__haste_crypto'] = window.crypto || window.msCrypto;
if(window['__haste_crypto'] && !window['__haste_crypto'].subtle && window.crypto.webkitSubtle) {
    window['__haste_crypto'].subtle = window.crypto.webkitSubtle;
}

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(738919189, 2683596561, true)
  var y = new Long(3648966346, 573393410, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var len = buffer.byteLength;
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': len % 2 ? null : new Int16Array(buffer)
        , 'i32': len % 4 ? null : new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': len % 2 ? null : new Uint16Array(buffer)
        , 'w32': len % 4 ? null : new Uint32Array(buffer)
        , 'f32': len % 4 ? null : new Float32Array(buffer)
        , 'f64': len % 8 ? null : new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __isUndef = function(x) {return typeof x == 'undefined';}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

/* Code for creating and querying the static pointer table. */
window.__hs_spt = [];

function __spt_insert(ptr) {
    ptr = E(B(ptr));
    var ks = [ (ptr.a.a.low>>>0).toString(16)
             , (ptr.a.a.high>>>0).toString(16)
             , (ptr.a.b.low>>>0).toString(16)
             , (ptr.a.b.high>>>0).toString(16)
             ]
    var key = ks.join();
    window.__hs_spt[key] = ptr;
}

function hs_spt_lookup(k) {
    var ks = [ k['v']['w32'][0].toString(16)
             , k['v']['w32'][1].toString(16)
             , k['v']['w32'][2].toString(16)
             , k['v']['w32'][3].toString(16)
             ]
    var key = ks.join();
    return window.__hs_spt[key];
}

var _0="deltaZ",_1="deltaY",_2="deltaX",_3=function(_4,_5){var _6=E(_4);return (_6._==0)?E(_5):new T2(1,_6.a,new T(function(){return B(_3(_6.b,_5));}));},_7=function(_8,_9){var _a=jsShowI(_8);return new F(function(){return _3(fromJSStr(_a),_9);});},_b=41,_c=40,_d=function(_e,_f,_g){if(_f>=0){return new F(function(){return _7(_f,_g);});}else{if(_e<=6){return new F(function(){return _7(_f,_g);});}else{return new T2(1,_c,new T(function(){var _h=jsShowI(_f);return B(_3(fromJSStr(_h),new T2(1,_b,_g)));}));}}},_i=new T(function(){return B(unCStr(")"));}),_j=new T(function(){return B(_d(0,2,_i));}),_k=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_j));}),_l=function(_m){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_d(0,_m,_k));}))));});},_n=function(_o,_){return new T(function(){var _p=Number(E(_o)),_q=jsTrunc(_p);if(_q<0){return B(_l(_q));}else{if(_q>2){return B(_l(_q));}else{return _q;}}});},_r=0,_s=new T3(0,_r,_r,_r),_t="button",_u=new T(function(){return eval("jsGetMouseCoords");}),_v=__Z,_w=function(_x,_){var _y=E(_x);if(!_y._){return _v;}else{var _z=B(_w(_y.b,_));return new T2(1,new T(function(){var _A=Number(E(_y.a));return jsTrunc(_A);}),_z);}},_B=function(_C,_){var _D=__arr2lst(0,_C);return new F(function(){return _w(_D,_);});},_E=function(_F,_){return new F(function(){return _B(E(_F),_);});},_G=function(_H,_){return new T(function(){var _I=Number(E(_H));return jsTrunc(_I);});},_J=new T2(0,_G,_E),_K=function(_L,_){var _M=E(_L);if(!_M._){return _v;}else{var _N=B(_K(_M.b,_));return new T2(1,_M.a,_N);}},_O=new T(function(){return B(unCStr("base"));}),_P=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Q=new T(function(){return B(unCStr("IOException"));}),_R=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_O,_P,_Q),_S=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_R,_v,_v),_T=function(_U){return E(_S);},_V=function(_W){return E(E(_W).a);},_X=function(_Y,_Z,_10){var _11=B(A1(_Y,_)),_12=B(A1(_Z,_)),_13=hs_eqWord64(_11.a,_12.a);if(!_13){return __Z;}else{var _14=hs_eqWord64(_11.b,_12.b);return (!_14)?__Z:new T1(1,_10);}},_15=function(_16){var _17=E(_16);return new F(function(){return _X(B(_V(_17.a)),_T,_17.b);});},_18=new T(function(){return B(unCStr(": "));}),_19=new T(function(){return B(unCStr(")"));}),_1a=new T(function(){return B(unCStr(" ("));}),_1b=new T(function(){return B(unCStr("interrupted"));}),_1c=new T(function(){return B(unCStr("system error"));}),_1d=new T(function(){return B(unCStr("unsatisified constraints"));}),_1e=new T(function(){return B(unCStr("user error"));}),_1f=new T(function(){return B(unCStr("permission denied"));}),_1g=new T(function(){return B(unCStr("illegal operation"));}),_1h=new T(function(){return B(unCStr("end of file"));}),_1i=new T(function(){return B(unCStr("resource exhausted"));}),_1j=new T(function(){return B(unCStr("resource busy"));}),_1k=new T(function(){return B(unCStr("does not exist"));}),_1l=new T(function(){return B(unCStr("already exists"));}),_1m=new T(function(){return B(unCStr("resource vanished"));}),_1n=new T(function(){return B(unCStr("timeout"));}),_1o=new T(function(){return B(unCStr("unsupported operation"));}),_1p=new T(function(){return B(unCStr("hardware fault"));}),_1q=new T(function(){return B(unCStr("inappropriate type"));}),_1r=new T(function(){return B(unCStr("invalid argument"));}),_1s=new T(function(){return B(unCStr("failed"));}),_1t=new T(function(){return B(unCStr("protocol error"));}),_1u=function(_1v,_1w){switch(E(_1v)){case 0:return new F(function(){return _3(_1l,_1w);});break;case 1:return new F(function(){return _3(_1k,_1w);});break;case 2:return new F(function(){return _3(_1j,_1w);});break;case 3:return new F(function(){return _3(_1i,_1w);});break;case 4:return new F(function(){return _3(_1h,_1w);});break;case 5:return new F(function(){return _3(_1g,_1w);});break;case 6:return new F(function(){return _3(_1f,_1w);});break;case 7:return new F(function(){return _3(_1e,_1w);});break;case 8:return new F(function(){return _3(_1d,_1w);});break;case 9:return new F(function(){return _3(_1c,_1w);});break;case 10:return new F(function(){return _3(_1t,_1w);});break;case 11:return new F(function(){return _3(_1s,_1w);});break;case 12:return new F(function(){return _3(_1r,_1w);});break;case 13:return new F(function(){return _3(_1q,_1w);});break;case 14:return new F(function(){return _3(_1p,_1w);});break;case 15:return new F(function(){return _3(_1o,_1w);});break;case 16:return new F(function(){return _3(_1n,_1w);});break;case 17:return new F(function(){return _3(_1m,_1w);});break;default:return new F(function(){return _3(_1b,_1w);});}},_1x=new T(function(){return B(unCStr("}"));}),_1y=new T(function(){return B(unCStr("{handle: "));}),_1z=function(_1A,_1B,_1C,_1D,_1E,_1F){var _1G=new T(function(){var _1H=new T(function(){var _1I=new T(function(){var _1J=E(_1D);if(!_1J._){return E(_1F);}else{var _1K=new T(function(){return B(_3(_1J,new T(function(){return B(_3(_19,_1F));},1)));},1);return B(_3(_1a,_1K));}},1);return B(_1u(_1B,_1I));}),_1L=E(_1C);if(!_1L._){return E(_1H);}else{return B(_3(_1L,new T(function(){return B(_3(_18,_1H));},1)));}}),_1M=E(_1E);if(!_1M._){var _1N=E(_1A);if(!_1N._){return E(_1G);}else{var _1O=E(_1N.a);if(!_1O._){var _1P=new T(function(){var _1Q=new T(function(){return B(_3(_1x,new T(function(){return B(_3(_18,_1G));},1)));},1);return B(_3(_1O.a,_1Q));},1);return new F(function(){return _3(_1y,_1P);});}else{var _1R=new T(function(){var _1S=new T(function(){return B(_3(_1x,new T(function(){return B(_3(_18,_1G));},1)));},1);return B(_3(_1O.a,_1S));},1);return new F(function(){return _3(_1y,_1R);});}}}else{return new F(function(){return _3(_1M.a,new T(function(){return B(_3(_18,_1G));},1));});}},_1T=function(_1U){var _1V=E(_1U);return new F(function(){return _1z(_1V.a,_1V.b,_1V.c,_1V.d,_1V.f,_v);});},_1W=function(_1X,_1Y,_1Z){var _20=E(_1Y);return new F(function(){return _1z(_20.a,_20.b,_20.c,_20.d,_20.f,_1Z);});},_21=function(_22,_23){var _24=E(_22);return new F(function(){return _1z(_24.a,_24.b,_24.c,_24.d,_24.f,_23);});},_25=44,_26=93,_27=91,_28=function(_29,_2a,_2b){var _2c=E(_2a);if(!_2c._){return new F(function(){return unAppCStr("[]",_2b);});}else{var _2d=new T(function(){var _2e=new T(function(){var _2f=function(_2g){var _2h=E(_2g);if(!_2h._){return E(new T2(1,_26,_2b));}else{var _2i=new T(function(){return B(A2(_29,_2h.a,new T(function(){return B(_2f(_2h.b));})));});return new T2(1,_25,_2i);}};return B(_2f(_2c.b));});return B(A2(_29,_2c.a,_2e));});return new T2(1,_27,_2d);}},_2j=function(_2k,_2l){return new F(function(){return _28(_21,_2k,_2l);});},_2m=new T3(0,_1W,_1T,_2j),_2n=new T(function(){return new T5(0,_T,_2m,_2o,_15,_1T);}),_2o=function(_2p){return new T2(0,_2n,_2p);},_2q=__Z,_2r=7,_2s=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2t=new T6(0,_2q,_2r,_v,_2s,_2q,_2q),_2u=new T(function(){return B(_2o(_2t));}),_2v=function(_){return new F(function(){return die(_2u);});},_2w=function(_2x){return E(E(_2x).a);},_2y=function(_2z,_2A,_2B,_){var _2C=__arr2lst(0,_2B),_2D=B(_K(_2C,_)),_2E=E(_2D);if(!_2E._){return new F(function(){return _2v(_);});}else{var _2F=E(_2E.b);if(!_2F._){return new F(function(){return _2v(_);});}else{if(!E(_2F.b)._){var _2G=B(A3(_2w,_2z,_2E.a,_)),_2H=B(A3(_2w,_2A,_2F.a,_));return new T2(0,_2G,_2H);}else{return new F(function(){return _2v(_);});}}}},_2I=function(_){return new F(function(){return __jsNull();});},_2J=function(_2K){var _2L=B(A1(_2K,_));return E(_2L);},_2M=new T(function(){return B(_2J(_2I));}),_2N=new T(function(){return E(_2M);}),_2O=function(_2P,_2Q,_){if(E(_2P)==7){var _2R=__app1(E(_u),_2Q),_2S=B(_2y(_J,_J,_2R,_)),_2T=__get(_2Q,E(_2)),_2U=__get(_2Q,E(_1)),_2V=__get(_2Q,E(_0));return new T(function(){return new T3(0,E(_2S),E(_2q),E(new T3(0,_2T,_2U,_2V)));});}else{var _2W=__app1(E(_u),_2Q),_2X=B(_2y(_J,_J,_2W,_)),_2Y=__get(_2Q,E(_t)),_2Z=__eq(_2Y,E(_2N));if(!E(_2Z)){var _30=__isUndef(_2Y);if(!E(_30)){var _31=B(_n(_2Y,_));return new T(function(){return new T3(0,E(_2X),E(new T1(1,_31)),E(_s));});}else{return new T(function(){return new T3(0,E(_2X),E(_2q),E(_s));});}}else{return new T(function(){return new T3(0,E(_2X),E(_2q),E(_s));});}}},_32=function(_33,_34,_){return new F(function(){return _2O(_33,E(_34),_);});},_35="mouseout",_36="mouseover",_37="mousemove",_38="mouseup",_39="mousedown",_3a="dblclick",_3b="click",_3c="wheel",_3d=function(_3e){switch(E(_3e)){case 0:return E(_3b);case 1:return E(_3a);case 2:return E(_39);case 3:return E(_38);case 4:return E(_37);case 5:return E(_36);case 6:return E(_35);default:return E(_3c);}},_3f=new T2(0,_3d,_32),_3g=function(_3h){return E(_3h);},_3i=function(_3j,_3k){return E(_3j)==E(_3k);},_3l=function(_3m,_3n){return E(_3m)!=E(_3n);},_3o=new T2(0,_3i,_3l),_3p="screenY",_3q="screenX",_3r="clientY",_3s="clientX",_3t="pageY",_3u="pageX",_3v="target",_3w="identifier",_3x=function(_3y,_){var _3z=__get(_3y,E(_3w)),_3A=__get(_3y,E(_3v)),_3B=__get(_3y,E(_3u)),_3C=__get(_3y,E(_3t)),_3D=__get(_3y,E(_3s)),_3E=__get(_3y,E(_3r)),_3F=__get(_3y,E(_3q)),_3G=__get(_3y,E(_3p));return new T(function(){var _3H=Number(_3z),_3I=jsTrunc(_3H);return new T5(0,_3I,_3A,E(new T2(0,new T(function(){var _3J=Number(_3B);return jsTrunc(_3J);}),new T(function(){var _3K=Number(_3C);return jsTrunc(_3K);}))),E(new T2(0,new T(function(){var _3L=Number(_3D);return jsTrunc(_3L);}),new T(function(){var _3M=Number(_3E);return jsTrunc(_3M);}))),E(new T2(0,new T(function(){var _3N=Number(_3F);return jsTrunc(_3N);}),new T(function(){var _3O=Number(_3G);return jsTrunc(_3O);}))));});},_3P=function(_3Q,_){var _3R=E(_3Q);if(!_3R._){return _v;}else{var _3S=B(_3x(E(_3R.a),_)),_3T=B(_3P(_3R.b,_));return new T2(1,_3S,_3T);}},_3U="touches",_3V=function(_3W){return E(E(_3W).b);},_3X=function(_3Y,_3Z,_){var _40=__arr2lst(0,_3Z),_41=new T(function(){return B(_3V(_3Y));}),_42=function(_43,_){var _44=E(_43);if(!_44._){return _v;}else{var _45=B(A2(_41,_44.a,_)),_46=B(_42(_44.b,_));return new T2(1,_45,_46);}};return new F(function(){return _42(_40,_);});},_47=function(_48,_){return new F(function(){return _3X(_J,E(_48),_);});},_49=new T2(0,_E,_47),_4a=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4b=function(_4c){return E(E(_4c).a);},_4d=function(_4e,_4f,_4g){while(1){var _4h=E(_4g);if(!_4h._){return false;}else{if(!B(A3(_4b,_4e,_4f,_4h.a))){_4g=_4h.b;continue;}else{return true;}}}},_4i=function(_4j,_4k){while(1){var _4l=B((function(_4m,_4n){var _4o=E(_4n);if(!_4o._){return __Z;}else{var _4p=_4o.a,_4q=_4o.b;if(!B(A1(_4m,_4p))){var _4r=_4m;_4j=_4r;_4k=_4q;return __continue;}else{return new T2(1,_4p,new T(function(){return B(_4i(_4m,_4q));}));}}})(_4j,_4k));if(_4l!=__continue){return _4l;}}},_4s=function(_4t,_){var _4u=__get(_4t,E(_3U)),_4v=__arr2lst(0,_4u),_4w=B(_3P(_4v,_)),_4x=__app1(E(_4a),_4t),_4y=B(_2y(_49,_49,_4x,_)),_4z=E(_4y),_4A=new T(function(){var _4B=function(_4C){return new F(function(){return _4d(_3o,new T(function(){return E(_4C).a;}),_4z.a);});};return B(_4i(_4B,_4w));}),_4D=new T(function(){var _4E=function(_4F){return new F(function(){return _4d(_3o,new T(function(){return E(_4F).a;}),_4z.b);});};return B(_4i(_4E,_4w));});return new T3(0,_4w,_4D,_4A);},_4G=function(_4H,_4I,_){return new F(function(){return _4s(E(_4I),_);});},_4J="touchcancel",_4K="touchend",_4L="touchmove",_4M="touchstart",_4N=function(_4O){switch(E(_4O)){case 0:return E(_4M);case 1:return E(_4L);case 2:return E(_4K);default:return E(_4J);}},_4P=new T2(0,_4N,_4G),_4Q=function(_4R,_4S,_){var _4T=B(A1(_4R,_)),_4U=B(A1(_4S,_));return _4T;},_4V=function(_4W,_4X,_){var _4Y=B(A1(_4W,_)),_4Z=B(A1(_4X,_));return new T(function(){return B(A1(_4Y,_4Z));});},_50=function(_51,_52,_){var _53=B(A1(_52,_));return _51;},_54=function(_55,_56,_){var _57=B(A1(_56,_));return new T(function(){return B(A1(_55,_57));});},_58=new T2(0,_54,_50),_59=function(_5a,_){return _5a;},_5b=function(_5c,_5d,_){var _5e=B(A1(_5c,_));return new F(function(){return A1(_5d,_);});},_5f=new T5(0,_58,_59,_4V,_5b,_4Q),_5g=new T(function(){return E(_2n);}),_5h=function(_5i){return E(E(_5i).c);},_5j=function(_5k){return new T6(0,_2q,_2r,_v,_5k,_2q,_2q);},_5l=function(_5m,_){var _5n=new T(function(){return B(A2(_5h,_5g,new T(function(){return B(A1(_5j,_5m));})));});return new F(function(){return die(_5n);});},_5o=function(_5p,_){return new F(function(){return _5l(_5p,_);});},_5q=function(_5r){return new F(function(){return A1(_5o,_5r);});},_5s=function(_5t,_5u,_){var _5v=B(A1(_5t,_));return new F(function(){return A2(_5u,_5v,_);});},_5w=new T5(0,_5f,_5s,_5b,_59,_5q),_5x=function(_5y){return E(_5y);},_5z=new T2(0,_5w,_5x),_5A=new T2(0,_5z,_59),_5B=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_5C=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_5D=new T(function(){return eval("(function(cv){return cv.height})");}),_5E=new T(function(){return eval("(function(cv){return cv.width})");}),_5F=function(_5G,_){var _5H=__app1(E(_5E),_5G),_5I=__app1(E(_5D),_5G),_5J=__app1(E(_5C),_5G),_5K=__app1(E(_5B),_5G);return new T2(0,new T2(0,_5H,_5I),new T2(0,_5J,_5K));},_5L=0,_5M=0,_5N=false,_5O=2,_5P=0,_5Q=true,_5R=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_5S=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_5T=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_5U=function(_5V){return E(E(_5V).b);},_5W=function(_5X,_5Y){return new F(function(){return A2(_5U,_5X,function(_){var _5Z=E(_5Y),_60=__app1(E(_5T),_5Z);if(!_60){return _2q;}else{var _61=__app1(E(_5S),_5Z);return new T1(1,new T2(0,_61,_5Z));}});});},_62=2,_63=1,_64=new T1(0,_63),_65=new T1(1,_64),_66=30,_67=100,_68=new T2(0,_67,_66),_69=new T2(1,_68,_v),_6a=370,_6b=200,_6c=80,_6d=new T4(0,_6c,_67,_6b,_6a),_6e=0,_6f=new T2(1,_6e,_v),_6g=new T(function(){return B(unCStr("\u3053\u3093\u306b\u3061\u306f\n\u5143\u6c23\u3067\u3059\u304b\uff1f"));}),_6h=new T2(1,_6g,_v),_6i=new T2(1,_63,_v),_6j=20,_6k=new T2(1,_6j,_v),_6l={_:0,a:0,b:E(_6d),c:E(_62),d:0,e:5,f:E(_69),g:E(_v),h:E(_6k),i:E(_6i),j:E(_6h),k:E(_6f),l:E(_v),m:E(_v),n:E(_2q),o:E(_65)},_6m=new T2(1,_6l,_v),_6n=new T2(0,0,0),_6o=new T5(0,E(_5N),E(_5N),E(_5N),E(_5N),E(_5N)),_6p={_:0,a:E(_2q),b:E(_6n),c:E(_2q),d:E(_2q),e:E(_6m),f:0,g:E(_6o),h:E(_v)},_6q=new T1(0,100),_6r=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:16:3-9"));}),_6s=new T6(0,_2q,_2r,_v,_6r,_2q,_2q),_6t=new T(function(){return B(_2o(_6s));}),_6u=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:17:3-8"));}),_6v=new T6(0,_2q,_2r,_v,_6u,_2q,_2q),_6w=new T(function(){return B(_2o(_6v));}),_6x=function(_6y,_6z,_6A){while(1){var _6B=E(_6A);if(!_6B._){return  -1;}else{var _6C=_6B.b,_6D=E(_6B.a),_6E=E(_6D.b),_6F=E(_6E.a);if(_6y<=_6F){_6A=_6C;continue;}else{if(_6y>=_6F+E(_6E.c)){_6A=_6C;continue;}else{var _6G=E(_6E.b);if(_6z<=_6G){_6A=_6C;continue;}else{if(_6z>=_6G+E(_6E.d)){_6A=_6C;continue;}else{return E(_6D.a);}}}}}}},_6H=function(_6I,_6J,_6K){while(1){var _6L=E(_6K);if(!_6L._){return  -1;}else{var _6M=_6L.b,_6N=E(_6L.a),_6O=E(_6N.b),_6P=E(_6O.a);if(_6I<=_6P){_6K=_6M;continue;}else{if(_6I>=_6P+E(_6O.c)){_6K=_6M;continue;}else{var _6Q=E(_6J),_6R=E(_6O.b);if(_6Q<=_6R){return new F(function(){return _6x(_6I,_6Q,_6M);});}else{if(_6Q>=_6R+E(_6O.d)){return new F(function(){return _6x(_6I,_6Q,_6M);});}else{return E(_6N.a);}}}}}}},_6S=function(_6T,_6U){while(1){var _6V=E(_6U);if(!_6V._){return __Z;}else{var _6W=E(_6V.a);if(_6T!=_6W.a){_6U=_6V.b;continue;}else{return new T1(1,_6W);}}}},_6X=new T(function(){return B(unCStr("!!: negative index"));}),_6Y=new T(function(){return B(unCStr("Prelude."));}),_6Z=new T(function(){return B(_3(_6Y,_6X));}),_70=new T(function(){return B(err(_6Z));}),_71=new T(function(){return B(unCStr("!!: index too large"));}),_72=new T(function(){return B(_3(_6Y,_71));}),_73=new T(function(){return B(err(_72));}),_74=function(_75,_76){while(1){var _77=E(_75);if(!_77._){return E(_73);}else{var _78=E(_76);if(!_78){return E(_77.a);}else{_75=_77.b;_76=_78-1|0;continue;}}}},_79=function(_7a,_7b){if(_7b>=0){return new F(function(){return _74(_7a,_7b);});}else{return E(_70);}},_7c=function(_7d,_7e){var _7f=E(_7d);if(!_7f._){var _7g=E(_7e);if(!_7g._){return new F(function(){return _3i(_7f.a,_7g.a);});}else{return false;}}else{var _7h=E(_7e);if(!_7h._){return false;}else{return new F(function(){return _3i(_7f.a,_7h.a);});}}},_7i=function(_7j,_7k){return (E(_7j)==0)?(E(_7k)==0)?false:true:(E(_7k)==0)?true:false;},_7l=function(_7m,_7n){return (E(_7m)==0)?(E(_7n)==0)?true:false:(E(_7n)==0)?false:true;},_7o=new T2(0,_7l,_7i),_7p=function(_7q,_7r,_7s){while(1){var _7t=E(_7r);if(!_7t._){return (E(_7s)._==0)?true:false;}else{var _7u=E(_7s);if(!_7u._){return false;}else{if(!B(A3(_4b,_7q,_7t.a,_7u.a))){return false;}else{_7r=_7t.b;_7s=_7u.b;continue;}}}}},_7v=function(_7w,_7x){while(1){var _7y=E(_7w);if(!_7y._){return (E(_7x)._==0)?true:false;}else{var _7z=E(_7x);if(!_7z._){return false;}else{if(E(_7y.a)!=E(_7z.a)){return false;}else{_7w=_7y.b;_7x=_7z.b;continue;}}}}},_7A=function(_7B,_7C){while(1){var _7D=E(_7B);if(!_7D._){return (E(_7C)._==0)?true:false;}else{var _7E=E(_7C);if(!_7E._){return false;}else{if(E(_7D.a)!=E(_7E.a)){return false;}else{_7B=_7D.b;_7C=_7E.b;continue;}}}}},_7F=function(_7G,_7H){while(1){var _7I=E(_7G);if(!_7I._){return (E(_7H)._==0)?true:false;}else{var _7J=E(_7H);if(!_7J._){return false;}else{if(!B(_7A(_7I.a,_7J.a))){return false;}else{_7G=_7I.b;_7H=_7J.b;continue;}}}}},_7K=function(_7L,_7M,_7N,_7O){return (_7L!=_7N)?true:(E(_7M)!=E(_7O))?true:false;},_7P=function(_7Q,_7R){var _7S=E(_7Q),_7T=E(_7R);return new F(function(){return _7K(E(_7S.a),_7S.b,E(_7T.a),_7T.b);});},_7U=function(_7V,_7W){return E(_7V)==E(_7W);},_7X=function(_7Y,_7Z,_80,_81){if(_7Y!=_80){return false;}else{return new F(function(){return _7U(_7Z,_81);});}},_82=function(_83,_84){var _85=E(_83),_86=E(_84);return new F(function(){return _7X(E(_85.a),_85.b,E(_86.a),_86.b);});},_87=new T2(0,_82,_7P),_88=function(_89,_8a,_8b,_8c,_8d,_8e,_8f,_8g,_8h,_8i,_8j,_8k,_8l,_8m,_8n,_8o,_8p,_8q,_8r,_8s,_8t,_8u,_8v,_8w,_8x,_8y,_8z,_8A,_8B,_8C,_8D,_8E,_8F,_8G,_8H,_8I){if(_89!=_8r){return false;}else{if(E(_8a)!=E(_8s)){return false;}else{if(E(_8b)!=E(_8t)){return false;}else{if(E(_8c)!=E(_8u)){return false;}else{if(E(_8d)!=E(_8v)){return false;}else{var _8J=function(_8K){if(!B(_7p(_87,_8h,_8z))){return false;}else{if(!B(_7p(_87,_8i,_8A))){return false;}else{if(!B(_7v(_8j,_8B))){return false;}else{if(!B(_7v(_8k,_8C))){return false;}else{if(!B(_7F(_8l,_8D))){return false;}else{if(!B(_7p(_7o,_8m,_8E))){return false;}else{if(!B(_7p(_87,_8n,_8F))){return false;}else{if(!B(_7v(_8o,_8G))){return false;}else{var _8L=function(_8M){var _8N=E(_8q);switch(_8N._){case 0:return (E(_8I)._==0)?true:false;case 1:var _8O=E(_8I);if(_8O._==1){return new F(function(){return _7c(_8N.a,_8O.a);});}else{return false;}break;case 2:var _8P=E(_8I);if(_8P._==2){return new F(function(){return _3i(_8N.a,_8P.a);});}else{return false;}break;default:var _8Q=E(_8I);if(_8Q._==3){return new F(function(){return _3i(_8N.a,_8Q.a);});}else{return false;}}},_8R=E(_8p);if(!_8R._){if(!E(_8H)._){return new F(function(){return _8L(_);});}else{return false;}}else{var _8S=E(_8H);if(!_8S._){return false;}else{if(E(_8R.a)!=E(_8S.a)){return false;}else{return new F(function(){return _8L(_);});}}}}}}}}}}}};switch(E(_8e)){case 0:if(!E(_8w)){if(_8f!=_8x){return false;}else{if(_8g!=_8y){return false;}else{return new F(function(){return _8J(_);});}}}else{return false;}break;case 1:if(E(_8w)==1){if(_8f!=_8x){return false;}else{if(_8g!=_8y){return false;}else{return new F(function(){return _8J(_);});}}}else{return false;}break;default:if(E(_8w)==2){if(_8f!=_8x){return false;}else{if(_8g!=_8y){return false;}else{return new F(function(){return _8J(_);});}}}else{return false;}}}}}}}},_8T=function(_8U,_8V){var _8W=E(_8U),_8X=E(_8W.b),_8Y=E(_8V),_8Z=E(_8Y.b);return (!B(_88(_8W.a,_8X.a,_8X.b,_8X.c,_8X.d,_8W.c,_8W.d,_8W.e,_8W.f,_8W.g,_8W.h,_8W.i,_8W.j,_8W.k,_8W.l,_8W.m,_8W.n,_8W.o,_8Y.a,_8Z.a,_8Z.b,_8Z.c,_8Z.d,_8Y.c,_8Y.d,_8Y.e,_8Y.f,_8Y.g,_8Y.h,_8Y.i,_8Y.j,_8Y.k,_8Y.l,_8Y.m,_8Y.n,_8Y.o)))?true:false;},_90=function(_91,_92){var _93=E(_91),_94=E(_93.b),_95=E(_92),_96=E(_95.b);return new F(function(){return _88(_93.a,_94.a,_94.b,_94.c,_94.d,_93.c,_93.d,_93.e,_93.f,_93.g,_93.h,_93.i,_93.j,_93.k,_93.l,_93.m,_93.n,_93.o,_95.a,_96.a,_96.b,_96.c,_96.d,_95.c,_95.d,_95.e,_95.f,_95.g,_95.h,_95.i,_95.j,_95.k,_95.l,_95.m,_95.n,_95.o);});},_97=new T2(0,_90,_8T),_98=function(_99,_9a){while(1){var _9b=E(_99);if(!_9b._){return (E(_9a)._==0)?true:false;}else{var _9c=E(_9a);if(!_9c._){return false;}else{if(E(_9b.a)!=E(_9c.a)){return false;}else{_99=_9b.b;_9a=_9c.b;continue;}}}}},_9d=function(_9e,_9f,_9g,_9h,_9i,_9j,_9k,_9l,_9m,_9n,_9o,_9p,_9q,_9r,_9s,_9t,_9u,_9v,_9w,_9x,_9y,_9z,_9A,_9B,_9C,_9D){var _9E=function(_9F){if(_9f!=_9s){return false;}else{if(_9g!=_9t){return false;}else{var _9G=function(_9H){var _9I=function(_9J){if(_9k!=_9x){return false;}else{var _9K=function(_9L){var _9M=function(_9N){var _9O=function(_9P){return (!E(_9o))?(!E(_9B))?(!E(_9p))?(!E(_9C))?true:false:E(_9C):false:(!E(_9B))?false:(!E(_9p))?(!E(_9C))?true:false:E(_9C);};if(!E(_9n)){if(!E(_9A)){return new F(function(){return _9O(_);});}else{return false;}}else{if(!E(_9A)){return false;}else{return new F(function(){return _9O(_);});}}};if(!E(_9m)){if(!E(_9z)){return new F(function(){return _9M(_);});}else{return false;}}else{if(!E(_9z)){return false;}else{return new F(function(){return _9M(_);});}}};if(!E(_9l)){if(!E(_9y)){if(!B(_9K(_))){return false;}else{return new F(function(){return _98(_9q,_9D);});}}else{return false;}}else{if(!E(_9y)){return false;}else{if(!B(_9K(_))){return false;}else{return new F(function(){return _98(_9q,_9D);});}}}}},_9Q=E(_9i);if(!_9Q._){if(!E(_9v)._){if(!B(_7p(_97,_9j,_9w))){return false;}else{return new F(function(){return _9I(_);});}}else{return false;}}else{var _9R=E(_9v);if(!_9R._){return false;}else{if(E(_9Q.a)!=E(_9R.a)){return false;}else{if(!B(_7p(_97,_9j,_9w))){return false;}else{return new F(function(){return _9I(_);});}}}}},_9S=E(_9h);if(!_9S._){if(!E(_9u)._){return new F(function(){return _9G(_);});}else{return false;}}else{var _9T=E(_9u);if(!_9T._){return false;}else{var _9U=E(_9S.a),_9V=E(_9T.a);if(!B(_7F(_9U.a,_9V.a))){return false;}else{if(!B(_7v(_9U.b,_9V.b))){return false;}else{if(_9U.c!=_9V.c){return false;}else{return new F(function(){return _9G(_);});}}}}}}}},_9W=E(_9e);if(!_9W._){if(!E(_9r)._){return new F(function(){return _9E(_);});}else{return false;}}else{var _9X=E(_9r);if(!_9X._){return false;}else{var _9Y=_9X.a,_9Z=E(_9W.a);if(!_9Z._){var _a0=E(_9Y);if(!_a0._){if(E(_9Z.a)!=E(_a0.a)){return false;}else{return new F(function(){return _9E(_);});}}else{return false;}}else{var _a1=E(_9Y);if(!_a1._){return false;}else{if(E(_9Z.a)!=E(_a1.a)){return false;}else{return new F(function(){return _9E(_);});}}}}}},_a2=function(_a3,_a4){while(1){var _a5=E(_a3);if(!_a5._){return E(_a4);}else{var _a6=_a4+1|0;_a3=_a5.b;_a4=_a6;continue;}}},_a7=function(_a8,_a9){while(1){var _aa=E(_a8);if(!_aa._){return E(_a9);}else{_a8=_aa.b;_a9=_aa.a;continue;}}},_ab=function(_ac,_ad,_ae){return new F(function(){return _a7(_ad,_ac);});},_af=function(_ag,_ah){while(1){var _ai=E(_ah);if(!_ai._){return __Z;}else{var _aj=_ai.b,_ak=E(_ag);if(_ak==1){return E(_aj);}else{_ag=_ak-1|0;_ah=_aj;continue;}}}},_al=function(_am,_an,_ao){var _ap=new T2(1,_am,new T(function(){var _aq=_an+1|0;if(_aq>0){return B(_af(_aq,_ao));}else{return E(_ao);}}));if(0>=_an){return E(_ap);}else{var _ar=function(_as,_at){var _au=E(_as);if(!_au._){return E(_ap);}else{var _av=_au.a,_aw=E(_at);return (_aw==1)?new T2(1,_av,_ap):new T2(1,_av,new T(function(){return B(_ar(_au.b,_aw-1|0));}));}};return new F(function(){return _ar(_ao,_an);});}},_ax=__Z,_ay=function(_az,_aA){while(1){var _aB=E(_az);if(!_aB._){return E(_aA);}else{_az=_aB.b;_aA=_aB.a;continue;}}},_aC=function(_aD,_aE){var _aF=E(_aE);return (_aF._==0)?__Z:new T2(1,_aD,new T(function(){return B(_aC(_aF.a,_aF.b));}));},_aG=new T(function(){return B(unCStr(": empty list"));}),_aH=function(_aI){return new F(function(){return err(B(_3(_6Y,new T(function(){return B(_3(_aI,_aG));},1))));});},_aJ=new T(function(){return B(unCStr("init"));}),_aK=new T(function(){return B(_aH(_aJ));}),_aL=new T(function(){return B(unCStr("last"));}),_aM=new T(function(){return B(_aH(_aL));}),_aN=new T(function(){return B(unCStr("base"));}),_aO=new T(function(){return B(unCStr("Control.Exception.Base"));}),_aP=new T(function(){return B(unCStr("PatternMatchFail"));}),_aQ=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_aN,_aO,_aP),_aR=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_aQ,_v,_v),_aS=function(_aT){return E(_aR);},_aU=function(_aV){var _aW=E(_aV);return new F(function(){return _X(B(_V(_aW.a)),_aS,_aW.b);});},_aX=function(_aY){return E(E(_aY).a);},_aZ=function(_b0){return new T2(0,_b1,_b0);},_b2=function(_b3,_b4){return new F(function(){return _3(E(_b3).a,_b4);});},_b5=function(_b6,_b7){return new F(function(){return _28(_b2,_b6,_b7);});},_b8=function(_b9,_ba,_bb){return new F(function(){return _3(E(_ba).a,_bb);});},_bc=new T3(0,_b8,_aX,_b5),_b1=new T(function(){return new T5(0,_aS,_bc,_aZ,_aU,_aX);}),_bd=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_be=function(_bf,_bg){return new F(function(){return die(new T(function(){return B(A2(_5h,_bg,_bf));}));});},_bh=function(_bi,_bj){return new F(function(){return _be(_bi,_bj);});},_bk=function(_bl,_bm){var _bn=E(_bm);if(!_bn._){return new T2(0,_v,_v);}else{var _bo=_bn.a;if(!B(A1(_bl,_bo))){return new T2(0,_v,_bn);}else{var _bp=new T(function(){var _bq=B(_bk(_bl,_bn.b));return new T2(0,_bq.a,_bq.b);});return new T2(0,new T2(1,_bo,new T(function(){return E(E(_bp).a);})),new T(function(){return E(E(_bp).b);}));}}},_br=32,_bs=new T(function(){return B(unCStr("\n"));}),_bt=function(_bu){return (E(_bu)==124)?false:true;},_bv=function(_bw,_bx){var _by=B(_bk(_bt,B(unCStr(_bw)))),_bz=_by.a,_bA=function(_bB,_bC){var _bD=new T(function(){var _bE=new T(function(){return B(_3(_bx,new T(function(){return B(_3(_bC,_bs));},1)));});return B(unAppCStr(": ",_bE));},1);return new F(function(){return _3(_bB,_bD);});},_bF=E(_by.b);if(!_bF._){return new F(function(){return _bA(_bz,_v);});}else{if(E(_bF.a)==124){return new F(function(){return _bA(_bz,new T2(1,_br,_bF.b));});}else{return new F(function(){return _bA(_bz,_v);});}}},_bG=function(_bH){return new F(function(){return _bh(new T1(0,new T(function(){return B(_bv(_bH,_bd));})),_b1);});},_bI=new T(function(){return B(_bG("Events.hs:90:7-27|(hco : tlCos)"));}),_bJ=0,_bK=new T1(1,_bJ),_bL=120,_bM=40,_bN=new T2(1,_bM,_v),_bO=new T(function(){return B(unCStr("\u305b\u3044\u304b\u3044\uff01"));}),_bP=new T2(1,_bO,_v),_bQ=1,_bR=new T1(1,_bQ),_bS=new T1(0,_bQ),_bT=new T(function(){return B(unCStr("\u306f"));}),_bU=new T(function(){return B(unCStr("\u3065"));}),_bV=new T(function(){return B(unCStr("\u308c"));}),_bW=new T2(1,_bV,_v),_bX=new T2(1,_bU,_bW),_bY=new T2(1,_bT,_bX),_bZ=function(_c0,_c1,_c2,_c3,_c4,_c5,_c6,_c7,_c8,_c9,_ca){var _cb=function(_cc){if(_cc!=_c1){var _cd=new T(function(){var _ce=E(_c7);if(!_ce._){return E(_bI);}else{return new T2(0,_ce.a,_ce.b);}}),_cf=new T(function(){var _cg=function(_ch){var _ci=new T(function(){return E(E(_cd).b);}),_cj=new T(function(){var _ck=B(_ay(_ci,_aM));return {_:0,a:_ck.a,b:E(_ck.b),c:E(_ck.c),d:_ck.d,e:_ck.e,f:E(_ck.f),g:E(_ck.g),h:E(_ck.h),i:E(_ck.i),j:E(_bY),k:E(_ck.k),l:E(_ck.l),m:E(_ck.m),n:E(_ck.n),o:E(new T1(1,new T(function(){var _cl=E(_c2);if(!_cl._){return E(_bS);}else{return E(_cl.a);}})))};}),_cm=function(_cn){var _co=E(_cn);return (_co._==0)?E(new T2(1,_cj,_v)):new T2(1,new T(function(){var _cp=E(_co.a);return {_:0,a:_cp.a,b:E(_cp.b),c:E(_cp.c),d:_cp.d,e:_cp.e,f:E(_cp.f),g:E(_cp.g),h:E(_cp.h),i:E(_cp.i),j:E(_cp.j),k:E(_cp.k),l:E(_cp.l),m:E(_cp.m),n:E(_cp.n),o:E(_ax)};}),new T(function(){return B(_cm(_co.b));}));},_cq=new T(function(){var _cr=E(_ci);if(!_cr._){return E(_aK);}else{return B(_aC(_cr.a,_cr.b));}}),_cs=new T(function(){return B(_al(new T(function(){var _ct=B(_79(_cq,_c1));return {_:0,a:_ct.a,b:E(_ct.b),c:E(_ct.c),d:3,e:_ct.e,f:E(_ct.f),g:E(_ct.g),h:E(_ct.h),i:E(_ct.i),j:E(_ct.j),k:E(_ct.k),l:E(_ct.l),m:E(_ct.m),n:E(_ct.n),o:E(_ct.o)};}),_c1,_cq));});return new F(function(){return _cm(B(_al(new T(function(){var _cu=B(_79(_cq,_ch));return {_:0,a:_cu.a,b:E(_cu.b),c:E(_cu.c),d:4,e:_cu.e,f:E(_cu.f),g:E(_cu.g),h:E(_cu.h),i:E(_cu.i),j:E(_cu.j),k:E(_cu.k),l:E(_cu.l),m:E(_cu.m),n:E(_cu.n),o:E(_cu.o)};}),_ch,_cs)));});},_cv=E(_c5);if(!_cv._){return B(_cg(0));}else{return B(_cg(E(_cv.a).c));}});return {_:0,a:_c2,b:new T2(0,_c3+1|0,_c4),c:_c5,d:_bR,e:new T2(1,new T(function(){return E(E(_cd).a);}),_cf),f:_c8,g:_c9,h:_ca};}else{var _cw=E(_c0),_cx=_cw.a,_cy=_cw.b,_cz=E(_c7);if(!_cz._){var _cA=E(_aK);}else{var _cB=_cz.a,_cC=_cz.b,_cD=new T(function(){var _cE=B(_ab(_cB,_cC,_aM)),_cF=new T(function(){return E(_cx)/3;}),_cG=new T(function(){return E(_cy)/6;}),_cH=new T(function(){var _cI=E(_c2);if(!_cI._){return E(_bS);}else{var _cJ=E(_cI.a);if(!_cJ._){return new T1(0,new T(function(){return E(_cJ.a)+1|0;}));}else{return new T1(1,new T(function(){return E(_cJ.a)+1|0;}));}}});return {_:0,a:_cE.a,b:E(new T4(0,_cF,_cG,new T(function(){var _cK=E(_cF);return E(_cx)-(_cK+_cK);}),new T(function(){var _cL=E(_cG);return E(_cy)-(_cL+_cL);}))),c:E(_cE.c),d:_cE.d,e:_cE.e,f:E(new T2(1,new T2(0,new T(function(){return E(_cx)/2-E(_cF)-20;}),_bL),_v)),g:E(_cE.g),h:E(_bN),i:E(_cE.i),j:E(_bP),k:E(_cE.k),l:E(_cE.l),m:E(_cE.m),n:E(_cE.n),o:E(new T1(1,_cH))};}),_cM=function(_cN){var _cO=E(_cN);return (_cO._==0)?E(new T2(1,_cD,_v)):new T2(1,new T(function(){var _cP=E(_cO.a);return {_:0,a:_cP.a,b:E(_cP.b),c:E(_cP.c),d:_cP.d,e:_cP.e,f:E(_cP.f),g:E(_cP.g),h:E(_cP.h),i:E(_cP.i),j:E(_cP.j),k:E(_cP.k),l:E(_cP.l),m:E(_cP.m),n:E(_cP.n),o:E(_ax)};}),new T(function(){return B(_cM(_cO.b));}));},_cA=B(_cM(B(_aC(_cB,_cC))));}return {_:0,a:_c2,b:new T2(0,_c3,_c4),c:_c5,d:_bK,e:_cA,f:_c8,g:_c9,h:_ca};}},_cQ=E(_c5);if(!_cQ._){return new F(function(){return _cb(0);});}else{return new F(function(){return _cb(E(_cQ.a).c);});}},_cR=new T2(1,_6e,_v),_cS=new T2(1,_6e,_cR),_cT=new T2(1,_6e,_cS),_cU=5,_cV=new T2(1,_cU,_v),_cW=new T2(1,_cU,_cV),_cX=new T2(1,_cU,_cW),_cY=50,_cZ=new T2(1,_cY,_v),_d0=new T2(1,_cY,_cZ),_d1=new T2(1,_cY,_d0),_d2=new T(function(){return B(unCStr("\u3075"));}),_d3=new T2(1,_d2,_v),_d4=new T(function(){return B(unCStr("\u305f"));}),_d5=new T2(1,_d4,_d3),_d6=new T(function(){return B(unCStr("\u3053"));}),_d7=new T2(1,_d6,_d5),_d8=50,_d9=function(_da,_db,_dc,_dd){var _de=new T(function(){return E(_da)/8*3-20;}),_df=new T(function(){return E(_da)/8;});return {_:0,a:_dc,b:E(new T4(0,_df,new T(function(){var _dg=E(_db);return _dg-_dg/6;}),new T(function(){var _dh=E(_df);return E(_da)-(_dh+_dh);}),new T(function(){return E(_db)/8;}))),c:E(_62),d:1,e:6,f:E(new T2(1,new T2(0,new T(function(){return E(_de)-50;}),_d8),new T2(1,new T2(0,_de,_d8),new T2(1,new T2(0,new T(function(){return E(_de)+50;}),_d8),_v)))),g:E(_v),h:E(_d1),i:E(_cX),j:E(_d7),k:E(_cT),l:E(_v),m:E(_v),n:E(_2q),o:E(new T1(3,_dd))};},_di=function(_dj){var _dk=E(_dj);return {_:0,a:_dk.a,b:E(_dk.b),c:E(_dk.c),d:0,e:7,f:E(_dk.f),g:E(_dk.g),h:E(_dk.h),i:E(_dk.i),j:E(_dk.j),k:E(_dk.k),l:E(_dk.l),m:E(_dk.m),n:E(_dk.n),o:E(_dk.o)};},_dl=new T(function(){return B(_bG("Events.hs:37:7-27|(hco : chCos)"));}),_dm=function(_dn,_do){var _dp=E(_do);return (_dp._==0)?__Z:new T2(1,new T(function(){return B(A1(_dn,_dp.a));}),new T(function(){return B(_dm(_dn,_dp.b));}));},_dq=function(_dr,_ds,_dt,_du,_dv,_dw,_dx,_dy,_dz,_dA,_dB){var _dC=new T(function(){var _dD=E(_dy);if(!_dD._){return E(_dl);}else{return new T2(0,_dD.a,_dD.b);}}),_dE=new T(function(){var _dF=function(_dG){var _dH=E(_dt),_dI=new T(function(){return E(E(_dC).b);}),_dJ=B(_al(new T(function(){var _dK=B(_79(_dI,_dH));return {_:0,a:_dK.a,b:E(_dK.b),c:E(_dK.c),d:4,e:8,f:E(_dK.f),g:E(_dK.g),h:E(_dK.h),i:E(_dK.i),j:E(_dK.j),k:E(_dK.k),l:E(_dK.l),m:E(_dK.m),n:E(_dK.n),o:E(_dK.o)};}),_dH,new T(function(){return B(_dm(_di,_dI));})));if((_dG+1|0)!=E(_ds)){var _dL=E(_dJ);if(!_dL._){return E(_aK);}else{return new F(function(){return _3(B(_aC(_dL.a,_dL.b)),new T2(1,new T(function(){var _dM=E(_dr);return B(_d9(_dM.a,_dM.b,_dG+1|0,_dH));}),_v));});}}else{return new F(function(){return _3(_dJ,new T2(1,new T(function(){var _dN=E(_dr);return B(_d9(_dN.a,_dN.b,_dG+1|0,_dH));}),_v));});}},_dO=E(_dw);if(!_dO._){return B(_dF(0));}else{return B(_dF(B(_a2(E(_dO.a).a,0))));}});return {_:0,a:_du,b:_dv,c:_dw,d:_dx,e:new T2(1,new T(function(){return E(E(_dC).a);}),_dE),f:_dz,g:_dA,h:_dB};},_dP=function(_){return _5L;},_dQ=function(_dR){return E(E(_dR).a);},_dS=function(_dT){return E(E(_dT).a);},_dU=new T1(1,_5N),_dV="false",_dW=new T1(1,_5Q),_dX="true",_dY=function(_dZ){var _e0=strEq(_dZ,E(_dX));if(!E(_e0)){var _e1=strEq(_dZ,E(_dV));return (E(_e1)==0)?__Z:E(_dU);}else{return E(_dW);}},_e2=2,_e3=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_e4="paused",_e5="ended",_e6=function(_e7,_e8){var _e9=function(_){var _ea=E(_e8),_eb=E(_e3),_ec=__app2(_eb,_ea,E(_e5)),_ed=String(_ec),_ee=function(_ef){var _eg=__app2(_eb,_ea,E(_e4));return new T(function(){var _eh=String(_eg),_ei=B(_dY(_eh));if(!_ei._){return 0;}else{if(!E(_ei.a)){return 0;}else{return 1;}}});},_ej=B(_dY(_ed));if(!_ej._){return new F(function(){return _ee(_);});}else{if(!E(_ej.a)){return new F(function(){return _ee(_);});}else{return _e2;}}};return new F(function(){return A2(_5U,_e7,_e9);});},_ek="duration",_el=new T(function(){return eval("(function(e,t) {e.currentTime = t;})");}),_em=function(_en,_eo,_ep){var _eq=new T(function(){var _er=E(_ep);switch(_er._){case 0:return function(_){var _es=__app2(E(_el),E(_eo),0);return new F(function(){return _dP(_);});};break;case 1:return function(_){var _et=E(_eo),_eu=__app2(E(_e3),_et,E(_ek)),_ev=String(_eu),_ew=Number(_ev),_ex=isDoubleNaN(_ew);if(!E(_ex)){var _ey=__app2(E(_el),_et,_ew);return new F(function(){return _dP(_);});}else{var _ez=__app2(E(_el),_et,0);return new F(function(){return _dP(_);});}};break;default:return function(_){var _eA=__app2(E(_el),E(_eo),E(_er.a));return new F(function(){return _dP(_);});};}});return new F(function(){return A2(_5U,_en,_eq);});},_eB=function(_eC){return E(E(_eC).c);},_eD=function(_eE){return E(E(_eE).b);},_eF=__Z,_eG=new T(function(){return eval("(function(x){x.play();})");}),_eH=function(_eI){return E(E(_eI).b);},_eJ=function(_eK,_eL){var _eM=new T(function(){return B(_em(_eK,_eL,_eF));}),_eN=B(_dS(_eK)),_eO=new T(function(){return B(A2(_eH,B(_dQ(_eN)),_5L));}),_eP=new T(function(){var _eQ=function(_){var _eR=__app1(E(_eG),E(_eL));return new F(function(){return _dP(_);});};return B(A2(_5U,_eK,_eQ));}),_eS=function(_eT){return new F(function(){return A3(_eB,_eN,new T(function(){if(E(_eT)==2){return E(_eM);}else{return E(_eO);}}),_eP);});};return new F(function(){return A3(_eD,_eN,new T(function(){return B(_e6(_eK,_eL));}),_eS);});},_eU=new T(function(){return eval("(function(e){e.width = e.width;})");}),_eV=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_eW=function(_eX,_eY,_eZ){var _f0=new T(function(){return toJSStr(E(_eZ));});return function(_f1,_){var _f2=__app4(E(_eV),E(_f1),E(_f0),E(_eX),E(_eY));return new F(function(){return _dP(_);});};},_f3=0,_f4=new T(function(){return B(_eW(_f3,_f3,_v));}),_f5=function(_f6,_f7){return E(_f6)!=E(_f7);},_f8=function(_f9,_fa){return E(_f9)==E(_fa);},_fb=new T2(0,_f8,_f5),_fc=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_fd=new T(function(){return eval("(function(ctx){ctx.save();})");}),_fe=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_ff=function(_fg,_fh,_fi,_){var _fj=__app1(E(_fd),_fi),_fk=__app2(E(_fe),_fi,E(_fg)),_fl=B(A2(_fh,_fi,_)),_fm=__app1(E(_fc),_fi);return new F(function(){return _dP(_);});},_fn=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_fo=function(_fp,_fq,_fr,_fs,_){var _ft=__app1(E(_fd),_fs),_fu=__app3(E(_fn),_fs,E(_fp),E(_fq)),_fv=B(A2(_fr,_fs,_)),_fw=__app1(E(_fc),_fs);return new F(function(){return _dP(_);});},_fx=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_fy=function(_fz,_fA,_fB,_fC,_){var _fD=__app1(E(_fd),_fC),_fE=__app3(E(_fx),_fC,E(_fz),E(_fA)),_fF=B(A2(_fB,_fC,_)),_fG=__app1(E(_fc),_fC);return new F(function(){return _dP(_);});},_fH=new T(function(){return eval("(function(ctx,i,x,y){ctx.drawImage(i,x,y);})");}),_fI=function(_fJ,_fK,_fL,_fM,_){var _fN=__app4(E(_fH),_fM,_fJ,_fK,_fL);return new F(function(){return _dP(_);});},_fO=function(_fP,_fQ,_fR){var _fS=E(_fR);return (_fS._==0)?0:(!B(A3(_4b,_fP,_fQ,_fS.a)))?1+B(_fO(_fP,_fQ,_fS.b))|0:0;},_fT=",",_fU="rgba(",_fV=new T(function(){return toJSStr(_v);}),_fW="rgb(",_fX=")",_fY=new T2(1,_fX,_v),_fZ=function(_g0){var _g1=E(_g0);if(!_g1._){var _g2=jsCat(new T2(1,_fW,new T2(1,new T(function(){return String(_g1.a);}),new T2(1,_fT,new T2(1,new T(function(){return String(_g1.b);}),new T2(1,_fT,new T2(1,new T(function(){return String(_g1.c);}),_fY)))))),E(_fV));return E(_g2);}else{var _g3=jsCat(new T2(1,_fU,new T2(1,new T(function(){return String(_g1.a);}),new T2(1,_fT,new T2(1,new T(function(){return String(_g1.b);}),new T2(1,_fT,new T2(1,new T(function(){return String(_g1.c);}),new T2(1,_fT,new T2(1,new T(function(){return String(_g1.d);}),_fY)))))))),E(_fV));return E(_g3);}},_g4="strokeStyle",_g5="fillStyle",_g6=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_g7=function(_g8,_g9){var _ga=new T(function(){return B(_fZ(_g8));});return function(_gb,_){var _gc=E(_gb),_gd=E(_g5),_ge=E(_e3),_gf=__app2(_ge,_gc,_gd),_gg=E(_g4),_gh=__app2(_ge,_gc,_gg),_gi=E(_ga),_gj=E(_g6),_gk=__app3(_gj,_gc,_gd,_gi),_gl=__app3(_gj,_gc,_gg,_gi),_gm=B(A2(_g9,_gc,_)),_gn=String(_gf),_go=__app3(_gj,_gc,_gd,_gn),_gp=String(_gh),_gq=__app3(_gj,_gc,_gg,_gp);return new F(function(){return _dP(_);});};},_gr="font",_gs=function(_gt,_gu){var _gv=new T(function(){return toJSStr(E(_gt));});return function(_gw,_){var _gx=E(_gw),_gy=E(_gr),_gz=__app2(E(_e3),_gx,_gy),_gA=E(_g6),_gB=__app3(_gA,_gx,_gy,E(_gv)),_gC=B(A2(_gu,_gx,_)),_gD=String(_gz),_gE=__app3(_gA,_gx,_gy,_gD);return new F(function(){return _dP(_);});};},_gF=0,_gG=new T(function(){return B(unCStr("px IPAGothic"));}),_gH=new T(function(){return B(unCStr("\u3042\u3044\u3046\u3048\u304axkhnmtrsy \u304b\u306f\u306a\u307e\u304d\u3072\u306b\u307f\u304f\u3075\u306c\u3080\u3051\u3078\u306d\u3081\u3053\u307b\u306e\u3082\u3068\u308d\u305d\u3088\u3092\u3066\u308c\u305b\u3091\u3064\u308b\u3059\u3086\u3093\u3061\u308a\u3057\u3090\u305f\u3089\u3055\u3084\u308f\u309b\u963f\u548c\u5b87\u543e\u4ed8\u9808\u88ab\u610f\u767e\u96c4\u9593\u6ce2\u304c9\u7a42\u305e\u8a71\u8449\u3056\u3050\u3073\u7dd2\u30693\u305a\u3070\u3076\u304e\u3079\u88dc\u82bd1\u5e9c\u5834\u3058\u500b\u6211\u3054\u56f3\u6642\u66fe\u706b\u65e5\u3060\u5ea7\u7fbd4\u99ac\u90e8\u7956\u7089\u5177\u8a9e\u3065\u5f8c\u5b50\u7537\u3067\u305c\u51fa\u88f3\u7f8e"));}),_gI=function(_gJ,_gK,_gL,_gM,_gN,_gO,_gP,_gQ,_gR,_gS,_){var _gT=E(_gS);if(!_gT._){return _5L;}else{var _gU=_gT.b,_gV=E(_gO),_gW=_gV.b,_gX=E(_gR),_gY=_gX.a,_gZ=_gX.b,_h0=E(_gT.a),_h1=new T(function(){return E(_gN);});if(E(_h0)==13){return new F(function(){return _h2(_gJ,_gK,_gL,_gM,_gN,_gV.a,_gW,_gP,0,new T(function(){return E(_gY)-E(_h1)*1.2;}),_gP,_gU,_);});}else{var _h3=function(_){var _h4=new T(function(){return E(_h1)*1.1;}),_h5=new T(function(){var _h6=E(_gQ),_h7=E(_gW)/E(_h4),_h8=_h7&4294967295;if(_h7>=_h8){return (_h6+1|0)>(_h8-2|0);}else{return (_h6+1|0)>((_h8-1|0)-2|0);}});return new F(function(){return _gI(_gJ,_gK,_gL,_gM,_gN,_gV,_gP,new T(function(){if(!E(_h5)){return E(_gQ)+1|0;}else{return E(_gF);}}),new T2(0,new T(function(){if(!E(_h5)){return E(_gY);}else{return E(_gY)-E(_h1)*1.2;}}),new T(function(){if(!E(_h5)){return E(_gZ)+E(_h4);}else{return E(_gP);}})),_gU,_);});};if(!E(_gM)){var _h9=new T(function(){var _ha=new T(function(){return B(_eW(_f3,_f3,new T2(1,_h0,_v)));}),_hb=function(_hc,_){return new F(function(){return _ff(_f3,_ha,E(_hc),_);});};return B(_gs(new T(function(){return B(_3(B(_d(0,E(_gN),_v)),_gG));},1),function(_hd,_){return new F(function(){return _fy(_gY,_gZ,_hb,E(_hd),_);});}));}),_he=B(A(_g7,[_gL,_h9,E(_gJ).a,_]));return new F(function(){return _h3(_);});}else{var _hf=new T(function(){return E(_gN)/20;}),_hg=function(_hh,_){return new F(function(){return _fo(_hf,_hf,function(_hi,_){if(!B(_4d(_fb,_h0,_gH))){return new F(function(){return _fI(B(_79(_gK,14)),0,0,E(_hi),_);});}else{return new F(function(){return _fI(B(_79(_gK,B(_fO(_fb,_h0,_gH)))),0,0,E(_hi),_);});}},E(_hh),_);});},_hj=B(_fy(new T(function(){return E(_gY)-E(_h1)/6;},1),new T(function(){return E(_gZ)-E(_h1)*3/4;},1),_hg,E(_gJ).a,_));return new F(function(){return _h3(_);});}}}},_h2=function(_hk,_hl,_hm,_hn,_ho,_hp,_hq,_hr,_hs,_ht,_hu,_hv,_){while(1){var _hw=B((function(_hx,_hy,_hz,_hA,_hB,_hC,_hD,_hE,_hF,_hG,_hH,_hI,_){var _hJ=E(_hI);if(!_hJ._){return _5L;}else{var _hK=_hJ.b,_hL=E(_hJ.a),_hM=new T(function(){return E(_hB);});if(E(_hL)==13){var _hN=_hx,_hO=_hy,_hP=_hz,_hQ=_hA,_hR=_hB,_hS=_hC,_hT=_hD,_hU=_hE,_hV=_hE;_hk=_hN;_hl=_hO;_hm=_hP;_hn=_hQ;_ho=_hR;_hp=_hS;_hq=_hT;_hr=_hU;_hs=0;_ht=new T(function(){return E(_hG)-E(_hM)*1.2;});_hu=_hV;_hv=_hK;return __continue;}else{var _hW=function(_){var _hX=new T(function(){return E(_hM)*1.1;}),_hY=new T(function(){var _hZ=E(_hD)/E(_hX),_i0=_hZ&4294967295;if(_hZ>=_i0){return (_hF+1|0)>(_i0-2|0);}else{return (_hF+1|0)>((_i0-1|0)-2|0);}});return new F(function(){return _gI(_hx,_hy,_hz,_hA,_hB,new T2(0,_hC,_hD),_hE,new T(function(){if(!E(_hY)){return _hF+1|0;}else{return E(_gF);}}),new T2(0,new T(function(){if(!E(_hY)){return E(_hG);}else{return E(_hG)-E(_hM)*1.2;}}),new T(function(){if(!E(_hY)){return E(_hH)+E(_hX);}else{return E(_hE);}})),_hK,_);});};if(!E(_hA)){var _i1=new T(function(){var _i2=new T(function(){return B(_eW(_f3,_f3,new T2(1,_hL,_v)));}),_i3=function(_i4,_){return new F(function(){return _ff(_f3,_i2,E(_i4),_);});};return B(_gs(new T(function(){return B(_3(B(_d(0,E(_hB),_v)),_gG));},1),function(_i5,_){return new F(function(){return _fy(_hG,_hH,_i3,E(_i5),_);});}));}),_i6=B(A(_g7,[_hz,_i1,E(_hx).a,_]));return new F(function(){return _hW(_);});}else{var _i7=new T(function(){return E(_hB)/20;}),_i8=function(_i9,_){return new F(function(){return _fo(_i7,_i7,function(_ia,_){if(!B(_4d(_fb,_hL,_gH))){return new F(function(){return _fI(B(_79(_hy,14)),0,0,E(_ia),_);});}else{return new F(function(){return _fI(B(_79(_hy,B(_fO(_fb,_hL,_gH)))),0,0,E(_ia),_);});}},E(_i9),_);});},_ib=B(_fy(new T(function(){return E(_hG)-E(_hM)/6;},1),new T(function(){return E(_hH)-E(_hM)*3/4;},1),_i8,E(_hx).a,_));return new F(function(){return _hW(_);});}}}})(_hk,_hl,_hm,_hn,_ho,_hp,_hq,_hr,_hs,_ht,_hu,_hv,_));if(_hw!=__continue){return _hw;}}},_ic=function(_id,_ie,_if,_ig,_ih,_ii,_ij,_ik,_il,_im,_in,_io,_ip,_){while(1){var _iq=B((function(_ir,_is,_it,_iu,_iv,_iw,_ix,_iy,_iz,_iA,_iB,_iC,_iD,_){var _iE=E(_iD);if(!_iE._){return _5L;}else{var _iF=_iE.b,_iG=E(_iE.a),_iH=new T(function(){return E(_iw);});if(E(_iG)==13){var _iI=_ir,_iJ=_is,_iK=_it,_iL=_iu,_iM=_iv,_iN=_iw,_iO=_ix,_iP=_iy,_iQ=_iz,_iR=_iz;_id=_iI;_ie=_iJ;_if=_iK;_ig=_iL;_ih=_iM;_ii=_iN;_ij=_iO;_ik=_iP;_il=_iQ;_im=0;_in=new T(function(){return E(_iB)-E(_iH)*1.2;});_io=_iR;_ip=_iF;return __continue;}else{var _iS=function(_){var _iT=new T(function(){return E(_iH)*1.1;}),_iU=new T(function(){var _iV=E(_iy)/E(_iT),_iW=_iV&4294967295;if(_iV>=_iW){return (_iA+1|0)>(_iW-2|0);}else{return (_iA+1|0)>((_iW-1|0)-2|0);}});return new F(function(){return _gI(new T2(0,_ir,_is),_it,_iu,_iv,_iw,new T2(0,_ix,_iy),_iz,new T(function(){if(!E(_iU)){return _iA+1|0;}else{return E(_gF);}}),new T2(0,new T(function(){if(!E(_iU)){return E(_iB);}else{return E(_iB)-E(_iH)*1.2;}}),new T(function(){if(!E(_iU)){return E(_iC)+E(_iT);}else{return E(_iz);}})),_iF,_);});};if(!E(_iv)){var _iX=new T(function(){var _iY=new T(function(){return B(_eW(_f3,_f3,new T2(1,_iG,_v)));}),_iZ=function(_j0,_){return new F(function(){return _ff(_f3,_iY,E(_j0),_);});};return B(_gs(new T(function(){return B(_3(B(_d(0,E(_iw),_v)),_gG));},1),function(_j1,_){return new F(function(){return _fy(_iB,_iC,_iZ,E(_j1),_);});}));}),_j2=B(A(_g7,[_iu,_iX,_ir,_]));return new F(function(){return _iS(_);});}else{var _j3=new T(function(){return E(_iw)/20;}),_j4=function(_j5,_){return new F(function(){return _fo(_j3,_j3,function(_j6,_){if(!B(_4d(_fb,_iG,_gH))){return new F(function(){return _fI(B(_79(_it,14)),0,0,E(_j6),_);});}else{return new F(function(){return _fI(B(_79(_it,B(_fO(_fb,_iG,_gH)))),0,0,E(_j6),_);});}},E(_j5),_);});},_j7=B(_fy(new T(function(){return E(_iB)-E(_iH)/6;},1),new T(function(){return E(_iC)-E(_iH)*3/4;},1),_j4,_ir,_));return new F(function(){return _iS(_);});}}}})(_id,_ie,_if,_ig,_ih,_ii,_ij,_ik,_il,_im,_in,_io,_ip,_));if(_iq!=__continue){return _iq;}}},_j8=new T(function(){return eval("(function(ctx, x, y, radius, fromAngle, toAngle){ctx.arc(x, y, radius, fromAngle, toAngle);})");}),_j9=function(_ja,_jb,_jc,_jd,_je,_jf,_){var _jg=__apply(E(_j8),new T2(1,_je,new T2(1,_jd,new T2(1,_jc,new T2(1,_jb,new T2(1,_ja,new T2(1,_jf,_v)))))));return new F(function(){return _dP(_);});},_jh=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_ji=new T(function(){return eval("(function(ctx,x,y){ctx.lineTo(x,y);})");}),_jj=function(_jk,_jl,_){var _jm=E(_jk);if(!_jm._){return _5L;}else{var _jn=E(_jm.a),_jo=E(_jl),_jp=__app3(E(_jh),_jo,E(_jn.a),E(_jn.b)),_jq=E(_jm.b);if(!_jq._){return _5L;}else{var _jr=E(_jq.a),_js=E(_ji),_jt=__app3(_js,_jo,E(_jr.a),E(_jr.b)),_ju=function(_jv,_){while(1){var _jw=E(_jv);if(!_jw._){return _5L;}else{var _jx=E(_jw.a),_jy=__app3(_js,_jo,E(_jx.a),E(_jx.b));_jv=_jw.b;continue;}}};return new F(function(){return _ju(_jq.b,_);});}}},_jz=function(_jA,_jB,_jC,_jD,_jE,_){var _jF=B(_j9(_jA+_jC-10,_jB+_jD-10,10,0,1.5707963267948966,_jE,_)),_jG=B(_j9(_jA+10,_jB+_jD-10,10,1.5707963267948966,3.141592653589793,_jE,_)),_jH=B(_j9(_jA+10,_jB+10,10,3.141592653589793,4.71238898038469,_jE,_)),_jI=B(_j9(_jA+_jC-10,_jB+10,10,4.71238898038469,6.283185307179586,_jE,_));return new F(function(){return _jj(new T2(1,new T2(0,_jA+_jC,_jB+_jD-10),new T2(1,new T2(0,_jA+_jC,_jB+10),_v)),_jE,_);});},_jJ=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_jK=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_jL=function(_jM,_jN,_){var _jO=__app1(E(_jJ),_jN),_jP=B(A2(_jM,_jN,_)),_jQ=__app1(E(_jK),_jN);return new F(function(){return _dP(_);});},_jR=function(_jS,_jT,_jU,_jV,_jW,_){return new F(function(){return _jj(new T2(1,new T2(0,_jS,_jT),new T2(1,new T2(0,_jU,_jT),new T2(1,new T2(0,_jU,_jV),new T2(1,new T2(0,_jS,_jV),new T2(1,new T2(0,_jS,_jT),_v))))),_jW,_);});},_jX=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_jY=function(_jZ,_k0,_){var _k1=__app1(E(_jJ),_k0),_k2=B(A2(_jZ,_k0,_)),_k3=__app1(E(_jX),_k0);return new F(function(){return _dP(_);});},_k4=new T3(0,200,255,200),_k5=new T3(0,255,204,153),_k6=new T3(0,255,153,204),_k7=new T3(0,153,255,255),_k8=new T3(0,0,128,128),_k9=new T3(0,255,255,100),_ka=new T3(0,0,0,0),_kb=new T3(0,100,100,100),_kc=new T2(1,_kb,_v),_kd=new T2(1,_ka,_kc),_ke=new T2(1,_k9,_kd),_kf=new T2(1,_k8,_ke),_kg=new T2(1,_k7,_kf),_kh=new T2(1,_k6,_kg),_ki=new T2(1,_k5,_kh),_kj=new T2(1,_k4,_ki),_kk=new T3(0,200,200,180),_kl=new T2(1,_kk,_kj),_km="lineWidth",_kn=function(_ko,_kp){var _kq=new T(function(){return String(E(_ko));});return function(_kr,_){var _ks=E(_kr),_kt=E(_km),_ku=__app2(E(_e3),_ks,_kt),_kv=E(_g6),_kw=__app3(_kv,_ks,_kt,E(_kq)),_kx=B(A2(_kp,_ks,_)),_ky=String(_ku),_kz=__app3(_kv,_ks,_kt,_ky);return new F(function(){return _dP(_);});};},_kA=3,_kB=function(_kC,_kD){var _kE=E(_kC);if(!_kE._){return __Z;}else{var _kF=E(_kD);return (_kF._==0)?__Z:new T2(1,new T2(0,_kE.a,_kF.a),new T(function(){return B(_kB(_kE.b,_kF.b));}));}},_kG=function(_kH,_kI,_kJ,_kK,_){var _kL=E(_kK);if(!_kL._){return _5L;}else{var _kM=E(E(_kI).a),_kN=new T(function(){return E(E(_kJ).b);}),_kO=function(_kP,_){while(1){var _kQ=B((function(_kR,_){var _kS=E(_kR);if(!_kS._){return _5L;}else{var _kT=_kS.b,_kU=E(_kS.a),_kV=_kU.d,_kW=E(_kU.b),_kX=_kW.a,_kY=_kW.b,_kZ=_kW.c,_l0=_kW.d,_l1=function(_){var _l2=function(_l3,_l4,_l5,_){while(1){var _l6=B((function(_l7,_l8,_l9,_){var _la=E(_l7);if(!_la._){return _5L;}else{var _lb=E(_l8);if(!_lb._){return _5L;}else{var _lc=E(_l9);if(!_lc._){return _5L;}else{var _ld=E(_lc.a),_le=E(_ld.a),_lf=E(_ld.b),_lg=new T(function(){return E(_le.b)+E(_kY);}),_lh=B(_h2(_kH,_kN,new T(function(){return B(_79(_kl,E(_lf.b)));}),_lb.a,_lf.a,_kZ,_l0,_lg,0,new T(function(){return E(_le.a)+E(_kX);}),_lg,_la.a,_));_l3=_la.b;_l4=_lb.b;_l5=_lc.b;return __continue;}}}})(_l3,_l4,_l5,_));if(_l6!=__continue){return _l6;}}},_li=new T(function(){return B(_kB(_kU.f,new T(function(){return B(_kB(_kU.h,_kU.i));},1)));},1);return new F(function(){return _l2(_kU.j,_kU.k,_li,_);});};switch(E(_kU.c)){case 0:var _lj=B(_l1(_));_kP=_kT;return __continue;case 1:var _lk=E(_kH),_ll=_lk.a,_lm=new T(function(){return E(_kX)+E(_kZ);}),_ln=new T(function(){return E(_kY)+E(_l0);}),_lo=function(_lp,_){return new F(function(){return _jR(_kX,_kY,_lm,_ln,_lp,_);});},_lq=B(A(_g7,[new T(function(){return B(_79(_kl,_kV));},1),function(_lr,_){return new F(function(){return _jY(_lo,E(_lr),_);});},_ll,_])),_ls=B(_l1(_)),_lt=function(_lu,_){while(1){var _lv=B((function(_lw,_){var _lx=E(_lw);if(!_lx._){return _5L;}else{var _ly=_lx.b,_lz=E(_lx.a),_lA=_lz.d,_lB=E(_lz.b),_lC=_lB.a,_lD=_lB.b,_lE=_lB.c,_lF=_lB.d,_lG=function(_){var _lH=function(_lI,_lJ,_lK,_){while(1){var _lL=B((function(_lM,_lN,_lO,_){var _lP=E(_lM);if(!_lP._){return _5L;}else{var _lQ=E(_lN);if(!_lQ._){return _5L;}else{var _lR=E(_lO);if(!_lR._){return _5L;}else{var _lS=E(_lR.a),_lT=E(_lS.a),_lU=E(_lS.b),_lV=new T(function(){return E(_lT.b)+E(_lD);}),_lW=B(_ic(_ll,_lk.b,_kN,new T(function(){return B(_79(_kl,E(_lU.b)));}),_lQ.a,_lU.a,_lE,_lF,_lV,0,new T(function(){return E(_lT.a)+E(_lC);}),_lV,_lP.a,_));_lI=_lP.b;_lJ=_lQ.b;_lK=_lR.b;return __continue;}}}})(_lI,_lJ,_lK,_));if(_lL!=__continue){return _lL;}}},_lX=new T(function(){return B(_kB(_lz.f,new T(function(){return B(_kB(_lz.h,_lz.i));},1)));},1);return new F(function(){return _lH(_lz.j,_lz.k,_lX,_);});};switch(E(_lz.c)){case 0:var _lY=B(_lG(_));_lu=_ly;return __continue;case 1:var _lZ=new T(function(){return E(_lC)+E(_lE);}),_m0=new T(function(){return E(_lD)+E(_lF);}),_m1=function(_m2,_){return new F(function(){return _jR(_lC,_lD,_lZ,_m0,_m2,_);});},_m3=B(A(_g7,[new T(function(){return B(_79(_kl,_lA));},1),function(_m4,_){return new F(function(){return _jY(_m1,E(_m4),_);});},_ll,_])),_m5=B(_lG(_));_lu=_ly;return __continue;default:var _m6=function(_m7,_){return new F(function(){return _jz(E(_lC),E(_lD),E(_lE),E(_lF),E(_m7),_);});},_m8=B(A(_g7,[new T(function(){return B(_79(_kl,_lz.e));},1),function(_m9,_){return new F(function(){return _jL(_m6,E(_m9),_);});},_ll,_])),_ma=new T(function(){var _mb=function(_mc,_){return new F(function(){return _jz(E(_lC),E(_lD),E(_lE),E(_lF),E(_mc),_);});};return B(_kn(_kA,function(_md,_){return new F(function(){return _jY(_mb,E(_md),_);});}));}),_me=B(A(_g7,[new T(function(){return B(_79(_kl,_lA));},1),_ma,_ll,_])),_mf=B(_lG(_));_lu=_ly;return __continue;}}})(_lu,_));if(_lv!=__continue){return _lv;}}};return new F(function(){return _lt(_kT,_);});break;default:var _mg=E(_kH),_mh=_mg.a,_mi=function(_mj,_){return new F(function(){return _jz(E(_kX),E(_kY),E(_kZ),E(_l0),E(_mj),_);});},_mk=B(A(_g7,[new T(function(){return B(_79(_kl,_kU.e));},1),function(_ml,_){return new F(function(){return _jL(_mi,E(_ml),_);});},_mh,_])),_mm=new T(function(){var _mn=function(_mo,_){return new F(function(){return _jz(E(_kX),E(_kY),E(_kZ),E(_l0),E(_mo),_);});};return B(_kn(_kA,function(_mp,_){return new F(function(){return _jY(_mn,E(_mp),_);});}));}),_mq=B(A(_g7,[new T(function(){return B(_79(_kl,_kV));},1),_mm,_mh,_])),_mr=B(_l1(_)),_ms=function(_mt,_){while(1){var _mu=B((function(_mv,_){var _mw=E(_mv);if(!_mw._){return _5L;}else{var _mx=_mw.b,_my=E(_mw.a),_mz=_my.d,_mA=E(_my.b),_mB=_mA.a,_mC=_mA.b,_mD=_mA.c,_mE=_mA.d,_mF=function(_){var _mG=function(_mH,_mI,_mJ,_){while(1){var _mK=B((function(_mL,_mM,_mN,_){var _mO=E(_mL);if(!_mO._){return _5L;}else{var _mP=E(_mM);if(!_mP._){return _5L;}else{var _mQ=E(_mN);if(!_mQ._){return _5L;}else{var _mR=E(_mQ.a),_mS=E(_mR.a),_mT=E(_mR.b),_mU=new T(function(){return E(_mS.b)+E(_mC);}),_mV=B(_ic(_mh,_mg.b,_kN,new T(function(){return B(_79(_kl,E(_mT.b)));}),_mP.a,_mT.a,_mD,_mE,_mU,0,new T(function(){return E(_mS.a)+E(_mB);}),_mU,_mO.a,_));_mH=_mO.b;_mI=_mP.b;_mJ=_mQ.b;return __continue;}}}})(_mH,_mI,_mJ,_));if(_mK!=__continue){return _mK;}}},_mW=new T(function(){return B(_kB(_my.f,new T(function(){return B(_kB(_my.h,_my.i));},1)));},1);return new F(function(){return _mG(_my.j,_my.k,_mW,_);});};switch(E(_my.c)){case 0:var _mX=B(_mF(_));_mt=_mx;return __continue;case 1:var _mY=new T(function(){return E(_mB)+E(_mD);}),_mZ=new T(function(){return E(_mC)+E(_mE);}),_n0=function(_n1,_){return new F(function(){return _jR(_mB,_mC,_mY,_mZ,_n1,_);});},_n2=B(A(_g7,[new T(function(){return B(_79(_kl,_mz));},1),function(_n3,_){return new F(function(){return _jY(_n0,E(_n3),_);});},_mh,_])),_n4=B(_mF(_));_mt=_mx;return __continue;default:var _n5=function(_n6,_){return new F(function(){return _jz(E(_mB),E(_mC),E(_mD),E(_mE),E(_n6),_);});},_n7=B(A(_g7,[new T(function(){return B(_79(_kl,_my.e));},1),function(_n8,_){return new F(function(){return _jL(_n5,E(_n8),_);});},_mh,_])),_n9=new T(function(){var _na=function(_nb,_){return new F(function(){return _jz(E(_mB),E(_mC),E(_mD),E(_mE),E(_nb),_);});};return B(_kn(_kA,function(_nc,_){return new F(function(){return _jY(_na,E(_nc),_);});}));}),_nd=B(A(_g7,[new T(function(){return B(_79(_kl,_mz));},1),_n9,_mh,_])),_ne=B(_mF(_));_mt=_mx;return __continue;}}})(_mt,_));if(_mu!=__continue){return _mu;}}};return new F(function(){return _ms(_kT,_);});}}})(_kP,_));if(_kQ!=__continue){return _kQ;}}},_nf=_kL.a,_ng=_kL.b,_nh=E(_nf),_ni=_nh.d,_nj=E(_nh.b),_nk=_nj.a,_nl=_nj.b,_nm=_nj.c,_nn=_nj.d,_no=function(_){var _np=function(_nq,_nr,_ns,_){while(1){var _nt=B((function(_nu,_nv,_nw,_){var _nx=E(_nu);if(!_nx._){return _5L;}else{var _ny=E(_nv);if(!_ny._){return _5L;}else{var _nz=E(_nw);if(!_nz._){return _5L;}else{var _nA=E(_nz.a),_nB=E(_nA.a),_nC=E(_nA.b),_nD=new T(function(){return E(_nB.b)+E(_nl);}),_nE=B(_h2(_kH,_kN,new T(function(){return B(_79(_kl,E(_nC.b)));}),_ny.a,_nC.a,_nm,_nn,_nD,0,new T(function(){return E(_nB.a)+E(_nk);}),_nD,_nx.a,_));_nq=_nx.b;_nr=_ny.b;_ns=_nz.b;return __continue;}}}})(_nq,_nr,_ns,_));if(_nt!=__continue){return _nt;}}},_nF=new T(function(){return B(_kB(_nh.f,new T(function(){return B(_kB(_nh.h,_nh.i));},1)));},1);return new F(function(){return _np(_nh.j,_nh.k,_nF,_);});};switch(E(_nh.c)){case 0:var _nG=B(_no(_));return new F(function(){return _kO(_ng,_);});break;case 1:var _nH=E(_kH),_nI=_nH.a,_nJ=new T(function(){return E(_nk)+E(_nm);}),_nK=new T(function(){return E(_nl)+E(_nn);}),_nL=function(_nM,_){return new F(function(){return _jR(_nk,_nl,_nJ,_nK,_nM,_);});},_nN=B(A(_g7,[new T(function(){return B(_79(_kl,_ni));},1),function(_nO,_){return new F(function(){return _jY(_nL,E(_nO),_);});},_nI,_])),_nP=B(_no(_)),_nQ=function(_nR,_){while(1){var _nS=B((function(_nT,_){var _nU=E(_nT);if(!_nU._){return _5L;}else{var _nV=_nU.b,_nW=E(_nU.a),_nX=_nW.d,_nY=E(_nW.b),_nZ=_nY.a,_o0=_nY.b,_o1=_nY.c,_o2=_nY.d,_o3=function(_){var _o4=function(_o5,_o6,_o7,_){while(1){var _o8=B((function(_o9,_oa,_ob,_){var _oc=E(_o9);if(!_oc._){return _5L;}else{var _od=E(_oa);if(!_od._){return _5L;}else{var _oe=E(_ob);if(!_oe._){return _5L;}else{var _of=E(_oe.a),_og=E(_of.a),_oh=E(_of.b),_oi=new T(function(){return E(_og.b)+E(_o0);}),_oj=B(_ic(_nI,_nH.b,_kN,new T(function(){return B(_79(_kl,E(_oh.b)));}),_od.a,_oh.a,_o1,_o2,_oi,0,new T(function(){return E(_og.a)+E(_nZ);}),_oi,_oc.a,_));_o5=_oc.b;_o6=_od.b;_o7=_oe.b;return __continue;}}}})(_o5,_o6,_o7,_));if(_o8!=__continue){return _o8;}}},_ok=new T(function(){return B(_kB(_nW.f,new T(function(){return B(_kB(_nW.h,_nW.i));},1)));},1);return new F(function(){return _o4(_nW.j,_nW.k,_ok,_);});};switch(E(_nW.c)){case 0:var _ol=B(_o3(_));_nR=_nV;return __continue;case 1:var _om=new T(function(){return E(_nZ)+E(_o1);}),_on=new T(function(){return E(_o0)+E(_o2);}),_oo=function(_op,_){return new F(function(){return _jR(_nZ,_o0,_om,_on,_op,_);});},_oq=B(A(_g7,[new T(function(){return B(_79(_kl,_nX));},1),function(_or,_){return new F(function(){return _jY(_oo,E(_or),_);});},_nI,_])),_os=B(_o3(_));_nR=_nV;return __continue;default:var _ot=function(_ou,_){return new F(function(){return _jz(E(_nZ),E(_o0),E(_o1),E(_o2),E(_ou),_);});},_ov=B(A(_g7,[new T(function(){return B(_79(_kl,_nW.e));},1),function(_ow,_){return new F(function(){return _jL(_ot,E(_ow),_);});},_nI,_])),_ox=new T(function(){var _oy=function(_oz,_){return new F(function(){return _jz(E(_nZ),E(_o0),E(_o1),E(_o2),E(_oz),_);});};return B(_kn(_kA,function(_oA,_){return new F(function(){return _jY(_oy,E(_oA),_);});}));}),_oB=B(A(_g7,[new T(function(){return B(_79(_kl,_nX));},1),_ox,_nI,_])),_oC=B(_o3(_));_nR=_nV;return __continue;}}})(_nR,_));if(_nS!=__continue){return _nS;}}};return new F(function(){return _nQ(_ng,_);});break;default:var _oD=E(_kH),_oE=_oD.a,_oF=function(_oG,_){return new F(function(){return _jz(E(_nk),E(_nl),E(_nm),E(_nn),E(_oG),_);});},_oH=B(A(_g7,[new T(function(){return B(_79(_kl,_nh.e));},1),function(_oI,_){return new F(function(){return _jL(_oF,E(_oI),_);});},_oE,_])),_oJ=new T(function(){var _oK=function(_oL,_){return new F(function(){return _jz(E(_nk),E(_nl),E(_nm),E(_nn),E(_oL),_);});};return B(_kn(_kA,function(_oM,_){return new F(function(){return _jY(_oK,E(_oM),_);});}));}),_oN=B(A(_g7,[new T(function(){return B(_79(_kl,_ni));},1),_oJ,_oE,_])),_oO=B(_no(_)),_oP=function(_oQ,_){while(1){var _oR=B((function(_oS,_){var _oT=E(_oS);if(!_oT._){return _5L;}else{var _oU=_oT.b,_oV=E(_oT.a),_oW=_oV.d,_oX=E(_oV.b),_oY=_oX.a,_oZ=_oX.b,_p0=_oX.c,_p1=_oX.d,_p2=function(_){var _p3=function(_p4,_p5,_p6,_){while(1){var _p7=B((function(_p8,_p9,_pa,_){var _pb=E(_p8);if(!_pb._){return _5L;}else{var _pc=E(_p9);if(!_pc._){return _5L;}else{var _pd=E(_pa);if(!_pd._){return _5L;}else{var _pe=E(_pd.a),_pf=E(_pe.a),_pg=E(_pe.b),_ph=new T(function(){return E(_pf.b)+E(_oZ);}),_pi=B(_ic(_oE,_oD.b,_kN,new T(function(){return B(_79(_kl,E(_pg.b)));}),_pc.a,_pg.a,_p0,_p1,_ph,0,new T(function(){return E(_pf.a)+E(_oY);}),_ph,_pb.a,_));_p4=_pb.b;_p5=_pc.b;_p6=_pd.b;return __continue;}}}})(_p4,_p5,_p6,_));if(_p7!=__continue){return _p7;}}},_pj=new T(function(){return B(_kB(_oV.f,new T(function(){return B(_kB(_oV.h,_oV.i));},1)));},1);return new F(function(){return _p3(_oV.j,_oV.k,_pj,_);});};switch(E(_oV.c)){case 0:var _pk=B(_p2(_));_oQ=_oU;return __continue;case 1:var _pl=new T(function(){return E(_oY)+E(_p0);}),_pm=new T(function(){return E(_oZ)+E(_p1);}),_pn=function(_po,_){return new F(function(){return _jR(_oY,_oZ,_pl,_pm,_po,_);});},_pp=B(A(_g7,[new T(function(){return B(_79(_kl,_oW));},1),function(_pq,_){return new F(function(){return _jY(_pn,E(_pq),_);});},_oE,_])),_pr=B(_p2(_));_oQ=_oU;return __continue;default:var _ps=function(_pt,_){return new F(function(){return _jz(E(_oY),E(_oZ),E(_p0),E(_p1),E(_pt),_);});},_pu=B(A(_g7,[new T(function(){return B(_79(_kl,_oV.e));},1),function(_pv,_){return new F(function(){return _jL(_ps,E(_pv),_);});},_oE,_])),_pw=new T(function(){var _px=function(_py,_){return new F(function(){return _jz(E(_oY),E(_oZ),E(_p0),E(_p1),E(_py),_);});};return B(_kn(_kA,function(_pz,_){return new F(function(){return _jY(_px,E(_pz),_);});}));}),_pA=B(A(_g7,[new T(function(){return B(_79(_kl,_oW));},1),_pw,_oE,_])),_pB=B(_p2(_));_oQ=_oU;return __continue;}}})(_oQ,_));if(_oR!=__continue){return _oR;}}};return new F(function(){return _oP(_ng,_);});}}},_pC=function(_pD){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_pD));}))));});},_pE=new T(function(){return B(_pC("ww_s5VG (Double, Double)"));}),_pF=new T(function(){return B(unCStr("Prelude.undefined"));}),_pG=new T(function(){return B(err(_pF));}),_pH=function(_pI){return E(_pG);},_pJ=new T(function(){return B(_pH(_));}),_pK=new T(function(){return B(unCStr("\u3059\u3054\u3044\uff01 \u5168\u554f\u6b63\u89e3\uff01"));}),_pL=new T(function(){return B(unCStr("\u56de\u307e\u3061\u304c\u3078\u3061\u3083\u3063\u305f\u306d\uff01"));}),_pM=function(_pN,_pO){if(_pN<=0){if(_pN>=0){return new F(function(){return quot(_pN,_pO);});}else{if(_pO<=0){return new F(function(){return quot(_pN,_pO);});}else{return quot(_pN+1|0,_pO)-1|0;}}}else{if(_pO>=0){if(_pN>=0){return new F(function(){return quot(_pN,_pO);});}else{if(_pO<=0){return new F(function(){return quot(_pN,_pO);});}else{return quot(_pN+1|0,_pO)-1|0;}}}else{return quot(_pN-1|0,_pO)-1|0;}}},_pP=function(_pQ,_pR){if(_pQ<=_pR){var _pS=function(_pT){return new T2(1,_pT,new T(function(){if(_pT!=_pR){return B(_pS(_pT+1|0));}else{return __Z;}}));};return new F(function(){return _pS(_pQ);});}else{return __Z;}},_pU=new T(function(){return B(_pP(0,2147483647));}),_pV=40,_pW=60,_pX=new T2(0,_pV,_pW),_pY=new T2(1,_pX,_v),_pZ=1,_q0=new T2(1,_pZ,_v),_q1=1,_q2=new T2(1,_q1,_v),_q3=function(_q4,_q5){var _q6=_q4%_q5;if(_q4<=0){if(_q4>=0){return E(_q6);}else{if(_q5<=0){return E(_q6);}else{var _q7=E(_q6);return (_q7==0)?0:_q7+_q5|0;}}}else{if(_q5>=0){if(_q4>=0){return E(_q6);}else{if(_q5<=0){return E(_q6);}else{var _q8=E(_q6);return (_q8==0)?0:_q8+_q5|0;}}}else{var _q9=E(_q6);return (_q9==0)?0:_q9+_q5|0;}}},_qa=function(_qb,_qc,_qd){var _qe=E(_qc);if(!_qe._){return __Z;}else{var _qf=E(_qd);return (_qf._==0)?__Z:new T2(1,new T(function(){return B(A2(_qb,_qe.a,_qf.a));}),new T(function(){return B(_qa(_qb,_qe.b,_qf.b));}));}},_qg=function(_qh,_qi,_qj,_qk,_ql){var _qm=new T(function(){var _qn=new T(function(){return B(_a2(_qj,0));}),_qo=new T(function(){return B(_pM(E(_qn)-3|0,2));}),_qp=new T(function(){var _qq=50-E(_qo)*8,_qr=_qq&4294967295;if(_qq>=_qr){return _qr;}else{return _qr-1|0;}}),_qs=new T(function(){return 40-E(_qp)/9*4*E(_qo);}),_qt=new T(function(){var _qu=E(_qn),_qv=B(_pM(_qu,2)),_qw=_qv+B(_q3(_qu,2))|0,_qx=_qw-1|0,_qy=new T(function(){return E(_qi)/5-B(_pM(_qu-3|0,2))*3;}),_qz=new T(function(){var _qA=E(_qi);return _qA/4+_qA/10;}),_qB=new T(function(){return E(_qh)/16-B(_pM(_qu-3|0,2));}),_qC=new T(function(){var _qD=E(_qB);return _qD+_qD;}),_qE=new T(function(){var _qF=E(_qC);return (E(_qh)-(_qF+_qF)-E(_qB)*(_qw-1))/_qw;}),_qG=new T(function(){var _qH=_qv-1|0;if(0<=_qH){var _qI=new T(function(){return E(_qz)+E(_qy)+E(_qh)/20;}),_qJ=new T(function(){return (E(_qh)-(E(_qE)*_qv+E(_qB)*(_qv-1)))/2;}),_qK=function(_qL){return new T2(1,new T4(0,new T(function(){return E(_qJ)+(E(_qE)+E(_qB))*_qL;}),_qI,_qE,_qy),new T(function(){if(_qL!=_qH){return B(_qK(_qL+1|0));}else{return __Z;}}));};return B(_qK(0));}else{return __Z;}});if(0<=_qx){var _qM=function(_qN){return new T2(1,new T4(0,new T(function(){return E(_qC)+(E(_qE)+E(_qB))*_qN;}),_qz,_qE,_qy),new T(function(){if(_qN!=_qx){return B(_qM(_qN+1|0));}else{return E(_qG);}}));};return B(_qM(0));}else{return E(_qG);}},1),_qO=function(_qP,_qQ){var _qR=E(_qP);return {_:0,a:_qR+1|0,b:E(_qQ),c:E(_62),d:0,e:7,f:E(new T2(1,new T2(0,_qs,_pW),_v)),g:E(_v),h:E(new T2(1,_qp,_v)),i:E(_q0),j:E(new T2(1,new T(function(){return B(_79(_qj,_qR));}),_v)),k:E(_q2),l:E(_v),m:E(_v),n:E(new T1(1,new T(function(){return B(_79(_qk,_qR));}))),o:E(new T1(2,_qR))};};return B(_qa(_qO,_pU,_qt));});return new T2(0,{_:0,a:0,b:E(new T4(0,new T(function(){return E(_qh)/8;}),new T(function(){return E(_qi)/10;}),new T(function(){return E(_qh)/3;}),new T(function(){return E(_qi)/5;}))),c:E(_62),d:0,e:5,f:E(_pY),g:E(_v),h:E(_cZ),i:E(_q0),j:E(new T2(1,new T(function(){return B(_79(_qj,_ql));}),_v)),k:E(_cR),l:E(_v),m:E(_v),n:E(new T1(1,new T(function(){return B(_79(_qk,_ql));}))),o:E(_ax)},_qm);},_qS=new T1(0,0),_qT=function(_qU,_qV){while(1){var _qW=E(_qU);if(!_qW._){var _qX=_qW.a,_qY=E(_qV);if(!_qY._){return new T1(0,(_qX>>>0|_qY.a>>>0)>>>0&4294967295);}else{_qU=new T1(1,I_fromInt(_qX));_qV=_qY;continue;}}else{var _qZ=E(_qV);if(!_qZ._){_qU=_qW;_qV=new T1(1,I_fromInt(_qZ.a));continue;}else{return new T1(1,I_or(_qW.a,_qZ.a));}}}},_r0=function(_r1,_r2){while(1){var _r3=E(_r1);if(!_r3._){_r1=new T1(1,I_fromInt(_r3.a));continue;}else{return new T1(1,I_shiftLeft(_r3.a,_r2));}}},_r4=function(_r5){var _r6=E(_r5);if(!_r6._){return E(_qS);}else{return new F(function(){return _qT(new T1(0,E(_r6.a)),B(_r0(B(_r4(_r6.b)),31)));});}},_r7=new T1(0,1),_r8=new T1(0,2147483647),_r9=function(_ra,_rb){while(1){var _rc=E(_ra);if(!_rc._){var _rd=_rc.a,_re=E(_rb);if(!_re._){var _rf=_re.a,_rg=addC(_rd,_rf);if(!E(_rg.b)){return new T1(0,_rg.a);}else{_ra=new T1(1,I_fromInt(_rd));_rb=new T1(1,I_fromInt(_rf));continue;}}else{_ra=new T1(1,I_fromInt(_rd));_rb=_re;continue;}}else{var _rh=E(_rb);if(!_rh._){_ra=_rc;_rb=new T1(1,I_fromInt(_rh.a));continue;}else{return new T1(1,I_add(_rc.a,_rh.a));}}}},_ri=new T(function(){return B(_r9(_r8,_r7));}),_rj=function(_rk){var _rl=E(_rk);if(!_rl._){var _rm=E(_rl.a);return (_rm==( -2147483648))?E(_ri):new T1(0, -_rm);}else{return new T1(1,I_negate(_rl.a));}},_rn=function(_ro,_rp){if(!E(_ro)){return new F(function(){return _rj(B(_r4(_rp)));});}else{return new F(function(){return _r4(_rp);});}},_rq=1420103680,_rr=465,_rs=new T2(1,_rr,_v),_rt=new T2(1,_rq,_rs),_ru=new T(function(){return B(_rn(_5Q,_rt));}),_rv=function(_rw){return E(_ru);},_rx=0,_ry=new T(function(){return B(unCStr("base"));}),_rz=new T(function(){return B(unCStr("GHC.Exception"));}),_rA=new T(function(){return B(unCStr("ArithException"));}),_rB=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_ry,_rz,_rA),_rC=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_rB,_v,_v),_rD=function(_rE){return E(_rC);},_rF=function(_rG){var _rH=E(_rG);return new F(function(){return _X(B(_V(_rH.a)),_rD,_rH.b);});},_rI=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_rJ=new T(function(){return B(unCStr("denormal"));}),_rK=new T(function(){return B(unCStr("divide by zero"));}),_rL=new T(function(){return B(unCStr("loss of precision"));}),_rM=new T(function(){return B(unCStr("arithmetic underflow"));}),_rN=new T(function(){return B(unCStr("arithmetic overflow"));}),_rO=function(_rP,_rQ){switch(E(_rP)){case 0:return new F(function(){return _3(_rN,_rQ);});break;case 1:return new F(function(){return _3(_rM,_rQ);});break;case 2:return new F(function(){return _3(_rL,_rQ);});break;case 3:return new F(function(){return _3(_rK,_rQ);});break;case 4:return new F(function(){return _3(_rJ,_rQ);});break;default:return new F(function(){return _3(_rI,_rQ);});}},_rR=function(_rS){return new F(function(){return _rO(_rS,_v);});},_rT=function(_rU,_rV,_rW){return new F(function(){return _rO(_rV,_rW);});},_rX=function(_rY,_rZ){return new F(function(){return _28(_rO,_rY,_rZ);});},_s0=new T3(0,_rT,_rR,_rX),_s1=new T(function(){return new T5(0,_rD,_s0,_s2,_rF,_rR);}),_s2=function(_bj){return new T2(0,_s1,_bj);},_s3=3,_s4=new T(function(){return B(_s2(_s3));}),_s5=new T(function(){return die(_s4);}),_s6=function(_s7,_s8){var _s9=E(_s8);switch(_s9){case  -1:return E(_rx);case 0:return E(_s5);default:return new F(function(){return _q3(E(_s7),_s9);});}},_sa=new T(function(){return B(unCStr("s"));}),_sb=function(_sc,_sd){while(1){var _se=E(_sc);if(!_se._){return E(_sd);}else{_sc=_se.b;_sd=_se.a;continue;}}},_sf=function(_sg,_sh,_si){return new F(function(){return _sb(_sh,_sg);});},_sj=new T1(0,1),_sk=new T1(0,1),_sl=function(_sm,_sn){var _so=E(_sm);return new T2(0,_so,new T(function(){var _sp=B(_sl(B(_r9(_so,_sn)),_sn));return new T2(1,_sp.a,_sp.b);}));},_sq=function(_sr){var _ss=B(_sl(_sr,_sk));return new T2(1,_ss.a,_ss.b);},_st=function(_su,_sv){while(1){var _sw=E(_su);if(!_sw._){var _sx=_sw.a,_sy=E(_sv);if(!_sy._){var _sz=_sy.a,_sA=subC(_sx,_sz);if(!E(_sA.b)){return new T1(0,_sA.a);}else{_su=new T1(1,I_fromInt(_sx));_sv=new T1(1,I_fromInt(_sz));continue;}}else{_su=new T1(1,I_fromInt(_sx));_sv=_sy;continue;}}else{var _sB=E(_sv);if(!_sB._){_su=_sw;_sv=new T1(1,I_fromInt(_sB.a));continue;}else{return new T1(1,I_sub(_sw.a,_sB.a));}}}},_sC=function(_sD,_sE){var _sF=B(_sl(_sD,new T(function(){return B(_st(_sE,_sD));})));return new T2(1,_sF.a,_sF.b);},_sG=new T1(0,0),_sH=function(_sI,_sJ){var _sK=E(_sI);if(!_sK._){var _sL=_sK.a,_sM=E(_sJ);return (_sM._==0)?_sL>=_sM.a:I_compareInt(_sM.a,_sL)<=0;}else{var _sN=_sK.a,_sO=E(_sJ);return (_sO._==0)?I_compareInt(_sN,_sO.a)>=0:I_compare(_sN,_sO.a)>=0;}},_sP=function(_sQ,_sR){var _sS=E(_sQ);if(!_sS._){var _sT=_sS.a,_sU=E(_sR);return (_sU._==0)?_sT>_sU.a:I_compareInt(_sU.a,_sT)<0;}else{var _sV=_sS.a,_sW=E(_sR);return (_sW._==0)?I_compareInt(_sV,_sW.a)>0:I_compare(_sV,_sW.a)>0;}},_sX=function(_sY,_sZ){var _t0=E(_sY);if(!_t0._){var _t1=_t0.a,_t2=E(_sZ);return (_t2._==0)?_t1<_t2.a:I_compareInt(_t2.a,_t1)>0;}else{var _t3=_t0.a,_t4=E(_sZ);return (_t4._==0)?I_compareInt(_t3,_t4.a)<0:I_compare(_t3,_t4.a)<0;}},_t5=function(_t6,_t7,_t8){if(!B(_sH(_t7,_sG))){var _t9=function(_ta){return (!B(_sX(_ta,_t8)))?new T2(1,_ta,new T(function(){return B(_t9(B(_r9(_ta,_t7))));})):__Z;};return new F(function(){return _t9(_t6);});}else{var _tb=function(_tc){return (!B(_sP(_tc,_t8)))?new T2(1,_tc,new T(function(){return B(_tb(B(_r9(_tc,_t7))));})):__Z;};return new F(function(){return _tb(_t6);});}},_td=function(_te,_tf,_tg){return new F(function(){return _t5(_te,B(_st(_tf,_te)),_tg);});},_th=function(_ti,_tj){return new F(function(){return _t5(_ti,_sk,_tj);});},_tk=function(_tl){var _tm=E(_tl);if(!_tm._){return E(_tm.a);}else{return new F(function(){return I_toInt(_tm.a);});}},_tn=function(_to){return new F(function(){return _tk(_to);});},_tp=function(_tq){return new F(function(){return _st(_tq,_sk);});},_tr=function(_ts){return new F(function(){return _r9(_ts,_sk);});},_tt=function(_tu){return new T1(0,_tu);},_tv=function(_tw){return new F(function(){return _tt(E(_tw));});},_tx={_:0,a:_tr,b:_tp,c:_tv,d:_tn,e:_sq,f:_sC,g:_th,h:_td},_ty=function(_tz,_tA){while(1){var _tB=E(_tz);if(!_tB._){var _tC=E(_tB.a);if(_tC==( -2147483648)){_tz=new T1(1,I_fromInt( -2147483648));continue;}else{var _tD=E(_tA);if(!_tD._){return new T1(0,B(_pM(_tC,_tD.a)));}else{_tz=new T1(1,I_fromInt(_tC));_tA=_tD;continue;}}}else{var _tE=_tB.a,_tF=E(_tA);return (_tF._==0)?new T1(1,I_div(_tE,I_fromInt(_tF.a))):new T1(1,I_div(_tE,_tF.a));}}},_tG=function(_tH,_tI){var _tJ=E(_tH);if(!_tJ._){var _tK=_tJ.a,_tL=E(_tI);return (_tL._==0)?_tK==_tL.a:(I_compareInt(_tL.a,_tK)==0)?true:false;}else{var _tM=_tJ.a,_tN=E(_tI);return (_tN._==0)?(I_compareInt(_tM,_tN.a)==0)?true:false:(I_compare(_tM,_tN.a)==0)?true:false;}},_tO=new T1(0,0),_tP=function(_tQ,_tR){if(!B(_tG(_tR,_tO))){return new F(function(){return _ty(_tQ,_tR);});}else{return E(_s5);}},_tS=function(_tT,_tU){while(1){var _tV=E(_tT);if(!_tV._){var _tW=E(_tV.a);if(_tW==( -2147483648)){_tT=new T1(1,I_fromInt( -2147483648));continue;}else{var _tX=E(_tU);if(!_tX._){var _tY=_tX.a;return new T2(0,new T1(0,B(_pM(_tW,_tY))),new T1(0,B(_q3(_tW,_tY))));}else{_tT=new T1(1,I_fromInt(_tW));_tU=_tX;continue;}}}else{var _tZ=E(_tU);if(!_tZ._){_tT=_tV;_tU=new T1(1,I_fromInt(_tZ.a));continue;}else{var _u0=I_divMod(_tV.a,_tZ.a);return new T2(0,new T1(1,_u0.a),new T1(1,_u0.b));}}}},_u1=function(_u2,_u3){if(!B(_tG(_u3,_tO))){var _u4=B(_tS(_u2,_u3));return new T2(0,_u4.a,_u4.b);}else{return E(_s5);}},_u5=function(_u6,_u7){while(1){var _u8=E(_u6);if(!_u8._){var _u9=E(_u8.a);if(_u9==( -2147483648)){_u6=new T1(1,I_fromInt( -2147483648));continue;}else{var _ua=E(_u7);if(!_ua._){return new T1(0,B(_q3(_u9,_ua.a)));}else{_u6=new T1(1,I_fromInt(_u9));_u7=_ua;continue;}}}else{var _ub=_u8.a,_uc=E(_u7);return (_uc._==0)?new T1(1,I_mod(_ub,I_fromInt(_uc.a))):new T1(1,I_mod(_ub,_uc.a));}}},_ud=function(_ue,_uf){if(!B(_tG(_uf,_tO))){return new F(function(){return _u5(_ue,_uf);});}else{return E(_s5);}},_ug=function(_uh,_ui){while(1){var _uj=E(_uh);if(!_uj._){var _uk=E(_uj.a);if(_uk==( -2147483648)){_uh=new T1(1,I_fromInt( -2147483648));continue;}else{var _ul=E(_ui);if(!_ul._){return new T1(0,quot(_uk,_ul.a));}else{_uh=new T1(1,I_fromInt(_uk));_ui=_ul;continue;}}}else{var _um=_uj.a,_un=E(_ui);return (_un._==0)?new T1(0,I_toInt(I_quot(_um,I_fromInt(_un.a)))):new T1(1,I_quot(_um,_un.a));}}},_uo=function(_up,_uq){if(!B(_tG(_uq,_tO))){return new F(function(){return _ug(_up,_uq);});}else{return E(_s5);}},_ur=function(_us,_ut){while(1){var _uu=E(_us);if(!_uu._){var _uv=E(_uu.a);if(_uv==( -2147483648)){_us=new T1(1,I_fromInt( -2147483648));continue;}else{var _uw=E(_ut);if(!_uw._){var _ux=_uw.a;return new T2(0,new T1(0,quot(_uv,_ux)),new T1(0,_uv%_ux));}else{_us=new T1(1,I_fromInt(_uv));_ut=_uw;continue;}}}else{var _uy=E(_ut);if(!_uy._){_us=_uu;_ut=new T1(1,I_fromInt(_uy.a));continue;}else{var _uz=I_quotRem(_uu.a,_uy.a);return new T2(0,new T1(1,_uz.a),new T1(1,_uz.b));}}}},_uA=function(_uB,_uC){if(!B(_tG(_uC,_tO))){var _uD=B(_ur(_uB,_uC));return new T2(0,_uD.a,_uD.b);}else{return E(_s5);}},_uE=function(_uF,_uG){while(1){var _uH=E(_uF);if(!_uH._){var _uI=E(_uH.a);if(_uI==( -2147483648)){_uF=new T1(1,I_fromInt( -2147483648));continue;}else{var _uJ=E(_uG);if(!_uJ._){return new T1(0,_uI%_uJ.a);}else{_uF=new T1(1,I_fromInt(_uI));_uG=_uJ;continue;}}}else{var _uK=_uH.a,_uL=E(_uG);return (_uL._==0)?new T1(1,I_rem(_uK,I_fromInt(_uL.a))):new T1(1,I_rem(_uK,_uL.a));}}},_uM=function(_uN,_uO){if(!B(_tG(_uO,_tO))){return new F(function(){return _uE(_uN,_uO);});}else{return E(_s5);}},_uP=function(_uQ){return E(_uQ);},_uR=function(_uS){return E(_uS);},_uT=function(_uU){var _uV=E(_uU);if(!_uV._){var _uW=E(_uV.a);return (_uW==( -2147483648))?E(_ri):(_uW<0)?new T1(0, -_uW):E(_uV);}else{var _uX=_uV.a;return (I_compareInt(_uX,0)>=0)?E(_uV):new T1(1,I_negate(_uX));}},_uY=new T1(0, -1),_uZ=function(_v0){var _v1=E(_v0);if(!_v1._){var _v2=_v1.a;return (_v2>=0)?(E(_v2)==0)?E(_qS):E(_r7):E(_uY);}else{var _v3=I_compareInt(_v1.a,0);return (_v3<=0)?(E(_v3)==0)?E(_qS):E(_uY):E(_r7);}},_v4=function(_v5,_v6){while(1){var _v7=E(_v5);if(!_v7._){var _v8=_v7.a,_v9=E(_v6);if(!_v9._){var _va=_v9.a;if(!(imul(_v8,_va)|0)){return new T1(0,imul(_v8,_va)|0);}else{_v5=new T1(1,I_fromInt(_v8));_v6=new T1(1,I_fromInt(_va));continue;}}else{_v5=new T1(1,I_fromInt(_v8));_v6=_v9;continue;}}else{var _vb=E(_v6);if(!_vb._){_v5=_v7;_v6=new T1(1,I_fromInt(_vb.a));continue;}else{return new T1(1,I_mul(_v7.a,_vb.a));}}}},_vc={_:0,a:_r9,b:_st,c:_v4,d:_rj,e:_uT,f:_uZ,g:_uR},_vd=function(_ve,_vf){var _vg=E(_ve);if(!_vg._){var _vh=_vg.a,_vi=E(_vf);return (_vi._==0)?_vh!=_vi.a:(I_compareInt(_vi.a,_vh)==0)?false:true;}else{var _vj=_vg.a,_vk=E(_vf);return (_vk._==0)?(I_compareInt(_vj,_vk.a)==0)?false:true:(I_compare(_vj,_vk.a)==0)?false:true;}},_vl=new T2(0,_tG,_vd),_vm=function(_vn,_vo){var _vp=E(_vn);if(!_vp._){var _vq=_vp.a,_vr=E(_vo);return (_vr._==0)?_vq<=_vr.a:I_compareInt(_vr.a,_vq)>=0;}else{var _vs=_vp.a,_vt=E(_vo);return (_vt._==0)?I_compareInt(_vs,_vt.a)<=0:I_compare(_vs,_vt.a)<=0;}},_vu=function(_vv,_vw){return (!B(_vm(_vv,_vw)))?E(_vv):E(_vw);},_vx=function(_vy,_vz){return (!B(_vm(_vy,_vz)))?E(_vz):E(_vy);},_vA=function(_vB,_vC){var _vD=E(_vB);if(!_vD._){var _vE=_vD.a,_vF=E(_vC);if(!_vF._){var _vG=_vF.a;return (_vE!=_vG)?(_vE>_vG)?2:0:1;}else{var _vH=I_compareInt(_vF.a,_vE);return (_vH<=0)?(_vH>=0)?1:2:0;}}else{var _vI=_vD.a,_vJ=E(_vC);if(!_vJ._){var _vK=I_compareInt(_vI,_vJ.a);return (_vK>=0)?(_vK<=0)?1:2:0;}else{var _vL=I_compare(_vI,_vJ.a);return (_vL>=0)?(_vL<=0)?1:2:0;}}},_vM={_:0,a:_vl,b:_vA,c:_sX,d:_vm,e:_sP,f:_sH,g:_vu,h:_vx},_vN=function(_vO){return new T2(0,E(_vO),E(_sj));},_vP=new T3(0,_vc,_vM,_vN),_vQ={_:0,a:_vP,b:_tx,c:_uo,d:_uM,e:_tP,f:_ud,g:_uA,h:_u1,i:_uP},_vR=new T1(0,0),_vS=function(_vT,_vU,_vV){var _vW=B(A1(_vT,_vU));if(!B(_tG(_vW,_vR))){return new F(function(){return _ty(B(_v4(_vU,_vV)),_vW);});}else{return E(_s5);}},_vX=function(_vY,_vZ){while(1){if(!B(_tG(_vZ,_tO))){var _w0=_vZ,_w1=B(_uM(_vY,_vZ));_vY=_w0;_vZ=_w1;continue;}else{return E(_vY);}}},_w2=5,_w3=new T(function(){return B(_s2(_w2));}),_w4=new T(function(){return die(_w3);}),_w5=function(_w6,_w7){if(!B(_tG(_w7,_tO))){var _w8=B(_vX(B(_uT(_w6)),B(_uT(_w7))));return (!B(_tG(_w8,_tO)))?new T2(0,B(_ug(_w6,_w8)),B(_ug(_w7,_w8))):E(_s5);}else{return E(_w4);}},_w9=function(_wa,_wb,_wc,_wd){var _we=B(_v4(_wb,_wc));return new F(function(){return _w5(B(_v4(B(_v4(_wa,_wd)),B(_uZ(_we)))),B(_uT(_we)));});},_wf=function(_wg){return E(E(_wg).a);},_wh=function(_wi){return E(E(_wi).a);},_wj=function(_wk){return E(E(_wk).g);},_wl=function(_wm,_wn,_wo){var _wp=new T(function(){if(!B(_tG(_wo,_tO))){var _wq=B(_ur(_wn,_wo));return new T2(0,_wq.a,_wq.b);}else{return E(_s5);}}),_wr=new T(function(){return B(A2(_wj,B(_wh(B(_wf(_wm)))),new T(function(){return E(E(_wp).a);})));});return new T2(0,_wr,new T(function(){return new T2(0,E(E(_wp).b),E(_wo));}));},_ws=function(_wt){return E(E(_wt).b);},_wu=function(_wv,_ww,_wx){var _wy=B(_wl(_wv,_ww,_wx)),_wz=_wy.a,_wA=E(_wy.b);if(!B(_sX(B(_v4(_wA.a,_sj)),B(_v4(_tO,_wA.b))))){return E(_wz);}else{var _wB=B(_wh(B(_wf(_wv))));return new F(function(){return A3(_ws,_wB,_wz,new T(function(){return B(A2(_wj,_wB,_sj));}));});}},_wC=479723520,_wD=40233135,_wE=new T2(1,_wD,_v),_wF=new T2(1,_wC,_wE),_wG=new T(function(){return B(_rn(_5Q,_wF));}),_wH=new T1(0,40587),_wI=function(_wJ){var _wK=new T(function(){var _wL=B(_w9(_wJ,_sj,_ru,_sj)),_wM=B(_w9(_wG,_sj,_ru,_sj)),_wN=B(_w9(_wL.a,_wL.b,_wM.a,_wM.b));return B(_wu(_vQ,_wN.a,_wN.b));});return new T2(0,new T(function(){return B(_r9(_wH,_wK));}),new T(function(){return B(_st(_wJ,B(_vS(_rv,B(_v4(_wK,_ru)),_wG))));}));},_wO=function(_wP,_wQ){var _wR=E(_wQ);if(!_wR._){return __Z;}else{var _wS=_wR.a,_wT=E(_wP);return (_wT==1)?new T2(1,_wS,_v):new T2(1,_wS,new T(function(){return B(_wO(_wT-1|0,_wR.b));}));}},_wU=function(_wV,_){var _wW=__get(_wV,0),_wX=__get(_wV,1),_wY=Number(_wW),_wZ=jsTrunc(_wY),_x0=Number(_wX),_x1=jsTrunc(_x0);return new T2(0,_wZ,_x1);},_x2=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_x3=660865024,_x4=465661287,_x5=new T2(1,_x4,_v),_x6=new T2(1,_x3,_x5),_x7=new T(function(){return B(_rn(_5Q,_x6));}),_x8=function(_){var _x9=__app0(E(_x2)),_xa=B(_wU(_x9,_));return new T(function(){var _xb=E(_xa);if(!B(_tG(_x7,_vR))){return B(_r9(B(_v4(B(_tt(E(_xb.a))),_ru)),B(_ty(B(_v4(B(_v4(B(_tt(E(_xb.b))),_ru)),_ru)),_x7))));}else{return E(_s5);}});},_xc=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_xd=new T(function(){return B(err(_xc));}),_xe=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_xf=new T(function(){return B(err(_xe));}),_xg=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_xh=function(_xi){return new F(function(){return _bh(new T1(0,new T(function(){return B(_bv(_xi,_xg));})),_b1);});},_xj=new T(function(){return B(_xh("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_xk=function(_xl,_xm){while(1){var _xn=B((function(_xo,_xp){var _xq=E(_xo);switch(_xq._){case 0:var _xr=E(_xp);if(!_xr._){return __Z;}else{_xl=B(A1(_xq.a,_xr.a));_xm=_xr.b;return __continue;}break;case 1:var _xs=B(A1(_xq.a,_xp)),_xt=_xp;_xl=_xs;_xm=_xt;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_xq.a,_xp),new T(function(){return B(_xk(_xq.b,_xp));}));default:return E(_xq.a);}})(_xl,_xm));if(_xn!=__continue){return _xn;}}},_xu=function(_xv,_xw){var _xx=function(_xy){var _xz=E(_xw);if(_xz._==3){return new T2(3,_xz.a,new T(function(){return B(_xu(_xv,_xz.b));}));}else{var _xA=E(_xv);if(_xA._==2){return E(_xz);}else{var _xB=E(_xz);if(_xB._==2){return E(_xA);}else{var _xC=function(_xD){var _xE=E(_xB);if(_xE._==4){var _xF=function(_xG){return new T1(4,new T(function(){return B(_3(B(_xk(_xA,_xG)),_xE.a));}));};return new T1(1,_xF);}else{var _xH=E(_xA);if(_xH._==1){var _xI=_xH.a,_xJ=E(_xE);if(!_xJ._){return new T1(1,function(_xK){return new F(function(){return _xu(B(A1(_xI,_xK)),_xJ);});});}else{var _xL=function(_xM){return new F(function(){return _xu(B(A1(_xI,_xM)),new T(function(){return B(A1(_xJ.a,_xM));}));});};return new T1(1,_xL);}}else{var _xN=E(_xE);if(!_xN._){return E(_xj);}else{var _xO=function(_xP){return new F(function(){return _xu(_xH,new T(function(){return B(A1(_xN.a,_xP));}));});};return new T1(1,_xO);}}}},_xQ=E(_xA);switch(_xQ._){case 1:var _xR=E(_xB);if(_xR._==4){var _xS=function(_xT){return new T1(4,new T(function(){return B(_3(B(_xk(B(A1(_xQ.a,_xT)),_xT)),_xR.a));}));};return new T1(1,_xS);}else{return new F(function(){return _xC(_);});}break;case 4:var _xU=_xQ.a,_xV=E(_xB);switch(_xV._){case 0:var _xW=function(_xX){var _xY=new T(function(){return B(_3(_xU,new T(function(){return B(_xk(_xV,_xX));},1)));});return new T1(4,_xY);};return new T1(1,_xW);case 1:var _xZ=function(_y0){var _y1=new T(function(){return B(_3(_xU,new T(function(){return B(_xk(B(A1(_xV.a,_y0)),_y0));},1)));});return new T1(4,_y1);};return new T1(1,_xZ);default:return new T1(4,new T(function(){return B(_3(_xU,_xV.a));}));}break;default:return new F(function(){return _xC(_);});}}}}},_y2=E(_xv);switch(_y2._){case 0:var _y3=E(_xw);if(!_y3._){var _y4=function(_y5){return new F(function(){return _xu(B(A1(_y2.a,_y5)),new T(function(){return B(A1(_y3.a,_y5));}));});};return new T1(0,_y4);}else{return new F(function(){return _xx(_);});}break;case 3:return new T2(3,_y2.a,new T(function(){return B(_xu(_y2.b,_xw));}));default:return new F(function(){return _xx(_);});}},_y6=new T(function(){return B(unCStr("("));}),_y7=new T(function(){return B(unCStr(")"));}),_y8=function(_y9,_ya){return (!B(_7A(_y9,_ya)))?true:false;},_yb=new T2(0,_7A,_y8),_yc=function(_yd,_ye){var _yf=E(_yd);switch(_yf._){case 0:return new T1(0,function(_yg){return new F(function(){return _yc(B(A1(_yf.a,_yg)),_ye);});});case 1:return new T1(1,function(_yh){return new F(function(){return _yc(B(A1(_yf.a,_yh)),_ye);});});case 2:return new T0(2);case 3:return new F(function(){return _xu(B(A1(_ye,_yf.a)),new T(function(){return B(_yc(_yf.b,_ye));}));});break;default:var _yi=function(_yj){var _yk=E(_yj);if(!_yk._){return __Z;}else{var _yl=E(_yk.a);return new F(function(){return _3(B(_xk(B(A1(_ye,_yl.a)),_yl.b)),new T(function(){return B(_yi(_yk.b));},1));});}},_ym=B(_yi(_yf.a));return (_ym._==0)?new T0(2):new T1(4,_ym);}},_yn=new T0(2),_yo=function(_yp){return new T2(3,_yp,_yn);},_yq=function(_yr,_ys){var _yt=E(_yr);if(!_yt){return new F(function(){return A1(_ys,_5L);});}else{var _yu=new T(function(){return B(_yq(_yt-1|0,_ys));});return new T1(0,function(_yv){return E(_yu);});}},_yw=function(_yx,_yy,_yz){var _yA=new T(function(){return B(A1(_yx,_yo));}),_yB=function(_yC,_yD,_yE,_yF){while(1){var _yG=B((function(_yH,_yI,_yJ,_yK){var _yL=E(_yH);switch(_yL._){case 0:var _yM=E(_yI);if(!_yM._){return new F(function(){return A1(_yy,_yK);});}else{var _yN=_yJ+1|0,_yO=_yK;_yC=B(A1(_yL.a,_yM.a));_yD=_yM.b;_yE=_yN;_yF=_yO;return __continue;}break;case 1:var _yP=B(A1(_yL.a,_yI)),_yQ=_yI,_yN=_yJ,_yO=_yK;_yC=_yP;_yD=_yQ;_yE=_yN;_yF=_yO;return __continue;case 2:return new F(function(){return A1(_yy,_yK);});break;case 3:var _yR=new T(function(){return B(_yc(_yL,_yK));});return new F(function(){return _yq(_yJ,function(_yS){return E(_yR);});});break;default:return new F(function(){return _yc(_yL,_yK);});}})(_yC,_yD,_yE,_yF));if(_yG!=__continue){return _yG;}}};return function(_yT){return new F(function(){return _yB(_yA,_yT,0,_yz);});};},_yU=function(_yV){return new F(function(){return A1(_yV,_v);});},_yW=function(_yX,_yY){var _yZ=function(_z0){var _z1=E(_z0);if(!_z1._){return E(_yU);}else{var _z2=_z1.a;if(!B(A1(_yX,_z2))){return E(_yU);}else{var _z3=new T(function(){return B(_yZ(_z1.b));}),_z4=function(_z5){var _z6=new T(function(){return B(A1(_z3,function(_z7){return new F(function(){return A1(_z5,new T2(1,_z2,_z7));});}));});return new T1(0,function(_z8){return E(_z6);});};return E(_z4);}}};return function(_z9){return new F(function(){return A2(_yZ,_z9,_yY);});};},_za=new T0(6),_zb=new T(function(){return B(unCStr("valDig: Bad base"));}),_zc=new T(function(){return B(err(_zb));}),_zd=function(_ze,_zf){var _zg=function(_zh,_zi){var _zj=E(_zh);if(!_zj._){var _zk=new T(function(){return B(A1(_zi,_v));});return function(_zl){return new F(function(){return A1(_zl,_zk);});};}else{var _zm=E(_zj.a),_zn=function(_zo){var _zp=new T(function(){return B(_zg(_zj.b,function(_zq){return new F(function(){return A1(_zi,new T2(1,_zo,_zq));});}));}),_zr=function(_zs){var _zt=new T(function(){return B(A1(_zp,_zs));});return new T1(0,function(_zu){return E(_zt);});};return E(_zr);};switch(E(_ze)){case 8:if(48>_zm){var _zv=new T(function(){return B(A1(_zi,_v));});return function(_zw){return new F(function(){return A1(_zw,_zv);});};}else{if(_zm>55){var _zx=new T(function(){return B(A1(_zi,_v));});return function(_zy){return new F(function(){return A1(_zy,_zx);});};}else{return new F(function(){return _zn(_zm-48|0);});}}break;case 10:if(48>_zm){var _zz=new T(function(){return B(A1(_zi,_v));});return function(_zA){return new F(function(){return A1(_zA,_zz);});};}else{if(_zm>57){var _zB=new T(function(){return B(A1(_zi,_v));});return function(_zC){return new F(function(){return A1(_zC,_zB);});};}else{return new F(function(){return _zn(_zm-48|0);});}}break;case 16:if(48>_zm){if(97>_zm){if(65>_zm){var _zD=new T(function(){return B(A1(_zi,_v));});return function(_zE){return new F(function(){return A1(_zE,_zD);});};}else{if(_zm>70){var _zF=new T(function(){return B(A1(_zi,_v));});return function(_zG){return new F(function(){return A1(_zG,_zF);});};}else{return new F(function(){return _zn((_zm-65|0)+10|0);});}}}else{if(_zm>102){if(65>_zm){var _zH=new T(function(){return B(A1(_zi,_v));});return function(_zI){return new F(function(){return A1(_zI,_zH);});};}else{if(_zm>70){var _zJ=new T(function(){return B(A1(_zi,_v));});return function(_zK){return new F(function(){return A1(_zK,_zJ);});};}else{return new F(function(){return _zn((_zm-65|0)+10|0);});}}}else{return new F(function(){return _zn((_zm-97|0)+10|0);});}}}else{if(_zm>57){if(97>_zm){if(65>_zm){var _zL=new T(function(){return B(A1(_zi,_v));});return function(_zM){return new F(function(){return A1(_zM,_zL);});};}else{if(_zm>70){var _zN=new T(function(){return B(A1(_zi,_v));});return function(_zO){return new F(function(){return A1(_zO,_zN);});};}else{return new F(function(){return _zn((_zm-65|0)+10|0);});}}}else{if(_zm>102){if(65>_zm){var _zP=new T(function(){return B(A1(_zi,_v));});return function(_zQ){return new F(function(){return A1(_zQ,_zP);});};}else{if(_zm>70){var _zR=new T(function(){return B(A1(_zi,_v));});return function(_zS){return new F(function(){return A1(_zS,_zR);});};}else{return new F(function(){return _zn((_zm-65|0)+10|0);});}}}else{return new F(function(){return _zn((_zm-97|0)+10|0);});}}}else{return new F(function(){return _zn(_zm-48|0);});}}break;default:return E(_zc);}}},_zT=function(_zU){var _zV=E(_zU);if(!_zV._){return new T0(2);}else{return new F(function(){return A1(_zf,_zV);});}};return function(_zW){return new F(function(){return A3(_zg,_zW,_5x,_zT);});};},_zX=16,_zY=8,_zZ=function(_A0){var _A1=function(_A2){return new F(function(){return A1(_A0,new T1(5,new T2(0,_zY,_A2)));});},_A3=function(_A4){return new F(function(){return A1(_A0,new T1(5,new T2(0,_zX,_A4)));});},_A5=function(_A6){switch(E(_A6)){case 79:return new T1(1,B(_zd(_zY,_A1)));case 88:return new T1(1,B(_zd(_zX,_A3)));case 111:return new T1(1,B(_zd(_zY,_A1)));case 120:return new T1(1,B(_zd(_zX,_A3)));default:return new T0(2);}};return function(_A7){return (E(_A7)==48)?E(new T1(0,_A5)):new T0(2);};},_A8=function(_A9){return new T1(0,B(_zZ(_A9)));},_Aa=function(_Ab){return new F(function(){return A1(_Ab,_2q);});},_Ac=function(_Ad){return new F(function(){return A1(_Ad,_2q);});},_Ae=10,_Af=new T1(0,10),_Ag=function(_Ah){return new F(function(){return _tt(E(_Ah));});},_Ai=new T(function(){return B(unCStr("this should not happen"));}),_Aj=new T(function(){return B(err(_Ai));}),_Ak=function(_Al,_Am){var _An=E(_Am);if(!_An._){return __Z;}else{var _Ao=E(_An.b);return (_Ao._==0)?E(_Aj):new T2(1,B(_r9(B(_v4(_An.a,_Al)),_Ao.a)),new T(function(){return B(_Ak(_Al,_Ao.b));}));}},_Ap=new T1(0,0),_Aq=function(_Ar,_As,_At){while(1){var _Au=B((function(_Av,_Aw,_Ax){var _Ay=E(_Ax);if(!_Ay._){return E(_Ap);}else{if(!E(_Ay.b)._){return E(_Ay.a);}else{var _Az=E(_Aw);if(_Az<=40){var _AA=function(_AB,_AC){while(1){var _AD=E(_AC);if(!_AD._){return E(_AB);}else{var _AE=B(_r9(B(_v4(_AB,_Av)),_AD.a));_AB=_AE;_AC=_AD.b;continue;}}};return new F(function(){return _AA(_Ap,_Ay);});}else{var _AF=B(_v4(_Av,_Av));if(!(_Az%2)){var _AG=B(_Ak(_Av,_Ay));_Ar=_AF;_As=quot(_Az+1|0,2);_At=_AG;return __continue;}else{var _AG=B(_Ak(_Av,new T2(1,_Ap,_Ay)));_Ar=_AF;_As=quot(_Az+1|0,2);_At=_AG;return __continue;}}}}})(_Ar,_As,_At));if(_Au!=__continue){return _Au;}}},_AH=function(_AI,_AJ){return new F(function(){return _Aq(_AI,new T(function(){return B(_a2(_AJ,0));},1),B(_dm(_Ag,_AJ)));});},_AK=function(_AL){var _AM=new T(function(){var _AN=new T(function(){var _AO=function(_AP){return new F(function(){return A1(_AL,new T1(1,new T(function(){return B(_AH(_Af,_AP));})));});};return new T1(1,B(_zd(_Ae,_AO)));}),_AQ=function(_AR){if(E(_AR)==43){var _AS=function(_AT){return new F(function(){return A1(_AL,new T1(1,new T(function(){return B(_AH(_Af,_AT));})));});};return new T1(1,B(_zd(_Ae,_AS)));}else{return new T0(2);}},_AU=function(_AV){if(E(_AV)==45){var _AW=function(_AX){return new F(function(){return A1(_AL,new T1(1,new T(function(){return B(_rj(B(_AH(_Af,_AX))));})));});};return new T1(1,B(_zd(_Ae,_AW)));}else{return new T0(2);}};return B(_xu(B(_xu(new T1(0,_AU),new T1(0,_AQ))),_AN));});return new F(function(){return _xu(new T1(0,function(_AY){return (E(_AY)==101)?E(_AM):new T0(2);}),new T1(0,function(_AZ){return (E(_AZ)==69)?E(_AM):new T0(2);}));});},_B0=function(_B1){var _B2=function(_B3){return new F(function(){return A1(_B1,new T1(1,_B3));});};return function(_B4){return (E(_B4)==46)?new T1(1,B(_zd(_Ae,_B2))):new T0(2);};},_B5=function(_B6){return new T1(0,B(_B0(_B6)));},_B7=function(_B8){var _B9=function(_Ba){var _Bb=function(_Bc){return new T1(1,B(_yw(_AK,_Aa,function(_Bd){return new F(function(){return A1(_B8,new T1(5,new T3(1,_Ba,_Bc,_Bd)));});})));};return new T1(1,B(_yw(_B5,_Ac,_Bb)));};return new F(function(){return _zd(_Ae,_B9);});},_Be=function(_Bf){return new T1(1,B(_B7(_Bf)));},_Bg=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_Bh=function(_Bi){return new F(function(){return _4d(_fb,_Bi,_Bg);});},_Bj=function(_Bk){var _Bl=new T(function(){return B(A1(_Bk,_zY));}),_Bm=new T(function(){return B(A1(_Bk,_zX));});return function(_Bn){switch(E(_Bn)){case 79:return E(_Bl);case 88:return E(_Bm);case 111:return E(_Bl);case 120:return E(_Bm);default:return new T0(2);}};},_Bo=function(_Bp){return new T1(0,B(_Bj(_Bp)));},_Bq=function(_Br){return new F(function(){return A1(_Br,_Ae);});},_Bs=function(_Bt){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_d(9,_Bt,_v));}))));});},_Bu=function(_Bv){return new T0(2);},_Bw=function(_Bx){var _By=E(_Bx);if(!_By._){return E(_Bu);}else{var _Bz=_By.a,_BA=E(_By.b);if(!_BA._){return E(_Bz);}else{var _BB=new T(function(){return B(_Bw(_BA));}),_BC=function(_BD){return new F(function(){return _xu(B(A1(_Bz,_BD)),new T(function(){return B(A1(_BB,_BD));}));});};return E(_BC);}}},_BE=function(_BF,_BG){var _BH=function(_BI,_BJ,_BK){var _BL=E(_BI);if(!_BL._){return new F(function(){return A1(_BK,_BF);});}else{var _BM=E(_BJ);if(!_BM._){return new T0(2);}else{if(E(_BL.a)!=E(_BM.a)){return new T0(2);}else{var _BN=new T(function(){return B(_BH(_BL.b,_BM.b,_BK));});return new T1(0,function(_BO){return E(_BN);});}}}};return function(_BP){return new F(function(){return _BH(_BF,_BP,_BG);});};},_BQ=new T(function(){return B(unCStr("SO"));}),_BR=14,_BS=function(_BT){var _BU=new T(function(){return B(A1(_BT,_BR));});return new T1(1,B(_BE(_BQ,function(_BV){return E(_BU);})));},_BW=new T(function(){return B(unCStr("SOH"));}),_BX=1,_BY=function(_BZ){var _C0=new T(function(){return B(A1(_BZ,_BX));});return new T1(1,B(_BE(_BW,function(_C1){return E(_C0);})));},_C2=function(_C3){return new T1(1,B(_yw(_BY,_BS,_C3)));},_C4=new T(function(){return B(unCStr("NUL"));}),_C5=0,_C6=function(_C7){var _C8=new T(function(){return B(A1(_C7,_C5));});return new T1(1,B(_BE(_C4,function(_C9){return E(_C8);})));},_Ca=new T(function(){return B(unCStr("STX"));}),_Cb=2,_Cc=function(_Cd){var _Ce=new T(function(){return B(A1(_Cd,_Cb));});return new T1(1,B(_BE(_Ca,function(_Cf){return E(_Ce);})));},_Cg=new T(function(){return B(unCStr("ETX"));}),_Ch=3,_Ci=function(_Cj){var _Ck=new T(function(){return B(A1(_Cj,_Ch));});return new T1(1,B(_BE(_Cg,function(_Cl){return E(_Ck);})));},_Cm=new T(function(){return B(unCStr("EOT"));}),_Cn=4,_Co=function(_Cp){var _Cq=new T(function(){return B(A1(_Cp,_Cn));});return new T1(1,B(_BE(_Cm,function(_Cr){return E(_Cq);})));},_Cs=new T(function(){return B(unCStr("ENQ"));}),_Ct=5,_Cu=function(_Cv){var _Cw=new T(function(){return B(A1(_Cv,_Ct));});return new T1(1,B(_BE(_Cs,function(_Cx){return E(_Cw);})));},_Cy=new T(function(){return B(unCStr("ACK"));}),_Cz=6,_CA=function(_CB){var _CC=new T(function(){return B(A1(_CB,_Cz));});return new T1(1,B(_BE(_Cy,function(_CD){return E(_CC);})));},_CE=new T(function(){return B(unCStr("BEL"));}),_CF=7,_CG=function(_CH){var _CI=new T(function(){return B(A1(_CH,_CF));});return new T1(1,B(_BE(_CE,function(_CJ){return E(_CI);})));},_CK=new T(function(){return B(unCStr("BS"));}),_CL=8,_CM=function(_CN){var _CO=new T(function(){return B(A1(_CN,_CL));});return new T1(1,B(_BE(_CK,function(_CP){return E(_CO);})));},_CQ=new T(function(){return B(unCStr("HT"));}),_CR=9,_CS=function(_CT){var _CU=new T(function(){return B(A1(_CT,_CR));});return new T1(1,B(_BE(_CQ,function(_CV){return E(_CU);})));},_CW=new T(function(){return B(unCStr("LF"));}),_CX=10,_CY=function(_CZ){var _D0=new T(function(){return B(A1(_CZ,_CX));});return new T1(1,B(_BE(_CW,function(_D1){return E(_D0);})));},_D2=new T(function(){return B(unCStr("VT"));}),_D3=11,_D4=function(_D5){var _D6=new T(function(){return B(A1(_D5,_D3));});return new T1(1,B(_BE(_D2,function(_D7){return E(_D6);})));},_D8=new T(function(){return B(unCStr("FF"));}),_D9=12,_Da=function(_Db){var _Dc=new T(function(){return B(A1(_Db,_D9));});return new T1(1,B(_BE(_D8,function(_Dd){return E(_Dc);})));},_De=new T(function(){return B(unCStr("CR"));}),_Df=13,_Dg=function(_Dh){var _Di=new T(function(){return B(A1(_Dh,_Df));});return new T1(1,B(_BE(_De,function(_Dj){return E(_Di);})));},_Dk=new T(function(){return B(unCStr("SI"));}),_Dl=15,_Dm=function(_Dn){var _Do=new T(function(){return B(A1(_Dn,_Dl));});return new T1(1,B(_BE(_Dk,function(_Dp){return E(_Do);})));},_Dq=new T(function(){return B(unCStr("DLE"));}),_Dr=16,_Ds=function(_Dt){var _Du=new T(function(){return B(A1(_Dt,_Dr));});return new T1(1,B(_BE(_Dq,function(_Dv){return E(_Du);})));},_Dw=new T(function(){return B(unCStr("DC1"));}),_Dx=17,_Dy=function(_Dz){var _DA=new T(function(){return B(A1(_Dz,_Dx));});return new T1(1,B(_BE(_Dw,function(_DB){return E(_DA);})));},_DC=new T(function(){return B(unCStr("DC2"));}),_DD=18,_DE=function(_DF){var _DG=new T(function(){return B(A1(_DF,_DD));});return new T1(1,B(_BE(_DC,function(_DH){return E(_DG);})));},_DI=new T(function(){return B(unCStr("DC3"));}),_DJ=19,_DK=function(_DL){var _DM=new T(function(){return B(A1(_DL,_DJ));});return new T1(1,B(_BE(_DI,function(_DN){return E(_DM);})));},_DO=new T(function(){return B(unCStr("DC4"));}),_DP=20,_DQ=function(_DR){var _DS=new T(function(){return B(A1(_DR,_DP));});return new T1(1,B(_BE(_DO,function(_DT){return E(_DS);})));},_DU=new T(function(){return B(unCStr("NAK"));}),_DV=21,_DW=function(_DX){var _DY=new T(function(){return B(A1(_DX,_DV));});return new T1(1,B(_BE(_DU,function(_DZ){return E(_DY);})));},_E0=new T(function(){return B(unCStr("SYN"));}),_E1=22,_E2=function(_E3){var _E4=new T(function(){return B(A1(_E3,_E1));});return new T1(1,B(_BE(_E0,function(_E5){return E(_E4);})));},_E6=new T(function(){return B(unCStr("ETB"));}),_E7=23,_E8=function(_E9){var _Ea=new T(function(){return B(A1(_E9,_E7));});return new T1(1,B(_BE(_E6,function(_Eb){return E(_Ea);})));},_Ec=new T(function(){return B(unCStr("CAN"));}),_Ed=24,_Ee=function(_Ef){var _Eg=new T(function(){return B(A1(_Ef,_Ed));});return new T1(1,B(_BE(_Ec,function(_Eh){return E(_Eg);})));},_Ei=new T(function(){return B(unCStr("EM"));}),_Ej=25,_Ek=function(_El){var _Em=new T(function(){return B(A1(_El,_Ej));});return new T1(1,B(_BE(_Ei,function(_En){return E(_Em);})));},_Eo=new T(function(){return B(unCStr("SUB"));}),_Ep=26,_Eq=function(_Er){var _Es=new T(function(){return B(A1(_Er,_Ep));});return new T1(1,B(_BE(_Eo,function(_Et){return E(_Es);})));},_Eu=new T(function(){return B(unCStr("ESC"));}),_Ev=27,_Ew=function(_Ex){var _Ey=new T(function(){return B(A1(_Ex,_Ev));});return new T1(1,B(_BE(_Eu,function(_Ez){return E(_Ey);})));},_EA=new T(function(){return B(unCStr("FS"));}),_EB=28,_EC=function(_ED){var _EE=new T(function(){return B(A1(_ED,_EB));});return new T1(1,B(_BE(_EA,function(_EF){return E(_EE);})));},_EG=new T(function(){return B(unCStr("GS"));}),_EH=29,_EI=function(_EJ){var _EK=new T(function(){return B(A1(_EJ,_EH));});return new T1(1,B(_BE(_EG,function(_EL){return E(_EK);})));},_EM=new T(function(){return B(unCStr("RS"));}),_EN=30,_EO=function(_EP){var _EQ=new T(function(){return B(A1(_EP,_EN));});return new T1(1,B(_BE(_EM,function(_ER){return E(_EQ);})));},_ES=new T(function(){return B(unCStr("US"));}),_ET=31,_EU=function(_EV){var _EW=new T(function(){return B(A1(_EV,_ET));});return new T1(1,B(_BE(_ES,function(_EX){return E(_EW);})));},_EY=new T(function(){return B(unCStr("SP"));}),_EZ=32,_F0=function(_F1){var _F2=new T(function(){return B(A1(_F1,_EZ));});return new T1(1,B(_BE(_EY,function(_F3){return E(_F2);})));},_F4=new T(function(){return B(unCStr("DEL"));}),_F5=127,_F6=function(_F7){var _F8=new T(function(){return B(A1(_F7,_F5));});return new T1(1,B(_BE(_F4,function(_F9){return E(_F8);})));},_Fa=new T2(1,_F6,_v),_Fb=new T2(1,_F0,_Fa),_Fc=new T2(1,_EU,_Fb),_Fd=new T2(1,_EO,_Fc),_Fe=new T2(1,_EI,_Fd),_Ff=new T2(1,_EC,_Fe),_Fg=new T2(1,_Ew,_Ff),_Fh=new T2(1,_Eq,_Fg),_Fi=new T2(1,_Ek,_Fh),_Fj=new T2(1,_Ee,_Fi),_Fk=new T2(1,_E8,_Fj),_Fl=new T2(1,_E2,_Fk),_Fm=new T2(1,_DW,_Fl),_Fn=new T2(1,_DQ,_Fm),_Fo=new T2(1,_DK,_Fn),_Fp=new T2(1,_DE,_Fo),_Fq=new T2(1,_Dy,_Fp),_Fr=new T2(1,_Ds,_Fq),_Fs=new T2(1,_Dm,_Fr),_Ft=new T2(1,_Dg,_Fs),_Fu=new T2(1,_Da,_Ft),_Fv=new T2(1,_D4,_Fu),_Fw=new T2(1,_CY,_Fv),_Fx=new T2(1,_CS,_Fw),_Fy=new T2(1,_CM,_Fx),_Fz=new T2(1,_CG,_Fy),_FA=new T2(1,_CA,_Fz),_FB=new T2(1,_Cu,_FA),_FC=new T2(1,_Co,_FB),_FD=new T2(1,_Ci,_FC),_FE=new T2(1,_Cc,_FD),_FF=new T2(1,_C6,_FE),_FG=new T2(1,_C2,_FF),_FH=new T(function(){return B(_Bw(_FG));}),_FI=34,_FJ=new T1(0,1114111),_FK=92,_FL=39,_FM=function(_FN){var _FO=new T(function(){return B(A1(_FN,_CF));}),_FP=new T(function(){return B(A1(_FN,_CL));}),_FQ=new T(function(){return B(A1(_FN,_CR));}),_FR=new T(function(){return B(A1(_FN,_CX));}),_FS=new T(function(){return B(A1(_FN,_D3));}),_FT=new T(function(){return B(A1(_FN,_D9));}),_FU=new T(function(){return B(A1(_FN,_Df));}),_FV=new T(function(){return B(A1(_FN,_FK));}),_FW=new T(function(){return B(A1(_FN,_FL));}),_FX=new T(function(){return B(A1(_FN,_FI));}),_FY=new T(function(){var _FZ=function(_G0){var _G1=new T(function(){return B(_tt(E(_G0)));}),_G2=function(_G3){var _G4=B(_AH(_G1,_G3));if(!B(_vm(_G4,_FJ))){return new T0(2);}else{return new F(function(){return A1(_FN,new T(function(){var _G5=B(_tk(_G4));if(_G5>>>0>1114111){return B(_Bs(_G5));}else{return _G5;}}));});}};return new T1(1,B(_zd(_G0,_G2)));},_G6=new T(function(){var _G7=new T(function(){return B(A1(_FN,_ET));}),_G8=new T(function(){return B(A1(_FN,_EN));}),_G9=new T(function(){return B(A1(_FN,_EH));}),_Ga=new T(function(){return B(A1(_FN,_EB));}),_Gb=new T(function(){return B(A1(_FN,_Ev));}),_Gc=new T(function(){return B(A1(_FN,_Ep));}),_Gd=new T(function(){return B(A1(_FN,_Ej));}),_Ge=new T(function(){return B(A1(_FN,_Ed));}),_Gf=new T(function(){return B(A1(_FN,_E7));}),_Gg=new T(function(){return B(A1(_FN,_E1));}),_Gh=new T(function(){return B(A1(_FN,_DV));}),_Gi=new T(function(){return B(A1(_FN,_DP));}),_Gj=new T(function(){return B(A1(_FN,_DJ));}),_Gk=new T(function(){return B(A1(_FN,_DD));}),_Gl=new T(function(){return B(A1(_FN,_Dx));}),_Gm=new T(function(){return B(A1(_FN,_Dr));}),_Gn=new T(function(){return B(A1(_FN,_Dl));}),_Go=new T(function(){return B(A1(_FN,_BR));}),_Gp=new T(function(){return B(A1(_FN,_Cz));}),_Gq=new T(function(){return B(A1(_FN,_Ct));}),_Gr=new T(function(){return B(A1(_FN,_Cn));}),_Gs=new T(function(){return B(A1(_FN,_Ch));}),_Gt=new T(function(){return B(A1(_FN,_Cb));}),_Gu=new T(function(){return B(A1(_FN,_BX));}),_Gv=new T(function(){return B(A1(_FN,_C5));}),_Gw=function(_Gx){switch(E(_Gx)){case 64:return E(_Gv);case 65:return E(_Gu);case 66:return E(_Gt);case 67:return E(_Gs);case 68:return E(_Gr);case 69:return E(_Gq);case 70:return E(_Gp);case 71:return E(_FO);case 72:return E(_FP);case 73:return E(_FQ);case 74:return E(_FR);case 75:return E(_FS);case 76:return E(_FT);case 77:return E(_FU);case 78:return E(_Go);case 79:return E(_Gn);case 80:return E(_Gm);case 81:return E(_Gl);case 82:return E(_Gk);case 83:return E(_Gj);case 84:return E(_Gi);case 85:return E(_Gh);case 86:return E(_Gg);case 87:return E(_Gf);case 88:return E(_Ge);case 89:return E(_Gd);case 90:return E(_Gc);case 91:return E(_Gb);case 92:return E(_Ga);case 93:return E(_G9);case 94:return E(_G8);case 95:return E(_G7);default:return new T0(2);}};return B(_xu(new T1(0,function(_Gy){return (E(_Gy)==94)?E(new T1(0,_Gw)):new T0(2);}),new T(function(){return B(A1(_FH,_FN));})));});return B(_xu(new T1(1,B(_yw(_Bo,_Bq,_FZ))),_G6));});return new F(function(){return _xu(new T1(0,function(_Gz){switch(E(_Gz)){case 34:return E(_FX);case 39:return E(_FW);case 92:return E(_FV);case 97:return E(_FO);case 98:return E(_FP);case 102:return E(_FT);case 110:return E(_FR);case 114:return E(_FU);case 116:return E(_FQ);case 118:return E(_FS);default:return new T0(2);}}),_FY);});},_GA=function(_GB){return new F(function(){return A1(_GB,_5L);});},_GC=function(_GD){var _GE=E(_GD);if(!_GE._){return E(_GA);}else{var _GF=E(_GE.a),_GG=_GF>>>0,_GH=new T(function(){return B(_GC(_GE.b));});if(_GG>887){var _GI=u_iswspace(_GF);if(!E(_GI)){return E(_GA);}else{var _GJ=function(_GK){var _GL=new T(function(){return B(A1(_GH,_GK));});return new T1(0,function(_GM){return E(_GL);});};return E(_GJ);}}else{var _GN=E(_GG);if(_GN==32){var _GO=function(_GP){var _GQ=new T(function(){return B(A1(_GH,_GP));});return new T1(0,function(_GR){return E(_GQ);});};return E(_GO);}else{if(_GN-9>>>0>4){if(E(_GN)==160){var _GS=function(_GT){var _GU=new T(function(){return B(A1(_GH,_GT));});return new T1(0,function(_GV){return E(_GU);});};return E(_GS);}else{return E(_GA);}}else{var _GW=function(_GX){var _GY=new T(function(){return B(A1(_GH,_GX));});return new T1(0,function(_GZ){return E(_GY);});};return E(_GW);}}}}},_H0=function(_H1){var _H2=new T(function(){return B(_H0(_H1));}),_H3=function(_H4){return (E(_H4)==92)?E(_H2):new T0(2);},_H5=function(_H6){return E(new T1(0,_H3));},_H7=new T1(1,function(_H8){return new F(function(){return A2(_GC,_H8,_H5);});}),_H9=new T(function(){return B(_FM(function(_Ha){return new F(function(){return A1(_H1,new T2(0,_Ha,_5Q));});}));}),_Hb=function(_Hc){var _Hd=E(_Hc);if(_Hd==38){return E(_H2);}else{var _He=_Hd>>>0;if(_He>887){var _Hf=u_iswspace(_Hd);return (E(_Hf)==0)?new T0(2):E(_H7);}else{var _Hg=E(_He);return (_Hg==32)?E(_H7):(_Hg-9>>>0>4)?(E(_Hg)==160)?E(_H7):new T0(2):E(_H7);}}};return new F(function(){return _xu(new T1(0,function(_Hh){return (E(_Hh)==92)?E(new T1(0,_Hb)):new T0(2);}),new T1(0,function(_Hi){var _Hj=E(_Hi);if(E(_Hj)==92){return E(_H9);}else{return new F(function(){return A1(_H1,new T2(0,_Hj,_5N));});}}));});},_Hk=function(_Hl,_Hm){var _Hn=new T(function(){return B(A1(_Hm,new T1(1,new T(function(){return B(A1(_Hl,_v));}))));}),_Ho=function(_Hp){var _Hq=E(_Hp),_Hr=E(_Hq.a);if(E(_Hr)==34){if(!E(_Hq.b)){return E(_Hn);}else{return new F(function(){return _Hk(function(_Hs){return new F(function(){return A1(_Hl,new T2(1,_Hr,_Hs));});},_Hm);});}}else{return new F(function(){return _Hk(function(_Ht){return new F(function(){return A1(_Hl,new T2(1,_Hr,_Ht));});},_Hm);});}};return new F(function(){return _H0(_Ho);});},_Hu=new T(function(){return B(unCStr("_\'"));}),_Hv=function(_Hw){var _Hx=u_iswalnum(_Hw);if(!E(_Hx)){return new F(function(){return _4d(_fb,_Hw,_Hu);});}else{return true;}},_Hy=function(_Hz){return new F(function(){return _Hv(E(_Hz));});},_HA=new T(function(){return B(unCStr(",;()[]{}`"));}),_HB=new T(function(){return B(unCStr("=>"));}),_HC=new T2(1,_HB,_v),_HD=new T(function(){return B(unCStr("~"));}),_HE=new T2(1,_HD,_HC),_HF=new T(function(){return B(unCStr("@"));}),_HG=new T2(1,_HF,_HE),_HH=new T(function(){return B(unCStr("->"));}),_HI=new T2(1,_HH,_HG),_HJ=new T(function(){return B(unCStr("<-"));}),_HK=new T2(1,_HJ,_HI),_HL=new T(function(){return B(unCStr("|"));}),_HM=new T2(1,_HL,_HK),_HN=new T(function(){return B(unCStr("\\"));}),_HO=new T2(1,_HN,_HM),_HP=new T(function(){return B(unCStr("="));}),_HQ=new T2(1,_HP,_HO),_HR=new T(function(){return B(unCStr("::"));}),_HS=new T2(1,_HR,_HQ),_HT=new T(function(){return B(unCStr(".."));}),_HU=new T2(1,_HT,_HS),_HV=function(_HW){var _HX=new T(function(){return B(A1(_HW,_za));}),_HY=new T(function(){var _HZ=new T(function(){var _I0=function(_I1){var _I2=new T(function(){return B(A1(_HW,new T1(0,_I1)));});return new T1(0,function(_I3){return (E(_I3)==39)?E(_I2):new T0(2);});};return B(_FM(_I0));}),_I4=function(_I5){var _I6=E(_I5);switch(E(_I6)){case 39:return new T0(2);case 92:return E(_HZ);default:var _I7=new T(function(){return B(A1(_HW,new T1(0,_I6)));});return new T1(0,function(_I8){return (E(_I8)==39)?E(_I7):new T0(2);});}},_I9=new T(function(){var _Ia=new T(function(){return B(_Hk(_5x,_HW));}),_Ib=new T(function(){var _Ic=new T(function(){var _Id=new T(function(){var _Ie=function(_If){var _Ig=E(_If),_Ih=u_iswalpha(_Ig);return (E(_Ih)==0)?(E(_Ig)==95)?new T1(1,B(_yW(_Hy,function(_Ii){return new F(function(){return A1(_HW,new T1(3,new T2(1,_Ig,_Ii)));});}))):new T0(2):new T1(1,B(_yW(_Hy,function(_Ij){return new F(function(){return A1(_HW,new T1(3,new T2(1,_Ig,_Ij)));});})));};return B(_xu(new T1(0,_Ie),new T(function(){return new T1(1,B(_yw(_A8,_Be,_HW)));})));}),_Ik=function(_Il){return (!B(_4d(_fb,_Il,_Bg)))?new T0(2):new T1(1,B(_yW(_Bh,function(_Im){var _In=new T2(1,_Il,_Im);if(!B(_4d(_yb,_In,_HU))){return new F(function(){return A1(_HW,new T1(4,_In));});}else{return new F(function(){return A1(_HW,new T1(2,_In));});}})));};return B(_xu(new T1(0,_Ik),_Id));});return B(_xu(new T1(0,function(_Io){if(!B(_4d(_fb,_Io,_HA))){return new T0(2);}else{return new F(function(){return A1(_HW,new T1(2,new T2(1,_Io,_v)));});}}),_Ic));});return B(_xu(new T1(0,function(_Ip){return (E(_Ip)==34)?E(_Ia):new T0(2);}),_Ib));});return B(_xu(new T1(0,function(_Iq){return (E(_Iq)==39)?E(new T1(0,_I4)):new T0(2);}),_I9));});return new F(function(){return _xu(new T1(1,function(_Ir){return (E(_Ir)._==0)?E(_HX):new T0(2);}),_HY);});},_Is=0,_It=function(_Iu,_Iv){var _Iw=new T(function(){var _Ix=new T(function(){var _Iy=function(_Iz){var _IA=new T(function(){var _IB=new T(function(){return B(A1(_Iv,_Iz));});return B(_HV(function(_IC){var _ID=E(_IC);return (_ID._==2)?(!B(_98(_ID.a,_y7)))?new T0(2):E(_IB):new T0(2);}));}),_IE=function(_IF){return E(_IA);};return new T1(1,function(_IG){return new F(function(){return A2(_GC,_IG,_IE);});});};return B(A2(_Iu,_Is,_Iy));});return B(_HV(function(_IH){var _II=E(_IH);return (_II._==2)?(!B(_98(_II.a,_y6)))?new T0(2):E(_Ix):new T0(2);}));}),_IJ=function(_IK){return E(_Iw);};return function(_IL){return new F(function(){return A2(_GC,_IL,_IJ);});};},_IM=function(_IN,_IO){var _IP=function(_IQ){var _IR=new T(function(){return B(A1(_IN,_IQ));}),_IS=function(_IT){return new F(function(){return _xu(B(A1(_IR,_IT)),new T(function(){return new T1(1,B(_It(_IP,_IT)));}));});};return E(_IS);},_IU=new T(function(){return B(A1(_IN,_IO));}),_IV=function(_IW){return new F(function(){return _xu(B(A1(_IU,_IW)),new T(function(){return new T1(1,B(_It(_IP,_IW)));}));});};return E(_IV);},_IX=function(_IY,_IZ){var _J0=function(_J1,_J2){var _J3=function(_J4){return new F(function(){return A1(_J2,new T(function(){return  -E(_J4);}));});},_J5=new T(function(){return B(_HV(function(_J6){return new F(function(){return A3(_IY,_J6,_J1,_J3);});}));}),_J7=function(_J8){return E(_J5);},_J9=function(_Ja){return new F(function(){return A2(_GC,_Ja,_J7);});},_Jb=new T(function(){return B(_HV(function(_Jc){var _Jd=E(_Jc);if(_Jd._==4){var _Je=E(_Jd.a);if(!_Je._){return new F(function(){return A3(_IY,_Jd,_J1,_J2);});}else{if(E(_Je.a)==45){if(!E(_Je.b)._){return E(new T1(1,_J9));}else{return new F(function(){return A3(_IY,_Jd,_J1,_J2);});}}else{return new F(function(){return A3(_IY,_Jd,_J1,_J2);});}}}else{return new F(function(){return A3(_IY,_Jd,_J1,_J2);});}}));}),_Jf=function(_Jg){return E(_Jb);};return new T1(1,function(_Jh){return new F(function(){return A2(_GC,_Jh,_Jf);});});};return new F(function(){return _IM(_J0,_IZ);});},_Ji=function(_Jj){var _Jk=E(_Jj);if(!_Jk._){var _Jl=_Jk.b,_Jm=new T(function(){return B(_Aq(new T(function(){return B(_tt(E(_Jk.a)));}),new T(function(){return B(_a2(_Jl,0));},1),B(_dm(_Ag,_Jl))));});return new T1(1,_Jm);}else{return (E(_Jk.b)._==0)?(E(_Jk.c)._==0)?new T1(1,new T(function(){return B(_AH(_Af,_Jk.a));})):__Z:__Z;}},_Jn=function(_Jo,_Jp){return new T0(2);},_Jq=function(_Jr){var _Js=E(_Jr);if(_Js._==5){var _Jt=B(_Ji(_Js.a));if(!_Jt._){return E(_Jn);}else{var _Ju=new T(function(){return B(_tk(_Jt.a));});return function(_Jv,_Jw){return new F(function(){return A1(_Jw,_Ju);});};}}else{return E(_Jn);}},_Jx=function(_Jy){var _Jz=function(_JA){return E(new T2(3,_Jy,_yn));};return new T1(1,function(_JB){return new F(function(){return A2(_GC,_JB,_Jz);});});},_JC=new T(function(){return B(A3(_IX,_Jq,_Is,_Jx));}),_JD=function(_JE){while(1){var _JF=B((function(_JG){var _JH=E(_JG);if(!_JH._){return __Z;}else{var _JI=_JH.b,_JJ=E(_JH.a);if(!E(_JJ.b)._){return new T2(1,_JJ.a,new T(function(){return B(_JD(_JI));}));}else{_JE=_JI;return __continue;}}})(_JE));if(_JF!=__continue){return _JF;}}},_JK=function(_JL,_JM,_JN){var _JO=E(_JN);if(!_JO._){return new T2(0,new T2(1,_JM,_v),_v);}else{var _JP=E(_JM),_JQ=new T(function(){var _JR=B(_JK(_JL,_JO.a,_JO.b));return new T2(0,_JR.a,_JR.b);});return (_JL!=_JP)?new T2(0,new T2(1,_JP,new T(function(){return E(E(_JQ).a);})),new T(function(){return E(E(_JQ).b);})):new T2(0,_v,new T2(1,new T(function(){return E(E(_JQ).a);}),new T(function(){return E(E(_JQ).b);})));}},_JS=new T1(0,1),_JT=new T1(0,10),_JU=function(_JV){while(1){var _JW=E(_JV);if(!_JW._){_JV=new T1(1,I_fromInt(_JW.a));continue;}else{return new F(function(){return I_toString(_JW.a);});}}},_JX=function(_JY,_JZ){return new F(function(){return _3(fromJSStr(B(_JU(_JY))),_JZ);});},_K0=new T1(0,0),_K1=function(_K2,_K3,_K4){if(_K2<=6){return new F(function(){return _JX(_K3,_K4);});}else{if(!B(_sX(_K3,_K0))){return new F(function(){return _JX(_K3,_K4);});}else{return new T2(1,_c,new T(function(){return B(_3(fromJSStr(B(_JU(_K3))),new T2(1,_b,_K4)));}));}}},_K5=function(_K6,_K7,_K8){while(1){if(!(_K7%2)){var _K9=B(_v4(_K6,_K6)),_Ka=quot(_K7,2);_K6=_K9;_K7=_Ka;continue;}else{var _Kb=E(_K7);if(_Kb==1){return new F(function(){return _v4(_K6,_K8);});}else{var _K9=B(_v4(_K6,_K6)),_Kc=B(_v4(_K6,_K8));_K6=_K9;_K7=quot(_Kb-1|0,2);_K8=_Kc;continue;}}}},_Kd=function(_Ke,_Kf){while(1){if(!(_Kf%2)){var _Kg=B(_v4(_Ke,_Ke)),_Kh=quot(_Kf,2);_Ke=_Kg;_Kf=_Kh;continue;}else{var _Ki=E(_Kf);if(_Ki==1){return E(_Ke);}else{return new F(function(){return _K5(B(_v4(_Ke,_Ke)),quot(_Ki-1|0,2),_Ke);});}}}},_Kj=new T(function(){return B(unCStr("Negative exponent"));}),_Kk=new T(function(){return B(err(_Kj));}),_Kl=function(_Km){return new F(function(){return _K1(0,_Km,_v);});},_Kn=new T(function(){return B(_tG(_JT,_vR));}),_Ko=function(_Kp){while(1){if(!B(_tG(_Kp,_vR))){if(!E(_Kn)){if(!B(_tG(B(_u5(_Kp,_JT)),_vR))){return new F(function(){return _Kl(_Kp);});}else{var _Kq=B(_ty(_Kp,_JT));_Kp=_Kq;continue;}}else{return E(_s5);}}else{return __Z;}}},_Kr=function(_Ks){var _Kt=E(_Ks);if(!_Kt._){return _Kt.a;}else{return new F(function(){return I_toNumber(_Kt.a);});}},_Ku=46,_Kv=48,_Kw=function(_Kx,_Ky,_Kz){if(!B(_sX(_Kz,_vR))){var _KA=B(A1(_Kx,_Kz));if(!B(_tG(_KA,_vR))){var _KB=B(_tS(_Kz,_KA)),_KC=_KB.b,_KD=new T(function(){var _KE=Math.log(B(_Kr(_KA)))/Math.log(10),_KF=_KE&4294967295,_KG=function(_KH){if(_KH>=0){var _KI=E(_KH);if(!_KI){var _KJ=B(_ty(B(_st(B(_r9(B(_v4(_KC,_sj)),_KA)),_JS)),_KA));}else{var _KJ=B(_ty(B(_st(B(_r9(B(_v4(_KC,B(_Kd(_JT,_KI)))),_KA)),_JS)),_KA));}var _KK=function(_KL){var _KM=B(_K1(0,_KJ,_v)),_KN=_KH-B(_a2(_KM,0))|0;if(0>=_KN){if(!E(_Ky)){return E(_KM);}else{return new F(function(){return _Ko(_KJ);});}}else{var _KO=new T(function(){if(!E(_Ky)){return E(_KM);}else{return B(_Ko(_KJ));}}),_KP=function(_KQ){var _KR=E(_KQ);return (_KR==1)?E(new T2(1,_Kv,_KO)):new T2(1,_Kv,new T(function(){return B(_KP(_KR-1|0));}));};return new F(function(){return _KP(_KN);});}};if(!E(_Ky)){var _KS=B(_KK(_));return (_KS._==0)?__Z:new T2(1,_Ku,_KS);}else{if(!B(_tG(_KJ,_vR))){var _KT=B(_KK(_));return (_KT._==0)?__Z:new T2(1,_Ku,_KT);}else{return __Z;}}}else{return E(_Kk);}};if(_KF>=_KE){return B(_KG(_KF));}else{return B(_KG(_KF+1|0));}},1);return new F(function(){return _3(B(_K1(0,_KB.a,_v)),_KD);});}else{return E(_s5);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_Kw(_Kx,_Ky,B(_rj(_Kz))));}));});}},_KU=function(_KV,_KW,_){var _KX=B(_x8(_)),_KY=new T(function(){var _KZ=new T(function(){var _L0=new T(function(){var _L1=B(_3(B(_Kw(_rv,_5Q,B(_wI(_KX)).b)),_sa));if(!_L1._){return E(_aK);}else{var _L2=B(_aC(_L1.a,_L1.b));if(!_L2._){return B(_sf(_v,_v,_aM));}else{var _L3=_L2.a,_L4=E(_L2.b);if(!_L4._){return B(_sf(new T2(1,_L3,_v),_v,_aM));}else{var _L5=E(_L3),_L6=new T(function(){var _L7=B(_JK(46,_L4.a,_L4.b));return new T2(0,_L7.a,_L7.b);});if(E(_L5)==46){return B(_sf(_v,new T2(1,new T(function(){return E(E(_L6).a);}),new T(function(){return E(E(_L6).b);})),_aM));}else{return B(_sf(new T2(1,_L5,new T(function(){return E(E(_L6).a);})),new T(function(){return E(E(_L6).b);}),_aM));}}}}}),_L8=B(_JD(B(_xk(_JC,_L0))));if(!_L8._){return E(_xf);}else{if(!E(_L8.b)._){return B(_wO(3,B(_d(0,E(_L8.a)+(imul(E(_KW),E(_KV)-1|0)|0)|0,_v))));}else{return E(_xd);}}}),_L9=B(_JD(B(_xk(_JC,_KZ))));if(!_L9._){return E(_xf);}else{if(!E(_L9.b)._){return E(_L9.a);}else{return E(_xd);}}});return new T2(0,new T(function(){return B(_s6(_KY,_KV));}),_KY);},_La=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_Lb=new T(function(){return B(err(_La));}),_Lc=function(_Ld,_Le){while(1){var _Lf=E(_Le);if(!_Lf._){return __Z;}else{var _Lg=_Lf.b,_Lh=E(_Ld);if(_Lh==1){return E(_Lg);}else{_Ld=_Lh-1|0;_Le=_Lg;continue;}}}},_Li=function(_Lj,_Lk){if(B(_a2(_Lk,0))>=(_Lj+1|0)){var _Ll=new T(function(){var _Lm=_Lj+1|0;if(_Lm>0){return B(_Lc(_Lm,_Lk));}else{return E(_Lk);}});if(0>=_Lj){return E(_Ll);}else{var _Ln=function(_Lo,_Lp){var _Lq=E(_Lo);if(!_Lq._){return E(_Ll);}else{var _Lr=_Lq.a,_Ls=E(_Lp);return (_Ls==1)?new T2(1,_Lr,_Ll):new T2(1,_Lr,new T(function(){return B(_Ln(_Lq.b,_Ls-1|0));}));}};return new F(function(){return _Ln(_Lk,_Lj);});}}else{return E(_Lk);}},_Lt=function(_Lu,_Lv){return new F(function(){return _Li(E(_Lu),_Lv);});},_Lw=function(_Lx){return E(E(_Lx).a);},_Ly=function(_Lz){return new F(function(){return _d(0,E(_Lz),_v);});},_LA=function(_LB,_LC,_LD){return new F(function(){return _d(E(_LB),E(_LC),_LD);});},_LE=function(_LF,_LG){return new F(function(){return _d(0,E(_LF),_LG);});},_LH=function(_LI,_LJ){return new F(function(){return _28(_LE,_LI,_LJ);});},_LK=new T3(0,_LA,_Ly,_LH),_LL=0,_LM=function(_LN,_LO,_LP){return new F(function(){return A1(_LN,new T2(1,_25,new T(function(){return B(A1(_LO,_LP));})));});},_LQ=new T(function(){return B(unCStr("foldr1"));}),_LR=new T(function(){return B(_aH(_LQ));}),_LS=function(_LT,_LU){var _LV=E(_LU);if(!_LV._){return E(_LR);}else{var _LW=_LV.a,_LX=E(_LV.b);if(!_LX._){return E(_LW);}else{return new F(function(){return A2(_LT,_LW,new T(function(){return B(_LS(_LT,_LX));}));});}}},_LY=new T(function(){return B(unCStr(" out of range "));}),_LZ=new T(function(){return B(unCStr("}.index: Index "));}),_M0=new T(function(){return B(unCStr("Ix{"));}),_M1=new T2(1,_b,_v),_M2=new T2(1,_b,_M1),_M3=0,_M4=function(_M5){return E(E(_M5).a);},_M6=function(_M7,_M8,_M9,_Ma,_Mb){var _Mc=new T(function(){var _Md=new T(function(){var _Me=new T(function(){var _Mf=new T(function(){var _Mg=new T(function(){return B(A3(_LS,_LM,new T2(1,new T(function(){return B(A3(_M4,_M9,_M3,_Ma));}),new T2(1,new T(function(){return B(A3(_M4,_M9,_M3,_Mb));}),_v)),_M2));});return B(_3(_LY,new T2(1,_c,new T2(1,_c,_Mg))));});return B(A(_M4,[_M9,_LL,_M8,new T2(1,_b,_Mf)]));});return B(_3(_LZ,new T2(1,_c,_Me)));},1);return B(_3(_M7,_Md));},1);return new F(function(){return err(B(_3(_M0,_Mc)));});},_Mh=function(_Mi,_Mj,_Mk,_Ml,_Mm){return new F(function(){return _M6(_Mi,_Mj,_Mm,_Mk,_Ml);});},_Mn=function(_Mo,_Mp,_Mq,_Mr){var _Ms=E(_Mq);return new F(function(){return _Mh(_Mo,_Mp,_Ms.a,_Ms.b,_Mr);});},_Mt=function(_Mu,_Mv,_Mw,_Mx){return new F(function(){return _Mn(_Mx,_Mw,_Mv,_Mu);});},_My=new T(function(){return B(unCStr("Int"));}),_Mz=function(_MA,_MB,_MC){return new F(function(){return _Mt(_LK,new T2(0,_MB,_MC),_MA,_My);});},_MD=0,_ME=new T(function(){return B(unCStr("Negative range size"));}),_MF=new T(function(){return B(err(_ME));}),_MG=function(_MH){var _MI=B(A1(_MH,_));return E(_MI);},_MJ=function(_MK,_ML,_MM,_){var _MN=E(_MK);if(!_MN){return new T2(0,_v,_ML);}else{var _MO=new T(function(){return B(_a2(_MM,0))-1|0;}),_MP=B(_KU(new T(function(){return E(_MO)+1|0;}),_ML,_)),_MQ=E(_MP),_MR=_MQ.a,_MS=_MQ.b,_MT=B(_MJ(_MN-1|0,_MS,new T(function(){return B(_Lt(_MR,_MM));}),_)),_MU=new T(function(){var _MV=function(_){var _MW=E(_MO),_MX=function(_MY){if(_MY>=0){var _MZ=newArr(_MY,_Lb),_N0=_MZ,_N1=E(_MY);if(!_N1){return new T4(0,E(_MD),E(_MW),0,_N0);}else{var _N2=function(_N3,_N4,_){while(1){var _N5=E(_N3);if(!_N5._){return E(_);}else{var _=_N0[_N4]=_N5.a;if(_N4!=(_N1-1|0)){var _N6=_N4+1|0;_N3=_N5.b;_N4=_N6;continue;}else{return E(_);}}}},_=B(_N2(_MM,0,_));return new T4(0,E(_MD),E(_MW),_N1,_N0);}}else{return E(_MF);}};if(0>_MW){return new F(function(){return _MX(0);});}else{return new F(function(){return _MX(_MW+1|0);});}},_N7=B(_MG(_MV)),_N8=E(_N7.a),_N9=E(_N7.b),_Na=E(_MR);if(_N8>_Na){return B(_Mz(_Na,_N8,_N9));}else{if(_Na>_N9){return B(_Mz(_Na,_N8,_N9));}else{return E(_N7.d[_Na-_N8|0]);}}});return new T2(0,new T2(1,_MU,new T(function(){return B(_Lw(_MT));})),_MS);}},_Nb=function(_Nc){var _Nd=E(_Nc);if(!_Nd._){return new T2(0,_v,_v);}else{var _Ne=E(_Nd.a),_Nf=new T(function(){var _Ng=B(_Nb(_Nd.b));return new T2(0,_Ng.a,_Ng.b);});return new T2(0,new T2(1,_Ne.a,new T(function(){return E(E(_Nf).a);})),new T2(1,_Ne.b,new T(function(){return E(E(_Nf).b);})));}},_Nh=function(_Ni){return new T2(1,_Ni,_v);},_Nj=new T(function(){return B(unCStr("\u3042\u304b\u306f\u306a\u307e\u3044\u304d\u3072\u306b\u307f\u3046\u304f\u3075\u306c\u3080\u3048\u3051\u3078\u306d\u3081\u304a\u3053\u307b\u306e\u3082\u3068\u308d\u305d\u3088\u3092\u3066\u308c\u305b\u3091\u3064\u308b\u3059\u3086\u3093\u3061\u308a\u3057\u3090\u305f\u3089\u3055\u3084\u308f"));}),_Nk=function(_Nl,_Nm,_){var _Nn=new T(function(){return 4+B(_pM(E(_Nm),8))|0;}),_No=B(_KU(_Nn,_Nl,_)),_Np=E(_No),_Nq=new T(function(){return B(_kB(_pU,new T(function(){var _Nr=E(_Nm)+3|0;if(0>=_Nr){return __Z;}else{return B(_wO(_Nr,_Nj));}},1)));}),_Ns=B(_MJ(E(_Nn),_Np.b,_Nq,_)),_Nt=E(_Ns);return new T2(0,new T(function(){var _Nu=B(_Nb(_Nt.a));return new T3(0,E(B(_dm(_Nh,_Nu.b))),E(_Nu.a),E(_Np.a));}),_Nt.b);},_Nv=function(_Nw){return E(_Nw).f;},_Nx=function(_Ny,_Nz,_NA,_NB,_){var _NC=B(_Nk(new T(function(){return B(_Nv(_NB));},1),_NA,_)),_ND=E(_NC),_NE=E(_ND.a),_NF=_NE.b,_NG=_NE.c,_NH=B(A3(_eJ,_5z,B(_79(_Nz,B(_79(_NF,_NG)))).a,_));return new T(function(){var _NI=E(_NB),_NJ=E(_Ny),_NK=B(_qg(_NJ.a,_NJ.b,_NE.a,_NF,_NG));return {_:0,a:E(_NI.a),b:E(_NI.b),c:E(new T1(1,_NE)),d:E(_NI.d),e:E(new T2(1,_NK.a,_NK.b)),f:E(_ND.b),g:E(_NI.g),h:E(_NI.h)};});},_NL=function(_NM,_NN,_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_O2,_O3,_O4,_){var _O5=function(_,_O6,_O7,_O8,_O9,_Oa,_Ob,_Oc,_Od,_Oe,_Of,_Og,_Oh,_Oi){var _Oj=function(_){var _Ok=E(_Oa);if(!_Ok._){return {_:0,a:E(_O6),b:E(new T2(0,_O7,_O8)),c:E(_O9),d:E(_2q),e:E(_Ob),f:_Oc,g:E(new T5(0,E(_Od),E(_Oe),E(_Of),E(_Og),E(_Oh))),h:E(_Oi)};}else{var _Ol=B(A3(_eJ,_5z,B(_79(_NQ,E(_Ok.a))).a,_));return {_:0,a:E(_O6),b:E(new T2(0,_O7,_O8)),c:E(_O9),d:E(_2q),e:E(_Ob),f:_Oc,g:E(new T5(0,E(_Od),E(_Oe),E(_Of),E(_Og),E(_Oh))),h:E(_Oi)};}};if(!B(_9d(_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_O2,_O3,_O4,_O6,_O7,_O8,_O9,_Oa,_Ob,_Oc,_Od,_Oe,_Of,_Og,_Oh,_Oi))){var _Om=E(_NM),_On=__app1(E(_eU),_Om.b),_Oo=B(A2(_f4,_Om.a,_)),_Op=B(_kG(_Om,new T2(0,_NN,_pE),_NO,_Ob,_));return new F(function(){return _Oj(_);});}else{return new F(function(){return _Oj(_);});}},_Oq=E(_NR);if(_Oq==( -1)){return new F(function(){return _O5(_,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_O2,_O3,_O4);});}else{var _Or=B(_6S(_Oq,_NX));if(!_Or._){return new F(function(){return _O5(_,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_O2,_O3,_O4);});}else{var _Os=E(E(_Or.a).o);switch(_Os._){case 0:return new F(function(){return _O5(_,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_O2,_O3,_O4);});break;case 1:var _Ot=E(_Os.a);if(!_Ot._){var _Ou=E(_Ot.a);if(_Ou<=45){var _Ov=B(_Nx(_NN,_NP,_Ou,{_:0,a:E(new T1(1,_Ot)),b:E(new T2(0,_NT,_NU)),c:E(_NV),d:E(_NW),e:E(_NX),f:_NY,g:E(new T5(0,E(_NZ),E(_O0),E(_O1),E(_O2),E(_O3))),h:E(_O4)},_)),_Ow=E(_Ov),_Ox=E(_Ow.b),_Oy=E(_Ow.g);return new F(function(){return _O5(_,_Ow.a,_Ox.a,_Ox.b,_Ow.c,_Ow.d,_Ow.e,_Ow.f,_Oy.a,_Oy.b,_Oy.c,_Oy.d,_Oy.e,_Ow.h);});}else{return new F(function(){return _O5(_,_NS,_NT,_NU,_NV,_NW,new T2(1,{_:0,a:0,b:E(_6d),c:E(_62),d:0,e:5,f:E(_69),g:E(_v),h:E(_6k),i:E(_6i),j:E(new T2(1,new T(function(){var _Oz=E(_NT);if(!_Oz){return E(_pK);}else{return B(_3(B(_d(0,_Oz,_v)),_pL));}}),_v)),k:E(_6f),l:E(_v),m:E(_v),n:E(_2q),o:E(_65)},_v),_NY,_NZ,_O0,_O1,_O2,_O3,_O4);});}}else{return E(_pJ);}break;case 2:var _OA=B(_dq(_NN,new T(function(){return B(_a2(_NX,0));},1),_Os.a,_NS,new T2(0,_NT,_NU),_NV,_NW,_NX,_NY,new T5(0,E(_NZ),E(_O0),E(_O1),E(_O2),E(_O3)),_O4)),_OB=E(_OA.b),_OC=E(_OA.g);return new F(function(){return _O5(_,_OA.a,_OB.a,_OB.b,_OA.c,_OA.d,_OA.e,_OA.f,_OC.a,_OC.b,_OC.c,_OC.d,_OC.e,_OA.h);});break;default:var _OD=B(_bZ(_NN,E(_Os.a),_NS,_NT,_NU,_NV,_NW,_NX,_NY,new T5(0,E(_NZ),E(_O0),E(_O1),E(_O2),E(_O3)),_O4)),_OE=E(_OD.b),_OF=E(_OD.g);return new F(function(){return _O5(_,_OD.a,_OE.a,_OE.b,_OD.c,_OD.d,_OD.e,_OD.f,_OF.a,_OF.b,_OF.c,_OF.d,_OF.e,_OD.h);});}}}},_OG=function(_OH,_OI){while(1){var _OJ=E(_OH);if(!_OJ._){return E(_OI);}else{var _OK=new T2(1,_OJ.a,_OI);_OH=_OJ.b;_OI=_OK;continue;}}},_OL=function(_OM,_ON,_OO,_OP,_OQ,_OR,_OS,_){var _OT=E(_ON),_OU=_OT.a,_OV=E(_OP),_OW=E(_OS),_OX=_OW.e,_OY=function(_OZ){var _P0=E(_OW.b),_P1=E(_OW.g);return new F(function(){return _NL(_OM,_OU,_OO,_OV.a,_OV.b,_OZ,_OW.a,_P0.a,_P0.b,_OW.c,_OW.d,_OX,_OW.f,_P1.a,_P1.b,_P1.c,_P1.d,_P1.e,_OW.h,_);});},_P2=B(_OG(_OX,_v));if(!_P2._){return new F(function(){return _OY( -1);});}else{var _P3=_P2.b,_P4=E(_OU),_P5=_P4.b,_P6=E(_OT.b),_P7=_P6.b,_P8=E(_OQ)*(E(_P4.a)/E(_P6.a)),_P9=E(_P2.a),_Pa=E(_P9.b),_Pb=E(_Pa.a);if(_P8<=_Pb){return new F(function(){return _OY(B(_6H(_P8,new T(function(){return E(_OR)*(E(_P5)/E(_P7));},1),_P3)));});}else{if(_P8>=_Pb+E(_Pa.c)){return new F(function(){return _OY(B(_6H(_P8,new T(function(){return E(_OR)*(E(_P5)/E(_P7));},1),_P3)));});}else{var _Pc=E(_OR)*(E(_P5)/E(_P7)),_Pd=E(_Pa.b);if(_Pc<=_Pd){return new F(function(){return _OY(B(_6x(_P8,_Pc,_P3)));});}else{if(_Pc>=_Pd+E(_Pa.d)){return new F(function(){return _OY(B(_6x(_P8,_Pc,_P3)));});}else{return new F(function(){return _OY(_P9.a);});}}}}}},_Pe=function(_Pf){return E(E(_Pf).a);},_Pg=function(_Ph){return E(E(_Ph).b);},_Pi=function(_Pj){return E(E(_Pj).a);},_Pk=function(_){return new F(function(){return nMV(_2q);});},_Pl=new T(function(){return B(_2J(_Pk));}),_Pm=function(_Pn){return E(E(_Pn).b);},_Po=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_Pp=function(_Pq){return E(E(_Pq).d);},_Pr=function(_Ps,_Pt,_Pu,_Pv,_Pw,_Px){var _Py=B(_Pe(_Ps)),_Pz=B(_dS(_Py)),_PA=new T(function(){return B(_5U(_Py));}),_PB=new T(function(){return B(_Pp(_Pz));}),_PC=new T(function(){return B(A1(_Pt,_Pv));}),_PD=new T(function(){return B(A2(_Pi,_Pu,_Pw));}),_PE=function(_PF){return new F(function(){return A1(_PB,new T3(0,_PD,_PC,_PF));});},_PG=function(_PH){var _PI=new T(function(){var _PJ=new T(function(){var _PK=__createJSFunc(2,function(_PL,_){var _PM=B(A2(E(_PH),_PL,_));return _2N;}),_PN=_PK;return function(_){return new F(function(){return __app3(E(_Po),E(_PC),E(_PD),_PN);});};});return B(A1(_PA,_PJ));});return new F(function(){return A3(_eD,_Pz,_PI,_PE);});},_PO=new T(function(){var _PP=new T(function(){return B(_5U(_Py));}),_PQ=function(_PR){var _PS=new T(function(){return B(A1(_PP,function(_){var _=wMV(E(_Pl),new T1(1,_PR));return new F(function(){return A(_Pg,[_Pu,_Pw,_PR,_]);});}));});return new F(function(){return A3(_eD,_Pz,_PS,_Px);});};return B(A2(_Pm,_Ps,_PQ));});return new F(function(){return A3(_eD,_Pz,_PO,_PG);});},_PT=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_PU=function(_){var _PV=rMV(E(_Pl)),_PW=E(_PV);if(!_PW._){var _PX=__app1(E(_PT),E(_2N));return new F(function(){return _dP(_);});}else{var _PY=__app1(E(_PT),E(_PW.a));return new F(function(){return _dP(_);});}},_PZ=new T(function(){return B(unCStr("\u4eca\u65e5\u3082\u6700\u9ad8\u306e\u4e00\u65e5\u306b\u306a\u308b\u3088\uff01\n\u30f2\u30b7\u30c6\u3092\u5b78\u3093\u3067\u3044\u304b\u3046\u3088\uff01\n\u304a\u3082\u3057\u308d\u3044\u3053\u3068\u306b\u306a\u3063\u3066\u304d\u305f\u306d\uff01\n\u3059\u3066\u304d\u306a \u51fa\u6703\u3072\u304c \u3042\u3063\u3066 \u3046\u308c\u3057\u3044\u306d\uff01\n\u5fc3\u306e\u6e96\u5099\u306f\u3067\u304d\u3066\u308b\uff1f\n\u3055\u3042 \u306f\u3058\u3081\u3084\u3046\u304b\uff01"));}),_Q0=function(_Q1,_Q2){var _Q3=E(_Q2);if(!_Q3._){return new T2(0,_v,_v);}else{var _Q4=_Q3.a;if(!B(A1(_Q1,_Q4))){var _Q5=new T(function(){var _Q6=B(_Q0(_Q1,_Q3.b));return new T2(0,_Q6.a,_Q6.b);});return new T2(0,new T2(1,_Q4,new T(function(){return E(E(_Q5).a);})),new T(function(){return E(E(_Q5).b);}));}else{return new T2(0,_v,_Q3);}}},_Q7=function(_Q8){return (E(_Q8)==10)?true:false;},_Q9=function(_Qa){var _Qb=E(_Qa);if(!_Qb._){return __Z;}else{var _Qc=new T(function(){var _Qd=B(_Q0(_Q7,_Qb));return new T2(0,_Qd.a,new T(function(){var _Qe=E(_Qd.b);if(!_Qe._){return __Z;}else{return B(_Q9(_Qe.b));}}));});return new T2(1,new T(function(){return E(E(_Qc).a);}),new T(function(){return E(E(_Qc).b);}));}},_Qf=new T(function(){return B(_Q9(_PZ));}),_Qg=function(_Qh,_Qi){while(1){var _Qj=E(_Qh);if(!_Qj._){return E(_Qi);}else{_Qh=_Qj.b;_Qi=_Qj.a;continue;}}},_Qk=function(_Ql,_Qm,_Qn,_Qo,_){var _Qp=B(_MJ(1,new T(function(){return E(_Qo).f;}),_Qf,_));return new F(function(){return _kG(_Ql,_Qm,_Qn,new T2(1,{_:0,a:0,b:E(_6d),c:E(_62),d:0,e:5,f:E(_69),g:E(_v),h:E(_6k),i:E(_6i),j:E(new T2(1,new T(function(){return B(_Qg(E(_Qp).a,_aM));}),_v)),k:E(_6f),l:E(_v),m:E(_v),n:E(_2q),o:E(_65)},_v),_);});},_Qq=new T(function(){return B(unCStr("vaw"));}),_Qr=new T(function(){return B(unCStr("ggo"));}),_Qs=new T(function(){return B(unCStr("3pm"));}),_Qt=0,_Qu=1,_Qv=2,_Qw=function(_Qx){var _Qy=B(_wO(3,B(_OG(fromJSStr(_Qx),_v))));return (!B(_98(_Qy,_Qs)))?(!B(_98(_Qy,_Qr)))?(!B(_98(_Qy,_Qq)))?__Z:new T1(1,new T2(0,E(_Qv),_Qx)):new T1(1,new T2(0,E(_Qu),_Qx)):new T1(1,new T2(0,E(_Qt),_Qx));},_Qz=new T(function(){return B(_bG("Browser.hs:84:7-34|Just adSrc"));}),_QA=2,_QB=new T6(0,E(_5N),E(_5N),E(_5N),E(_QA),E(_5N),1),_QC=new T(function(){return B(unCStr(".mp3"));}),_QD=function(_QE){return new T1(1,E(_QE));},_QF=function(_QG,_QH){return new F(function(){return A2(_Pp,B(_dS(_QG)),new T1(1,_QH));});},_QI=new T2(0,_5x,_QF),_QJ="auto",_QK="metadata",_QL="none",_QM=new T(function(){return new T1(0,"preload");}),_QN=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_QO=function(_){return new F(function(){return __app1(E(_QN),"source");});},_QP=new T(function(){return new T1(0,"src");}),_QQ="audio/wav",_QR="audio/ogg",_QS="audio/mpeg",_QT=new T(function(){return new T1(0,"type");}),_QU=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_QV=function(_QW){return E(E(_QW).a);},_QX=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_QY=new T(function(){return eval("(function(e,p,v){e.style[p] = v;})");}),_QZ=function(_R0,_R1,_R2,_R3){var _R4=new T(function(){return B(A2(_QV,_R0,_R2));}),_R5=function(_R6,_){var _R7=E(_R6);if(!_R7._){return _5L;}else{var _R8=E(_R4),_R9=E(_QU),_Ra=__app2(_R9,E(_R7.a),_R8),_Rb=function(_Rc,_){while(1){var _Rd=E(_Rc);if(!_Rd._){return _5L;}else{var _Re=__app2(_R9,E(_Rd.a),_R8);_Rc=_Rd.b;continue;}}};return new F(function(){return _Rb(_R7.b,_);});}},_Rf=function(_Rg,_){while(1){var _Rh=B((function(_Ri,_){var _Rj=E(_Ri);if(!_Rj._){return _5L;}else{var _Rk=_Rj.b,_Rl=E(_Rj.a);if(!_Rl._){var _Rm=_Rl.b,_Rn=E(_Rl.a);switch(_Rn._){case 0:var _Ro=E(_R4),_Rp=E(_g6),_Rq=__app3(_Rp,_Ro,_Rn.a,_Rm),_Rr=function(_Rs,_){while(1){var _Rt=E(_Rs);if(!_Rt._){return _5L;}else{var _Ru=_Rt.b,_Rv=E(_Rt.a);if(!_Rv._){var _Rw=_Rv.b,_Rx=E(_Rv.a);switch(_Rx._){case 0:var _Ry=__app3(_Rp,_Ro,_Rx.a,_Rw);_Rs=_Ru;continue;case 1:var _Rz=__app3(E(_QY),_Ro,_Rx.a,_Rw);_Rs=_Ru;continue;default:var _RA=__app3(E(_QX),_Ro,_Rx.a,_Rw);_Rs=_Ru;continue;}}else{var _RB=B(_R5(_Rv.a,_));_Rs=_Ru;continue;}}}};return new F(function(){return _Rr(_Rk,_);});break;case 1:var _RC=E(_R4),_RD=E(_QY),_RE=__app3(_RD,_RC,_Rn.a,_Rm),_RF=function(_RG,_){while(1){var _RH=E(_RG);if(!_RH._){return _5L;}else{var _RI=_RH.b,_RJ=E(_RH.a);if(!_RJ._){var _RK=_RJ.b,_RL=E(_RJ.a);switch(_RL._){case 0:var _RM=__app3(E(_g6),_RC,_RL.a,_RK);_RG=_RI;continue;case 1:var _RN=__app3(_RD,_RC,_RL.a,_RK);_RG=_RI;continue;default:var _RO=__app3(E(_QX),_RC,_RL.a,_RK);_RG=_RI;continue;}}else{var _RP=B(_R5(_RJ.a,_));_RG=_RI;continue;}}}};return new F(function(){return _RF(_Rk,_);});break;default:var _RQ=E(_R4),_RR=E(_QX),_RS=__app3(_RR,_RQ,_Rn.a,_Rm),_RT=function(_RU,_){while(1){var _RV=E(_RU);if(!_RV._){return _5L;}else{var _RW=_RV.b,_RX=E(_RV.a);if(!_RX._){var _RY=_RX.b,_RZ=E(_RX.a);switch(_RZ._){case 0:var _S0=__app3(E(_g6),_RQ,_RZ.a,_RY);_RU=_RW;continue;case 1:var _S1=__app3(E(_QY),_RQ,_RZ.a,_RY);_RU=_RW;continue;default:var _S2=__app3(_RR,_RQ,_RZ.a,_RY);_RU=_RW;continue;}}else{var _S3=B(_R5(_RX.a,_));_RU=_RW;continue;}}}};return new F(function(){return _RT(_Rk,_);});}}else{var _S4=B(_R5(_Rl.a,_));_Rg=_Rk;return __continue;}}})(_Rg,_));if(_Rh!=__continue){return _Rh;}}};return new F(function(){return A2(_5U,_R1,function(_){return new F(function(){return _Rf(_R3,_);});});});},_S5=function(_S6,_S7,_S8,_S9){var _Sa=B(_dS(_S7)),_Sb=function(_Sc){return new F(function(){return A3(_eB,_Sa,new T(function(){return B(_QZ(_S6,_S7,_Sc,_S9));}),new T(function(){return B(A2(_Pp,_Sa,_Sc));}));});};return new F(function(){return A3(_eD,_Sa,_S8,_Sb);});},_Sd=function(_Se,_){var _Sf=E(_Se);if(!_Sf._){return _v;}else{var _Sg=E(_Sf.a),_Sh=B(A(_S5,[_QI,_5z,_QO,new T2(1,new T(function(){var _Si=E(_QT);switch(E(_Sg.a)){case 0:return new T2(0,E(_Si),E(_QS));break;case 1:return new T2(0,E(_Si),E(_QR));break;default:return new T2(0,E(_Si),E(_QQ));}}),new T2(1,new T(function(){return new T2(0,E(_QP),_Sg.b);}),_v)),_])),_Sj=B(_Sd(_Sf.b,_));return new T2(1,_Sh,_Sj);}},_Sk=new T(function(){return new T1(0,"volume");}),_Sl=new T(function(){return new T1(0,"muted");}),_Sm=new T(function(){return new T1(0,"loop");}),_Sn=new T(function(){return new T1(0,"autoplay");}),_So="true",_Sp=new T(function(){return toJSStr(_v);}),_Sq=new T(function(){return new T1(0,"controls");}),_Sr=function(_){return new F(function(){return __app1(E(_QN),"audio");});},_Ss=function(_St,_Su,_Sv){var _Sw=function(_){var _Sx=B(_Sd(_Sv,_)),_Sy=B(A(_S5,[_QI,_5z,_Sr,new T2(1,new T(function(){var _Sz=E(_Sq);if(!E(E(_Su).a)){return new T2(0,E(_Sz),E(_Sp));}else{return new T2(0,E(_Sz),E(_So));}}),new T2(1,new T(function(){var _SA=E(_Sn);if(!E(E(_Su).b)){return new T2(0,E(_SA),E(_Sp));}else{return new T2(0,E(_SA),E(_So));}}),new T2(1,new T(function(){var _SB=E(_Sm);if(!E(E(_Su).c)){return new T2(0,E(_SB),E(_Sp));}else{return new T2(0,E(_SB),E(_So));}}),new T2(1,new T(function(){var _SC=E(_Sl);if(!E(E(_Su).e)){return new T2(0,E(_SC),E(_Sp));}else{return new T2(0,E(_SC),E(_So));}}),new T2(1,new T(function(){var _SD=String(E(_Su).f);return new T2(0,E(_Sk),_SD);}),new T2(1,new T(function(){var _SE=E(_QM);switch(E(E(_Su).d)){case 0:return new T2(0,E(_SE),E(_QL));break;case 1:return new T2(0,E(_SE),E(_QK));break;default:return new T2(0,E(_SE),E(_QJ));}}),new T2(1,new T(function(){return B(_QD(_Sx));}),_v))))))),_]));return new T1(0,_Sy);};return new F(function(){return A2(_5U,_St,_Sw);});},_SF=function(_SG,_SH){var _SI=E(_SG);if(_SI==( -1)){return __Z;}else{var _SJ=new T(function(){var _SK=new T(function(){var _SL=B(_Qw(toJSStr(B(_3(_SH,new T(function(){return B(_3(B(_d(0,_SI,_v)),_QC));},1))))));if(!_SL._){return E(_Qz);}else{return E(_SL.a);}});return B(_Ss(_5z,_QB,new T2(1,_SK,_v)));});return new F(function(){return _3(B(_SF(_SI-1|0,_SH)),new T2(1,_SJ,_v));});}},_SM=new T(function(){return B(unCStr("Audio/se"));}),_SN=new T(function(){return B(_SF(3,_SM));}),_SO=function(_SP,_){var _SQ=E(_SP);if(!_SQ._){return _v;}else{var _SR=B(A1(_SQ.a,_)),_SS=B(_SO(_SQ.b,_));return new T2(1,_SR,_SS);}},_ST=new T(function(){return B(unCStr("Audio/os"));}),_SU=new T(function(){return B(_SF(47,_ST));}),_SV=function(_SW,_){var _SX=E(_SW);if(!_SX._){return _v;}else{var _SY=B(A1(_SX.a,_)),_SZ=B(_SV(_SX.b,_));return new T2(1,_SY,_SZ);}},_T0="src",_T1=new T(function(){return B(unCStr("img"));}),_T2=function(_T3,_T4){return new F(function(){return A2(_5U,_T3,function(_){var _T5=__app1(E(_QN),toJSStr(E(_T1))),_T6=__app3(E(_g6),_T5,E(_T0),E(_T4));return _T5;});});},_T7=new T(function(){return B(unCStr(".png"));}),_T8=function(_T9,_Ta){var _Tb=E(_T9);if(_Tb==( -1)){return __Z;}else{var _Tc=new T(function(){var _Td=new T(function(){return toJSStr(B(_3(_Ta,new T(function(){return B(_3(B(_d(0,_Tb,_v)),_T7));},1))));});return B(_T2(_5z,_Td));});return new F(function(){return _3(B(_T8(_Tb-1|0,_Ta)),new T2(1,_Tc,_v));});}},_Te=new T(function(){return B(unCStr("Images/Wst/wst"));}),_Tf=new T(function(){return B(_T8(120,_Te));}),_Tg=function(_Th,_){var _Ti=E(_Th);if(!_Ti._){return _v;}else{var _Tj=B(A1(_Ti.a,_)),_Tk=B(_Tg(_Ti.b,_));return new T2(1,_Tj,_Tk);}},_Tl=new T(function(){return B(unCStr("Images/img"));}),_Tm=new T(function(){return B(_T8(5,_Tl));}),_Tn=function(_To,_){var _Tp=E(_To);if(!_Tp._){return _v;}else{var _Tq=B(A1(_Tp.a,_)),_Tr=B(_Tn(_Tp.b,_));return new T2(1,_Tq,_Tr);}},_Ts=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_Tt=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_Tu=function(_Tv,_Tw,_Tx){var _Ty=B(_Pe(_Tv)),_Tz=new T(function(){return B(_5U(_Ty));}),_TA=function(_TB){var _TC=function(_){var _TD=E(_Tw);if(!_TD._){var _TE=B(A1(_TB,_5L)),_TF=__createJSFunc(0,function(_){var _TG=B(A1(_TE,_));return _2N;}),_TH=__app2(E(_Tt),_TD.a,_TF);return new T(function(){var _TI=Number(_TH),_TJ=jsTrunc(_TI);return new T2(0,_TJ,E(_TD));});}else{var _TK=B(A1(_TB,_5L)),_TL=__createJSFunc(0,function(_){var _TM=B(A1(_TK,_));return _2N;}),_TN=__app2(E(_Ts),_TD.a,_TL);return new T(function(){var _TO=Number(_TN),_TP=jsTrunc(_TO);return new T2(0,_TP,E(_TD));});}};return new F(function(){return A1(_Tz,_TC);});},_TQ=new T(function(){return B(A2(_Pm,_Tv,function(_TR){return E(_Tx);}));});return new F(function(){return A3(_eD,B(_dS(_Ty)),_TQ,_TA);});},_TS=function(_){var _TT=B(_Tn(_Tm,_)),_TU=B(_Tg(_Tf,_)),_TV=B(_SV(_SU,_)),_TW=_TV,_TX=B(_SO(_SN,_)),_TY=_TX,_TZ=__app1(E(_5R),"canvas"),_U0=__eq(_TZ,E(_2N));if(!E(_U0)){var _U1=__isUndef(_TZ);if(!E(_U1)){var _U2=B(A3(_5W,_5z,_TZ,_)),_U3=E(_U2);if(!_U3._){return new F(function(){return die(_6w);});}else{var _U4=E(_U3.a),_U5=B(_5F(_U4.b,_)),_U6=_U5,_U7=nMV(_6p),_U8=_U7,_U9=new T2(0,_TT,_TU),_Ua=B(_Qk(_U4,_U6,_U9,_6p,_)),_Ub=B(A(_Pr,[_5A,_3g,_3f,_TZ,_5M,function(_Uc,_){var _Ud=E(E(_Uc).a),_Ue=rMV(_U8),_Uf=B(_OL(_U4,_U6,_U9,new T2(0,_TW,_TY),_Ud.a,_Ud.b,_Ue,_)),_=wMV(_U8,_Uf);return _5L;},_])),_Ug=B(A(_Pr,[_5A,_3g,_4P,_TZ,_5P,function(_Uh,_){var _Ui=E(_Uh),_Uj=rMV(_U8),_Uk=E(_Uj);if(!E(E(_Uk.g).c)){var _=wMV(_U8,_Uk);return _5L;}else{var _Ul=B(_PU(_)),_=wMV(_U8,_Uk);return _5L;}},_])),_Um=function(_){var _Un=rMV(_U8),_=wMV(_U8,new T(function(){var _Uo=E(_Un),_Up=E(_Uo.g);return {_:0,a:E(_Uo.a),b:E(_Uo.b),c:E(_Uo.c),d:E(_Uo.d),e:E(_Uo.e),f:_Uo.f,g:E(new T5(0,E(_Up.a),E(_Up.b),E(_5N),E(_Up.d),E(_Up.e))),h:E(_Uo.h)};}));return _5L;},_Uq=function(_Ur,_){var _Us=E(_Ur),_Ut=rMV(_U8),_=wMV(_U8,new T(function(){var _Uu=E(_Ut),_Uv=E(_Uu.g);return {_:0,a:E(_Uu.a),b:E(_Uu.b),c:E(_Uu.c),d:E(_Uu.d),e:E(_Uu.e),f:_Uu.f,g:E(new T5(0,E(_Uv.a),E(_Uv.b),E(_5Q),E(_Uv.d),E(_Uv.e))),h:E(_Uu.h)};})),_Uw=B(A(_Tu,[_5A,_6q,_Um,_]));return _5L;},_Ux=B(A(_Pr,[_5A,_3g,_4P,_TZ,_5O,_Uq,_]));return _5L;}}else{return new F(function(){return die(_6t);});}}else{return new F(function(){return die(_6t);});}},_Uy=function(_){return new F(function(){return _TS(_);});};
var hasteMain = function() {B(A(_Uy, [0]));};window.onload = hasteMain;