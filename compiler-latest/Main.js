"use strict";
var __haste_prog_id = '23b1b05b48da18a5fb14816e9319c35e8fb008b35d7358d5c1a98dac880a2bee';
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

var _0="deltaZ",_1="deltaY",_2="deltaX",_3=function(_4,_5){var _6=E(_4);return (_6._==0)?E(_5):new T2(1,_6.a,new T(function(){return B(_3(_6.b,_5));}));},_7=function(_8,_9){var _a=jsShowI(_8);return new F(function(){return _3(fromJSStr(_a),_9);});},_b=41,_c=40,_d=function(_e,_f,_g){if(_f>=0){return new F(function(){return _7(_f,_g);});}else{if(_e<=6){return new F(function(){return _7(_f,_g);});}else{return new T2(1,_c,new T(function(){var _h=jsShowI(_f);return B(_3(fromJSStr(_h),new T2(1,_b,_g)));}));}}},_i=new T(function(){return B(unCStr(")"));}),_j=new T(function(){return B(_d(0,2,_i));}),_k=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_j));}),_l=function(_m){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_d(0,_m,_k));}))));});},_n=function(_o,_){return new T(function(){var _p=Number(E(_o)),_q=jsTrunc(_p);if(_q<0){return B(_l(_q));}else{if(_q>2){return B(_l(_q));}else{return _q;}}});},_r=0,_s=new T3(0,_r,_r,_r),_t="button",_u=new T(function(){return eval("jsGetMouseCoords");}),_v=__Z,_w=function(_x,_){var _y=E(_x);if(!_y._){return _v;}else{var _z=B(_w(_y.b,_));return new T2(1,new T(function(){var _A=Number(E(_y.a));return jsTrunc(_A);}),_z);}},_B=function(_C,_){var _D=__arr2lst(0,_C);return new F(function(){return _w(_D,_);});},_E=function(_F,_){return new F(function(){return _B(E(_F),_);});},_G=function(_H,_){return new T(function(){var _I=Number(E(_H));return jsTrunc(_I);});},_J=new T2(0,_G,_E),_K=function(_L,_){var _M=E(_L);if(!_M._){return _v;}else{var _N=B(_K(_M.b,_));return new T2(1,_M.a,_N);}},_O=new T(function(){return B(unCStr("base"));}),_P=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Q=new T(function(){return B(unCStr("IOException"));}),_R=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_O,_P,_Q),_S=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_R,_v,_v),_T=function(_U){return E(_S);},_V=function(_W){return E(E(_W).a);},_X=function(_Y,_Z,_10){var _11=B(A1(_Y,_)),_12=B(A1(_Z,_)),_13=hs_eqWord64(_11.a,_12.a);if(!_13){return __Z;}else{var _14=hs_eqWord64(_11.b,_12.b);return (!_14)?__Z:new T1(1,_10);}},_15=function(_16){var _17=E(_16);return new F(function(){return _X(B(_V(_17.a)),_T,_17.b);});},_18=new T(function(){return B(unCStr(": "));}),_19=new T(function(){return B(unCStr(")"));}),_1a=new T(function(){return B(unCStr(" ("));}),_1b=new T(function(){return B(unCStr("interrupted"));}),_1c=new T(function(){return B(unCStr("system error"));}),_1d=new T(function(){return B(unCStr("unsatisified constraints"));}),_1e=new T(function(){return B(unCStr("user error"));}),_1f=new T(function(){return B(unCStr("permission denied"));}),_1g=new T(function(){return B(unCStr("illegal operation"));}),_1h=new T(function(){return B(unCStr("end of file"));}),_1i=new T(function(){return B(unCStr("resource exhausted"));}),_1j=new T(function(){return B(unCStr("resource busy"));}),_1k=new T(function(){return B(unCStr("does not exist"));}),_1l=new T(function(){return B(unCStr("already exists"));}),_1m=new T(function(){return B(unCStr("resource vanished"));}),_1n=new T(function(){return B(unCStr("timeout"));}),_1o=new T(function(){return B(unCStr("unsupported operation"));}),_1p=new T(function(){return B(unCStr("hardware fault"));}),_1q=new T(function(){return B(unCStr("inappropriate type"));}),_1r=new T(function(){return B(unCStr("invalid argument"));}),_1s=new T(function(){return B(unCStr("failed"));}),_1t=new T(function(){return B(unCStr("protocol error"));}),_1u=function(_1v,_1w){switch(E(_1v)){case 0:return new F(function(){return _3(_1l,_1w);});break;case 1:return new F(function(){return _3(_1k,_1w);});break;case 2:return new F(function(){return _3(_1j,_1w);});break;case 3:return new F(function(){return _3(_1i,_1w);});break;case 4:return new F(function(){return _3(_1h,_1w);});break;case 5:return new F(function(){return _3(_1g,_1w);});break;case 6:return new F(function(){return _3(_1f,_1w);});break;case 7:return new F(function(){return _3(_1e,_1w);});break;case 8:return new F(function(){return _3(_1d,_1w);});break;case 9:return new F(function(){return _3(_1c,_1w);});break;case 10:return new F(function(){return _3(_1t,_1w);});break;case 11:return new F(function(){return _3(_1s,_1w);});break;case 12:return new F(function(){return _3(_1r,_1w);});break;case 13:return new F(function(){return _3(_1q,_1w);});break;case 14:return new F(function(){return _3(_1p,_1w);});break;case 15:return new F(function(){return _3(_1o,_1w);});break;case 16:return new F(function(){return _3(_1n,_1w);});break;case 17:return new F(function(){return _3(_1m,_1w);});break;default:return new F(function(){return _3(_1b,_1w);});}},_1x=new T(function(){return B(unCStr("}"));}),_1y=new T(function(){return B(unCStr("{handle: "));}),_1z=function(_1A,_1B,_1C,_1D,_1E,_1F){var _1G=new T(function(){var _1H=new T(function(){var _1I=new T(function(){var _1J=E(_1D);if(!_1J._){return E(_1F);}else{var _1K=new T(function(){return B(_3(_1J,new T(function(){return B(_3(_19,_1F));},1)));},1);return B(_3(_1a,_1K));}},1);return B(_1u(_1B,_1I));}),_1L=E(_1C);if(!_1L._){return E(_1H);}else{return B(_3(_1L,new T(function(){return B(_3(_18,_1H));},1)));}}),_1M=E(_1E);if(!_1M._){var _1N=E(_1A);if(!_1N._){return E(_1G);}else{var _1O=E(_1N.a);if(!_1O._){var _1P=new T(function(){var _1Q=new T(function(){return B(_3(_1x,new T(function(){return B(_3(_18,_1G));},1)));},1);return B(_3(_1O.a,_1Q));},1);return new F(function(){return _3(_1y,_1P);});}else{var _1R=new T(function(){var _1S=new T(function(){return B(_3(_1x,new T(function(){return B(_3(_18,_1G));},1)));},1);return B(_3(_1O.a,_1S));},1);return new F(function(){return _3(_1y,_1R);});}}}else{return new F(function(){return _3(_1M.a,new T(function(){return B(_3(_18,_1G));},1));});}},_1T=function(_1U){var _1V=E(_1U);return new F(function(){return _1z(_1V.a,_1V.b,_1V.c,_1V.d,_1V.f,_v);});},_1W=function(_1X,_1Y,_1Z){var _20=E(_1Y);return new F(function(){return _1z(_20.a,_20.b,_20.c,_20.d,_20.f,_1Z);});},_21=function(_22,_23){var _24=E(_22);return new F(function(){return _1z(_24.a,_24.b,_24.c,_24.d,_24.f,_23);});},_25=44,_26=93,_27=91,_28=function(_29,_2a,_2b){var _2c=E(_2a);if(!_2c._){return new F(function(){return unAppCStr("[]",_2b);});}else{var _2d=new T(function(){var _2e=new T(function(){var _2f=function(_2g){var _2h=E(_2g);if(!_2h._){return E(new T2(1,_26,_2b));}else{var _2i=new T(function(){return B(A2(_29,_2h.a,new T(function(){return B(_2f(_2h.b));})));});return new T2(1,_25,_2i);}};return B(_2f(_2c.b));});return B(A2(_29,_2c.a,_2e));});return new T2(1,_27,_2d);}},_2j=function(_2k,_2l){return new F(function(){return _28(_21,_2k,_2l);});},_2m=new T3(0,_1W,_1T,_2j),_2n=new T(function(){return new T5(0,_T,_2m,_2o,_15,_1T);}),_2o=function(_2p){return new T2(0,_2n,_2p);},_2q=__Z,_2r=7,_2s=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2t=new T6(0,_2q,_2r,_v,_2s,_2q,_2q),_2u=new T(function(){return B(_2o(_2t));}),_2v=function(_){return new F(function(){return die(_2u);});},_2w=function(_2x){return E(E(_2x).a);},_2y=function(_2z,_2A,_2B,_){var _2C=__arr2lst(0,_2B),_2D=B(_K(_2C,_)),_2E=E(_2D);if(!_2E._){return new F(function(){return _2v(_);});}else{var _2F=E(_2E.b);if(!_2F._){return new F(function(){return _2v(_);});}else{if(!E(_2F.b)._){var _2G=B(A3(_2w,_2z,_2E.a,_)),_2H=B(A3(_2w,_2A,_2F.a,_));return new T2(0,_2G,_2H);}else{return new F(function(){return _2v(_);});}}}},_2I=function(_){return new F(function(){return __jsNull();});},_2J=function(_2K){var _2L=B(A1(_2K,_));return E(_2L);},_2M=new T(function(){return B(_2J(_2I));}),_2N=new T(function(){return E(_2M);}),_2O=function(_2P,_2Q,_){if(E(_2P)==7){var _2R=__app1(E(_u),_2Q),_2S=B(_2y(_J,_J,_2R,_)),_2T=__get(_2Q,E(_2)),_2U=__get(_2Q,E(_1)),_2V=__get(_2Q,E(_0));return new T(function(){return new T3(0,E(_2S),E(_2q),E(new T3(0,_2T,_2U,_2V)));});}else{var _2W=__app1(E(_u),_2Q),_2X=B(_2y(_J,_J,_2W,_)),_2Y=__get(_2Q,E(_t)),_2Z=__eq(_2Y,E(_2N));if(!E(_2Z)){var _30=__isUndef(_2Y);if(!E(_30)){var _31=B(_n(_2Y,_));return new T(function(){return new T3(0,E(_2X),E(new T1(1,_31)),E(_s));});}else{return new T(function(){return new T3(0,E(_2X),E(_2q),E(_s));});}}else{return new T(function(){return new T3(0,E(_2X),E(_2q),E(_s));});}}},_32=function(_33,_34,_){return new F(function(){return _2O(_33,E(_34),_);});},_35="mouseout",_36="mouseover",_37="mousemove",_38="mouseup",_39="mousedown",_3a="dblclick",_3b="click",_3c="wheel",_3d=function(_3e){switch(E(_3e)){case 0:return E(_3b);case 1:return E(_3a);case 2:return E(_39);case 3:return E(_38);case 4:return E(_37);case 5:return E(_36);case 6:return E(_35);default:return E(_3c);}},_3f=new T2(0,_3d,_32),_3g=function(_3h){return E(_3h);},_3i=function(_3j,_3k){return E(_3j)==E(_3k);},_3l=function(_3m,_3n){return E(_3m)!=E(_3n);},_3o=new T2(0,_3i,_3l),_3p="screenY",_3q="screenX",_3r="clientY",_3s="clientX",_3t="pageY",_3u="pageX",_3v="target",_3w="identifier",_3x=function(_3y,_){var _3z=__get(_3y,E(_3w)),_3A=__get(_3y,E(_3v)),_3B=__get(_3y,E(_3u)),_3C=__get(_3y,E(_3t)),_3D=__get(_3y,E(_3s)),_3E=__get(_3y,E(_3r)),_3F=__get(_3y,E(_3q)),_3G=__get(_3y,E(_3p));return new T(function(){var _3H=Number(_3z),_3I=jsTrunc(_3H);return new T5(0,_3I,_3A,E(new T2(0,new T(function(){var _3J=Number(_3B);return jsTrunc(_3J);}),new T(function(){var _3K=Number(_3C);return jsTrunc(_3K);}))),E(new T2(0,new T(function(){var _3L=Number(_3D);return jsTrunc(_3L);}),new T(function(){var _3M=Number(_3E);return jsTrunc(_3M);}))),E(new T2(0,new T(function(){var _3N=Number(_3F);return jsTrunc(_3N);}),new T(function(){var _3O=Number(_3G);return jsTrunc(_3O);}))));});},_3P=function(_3Q,_){var _3R=E(_3Q);if(!_3R._){return _v;}else{var _3S=B(_3x(E(_3R.a),_)),_3T=B(_3P(_3R.b,_));return new T2(1,_3S,_3T);}},_3U="touches",_3V=function(_3W){return E(E(_3W).b);},_3X=function(_3Y,_3Z,_){var _40=__arr2lst(0,_3Z),_41=new T(function(){return B(_3V(_3Y));}),_42=function(_43,_){var _44=E(_43);if(!_44._){return _v;}else{var _45=B(A2(_41,_44.a,_)),_46=B(_42(_44.b,_));return new T2(1,_45,_46);}};return new F(function(){return _42(_40,_);});},_47=function(_48,_){return new F(function(){return _3X(_J,E(_48),_);});},_49=new T2(0,_E,_47),_4a=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4b=function(_4c){return E(E(_4c).a);},_4d=function(_4e,_4f,_4g){while(1){var _4h=E(_4g);if(!_4h._){return false;}else{if(!B(A3(_4b,_4e,_4f,_4h.a))){_4g=_4h.b;continue;}else{return true;}}}},_4i=function(_4j,_4k){while(1){var _4l=B((function(_4m,_4n){var _4o=E(_4n);if(!_4o._){return __Z;}else{var _4p=_4o.a,_4q=_4o.b;if(!B(A1(_4m,_4p))){var _4r=_4m;_4j=_4r;_4k=_4q;return __continue;}else{return new T2(1,_4p,new T(function(){return B(_4i(_4m,_4q));}));}}})(_4j,_4k));if(_4l!=__continue){return _4l;}}},_4s=function(_4t,_){var _4u=__get(_4t,E(_3U)),_4v=__arr2lst(0,_4u),_4w=B(_3P(_4v,_)),_4x=__app1(E(_4a),_4t),_4y=B(_2y(_49,_49,_4x,_)),_4z=E(_4y),_4A=new T(function(){var _4B=function(_4C){return new F(function(){return _4d(_3o,new T(function(){return E(_4C).a;}),_4z.a);});};return B(_4i(_4B,_4w));}),_4D=new T(function(){var _4E=function(_4F){return new F(function(){return _4d(_3o,new T(function(){return E(_4F).a;}),_4z.b);});};return B(_4i(_4E,_4w));});return new T3(0,_4w,_4D,_4A);},_4G=function(_4H,_4I,_){return new F(function(){return _4s(E(_4I),_);});},_4J="touchcancel",_4K="touchend",_4L="touchmove",_4M="touchstart",_4N=function(_4O){switch(E(_4O)){case 0:return E(_4M);case 1:return E(_4L);case 2:return E(_4K);default:return E(_4J);}},_4P=new T2(0,_4N,_4G),_4Q=function(_4R,_4S,_){var _4T=B(A1(_4R,_)),_4U=B(A1(_4S,_));return _4T;},_4V=function(_4W,_4X,_){var _4Y=B(A1(_4W,_)),_4Z=B(A1(_4X,_));return new T(function(){return B(A1(_4Y,_4Z));});},_50=function(_51,_52,_){var _53=B(A1(_52,_));return _51;},_54=function(_55,_56,_){var _57=B(A1(_56,_));return new T(function(){return B(A1(_55,_57));});},_58=new T2(0,_54,_50),_59=function(_5a,_){return _5a;},_5b=function(_5c,_5d,_){var _5e=B(A1(_5c,_));return new F(function(){return A1(_5d,_);});},_5f=new T5(0,_58,_59,_4V,_5b,_4Q),_5g=new T(function(){return E(_2n);}),_5h=function(_5i){return E(E(_5i).c);},_5j=function(_5k){return new T6(0,_2q,_2r,_v,_5k,_2q,_2q);},_5l=function(_5m,_){var _5n=new T(function(){return B(A2(_5h,_5g,new T(function(){return B(A1(_5j,_5m));})));});return new F(function(){return die(_5n);});},_5o=function(_5p,_){return new F(function(){return _5l(_5p,_);});},_5q=function(_5r){return new F(function(){return A1(_5o,_5r);});},_5s=function(_5t,_5u,_){var _5v=B(A1(_5t,_));return new F(function(){return A2(_5u,_5v,_);});},_5w=new T5(0,_5f,_5s,_5b,_59,_5q),_5x=function(_5y){return E(_5y);},_5z=new T2(0,_5w,_5x),_5A=new T2(0,_5z,_59),_5B=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_5C=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_5D=new T(function(){return eval("(function(cv){return cv.height})");}),_5E=new T(function(){return eval("(function(cv){return cv.width})");}),_5F=function(_5G,_){var _5H=__app1(E(_5E),_5G),_5I=__app1(E(_5D),_5G),_5J=__app1(E(_5C),_5G),_5K=__app1(E(_5B),_5G);return new T2(0,new T2(0,_5H,_5I),new T2(0,_5J,_5K));},_5L=0,_5M=0,_5N=false,_5O=2,_5P=0,_5Q=true,_5R=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_5S=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_5T=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_5U=function(_5V){return E(E(_5V).b);},_5W=function(_5X,_5Y){return new F(function(){return A2(_5U,_5X,function(_){var _5Z=E(_5Y),_60=__app1(E(_5T),_5Z);if(!_60){return _2q;}else{var _61=__app1(E(_5S),_5Z);return new T1(1,new T2(0,_61,_5Z));}});});},_62=2,_63=1,_64=new T1(0,_63),_65=new T1(1,_64),_66=30,_67=100,_68=new T2(0,_67,_66),_69=new T2(1,_68,_v),_6a=370,_6b=200,_6c=80,_6d=new T4(0,_6c,_67,_6b,_6a),_6e=0,_6f=new T2(1,_6e,_v),_6g=new T(function(){return B(unCStr("\u3053\u3093\u306b\u3061\u306f\n\u5143\u6c23\u3067\u3059\u304b\uff1f"));}),_6h=new T2(1,_6g,_v),_6i=new T2(1,_63,_v),_6j=20,_6k=new T2(1,_6j,_v),_6l={_:0,a:0,b:E(_6d),c:E(_62),d:0,e:5,f:E(_69),g:E(_v),h:E(_6k),i:E(_6i),j:E(_6h),k:E(_6f),l:E(_v),m:E(_v),n:E(_2q),o:E(_65)},_6m=new T2(1,_6l,_v),_6n=new T5(0,E(_5N),E(_5N),E(_5N),E(_5N),E(_5N)),_6o={_:0,a:E(_2q),b:E(_2q),c:E(_2q),d:E(_6m),e:0,f:E(_6n),g:E(_v)},_6p=new T1(0,100),_6q=new T(function(){return B(unCStr("Pattern match failure in do expression at /home/yokop/Documents/haskell/haste/hotuma/Main.hs:16:3-9"));}),_6r=new T6(0,_2q,_2r,_v,_6q,_2q,_2q),_6s=new T(function(){return B(_2o(_6r));}),_6t=new T(function(){return B(unCStr("Pattern match failure in do expression at /home/yokop/Documents/haskell/haste/hotuma/Main.hs:17:3-8"));}),_6u=new T6(0,_2q,_2r,_v,_6t,_2q,_2q),_6v=new T(function(){return B(_2o(_6u));}),_6w=function(_6x,_6y,_6z){while(1){var _6A=E(_6z);if(!_6A._){return  -1;}else{var _6B=_6A.b,_6C=E(_6A.a),_6D=E(_6C.b),_6E=E(_6D.a);if(_6x<=_6E){_6z=_6B;continue;}else{if(_6x>=_6E+E(_6D.c)){_6z=_6B;continue;}else{var _6F=E(_6D.b);if(_6y<=_6F){_6z=_6B;continue;}else{if(_6y>=_6F+E(_6D.d)){_6z=_6B;continue;}else{return E(_6C.a);}}}}}}},_6G=function(_6H,_6I,_6J){while(1){var _6K=E(_6J);if(!_6K._){return  -1;}else{var _6L=_6K.b,_6M=E(_6K.a),_6N=E(_6M.b),_6O=E(_6N.a);if(_6H<=_6O){_6J=_6L;continue;}else{if(_6H>=_6O+E(_6N.c)){_6J=_6L;continue;}else{var _6P=E(_6I),_6Q=E(_6N.b);if(_6P<=_6Q){return new F(function(){return _6w(_6H,_6P,_6L);});}else{if(_6P>=_6Q+E(_6N.d)){return new F(function(){return _6w(_6H,_6P,_6L);});}else{return E(_6M.a);}}}}}}},_6R=function(_6S,_6T){while(1){var _6U=E(_6T);if(!_6U._){return __Z;}else{var _6V=E(_6U.a);if(_6S!=_6V.a){_6T=_6U.b;continue;}else{return new T1(1,_6V);}}}},_6W=new T(function(){return B(unCStr("!!: negative index"));}),_6X=new T(function(){return B(unCStr("Prelude."));}),_6Y=new T(function(){return B(_3(_6X,_6W));}),_6Z=new T(function(){return B(err(_6Y));}),_70=new T(function(){return B(unCStr("!!: index too large"));}),_71=new T(function(){return B(_3(_6X,_70));}),_72=new T(function(){return B(err(_71));}),_73=function(_74,_75){while(1){var _76=E(_74);if(!_76._){return E(_72);}else{var _77=E(_75);if(!_77){return E(_76.a);}else{_74=_76.b;_75=_77-1|0;continue;}}}},_78=function(_79,_7a){if(_7a>=0){return new F(function(){return _73(_79,_7a);});}else{return E(_6Z);}},_7b=function(_7c,_7d){var _7e=E(_7c);if(!_7e._){var _7f=E(_7d);if(!_7f._){return new F(function(){return _3i(_7e.a,_7f.a);});}else{return false;}}else{var _7g=E(_7d);if(!_7g._){return false;}else{return new F(function(){return _3i(_7e.a,_7g.a);});}}},_7h=function(_7i,_7j){return (E(_7i)==0)?(E(_7j)==0)?false:true:(E(_7j)==0)?true:false;},_7k=function(_7l,_7m){return (E(_7l)==0)?(E(_7m)==0)?true:false:(E(_7m)==0)?false:true;},_7n=new T2(0,_7k,_7h),_7o=function(_7p,_7q,_7r){while(1){var _7s=E(_7q);if(!_7s._){return (E(_7r)._==0)?true:false;}else{var _7t=E(_7r);if(!_7t._){return false;}else{if(!B(A3(_4b,_7p,_7s.a,_7t.a))){return false;}else{_7q=_7s.b;_7r=_7t.b;continue;}}}}},_7u=function(_7v,_7w){while(1){var _7x=E(_7v);if(!_7x._){return (E(_7w)._==0)?true:false;}else{var _7y=E(_7w);if(!_7y._){return false;}else{if(E(_7x.a)!=E(_7y.a)){return false;}else{_7v=_7x.b;_7w=_7y.b;continue;}}}}},_7z=function(_7A,_7B){while(1){var _7C=E(_7A);if(!_7C._){return (E(_7B)._==0)?true:false;}else{var _7D=E(_7B);if(!_7D._){return false;}else{if(E(_7C.a)!=E(_7D.a)){return false;}else{_7A=_7C.b;_7B=_7D.b;continue;}}}}},_7E=function(_7F,_7G){while(1){var _7H=E(_7F);if(!_7H._){return (E(_7G)._==0)?true:false;}else{var _7I=E(_7G);if(!_7I._){return false;}else{if(!B(_7z(_7H.a,_7I.a))){return false;}else{_7F=_7H.b;_7G=_7I.b;continue;}}}}},_7J=function(_7K,_7L,_7M,_7N){return (_7K!=_7M)?true:(E(_7L)!=E(_7N))?true:false;},_7O=function(_7P,_7Q){var _7R=E(_7P),_7S=E(_7Q);return new F(function(){return _7J(E(_7R.a),_7R.b,E(_7S.a),_7S.b);});},_7T=function(_7U,_7V){return E(_7U)==E(_7V);},_7W=function(_7X,_7Y,_7Z,_80){if(_7X!=_7Z){return false;}else{return new F(function(){return _7T(_7Y,_80);});}},_81=function(_82,_83){var _84=E(_82),_85=E(_83);return new F(function(){return _7W(E(_84.a),_84.b,E(_85.a),_85.b);});},_86=new T2(0,_81,_7O),_87=function(_88,_89,_8a,_8b,_8c,_8d,_8e,_8f,_8g,_8h,_8i,_8j,_8k,_8l,_8m,_8n,_8o,_8p,_8q,_8r,_8s,_8t,_8u,_8v,_8w,_8x,_8y,_8z,_8A,_8B,_8C,_8D,_8E,_8F,_8G,_8H){if(_88!=_8q){return false;}else{if(E(_89)!=E(_8r)){return false;}else{if(E(_8a)!=E(_8s)){return false;}else{if(E(_8b)!=E(_8t)){return false;}else{if(E(_8c)!=E(_8u)){return false;}else{var _8I=function(_8J){if(!B(_7o(_86,_8g,_8y))){return false;}else{if(!B(_7o(_86,_8h,_8z))){return false;}else{if(!B(_7u(_8i,_8A))){return false;}else{if(!B(_7u(_8j,_8B))){return false;}else{if(!B(_7E(_8k,_8C))){return false;}else{if(!B(_7o(_7n,_8l,_8D))){return false;}else{if(!B(_7o(_86,_8m,_8E))){return false;}else{if(!B(_7u(_8n,_8F))){return false;}else{var _8K=function(_8L){var _8M=E(_8p);switch(_8M._){case 0:return (E(_8H)._==0)?true:false;case 1:var _8N=E(_8H);if(_8N._==1){return new F(function(){return _7b(_8M.a,_8N.a);});}else{return false;}break;case 2:var _8O=E(_8H);if(_8O._==2){return new F(function(){return _3i(_8M.a,_8O.a);});}else{return false;}break;default:var _8P=E(_8H);if(_8P._==3){return new F(function(){return _3i(_8M.a,_8P.a);});}else{return false;}}},_8Q=E(_8o);if(!_8Q._){if(!E(_8G)._){return new F(function(){return _8K(_);});}else{return false;}}else{var _8R=E(_8G);if(!_8R._){return false;}else{if(E(_8Q.a)!=E(_8R.a)){return false;}else{return new F(function(){return _8K(_);});}}}}}}}}}}}};switch(E(_8d)){case 0:if(!E(_8v)){if(_8e!=_8w){return false;}else{if(_8f!=_8x){return false;}else{return new F(function(){return _8I(_);});}}}else{return false;}break;case 1:if(E(_8v)==1){if(_8e!=_8w){return false;}else{if(_8f!=_8x){return false;}else{return new F(function(){return _8I(_);});}}}else{return false;}break;default:if(E(_8v)==2){if(_8e!=_8w){return false;}else{if(_8f!=_8x){return false;}else{return new F(function(){return _8I(_);});}}}else{return false;}}}}}}}},_8S=function(_8T,_8U){var _8V=E(_8T),_8W=E(_8V.b),_8X=E(_8U),_8Y=E(_8X.b);return (!B(_87(_8V.a,_8W.a,_8W.b,_8W.c,_8W.d,_8V.c,_8V.d,_8V.e,_8V.f,_8V.g,_8V.h,_8V.i,_8V.j,_8V.k,_8V.l,_8V.m,_8V.n,_8V.o,_8X.a,_8Y.a,_8Y.b,_8Y.c,_8Y.d,_8X.c,_8X.d,_8X.e,_8X.f,_8X.g,_8X.h,_8X.i,_8X.j,_8X.k,_8X.l,_8X.m,_8X.n,_8X.o)))?true:false;},_8Z=function(_90,_91){var _92=E(_90),_93=E(_92.b),_94=E(_91),_95=E(_94.b);return new F(function(){return _87(_92.a,_93.a,_93.b,_93.c,_93.d,_92.c,_92.d,_92.e,_92.f,_92.g,_92.h,_92.i,_92.j,_92.k,_92.l,_92.m,_92.n,_92.o,_94.a,_95.a,_95.b,_95.c,_95.d,_94.c,_94.d,_94.e,_94.f,_94.g,_94.h,_94.i,_94.j,_94.k,_94.l,_94.m,_94.n,_94.o);});},_96=new T2(0,_8Z,_8S),_97=function(_98,_99){while(1){var _9a=E(_98);if(!_9a._){return (E(_99)._==0)?true:false;}else{var _9b=E(_99);if(!_9b._){return false;}else{if(E(_9a.a)!=E(_9b.a)){return false;}else{_98=_9a.b;_99=_9b.b;continue;}}}}},_9c=function(_9d,_9e,_9f,_9g,_9h,_9i,_9j,_9k,_9l,_9m,_9n,_9o,_9p,_9q,_9r,_9s,_9t,_9u,_9v,_9w,_9x,_9y){var _9z=function(_9A){var _9B=function(_9C){var _9D=function(_9E){if(_9h!=_9s){return false;}else{var _9F=function(_9G){var _9H=function(_9I){var _9J=function(_9K){return (!E(_9l))?(!E(_9w))?(!E(_9m))?(!E(_9x))?true:false:E(_9x):false:(!E(_9w))?false:(!E(_9m))?(!E(_9x))?true:false:E(_9x);};if(!E(_9k)){if(!E(_9v)){return new F(function(){return _9J(_);});}else{return false;}}else{if(!E(_9v)){return false;}else{return new F(function(){return _9J(_);});}}};if(!E(_9j)){if(!E(_9u)){return new F(function(){return _9H(_);});}else{return false;}}else{if(!E(_9u)){return false;}else{return new F(function(){return _9H(_);});}}};if(!E(_9i)){if(!E(_9t)){if(!B(_9F(_))){return false;}else{return new F(function(){return _97(_9n,_9y);});}}else{return false;}}else{if(!E(_9t)){return false;}else{if(!B(_9F(_))){return false;}else{return new F(function(){return _97(_9n,_9y);});}}}}},_9L=E(_9f);if(!_9L._){if(!E(_9q)._){if(!B(_7o(_96,_9g,_9r))){return false;}else{return new F(function(){return _9D(_);});}}else{return false;}}else{var _9M=E(_9q);if(!_9M._){return false;}else{if(E(_9L.a)!=E(_9M.a)){return false;}else{if(!B(_7o(_96,_9g,_9r))){return false;}else{return new F(function(){return _9D(_);});}}}}},_9N=E(_9e);if(!_9N._){if(!E(_9p)._){return new F(function(){return _9B(_);});}else{return false;}}else{var _9O=E(_9p);if(!_9O._){return false;}else{var _9P=E(_9N.a),_9Q=E(_9O.a);if(!B(_7E(_9P.a,_9Q.a))){return false;}else{if(!B(_7u(_9P.b,_9Q.b))){return false;}else{if(_9P.c!=_9Q.c){return false;}else{return new F(function(){return _9B(_);});}}}}}},_9R=E(_9d);if(!_9R._){if(!E(_9o)._){return new F(function(){return _9z(_);});}else{return false;}}else{var _9S=E(_9o);if(!_9S._){return false;}else{var _9T=_9S.a,_9U=E(_9R.a);if(!_9U._){var _9V=E(_9T);if(!_9V._){if(E(_9U.a)!=E(_9V.a)){return false;}else{return new F(function(){return _9z(_);});}}else{return false;}}else{var _9W=E(_9T);if(!_9W._){return false;}else{if(E(_9U.a)!=E(_9W.a)){return false;}else{return new F(function(){return _9z(_);});}}}}}},_9X=function(_9Y,_9Z){while(1){var _a0=E(_9Y);if(!_a0._){return E(_9Z);}else{var _a1=_9Z+1|0;_9Y=_a0.b;_9Z=_a1;continue;}}},_a2=function(_a3,_a4){while(1){var _a5=E(_a3);if(!_a5._){return E(_a4);}else{_a3=_a5.b;_a4=_a5.a;continue;}}},_a6=function(_a7,_a8,_a9){return new F(function(){return _a2(_a8,_a7);});},_aa=function(_ab,_ac){while(1){var _ad=E(_ac);if(!_ad._){return __Z;}else{var _ae=_ad.b,_af=E(_ab);if(_af==1){return E(_ae);}else{_ab=_af-1|0;_ac=_ae;continue;}}}},_ag=function(_ah,_ai,_aj){var _ak=new T2(1,_ah,new T(function(){var _al=_ai+1|0;if(_al>0){return B(_aa(_al,_aj));}else{return E(_aj);}}));if(0>=_ai){return E(_ak);}else{var _am=function(_an,_ao){var _ap=E(_an);if(!_ap._){return E(_ak);}else{var _aq=_ap.a,_ar=E(_ao);return (_ar==1)?new T2(1,_aq,_ak):new T2(1,_aq,new T(function(){return B(_am(_ap.b,_ar-1|0));}));}};return new F(function(){return _am(_aj,_ai);});}},_as=__Z,_at=function(_au,_av){while(1){var _aw=E(_au);if(!_aw._){return E(_av);}else{_au=_aw.b;_av=_aw.a;continue;}}},_ax=function(_ay,_az){var _aA=E(_az);return (_aA._==0)?__Z:new T2(1,_ay,new T(function(){return B(_ax(_aA.a,_aA.b));}));},_aB=new T(function(){return B(unCStr(": empty list"));}),_aC=function(_aD){return new F(function(){return err(B(_3(_6X,new T(function(){return B(_3(_aD,_aB));},1))));});},_aE=new T(function(){return B(unCStr("init"));}),_aF=new T(function(){return B(_aC(_aE));}),_aG=new T(function(){return B(unCStr("last"));}),_aH=new T(function(){return B(_aC(_aG));}),_aI=new T(function(){return B(unCStr("base"));}),_aJ=new T(function(){return B(unCStr("Control.Exception.Base"));}),_aK=new T(function(){return B(unCStr("PatternMatchFail"));}),_aL=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_aI,_aJ,_aK),_aM=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_aL,_v,_v),_aN=function(_aO){return E(_aM);},_aP=function(_aQ){var _aR=E(_aQ);return new F(function(){return _X(B(_V(_aR.a)),_aN,_aR.b);});},_aS=function(_aT){return E(E(_aT).a);},_aU=function(_aV){return new T2(0,_aW,_aV);},_aX=function(_aY,_aZ){return new F(function(){return _3(E(_aY).a,_aZ);});},_b0=function(_b1,_b2){return new F(function(){return _28(_aX,_b1,_b2);});},_b3=function(_b4,_b5,_b6){return new F(function(){return _3(E(_b5).a,_b6);});},_b7=new T3(0,_b3,_aS,_b0),_aW=new T(function(){return new T5(0,_aN,_b7,_aU,_aP,_aS);}),_b8=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_b9=function(_ba,_bb){return new F(function(){return die(new T(function(){return B(A2(_5h,_bb,_ba));}));});},_bc=function(_bd,_be){return new F(function(){return _b9(_bd,_be);});},_bf=function(_bg,_bh){var _bi=E(_bh);if(!_bi._){return new T2(0,_v,_v);}else{var _bj=_bi.a;if(!B(A1(_bg,_bj))){return new T2(0,_v,_bi);}else{var _bk=new T(function(){var _bl=B(_bf(_bg,_bi.b));return new T2(0,_bl.a,_bl.b);});return new T2(0,new T2(1,_bj,new T(function(){return E(E(_bk).a);})),new T(function(){return E(E(_bk).b);}));}}},_bm=32,_bn=new T(function(){return B(unCStr("\n"));}),_bo=function(_bp){return (E(_bp)==124)?false:true;},_bq=function(_br,_bs){var _bt=B(_bf(_bo,B(unCStr(_br)))),_bu=_bt.a,_bv=function(_bw,_bx){var _by=new T(function(){var _bz=new T(function(){return B(_3(_bs,new T(function(){return B(_3(_bx,_bn));},1)));});return B(unAppCStr(": ",_bz));},1);return new F(function(){return _3(_bw,_by);});},_bA=E(_bt.b);if(!_bA._){return new F(function(){return _bv(_bu,_v);});}else{if(E(_bA.a)==124){return new F(function(){return _bv(_bu,new T2(1,_bm,_bA.b));});}else{return new F(function(){return _bv(_bu,_v);});}}},_bB=function(_bC){return new F(function(){return _bc(new T1(0,new T(function(){return B(_bq(_bC,_b8));})),_aW);});},_bD=new T(function(){return B(_bB("Events.hs:79:7-27|(hco : tlCos)"));}),_bE=0,_bF=new T1(1,_bE),_bG=120,_bH=40,_bI=new T2(1,_bH,_v),_bJ=new T(function(){return B(unCStr("\u305b\u3044\u304b\u3044\uff01"));}),_bK=new T2(1,_bJ,_v),_bL=1,_bM=new T1(1,_bL),_bN=new T1(0,_bL),_bO=new T(function(){return B(unCStr("\u306f"));}),_bP=new T(function(){return B(unCStr("\u3065"));}),_bQ=new T(function(){return B(unCStr("\u308c"));}),_bR=new T2(1,_bQ,_v),_bS=new T2(1,_bP,_bR),_bT=new T2(1,_bO,_bS),_bU=function(_bV,_bW,_bX,_bY,_bZ,_c0,_c1,_c2,_c3){var _c4=function(_c5){if(_c5!=_bW){var _c6=new T(function(){var _c7=E(_c0);if(!_c7._){return E(_bD);}else{return new T2(0,_c7.a,_c7.b);}}),_c8=new T(function(){var _c9=function(_ca){var _cb=new T(function(){return E(E(_c6).b);}),_cc=new T(function(){var _cd=B(_at(_cb,_aH));return {_:0,a:_cd.a,b:E(_cd.b),c:E(_cd.c),d:_cd.d,e:_cd.e,f:E(_cd.f),g:E(_cd.g),h:E(_cd.h),i:E(_cd.i),j:E(_bT),k:E(_cd.k),l:E(_cd.l),m:E(_cd.m),n:E(_cd.n),o:E(new T1(1,new T(function(){var _ce=E(_bX);if(!_ce._){return E(_bN);}else{return E(_ce.a);}})))};}),_cf=function(_cg){var _ch=E(_cg);return (_ch._==0)?E(new T2(1,_cc,_v)):new T2(1,new T(function(){var _ci=E(_ch.a);return {_:0,a:_ci.a,b:E(_ci.b),c:E(_ci.c),d:_ci.d,e:_ci.e,f:E(_ci.f),g:E(_ci.g),h:E(_ci.h),i:E(_ci.i),j:E(_ci.j),k:E(_ci.k),l:E(_ci.l),m:E(_ci.m),n:E(_ci.n),o:E(_as)};}),new T(function(){return B(_cf(_ch.b));}));},_cj=new T(function(){var _ck=E(_cb);if(!_ck._){return E(_aF);}else{return B(_ax(_ck.a,_ck.b));}}),_cl=new T(function(){return B(_ag(new T(function(){var _cm=B(_78(_cj,_bW));return {_:0,a:_cm.a,b:E(_cm.b),c:E(_cm.c),d:3,e:_cm.e,f:E(_cm.f),g:E(_cm.g),h:E(_cm.h),i:E(_cm.i),j:E(_cm.j),k:E(_cm.k),l:E(_cm.l),m:E(_cm.m),n:E(_cm.n),o:E(_cm.o)};}),_bW,_cj));});return new F(function(){return _cf(B(_ag(new T(function(){var _cn=B(_78(_cj,_ca));return {_:0,a:_cn.a,b:E(_cn.b),c:E(_cn.c),d:4,e:_cn.e,f:E(_cn.f),g:E(_cn.g),h:E(_cn.h),i:E(_cn.i),j:E(_cn.j),k:E(_cn.k),l:E(_cn.l),m:E(_cn.m),n:E(_cn.n),o:E(_cn.o)};}),_ca,_cl)));});},_co=E(_bY);if(!_co._){return B(_c9(0));}else{return B(_c9(E(_co.a).c));}});return {_:0,a:_bX,b:_bY,c:_bM,d:new T2(1,new T(function(){return E(E(_c6).a);}),_c8),e:_c1,f:_c2,g:_c3};}else{var _cp=E(_bV),_cq=_cp.a,_cr=_cp.b,_cs=E(_c0);if(!_cs._){var _ct=E(_aF);}else{var _cu=_cs.a,_cv=_cs.b,_cw=new T(function(){var _cx=B(_a6(_cu,_cv,_aH)),_cy=new T(function(){return E(_cq)/3;}),_cz=new T(function(){return E(_cr)/6;}),_cA=new T(function(){var _cB=E(_bX);if(!_cB._){return E(_bN);}else{var _cC=E(_cB.a);if(!_cC._){return new T1(0,new T(function(){return E(_cC.a)+1|0;}));}else{return new T1(1,new T(function(){return E(_cC.a)+1|0;}));}}});return {_:0,a:_cx.a,b:E(new T4(0,_cy,_cz,new T(function(){var _cD=E(_cy);return E(_cq)-(_cD+_cD);}),new T(function(){var _cE=E(_cz);return E(_cr)-(_cE+_cE);}))),c:E(_cx.c),d:_cx.d,e:_cx.e,f:E(new T2(1,new T2(0,new T(function(){return E(_cq)/2-E(_cy)-20;}),_bG),_v)),g:E(_cx.g),h:E(_bI),i:E(_cx.i),j:E(_bK),k:E(_cx.k),l:E(_cx.l),m:E(_cx.m),n:E(_cx.n),o:E(new T1(1,_cA))};}),_cF=function(_cG){var _cH=E(_cG);return (_cH._==0)?E(new T2(1,_cw,_v)):new T2(1,new T(function(){var _cI=E(_cH.a);return {_:0,a:_cI.a,b:E(_cI.b),c:E(_cI.c),d:_cI.d,e:_cI.e,f:E(_cI.f),g:E(_cI.g),h:E(_cI.h),i:E(_cI.i),j:E(_cI.j),k:E(_cI.k),l:E(_cI.l),m:E(_cI.m),n:E(_cI.n),o:E(_as)};}),new T(function(){return B(_cF(_cH.b));}));},_ct=B(_cF(B(_ax(_cu,_cv))));}return {_:0,a:_bX,b:_bY,c:_bF,d:_ct,e:_c1,f:_c2,g:_c3};}},_cJ=E(_bY);if(!_cJ._){return new F(function(){return _c4(0);});}else{return new F(function(){return _c4(E(_cJ.a).c);});}},_cK=new T2(1,_6e,_v),_cL=new T2(1,_6e,_cK),_cM=new T2(1,_6e,_cL),_cN=5,_cO=new T2(1,_cN,_v),_cP=new T2(1,_cN,_cO),_cQ=new T2(1,_cN,_cP),_cR=50,_cS=new T2(1,_cR,_v),_cT=new T2(1,_cR,_cS),_cU=new T2(1,_cR,_cT),_cV=new T(function(){return B(unCStr("\u3075"));}),_cW=new T2(1,_cV,_v),_cX=new T(function(){return B(unCStr("\u305f"));}),_cY=new T2(1,_cX,_cW),_cZ=new T(function(){return B(unCStr("\u3053"));}),_d0=new T2(1,_cZ,_cY),_d1=50,_d2=function(_d3,_d4,_d5,_d6){var _d7=new T(function(){return E(_d3)/8*3-20;}),_d8=new T(function(){return E(_d3)/8;});return {_:0,a:_d5,b:E(new T4(0,_d8,new T(function(){var _d9=E(_d4);return _d9-_d9/6;}),new T(function(){var _da=E(_d8);return E(_d3)-(_da+_da);}),new T(function(){return E(_d4)/8;}))),c:E(_62),d:1,e:6,f:E(new T2(1,new T2(0,new T(function(){return E(_d7)-50;}),_d1),new T2(1,new T2(0,_d7,_d1),new T2(1,new T2(0,new T(function(){return E(_d7)+50;}),_d1),_v)))),g:E(_v),h:E(_cU),i:E(_cQ),j:E(_d0),k:E(_cM),l:E(_v),m:E(_v),n:E(_2q),o:E(new T1(3,_d6))};},_db=function(_dc){var _dd=E(_dc);return {_:0,a:_dd.a,b:E(_dd.b),c:E(_dd.c),d:0,e:7,f:E(_dd.f),g:E(_dd.g),h:E(_dd.h),i:E(_dd.i),j:E(_dd.j),k:E(_dd.k),l:E(_dd.l),m:E(_dd.m),n:E(_dd.n),o:E(_dd.o)};},_de=new T(function(){return B(_bB("Events.hs:26:7-27|(hco : chCos)"));}),_df=function(_dg,_dh){var _di=E(_dh);return (_di._==0)?__Z:new T2(1,new T(function(){return B(A1(_dg,_di.a));}),new T(function(){return B(_df(_dg,_di.b));}));},_dj=function(_dk,_dl,_dm,_dn,_do,_dp,_dq,_dr,_ds,_dt){var _du=new T(function(){var _dv=E(_dq);if(!_dv._){return E(_de);}else{return new T2(0,_dv.a,_dv.b);}}),_dw=new T(function(){var _dx=function(_dy){var _dz=E(_dm),_dA=new T(function(){return E(E(_du).b);}),_dB=B(_ag(new T(function(){var _dC=B(_78(_dA,_dz));return {_:0,a:_dC.a,b:E(_dC.b),c:E(_dC.c),d:4,e:8,f:E(_dC.f),g:E(_dC.g),h:E(_dC.h),i:E(_dC.i),j:E(_dC.j),k:E(_dC.k),l:E(_dC.l),m:E(_dC.m),n:E(_dC.n),o:E(_dC.o)};}),_dz,new T(function(){return B(_df(_db,_dA));})));if((_dy+1|0)!=E(_dl)){var _dD=E(_dB);if(!_dD._){return E(_aF);}else{return new F(function(){return _3(B(_ax(_dD.a,_dD.b)),new T2(1,new T(function(){var _dE=E(_dk);return B(_d2(_dE.a,_dE.b,_dy+1|0,_dz));}),_v));});}}else{return new F(function(){return _3(_dB,new T2(1,new T(function(){var _dF=E(_dk);return B(_d2(_dF.a,_dF.b,_dy+1|0,_dz));}),_v));});}},_dG=E(_do);if(!_dG._){return B(_dx(0));}else{return B(_dx(B(_9X(E(_dG.a).a,0))));}});return {_:0,a:_dn,b:_do,c:_dp,d:new T2(1,new T(function(){return E(E(_du).a);}),_dw),e:_dr,f:_ds,g:_dt};},_dH=function(_){return _5L;},_dI=function(_dJ){return E(E(_dJ).a);},_dK=function(_dL){return E(E(_dL).a);},_dM=new T1(1,_5N),_dN="false",_dO=new T1(1,_5Q),_dP="true",_dQ=function(_dR){var _dS=strEq(_dR,E(_dP));if(!E(_dS)){var _dT=strEq(_dR,E(_dN));return (E(_dT)==0)?__Z:E(_dM);}else{return E(_dO);}},_dU=2,_dV=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_dW="paused",_dX="ended",_dY=function(_dZ,_e0){var _e1=function(_){var _e2=E(_e0),_e3=E(_dV),_e4=__app2(_e3,_e2,E(_dX)),_e5=String(_e4),_e6=function(_e7){var _e8=__app2(_e3,_e2,E(_dW));return new T(function(){var _e9=String(_e8),_ea=B(_dQ(_e9));if(!_ea._){return 0;}else{if(!E(_ea.a)){return 0;}else{return 1;}}});},_eb=B(_dQ(_e5));if(!_eb._){return new F(function(){return _e6(_);});}else{if(!E(_eb.a)){return new F(function(){return _e6(_);});}else{return _dU;}}};return new F(function(){return A2(_5U,_dZ,_e1);});},_ec="duration",_ed=new T(function(){return eval("(function(e,t) {e.currentTime = t;})");}),_ee=function(_ef,_eg,_eh){var _ei=new T(function(){var _ej=E(_eh);switch(_ej._){case 0:return function(_){var _ek=__app2(E(_ed),E(_eg),0);return new F(function(){return _dH(_);});};break;case 1:return function(_){var _el=E(_eg),_em=__app2(E(_dV),_el,E(_ec)),_en=String(_em),_eo=Number(_en),_ep=isDoubleNaN(_eo);if(!E(_ep)){var _eq=__app2(E(_ed),_el,_eo);return new F(function(){return _dH(_);});}else{var _er=__app2(E(_ed),_el,0);return new F(function(){return _dH(_);});}};break;default:return function(_){var _es=__app2(E(_ed),E(_eg),E(_ej.a));return new F(function(){return _dH(_);});};}});return new F(function(){return A2(_5U,_ef,_ei);});},_et=function(_eu){return E(E(_eu).c);},_ev=function(_ew){return E(E(_ew).b);},_ex=__Z,_ey=new T(function(){return eval("(function(x){x.play();})");}),_ez=function(_eA){return E(E(_eA).b);},_eB=function(_eC,_eD){var _eE=new T(function(){return B(_ee(_eC,_eD,_ex));}),_eF=B(_dK(_eC)),_eG=new T(function(){return B(A2(_ez,B(_dI(_eF)),_5L));}),_eH=new T(function(){var _eI=function(_){var _eJ=__app1(E(_ey),E(_eD));return new F(function(){return _dH(_);});};return B(A2(_5U,_eC,_eI));}),_eK=function(_eL){return new F(function(){return A3(_et,_eF,new T(function(){if(E(_eL)==2){return E(_eE);}else{return E(_eG);}}),_eH);});};return new F(function(){return A3(_ev,_eF,new T(function(){return B(_dY(_eC,_eD));}),_eK);});},_eM=new T(function(){return eval("(function(e){e.width = e.width;})");}),_eN=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_eO=function(_eP,_eQ,_eR){var _eS=new T(function(){return toJSStr(E(_eR));});return function(_eT,_){var _eU=__app4(E(_eN),E(_eT),E(_eS),E(_eP),E(_eQ));return new F(function(){return _dH(_);});};},_eV=0,_eW=new T(function(){return B(_eO(_eV,_eV,_v));}),_eX=function(_eY,_eZ){return E(_eY)!=E(_eZ);},_f0=function(_f1,_f2){return E(_f1)==E(_f2);},_f3=new T2(0,_f0,_eX),_f4=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_f5=new T(function(){return eval("(function(ctx){ctx.save();})");}),_f6=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_f7=function(_f8,_f9,_fa,_){var _fb=__app1(E(_f5),_fa),_fc=__app2(E(_f6),_fa,E(_f8)),_fd=B(A2(_f9,_fa,_)),_fe=__app1(E(_f4),_fa);return new F(function(){return _dH(_);});},_ff=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_fg=function(_fh,_fi,_fj,_fk,_){var _fl=__app1(E(_f5),_fk),_fm=__app3(E(_ff),_fk,E(_fh),E(_fi)),_fn=B(A2(_fj,_fk,_)),_fo=__app1(E(_f4),_fk);return new F(function(){return _dH(_);});},_fp=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_fq=function(_fr,_fs,_ft,_fu,_){var _fv=__app1(E(_f5),_fu),_fw=__app3(E(_fp),_fu,E(_fr),E(_fs)),_fx=B(A2(_ft,_fu,_)),_fy=__app1(E(_f4),_fu);return new F(function(){return _dH(_);});},_fz=new T(function(){return eval("(function(ctx,i,x,y){ctx.drawImage(i,x,y);})");}),_fA=function(_fB,_fC,_fD,_fE,_){var _fF=__app4(E(_fz),_fE,_fB,_fC,_fD);return new F(function(){return _dH(_);});},_fG=function(_fH,_fI,_fJ){var _fK=E(_fJ);return (_fK._==0)?0:(!B(A3(_4b,_fH,_fI,_fK.a)))?1+B(_fG(_fH,_fI,_fK.b))|0:0;},_fL=",",_fM="rgba(",_fN=new T(function(){return toJSStr(_v);}),_fO="rgb(",_fP=")",_fQ=new T2(1,_fP,_v),_fR=function(_fS){var _fT=E(_fS);if(!_fT._){var _fU=jsCat(new T2(1,_fO,new T2(1,new T(function(){return String(_fT.a);}),new T2(1,_fL,new T2(1,new T(function(){return String(_fT.b);}),new T2(1,_fL,new T2(1,new T(function(){return String(_fT.c);}),_fQ)))))),E(_fN));return E(_fU);}else{var _fV=jsCat(new T2(1,_fM,new T2(1,new T(function(){return String(_fT.a);}),new T2(1,_fL,new T2(1,new T(function(){return String(_fT.b);}),new T2(1,_fL,new T2(1,new T(function(){return String(_fT.c);}),new T2(1,_fL,new T2(1,new T(function(){return String(_fT.d);}),_fQ)))))))),E(_fN));return E(_fV);}},_fW="strokeStyle",_fX="fillStyle",_fY=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_fZ=function(_g0,_g1){var _g2=new T(function(){return B(_fR(_g0));});return function(_g3,_){var _g4=E(_g3),_g5=E(_fX),_g6=E(_dV),_g7=__app2(_g6,_g4,_g5),_g8=E(_fW),_g9=__app2(_g6,_g4,_g8),_ga=E(_g2),_gb=E(_fY),_gc=__app3(_gb,_g4,_g5,_ga),_gd=__app3(_gb,_g4,_g8,_ga),_ge=B(A2(_g1,_g4,_)),_gf=String(_g7),_gg=__app3(_gb,_g4,_g5,_gf),_gh=String(_g9),_gi=__app3(_gb,_g4,_g8,_gh);return new F(function(){return _dH(_);});};},_gj="font",_gk=function(_gl,_gm){var _gn=new T(function(){return toJSStr(E(_gl));});return function(_go,_){var _gp=E(_go),_gq=E(_gj),_gr=__app2(E(_dV),_gp,_gq),_gs=E(_fY),_gt=__app3(_gs,_gp,_gq,E(_gn)),_gu=B(A2(_gm,_gp,_)),_gv=String(_gr),_gw=__app3(_gs,_gp,_gq,_gv);return new F(function(){return _dH(_);});};},_gx=0,_gy=new T(function(){return B(unCStr("px IPAGothic"));}),_gz=new T(function(){return B(unCStr("\u3042\u3044\u3046\u3048\u304axkhnmtrsy \u304b\u306f\u306a\u307e\u304d\u3072\u306b\u307f\u304f\u3075\u306c\u3080\u3051\u3078\u306d\u3081\u3053\u307b\u306e\u3082\u3068\u308d\u305d\u3088\u3092\u3066\u308c\u305b\u3091\u3064\u308b\u3059\u3086\u3093\u3061\u308a\u3057\u3090\u305f\u3089\u3055\u3084\u308f\u309b\u963f\u548c\u5b87\u543e\u4ed8\u9808\u88ab\u610f\u767e\u96c4\u9593\u6ce2\u304c9\u7a42\u305e\u8a71\u8449\u3056\u3050\u3073\u7dd2\u30693\u305a\u3070\u3076\u304e\u3079\u88dc\u82bd1\u5e9c\u5834\u3058\u500b\u6211\u3054\u56f3\u6642\u66fe\u706b\u65e5\u3060\u5ea7\u7fbd4\u99ac\u90e8\u7956\u7089\u5177\u8a9e\u3065\u5f8c\u5b50\u7537\u3067\u305c\u51fa\u88f3\u7f8e"));}),_gA=function(_gB,_gC,_gD,_gE,_gF,_gG,_gH,_gI,_gJ,_gK,_){var _gL=E(_gK);if(!_gL._){return _5L;}else{var _gM=_gL.b,_gN=E(_gG),_gO=_gN.b,_gP=E(_gJ),_gQ=_gP.a,_gR=_gP.b,_gS=E(_gL.a),_gT=new T(function(){return E(_gF);});if(E(_gS)==13){return new F(function(){return _gU(_gB,_gC,_gD,_gE,_gF,_gN.a,_gO,_gH,0,new T(function(){return E(_gQ)-E(_gT)*1.2;}),_gH,_gM,_);});}else{var _gV=function(_){var _gW=new T(function(){return E(_gT)*1.1;}),_gX=new T(function(){var _gY=E(_gI),_gZ=E(_gO)/E(_gW),_h0=_gZ&4294967295;if(_gZ>=_h0){return (_gY+1|0)>(_h0-2|0);}else{return (_gY+1|0)>((_h0-1|0)-2|0);}});return new F(function(){return _gA(_gB,_gC,_gD,_gE,_gF,_gN,_gH,new T(function(){if(!E(_gX)){return E(_gI)+1|0;}else{return E(_gx);}}),new T2(0,new T(function(){if(!E(_gX)){return E(_gQ);}else{return E(_gQ)-E(_gT)*1.2;}}),new T(function(){if(!E(_gX)){return E(_gR)+E(_gW);}else{return E(_gH);}})),_gM,_);});};if(!E(_gE)){var _h1=new T(function(){var _h2=new T(function(){return B(_eO(_eV,_eV,new T2(1,_gS,_v)));}),_h3=function(_h4,_){return new F(function(){return _f7(_eV,_h2,E(_h4),_);});};return B(_gk(new T(function(){return B(_3(B(_d(0,E(_gF),_v)),_gy));},1),function(_h5,_){return new F(function(){return _fq(_gQ,_gR,_h3,E(_h5),_);});}));}),_h6=B(A(_fZ,[_gD,_h1,E(_gB).a,_]));return new F(function(){return _gV(_);});}else{var _h7=new T(function(){return E(_gF)/20;}),_h8=function(_h9,_){return new F(function(){return _fg(_h7,_h7,function(_ha,_){if(!B(_4d(_f3,_gS,_gz))){return new F(function(){return _fA(B(_78(_gC,14)),0,0,E(_ha),_);});}else{return new F(function(){return _fA(B(_78(_gC,B(_fG(_f3,_gS,_gz)))),0,0,E(_ha),_);});}},E(_h9),_);});},_hb=B(_fq(new T(function(){return E(_gQ)-E(_gT)/6;},1),new T(function(){return E(_gR)-E(_gT)*3/4;},1),_h8,E(_gB).a,_));return new F(function(){return _gV(_);});}}}},_gU=function(_hc,_hd,_he,_hf,_hg,_hh,_hi,_hj,_hk,_hl,_hm,_hn,_){while(1){var _ho=B((function(_hp,_hq,_hr,_hs,_ht,_hu,_hv,_hw,_hx,_hy,_hz,_hA,_){var _hB=E(_hA);if(!_hB._){return _5L;}else{var _hC=_hB.b,_hD=E(_hB.a),_hE=new T(function(){return E(_ht);});if(E(_hD)==13){var _hF=_hp,_hG=_hq,_hH=_hr,_hI=_hs,_hJ=_ht,_hK=_hu,_hL=_hv,_hM=_hw,_hN=_hw;_hc=_hF;_hd=_hG;_he=_hH;_hf=_hI;_hg=_hJ;_hh=_hK;_hi=_hL;_hj=_hM;_hk=0;_hl=new T(function(){return E(_hy)-E(_hE)*1.2;});_hm=_hN;_hn=_hC;return __continue;}else{var _hO=function(_){var _hP=new T(function(){return E(_hE)*1.1;}),_hQ=new T(function(){var _hR=E(_hv)/E(_hP),_hS=_hR&4294967295;if(_hR>=_hS){return (_hx+1|0)>(_hS-2|0);}else{return (_hx+1|0)>((_hS-1|0)-2|0);}});return new F(function(){return _gA(_hp,_hq,_hr,_hs,_ht,new T2(0,_hu,_hv),_hw,new T(function(){if(!E(_hQ)){return _hx+1|0;}else{return E(_gx);}}),new T2(0,new T(function(){if(!E(_hQ)){return E(_hy);}else{return E(_hy)-E(_hE)*1.2;}}),new T(function(){if(!E(_hQ)){return E(_hz)+E(_hP);}else{return E(_hw);}})),_hC,_);});};if(!E(_hs)){var _hT=new T(function(){var _hU=new T(function(){return B(_eO(_eV,_eV,new T2(1,_hD,_v)));}),_hV=function(_hW,_){return new F(function(){return _f7(_eV,_hU,E(_hW),_);});};return B(_gk(new T(function(){return B(_3(B(_d(0,E(_ht),_v)),_gy));},1),function(_hX,_){return new F(function(){return _fq(_hy,_hz,_hV,E(_hX),_);});}));}),_hY=B(A(_fZ,[_hr,_hT,E(_hp).a,_]));return new F(function(){return _hO(_);});}else{var _hZ=new T(function(){return E(_ht)/20;}),_i0=function(_i1,_){return new F(function(){return _fg(_hZ,_hZ,function(_i2,_){if(!B(_4d(_f3,_hD,_gz))){return new F(function(){return _fA(B(_78(_hq,14)),0,0,E(_i2),_);});}else{return new F(function(){return _fA(B(_78(_hq,B(_fG(_f3,_hD,_gz)))),0,0,E(_i2),_);});}},E(_i1),_);});},_i3=B(_fq(new T(function(){return E(_hy)-E(_hE)/6;},1),new T(function(){return E(_hz)-E(_hE)*3/4;},1),_i0,E(_hp).a,_));return new F(function(){return _hO(_);});}}}})(_hc,_hd,_he,_hf,_hg,_hh,_hi,_hj,_hk,_hl,_hm,_hn,_));if(_ho!=__continue){return _ho;}}},_i4=function(_i5,_i6,_i7,_i8,_i9,_ia,_ib,_ic,_id,_ie,_if,_ig,_ih,_){while(1){var _ii=B((function(_ij,_ik,_il,_im,_in,_io,_ip,_iq,_ir,_is,_it,_iu,_iv,_){var _iw=E(_iv);if(!_iw._){return _5L;}else{var _ix=_iw.b,_iy=E(_iw.a),_iz=new T(function(){return E(_io);});if(E(_iy)==13){var _iA=_ij,_iB=_ik,_iC=_il,_iD=_im,_iE=_in,_iF=_io,_iG=_ip,_iH=_iq,_iI=_ir,_iJ=_ir;_i5=_iA;_i6=_iB;_i7=_iC;_i8=_iD;_i9=_iE;_ia=_iF;_ib=_iG;_ic=_iH;_id=_iI;_ie=0;_if=new T(function(){return E(_it)-E(_iz)*1.2;});_ig=_iJ;_ih=_ix;return __continue;}else{var _iK=function(_){var _iL=new T(function(){return E(_iz)*1.1;}),_iM=new T(function(){var _iN=E(_iq)/E(_iL),_iO=_iN&4294967295;if(_iN>=_iO){return (_is+1|0)>(_iO-2|0);}else{return (_is+1|0)>((_iO-1|0)-2|0);}});return new F(function(){return _gA(new T2(0,_ij,_ik),_il,_im,_in,_io,new T2(0,_ip,_iq),_ir,new T(function(){if(!E(_iM)){return _is+1|0;}else{return E(_gx);}}),new T2(0,new T(function(){if(!E(_iM)){return E(_it);}else{return E(_it)-E(_iz)*1.2;}}),new T(function(){if(!E(_iM)){return E(_iu)+E(_iL);}else{return E(_ir);}})),_ix,_);});};if(!E(_in)){var _iP=new T(function(){var _iQ=new T(function(){return B(_eO(_eV,_eV,new T2(1,_iy,_v)));}),_iR=function(_iS,_){return new F(function(){return _f7(_eV,_iQ,E(_iS),_);});};return B(_gk(new T(function(){return B(_3(B(_d(0,E(_io),_v)),_gy));},1),function(_iT,_){return new F(function(){return _fq(_it,_iu,_iR,E(_iT),_);});}));}),_iU=B(A(_fZ,[_im,_iP,_ij,_]));return new F(function(){return _iK(_);});}else{var _iV=new T(function(){return E(_io)/20;}),_iW=function(_iX,_){return new F(function(){return _fg(_iV,_iV,function(_iY,_){if(!B(_4d(_f3,_iy,_gz))){return new F(function(){return _fA(B(_78(_il,14)),0,0,E(_iY),_);});}else{return new F(function(){return _fA(B(_78(_il,B(_fG(_f3,_iy,_gz)))),0,0,E(_iY),_);});}},E(_iX),_);});},_iZ=B(_fq(new T(function(){return E(_it)-E(_iz)/6;},1),new T(function(){return E(_iu)-E(_iz)*3/4;},1),_iW,_ij,_));return new F(function(){return _iK(_);});}}}})(_i5,_i6,_i7,_i8,_i9,_ia,_ib,_ic,_id,_ie,_if,_ig,_ih,_));if(_ii!=__continue){return _ii;}}},_j0=new T(function(){return eval("(function(ctx, x, y, radius, fromAngle, toAngle){ctx.arc(x, y, radius, fromAngle, toAngle);})");}),_j1=function(_j2,_j3,_j4,_j5,_j6,_j7,_){var _j8=__apply(E(_j0),new T2(1,_j6,new T2(1,_j5,new T2(1,_j4,new T2(1,_j3,new T2(1,_j2,new T2(1,_j7,_v)))))));return new F(function(){return _dH(_);});},_j9=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_ja=new T(function(){return eval("(function(ctx,x,y){ctx.lineTo(x,y);})");}),_jb=function(_jc,_jd,_){var _je=E(_jc);if(!_je._){return _5L;}else{var _jf=E(_je.a),_jg=E(_jd),_jh=__app3(E(_j9),_jg,E(_jf.a),E(_jf.b)),_ji=E(_je.b);if(!_ji._){return _5L;}else{var _jj=E(_ji.a),_jk=E(_ja),_jl=__app3(_jk,_jg,E(_jj.a),E(_jj.b)),_jm=function(_jn,_){while(1){var _jo=E(_jn);if(!_jo._){return _5L;}else{var _jp=E(_jo.a),_jq=__app3(_jk,_jg,E(_jp.a),E(_jp.b));_jn=_jo.b;continue;}}};return new F(function(){return _jm(_ji.b,_);});}}},_jr=function(_js,_jt,_ju,_jv,_jw,_){var _jx=B(_j1(_js+_ju-10,_jt+_jv-10,10,0,1.5707963267948966,_jw,_)),_jy=B(_j1(_js+10,_jt+_jv-10,10,1.5707963267948966,3.141592653589793,_jw,_)),_jz=B(_j1(_js+10,_jt+10,10,3.141592653589793,4.71238898038469,_jw,_)),_jA=B(_j1(_js+_ju-10,_jt+10,10,4.71238898038469,6.283185307179586,_jw,_));return new F(function(){return _jb(new T2(1,new T2(0,_js+_ju,_jt+_jv-10),new T2(1,new T2(0,_js+_ju,_jt+10),_v)),_jw,_);});},_jB=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_jC=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_jD=function(_jE,_jF,_){var _jG=__app1(E(_jB),_jF),_jH=B(A2(_jE,_jF,_)),_jI=__app1(E(_jC),_jF);return new F(function(){return _dH(_);});},_jJ=function(_jK,_jL,_jM,_jN,_jO,_){return new F(function(){return _jb(new T2(1,new T2(0,_jK,_jL),new T2(1,new T2(0,_jM,_jL),new T2(1,new T2(0,_jM,_jN),new T2(1,new T2(0,_jK,_jN),new T2(1,new T2(0,_jK,_jL),_v))))),_jO,_);});},_jP=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_jQ=function(_jR,_jS,_){var _jT=__app1(E(_jB),_jS),_jU=B(A2(_jR,_jS,_)),_jV=__app1(E(_jP),_jS);return new F(function(){return _dH(_);});},_jW=new T3(0,200,255,200),_jX=new T3(0,255,204,153),_jY=new T3(0,255,153,204),_jZ=new T3(0,153,255,255),_k0=new T3(0,0,128,128),_k1=new T3(0,255,255,100),_k2=new T3(0,0,0,0),_k3=new T3(0,100,100,100),_k4=new T2(1,_k3,_v),_k5=new T2(1,_k2,_k4),_k6=new T2(1,_k1,_k5),_k7=new T2(1,_k0,_k6),_k8=new T2(1,_jZ,_k7),_k9=new T2(1,_jY,_k8),_ka=new T2(1,_jX,_k9),_kb=new T2(1,_jW,_ka),_kc=new T3(0,200,200,180),_kd=new T2(1,_kc,_kb),_ke="lineWidth",_kf=function(_kg,_kh){var _ki=new T(function(){return String(E(_kg));});return function(_kj,_){var _kk=E(_kj),_kl=E(_ke),_km=__app2(E(_dV),_kk,_kl),_kn=E(_fY),_ko=__app3(_kn,_kk,_kl,E(_ki)),_kp=B(A2(_kh,_kk,_)),_kq=String(_km),_kr=__app3(_kn,_kk,_kl,_kq);return new F(function(){return _dH(_);});};},_ks=3,_kt=function(_ku,_kv){var _kw=E(_ku);if(!_kw._){return __Z;}else{var _kx=E(_kv);return (_kx._==0)?__Z:new T2(1,new T2(0,_kw.a,_kx.a),new T(function(){return B(_kt(_kw.b,_kx.b));}));}},_ky=function(_kz,_kA,_kB,_kC,_){var _kD=E(_kC);if(!_kD._){return _5L;}else{var _kE=E(E(_kA).a),_kF=new T(function(){return E(E(_kB).b);}),_kG=function(_kH,_){while(1){var _kI=B((function(_kJ,_){var _kK=E(_kJ);if(!_kK._){return _5L;}else{var _kL=_kK.b,_kM=E(_kK.a),_kN=_kM.d,_kO=E(_kM.b),_kP=_kO.a,_kQ=_kO.b,_kR=_kO.c,_kS=_kO.d,_kT=function(_){var _kU=function(_kV,_kW,_kX,_){while(1){var _kY=B((function(_kZ,_l0,_l1,_){var _l2=E(_kZ);if(!_l2._){return _5L;}else{var _l3=E(_l0);if(!_l3._){return _5L;}else{var _l4=E(_l1);if(!_l4._){return _5L;}else{var _l5=E(_l4.a),_l6=E(_l5.a),_l7=E(_l5.b),_l8=new T(function(){return E(_l6.b)+E(_kQ);}),_l9=B(_gU(_kz,_kF,new T(function(){return B(_78(_kd,E(_l7.b)));}),_l3.a,_l7.a,_kR,_kS,_l8,0,new T(function(){return E(_l6.a)+E(_kP);}),_l8,_l2.a,_));_kV=_l2.b;_kW=_l3.b;_kX=_l4.b;return __continue;}}}})(_kV,_kW,_kX,_));if(_kY!=__continue){return _kY;}}},_la=new T(function(){return B(_kt(_kM.f,new T(function(){return B(_kt(_kM.h,_kM.i));},1)));},1);return new F(function(){return _kU(_kM.j,_kM.k,_la,_);});};switch(E(_kM.c)){case 0:var _lb=B(_kT(_));_kH=_kL;return __continue;case 1:var _lc=E(_kz),_ld=_lc.a,_le=new T(function(){return E(_kP)+E(_kR);}),_lf=new T(function(){return E(_kQ)+E(_kS);}),_lg=function(_lh,_){return new F(function(){return _jJ(_kP,_kQ,_le,_lf,_lh,_);});},_li=B(A(_fZ,[new T(function(){return B(_78(_kd,_kN));},1),function(_lj,_){return new F(function(){return _jQ(_lg,E(_lj),_);});},_ld,_])),_lk=B(_kT(_)),_ll=function(_lm,_){while(1){var _ln=B((function(_lo,_){var _lp=E(_lo);if(!_lp._){return _5L;}else{var _lq=_lp.b,_lr=E(_lp.a),_ls=_lr.d,_lt=E(_lr.b),_lu=_lt.a,_lv=_lt.b,_lw=_lt.c,_lx=_lt.d,_ly=function(_){var _lz=function(_lA,_lB,_lC,_){while(1){var _lD=B((function(_lE,_lF,_lG,_){var _lH=E(_lE);if(!_lH._){return _5L;}else{var _lI=E(_lF);if(!_lI._){return _5L;}else{var _lJ=E(_lG);if(!_lJ._){return _5L;}else{var _lK=E(_lJ.a),_lL=E(_lK.a),_lM=E(_lK.b),_lN=new T(function(){return E(_lL.b)+E(_lv);}),_lO=B(_i4(_ld,_lc.b,_kF,new T(function(){return B(_78(_kd,E(_lM.b)));}),_lI.a,_lM.a,_lw,_lx,_lN,0,new T(function(){return E(_lL.a)+E(_lu);}),_lN,_lH.a,_));_lA=_lH.b;_lB=_lI.b;_lC=_lJ.b;return __continue;}}}})(_lA,_lB,_lC,_));if(_lD!=__continue){return _lD;}}},_lP=new T(function(){return B(_kt(_lr.f,new T(function(){return B(_kt(_lr.h,_lr.i));},1)));},1);return new F(function(){return _lz(_lr.j,_lr.k,_lP,_);});};switch(E(_lr.c)){case 0:var _lQ=B(_ly(_));_lm=_lq;return __continue;case 1:var _lR=new T(function(){return E(_lu)+E(_lw);}),_lS=new T(function(){return E(_lv)+E(_lx);}),_lT=function(_lU,_){return new F(function(){return _jJ(_lu,_lv,_lR,_lS,_lU,_);});},_lV=B(A(_fZ,[new T(function(){return B(_78(_kd,_ls));},1),function(_lW,_){return new F(function(){return _jQ(_lT,E(_lW),_);});},_ld,_])),_lX=B(_ly(_));_lm=_lq;return __continue;default:var _lY=function(_lZ,_){return new F(function(){return _jr(E(_lu),E(_lv),E(_lw),E(_lx),E(_lZ),_);});},_m0=B(A(_fZ,[new T(function(){return B(_78(_kd,_lr.e));},1),function(_m1,_){return new F(function(){return _jD(_lY,E(_m1),_);});},_ld,_])),_m2=new T(function(){var _m3=function(_m4,_){return new F(function(){return _jr(E(_lu),E(_lv),E(_lw),E(_lx),E(_m4),_);});};return B(_kf(_ks,function(_m5,_){return new F(function(){return _jQ(_m3,E(_m5),_);});}));}),_m6=B(A(_fZ,[new T(function(){return B(_78(_kd,_ls));},1),_m2,_ld,_])),_m7=B(_ly(_));_lm=_lq;return __continue;}}})(_lm,_));if(_ln!=__continue){return _ln;}}};return new F(function(){return _ll(_kL,_);});break;default:var _m8=E(_kz),_m9=_m8.a,_ma=function(_mb,_){return new F(function(){return _jr(E(_kP),E(_kQ),E(_kR),E(_kS),E(_mb),_);});},_mc=B(A(_fZ,[new T(function(){return B(_78(_kd,_kM.e));},1),function(_md,_){return new F(function(){return _jD(_ma,E(_md),_);});},_m9,_])),_me=new T(function(){var _mf=function(_mg,_){return new F(function(){return _jr(E(_kP),E(_kQ),E(_kR),E(_kS),E(_mg),_);});};return B(_kf(_ks,function(_mh,_){return new F(function(){return _jQ(_mf,E(_mh),_);});}));}),_mi=B(A(_fZ,[new T(function(){return B(_78(_kd,_kN));},1),_me,_m9,_])),_mj=B(_kT(_)),_mk=function(_ml,_){while(1){var _mm=B((function(_mn,_){var _mo=E(_mn);if(!_mo._){return _5L;}else{var _mp=_mo.b,_mq=E(_mo.a),_mr=_mq.d,_ms=E(_mq.b),_mt=_ms.a,_mu=_ms.b,_mv=_ms.c,_mw=_ms.d,_mx=function(_){var _my=function(_mz,_mA,_mB,_){while(1){var _mC=B((function(_mD,_mE,_mF,_){var _mG=E(_mD);if(!_mG._){return _5L;}else{var _mH=E(_mE);if(!_mH._){return _5L;}else{var _mI=E(_mF);if(!_mI._){return _5L;}else{var _mJ=E(_mI.a),_mK=E(_mJ.a),_mL=E(_mJ.b),_mM=new T(function(){return E(_mK.b)+E(_mu);}),_mN=B(_i4(_m9,_m8.b,_kF,new T(function(){return B(_78(_kd,E(_mL.b)));}),_mH.a,_mL.a,_mv,_mw,_mM,0,new T(function(){return E(_mK.a)+E(_mt);}),_mM,_mG.a,_));_mz=_mG.b;_mA=_mH.b;_mB=_mI.b;return __continue;}}}})(_mz,_mA,_mB,_));if(_mC!=__continue){return _mC;}}},_mO=new T(function(){return B(_kt(_mq.f,new T(function(){return B(_kt(_mq.h,_mq.i));},1)));},1);return new F(function(){return _my(_mq.j,_mq.k,_mO,_);});};switch(E(_mq.c)){case 0:var _mP=B(_mx(_));_ml=_mp;return __continue;case 1:var _mQ=new T(function(){return E(_mt)+E(_mv);}),_mR=new T(function(){return E(_mu)+E(_mw);}),_mS=function(_mT,_){return new F(function(){return _jJ(_mt,_mu,_mQ,_mR,_mT,_);});},_mU=B(A(_fZ,[new T(function(){return B(_78(_kd,_mr));},1),function(_mV,_){return new F(function(){return _jQ(_mS,E(_mV),_);});},_m9,_])),_mW=B(_mx(_));_ml=_mp;return __continue;default:var _mX=function(_mY,_){return new F(function(){return _jr(E(_mt),E(_mu),E(_mv),E(_mw),E(_mY),_);});},_mZ=B(A(_fZ,[new T(function(){return B(_78(_kd,_mq.e));},1),function(_n0,_){return new F(function(){return _jD(_mX,E(_n0),_);});},_m9,_])),_n1=new T(function(){var _n2=function(_n3,_){return new F(function(){return _jr(E(_mt),E(_mu),E(_mv),E(_mw),E(_n3),_);});};return B(_kf(_ks,function(_n4,_){return new F(function(){return _jQ(_n2,E(_n4),_);});}));}),_n5=B(A(_fZ,[new T(function(){return B(_78(_kd,_mr));},1),_n1,_m9,_])),_n6=B(_mx(_));_ml=_mp;return __continue;}}})(_ml,_));if(_mm!=__continue){return _mm;}}};return new F(function(){return _mk(_kL,_);});}}})(_kH,_));if(_kI!=__continue){return _kI;}}},_n7=_kD.a,_n8=_kD.b,_n9=E(_n7),_na=_n9.d,_nb=E(_n9.b),_nc=_nb.a,_nd=_nb.b,_ne=_nb.c,_nf=_nb.d,_ng=function(_){var _nh=function(_ni,_nj,_nk,_){while(1){var _nl=B((function(_nm,_nn,_no,_){var _np=E(_nm);if(!_np._){return _5L;}else{var _nq=E(_nn);if(!_nq._){return _5L;}else{var _nr=E(_no);if(!_nr._){return _5L;}else{var _ns=E(_nr.a),_nt=E(_ns.a),_nu=E(_ns.b),_nv=new T(function(){return E(_nt.b)+E(_nd);}),_nw=B(_gU(_kz,_kF,new T(function(){return B(_78(_kd,E(_nu.b)));}),_nq.a,_nu.a,_ne,_nf,_nv,0,new T(function(){return E(_nt.a)+E(_nc);}),_nv,_np.a,_));_ni=_np.b;_nj=_nq.b;_nk=_nr.b;return __continue;}}}})(_ni,_nj,_nk,_));if(_nl!=__continue){return _nl;}}},_nx=new T(function(){return B(_kt(_n9.f,new T(function(){return B(_kt(_n9.h,_n9.i));},1)));},1);return new F(function(){return _nh(_n9.j,_n9.k,_nx,_);});};switch(E(_n9.c)){case 0:var _ny=B(_ng(_));return new F(function(){return _kG(_n8,_);});break;case 1:var _nz=E(_kz),_nA=_nz.a,_nB=new T(function(){return E(_nc)+E(_ne);}),_nC=new T(function(){return E(_nd)+E(_nf);}),_nD=function(_nE,_){return new F(function(){return _jJ(_nc,_nd,_nB,_nC,_nE,_);});},_nF=B(A(_fZ,[new T(function(){return B(_78(_kd,_na));},1),function(_nG,_){return new F(function(){return _jQ(_nD,E(_nG),_);});},_nA,_])),_nH=B(_ng(_)),_nI=function(_nJ,_){while(1){var _nK=B((function(_nL,_){var _nM=E(_nL);if(!_nM._){return _5L;}else{var _nN=_nM.b,_nO=E(_nM.a),_nP=_nO.d,_nQ=E(_nO.b),_nR=_nQ.a,_nS=_nQ.b,_nT=_nQ.c,_nU=_nQ.d,_nV=function(_){var _nW=function(_nX,_nY,_nZ,_){while(1){var _o0=B((function(_o1,_o2,_o3,_){var _o4=E(_o1);if(!_o4._){return _5L;}else{var _o5=E(_o2);if(!_o5._){return _5L;}else{var _o6=E(_o3);if(!_o6._){return _5L;}else{var _o7=E(_o6.a),_o8=E(_o7.a),_o9=E(_o7.b),_oa=new T(function(){return E(_o8.b)+E(_nS);}),_ob=B(_i4(_nA,_nz.b,_kF,new T(function(){return B(_78(_kd,E(_o9.b)));}),_o5.a,_o9.a,_nT,_nU,_oa,0,new T(function(){return E(_o8.a)+E(_nR);}),_oa,_o4.a,_));_nX=_o4.b;_nY=_o5.b;_nZ=_o6.b;return __continue;}}}})(_nX,_nY,_nZ,_));if(_o0!=__continue){return _o0;}}},_oc=new T(function(){return B(_kt(_nO.f,new T(function(){return B(_kt(_nO.h,_nO.i));},1)));},1);return new F(function(){return _nW(_nO.j,_nO.k,_oc,_);});};switch(E(_nO.c)){case 0:var _od=B(_nV(_));_nJ=_nN;return __continue;case 1:var _oe=new T(function(){return E(_nR)+E(_nT);}),_of=new T(function(){return E(_nS)+E(_nU);}),_og=function(_oh,_){return new F(function(){return _jJ(_nR,_nS,_oe,_of,_oh,_);});},_oi=B(A(_fZ,[new T(function(){return B(_78(_kd,_nP));},1),function(_oj,_){return new F(function(){return _jQ(_og,E(_oj),_);});},_nA,_])),_ok=B(_nV(_));_nJ=_nN;return __continue;default:var _ol=function(_om,_){return new F(function(){return _jr(E(_nR),E(_nS),E(_nT),E(_nU),E(_om),_);});},_on=B(A(_fZ,[new T(function(){return B(_78(_kd,_nO.e));},1),function(_oo,_){return new F(function(){return _jD(_ol,E(_oo),_);});},_nA,_])),_op=new T(function(){var _oq=function(_or,_){return new F(function(){return _jr(E(_nR),E(_nS),E(_nT),E(_nU),E(_or),_);});};return B(_kf(_ks,function(_os,_){return new F(function(){return _jQ(_oq,E(_os),_);});}));}),_ot=B(A(_fZ,[new T(function(){return B(_78(_kd,_nP));},1),_op,_nA,_])),_ou=B(_nV(_));_nJ=_nN;return __continue;}}})(_nJ,_));if(_nK!=__continue){return _nK;}}};return new F(function(){return _nI(_n8,_);});break;default:var _ov=E(_kz),_ow=_ov.a,_ox=function(_oy,_){return new F(function(){return _jr(E(_nc),E(_nd),E(_ne),E(_nf),E(_oy),_);});},_oz=B(A(_fZ,[new T(function(){return B(_78(_kd,_n9.e));},1),function(_oA,_){return new F(function(){return _jD(_ox,E(_oA),_);});},_ow,_])),_oB=new T(function(){var _oC=function(_oD,_){return new F(function(){return _jr(E(_nc),E(_nd),E(_ne),E(_nf),E(_oD),_);});};return B(_kf(_ks,function(_oE,_){return new F(function(){return _jQ(_oC,E(_oE),_);});}));}),_oF=B(A(_fZ,[new T(function(){return B(_78(_kd,_na));},1),_oB,_ow,_])),_oG=B(_ng(_)),_oH=function(_oI,_){while(1){var _oJ=B((function(_oK,_){var _oL=E(_oK);if(!_oL._){return _5L;}else{var _oM=_oL.b,_oN=E(_oL.a),_oO=_oN.d,_oP=E(_oN.b),_oQ=_oP.a,_oR=_oP.b,_oS=_oP.c,_oT=_oP.d,_oU=function(_){var _oV=function(_oW,_oX,_oY,_){while(1){var _oZ=B((function(_p0,_p1,_p2,_){var _p3=E(_p0);if(!_p3._){return _5L;}else{var _p4=E(_p1);if(!_p4._){return _5L;}else{var _p5=E(_p2);if(!_p5._){return _5L;}else{var _p6=E(_p5.a),_p7=E(_p6.a),_p8=E(_p6.b),_p9=new T(function(){return E(_p7.b)+E(_oR);}),_pa=B(_i4(_ow,_ov.b,_kF,new T(function(){return B(_78(_kd,E(_p8.b)));}),_p4.a,_p8.a,_oS,_oT,_p9,0,new T(function(){return E(_p7.a)+E(_oQ);}),_p9,_p3.a,_));_oW=_p3.b;_oX=_p4.b;_oY=_p5.b;return __continue;}}}})(_oW,_oX,_oY,_));if(_oZ!=__continue){return _oZ;}}},_pb=new T(function(){return B(_kt(_oN.f,new T(function(){return B(_kt(_oN.h,_oN.i));},1)));},1);return new F(function(){return _oV(_oN.j,_oN.k,_pb,_);});};switch(E(_oN.c)){case 0:var _pc=B(_oU(_));_oI=_oM;return __continue;case 1:var _pd=new T(function(){return E(_oQ)+E(_oS);}),_pe=new T(function(){return E(_oR)+E(_oT);}),_pf=function(_pg,_){return new F(function(){return _jJ(_oQ,_oR,_pd,_pe,_pg,_);});},_ph=B(A(_fZ,[new T(function(){return B(_78(_kd,_oO));},1),function(_pi,_){return new F(function(){return _jQ(_pf,E(_pi),_);});},_ow,_])),_pj=B(_oU(_));_oI=_oM;return __continue;default:var _pk=function(_pl,_){return new F(function(){return _jr(E(_oQ),E(_oR),E(_oS),E(_oT),E(_pl),_);});},_pm=B(A(_fZ,[new T(function(){return B(_78(_kd,_oN.e));},1),function(_pn,_){return new F(function(){return _jD(_pk,E(_pn),_);});},_ow,_])),_po=new T(function(){var _pp=function(_pq,_){return new F(function(){return _jr(E(_oQ),E(_oR),E(_oS),E(_oT),E(_pq),_);});};return B(_kf(_ks,function(_pr,_){return new F(function(){return _jQ(_pp,E(_pr),_);});}));}),_ps=B(A(_fZ,[new T(function(){return B(_78(_kd,_oO));},1),_po,_ow,_])),_pt=B(_oU(_));_oI=_oM;return __continue;}}})(_oI,_));if(_oJ!=__continue){return _oJ;}}};return new F(function(){return _oH(_n8,_);});}}},_pu=function(_pv){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_pv));}))));});},_pw=new T(function(){return B(_pu("ww_s5Ar (Double, Double)"));}),_px=new T(function(){return B(unCStr("Prelude.undefined"));}),_py=new T(function(){return B(err(_px));}),_pz=function(_pA){return E(_py);},_pB=new T(function(){return B(_pz(_));}),_pC=function(_pD,_pE){if(_pD<=0){if(_pD>=0){return new F(function(){return quot(_pD,_pE);});}else{if(_pE<=0){return new F(function(){return quot(_pD,_pE);});}else{return quot(_pD+1|0,_pE)-1|0;}}}else{if(_pE>=0){if(_pD>=0){return new F(function(){return quot(_pD,_pE);});}else{if(_pE<=0){return new F(function(){return quot(_pD,_pE);});}else{return quot(_pD+1|0,_pE)-1|0;}}}else{return quot(_pD-1|0,_pE)-1|0;}}},_pF=function(_pG,_pH){if(_pG<=_pH){var _pI=function(_pJ){return new T2(1,_pJ,new T(function(){if(_pJ!=_pH){return B(_pI(_pJ+1|0));}else{return __Z;}}));};return new F(function(){return _pI(_pG);});}else{return __Z;}},_pK=new T(function(){return B(_pF(0,2147483647));}),_pL=40,_pM=60,_pN=new T2(0,_pL,_pM),_pO=new T2(1,_pN,_v),_pP=1,_pQ=new T2(1,_pP,_v),_pR=1,_pS=new T2(1,_pR,_v),_pT=function(_pU,_pV){var _pW=_pU%_pV;if(_pU<=0){if(_pU>=0){return E(_pW);}else{if(_pV<=0){return E(_pW);}else{var _pX=E(_pW);return (_pX==0)?0:_pX+_pV|0;}}}else{if(_pV>=0){if(_pU>=0){return E(_pW);}else{if(_pV<=0){return E(_pW);}else{var _pY=E(_pW);return (_pY==0)?0:_pY+_pV|0;}}}else{var _pZ=E(_pW);return (_pZ==0)?0:_pZ+_pV|0;}}},_q0=function(_q1,_q2,_q3){var _q4=E(_q2);if(!_q4._){return __Z;}else{var _q5=E(_q3);return (_q5._==0)?__Z:new T2(1,new T(function(){return B(A2(_q1,_q4.a,_q5.a));}),new T(function(){return B(_q0(_q1,_q4.b,_q5.b));}));}},_q6=function(_q7,_q8,_q9,_qa,_qb){var _qc=new T(function(){var _qd=new T(function(){return B(_9X(_q9,0));}),_qe=new T(function(){return B(_pC(E(_qd)-3|0,2));}),_qf=new T(function(){var _qg=50-E(_qe)*8,_qh=_qg&4294967295;if(_qg>=_qh){return _qh;}else{return _qh-1|0;}}),_qi=new T(function(){return 40-E(_qf)/9*4*E(_qe);}),_qj=new T(function(){var _qk=E(_qd),_ql=B(_pC(_qk,2)),_qm=_ql+B(_pT(_qk,2))|0,_qn=_qm-1|0,_qo=new T(function(){return E(_q8)/5-B(_pC(_qk-3|0,2))*3;}),_qp=new T(function(){var _qq=E(_q8);return _qq/4+_qq/10;}),_qr=new T(function(){return E(_q7)/16-B(_pC(_qk-3|0,2));}),_qs=new T(function(){var _qt=E(_qr);return _qt+_qt;}),_qu=new T(function(){var _qv=E(_qs);return (E(_q7)-(_qv+_qv)-E(_qr)*(_qm-1))/_qm;}),_qw=new T(function(){var _qx=_ql-1|0;if(0<=_qx){var _qy=new T(function(){return E(_qp)+E(_qo)+E(_q7)/20;}),_qz=new T(function(){return (E(_q7)-(E(_qu)*_ql+E(_qr)*(_ql-1)))/2;}),_qA=function(_qB){return new T2(1,new T4(0,new T(function(){return E(_qz)+(E(_qu)+E(_qr))*_qB;}),_qy,_qu,_qo),new T(function(){if(_qB!=_qx){return B(_qA(_qB+1|0));}else{return __Z;}}));};return B(_qA(0));}else{return __Z;}});if(0<=_qn){var _qC=function(_qD){return new T2(1,new T4(0,new T(function(){return E(_qs)+(E(_qu)+E(_qr))*_qD;}),_qp,_qu,_qo),new T(function(){if(_qD!=_qn){return B(_qC(_qD+1|0));}else{return E(_qw);}}));};return B(_qC(0));}else{return E(_qw);}},1),_qE=function(_qF,_qG){var _qH=E(_qF);return {_:0,a:_qH+1|0,b:E(_qG),c:E(_62),d:0,e:7,f:E(new T2(1,new T2(0,_qi,_pM),_v)),g:E(_v),h:E(new T2(1,_qf,_v)),i:E(_pQ),j:E(new T2(1,new T(function(){return B(_78(_q9,_qH));}),_v)),k:E(_pS),l:E(_v),m:E(_v),n:E(new T1(1,new T(function(){return B(_78(_qa,_qH));}))),o:E(new T1(2,_qH))};};return B(_q0(_qE,_pK,_qj));});return new T2(0,{_:0,a:0,b:E(new T4(0,new T(function(){return E(_q7)/8;}),new T(function(){return E(_q8)/10;}),new T(function(){return E(_q7)/3;}),new T(function(){return E(_q8)/5;}))),c:E(_62),d:0,e:5,f:E(_pO),g:E(_v),h:E(_cS),i:E(_pQ),j:E(new T2(1,new T(function(){return B(_78(_q9,_qb));}),_v)),k:E(_cK),l:E(_v),m:E(_v),n:E(new T1(1,new T(function(){return B(_78(_qa,_qb));}))),o:E(_as)},_qc);},_qI=new T(function(){return B(unCStr("base"));}),_qJ=new T(function(){return B(unCStr("GHC.Exception"));}),_qK=new T(function(){return B(unCStr("ArithException"));}),_qL=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_qI,_qJ,_qK),_qM=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_qL,_v,_v),_qN=function(_qO){return E(_qM);},_qP=function(_qQ){var _qR=E(_qQ);return new F(function(){return _X(B(_V(_qR.a)),_qN,_qR.b);});},_qS=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_qT=new T(function(){return B(unCStr("denormal"));}),_qU=new T(function(){return B(unCStr("divide by zero"));}),_qV=new T(function(){return B(unCStr("loss of precision"));}),_qW=new T(function(){return B(unCStr("arithmetic underflow"));}),_qX=new T(function(){return B(unCStr("arithmetic overflow"));}),_qY=function(_qZ,_r0){switch(E(_qZ)){case 0:return new F(function(){return _3(_qX,_r0);});break;case 1:return new F(function(){return _3(_qW,_r0);});break;case 2:return new F(function(){return _3(_qV,_r0);});break;case 3:return new F(function(){return _3(_qU,_r0);});break;case 4:return new F(function(){return _3(_qT,_r0);});break;default:return new F(function(){return _3(_qS,_r0);});}},_r1=function(_r2){return new F(function(){return _qY(_r2,_v);});},_r3=function(_r4,_r5,_r6){return new F(function(){return _qY(_r5,_r6);});},_r7=function(_r8,_r9){return new F(function(){return _28(_qY,_r8,_r9);});},_ra=new T3(0,_r3,_r1,_r7),_rb=new T(function(){return new T5(0,_qN,_ra,_rc,_qP,_r1);}),_rc=function(_be){return new T2(0,_rb,_be);},_rd=3,_re=new T(function(){return B(_rc(_rd));}),_rf=new T(function(){return die(_re);}),_rg=0,_rh=new T(function(){return B(_rc(_rg));}),_ri=new T(function(){return die(_rh);}),_rj=function(_rk,_rl){var _rm=E(_rl);switch(_rm){case  -1:var _rn=E(_rk);if(_rn==( -2147483648)){return E(_ri);}else{return new F(function(){return _pC(_rn, -1);});}break;case 0:return E(_rf);default:return new F(function(){return _pC(_rk,_rm);});}},_ro=new T1(0,0),_rp=function(_rq,_rr){while(1){var _rs=E(_rq);if(!_rs._){var _rt=_rs.a,_ru=E(_rr);if(!_ru._){return new T1(0,(_rt>>>0|_ru.a>>>0)>>>0&4294967295);}else{_rq=new T1(1,I_fromInt(_rt));_rr=_ru;continue;}}else{var _rv=E(_rr);if(!_rv._){_rq=_rs;_rr=new T1(1,I_fromInt(_rv.a));continue;}else{return new T1(1,I_or(_rs.a,_rv.a));}}}},_rw=function(_rx,_ry){while(1){var _rz=E(_rx);if(!_rz._){_rx=new T1(1,I_fromInt(_rz.a));continue;}else{return new T1(1,I_shiftLeft(_rz.a,_ry));}}},_rA=function(_rB){var _rC=E(_rB);if(!_rC._){return E(_ro);}else{return new F(function(){return _rp(new T1(0,E(_rC.a)),B(_rw(B(_rA(_rC.b)),31)));});}},_rD=new T1(0,1),_rE=new T1(0,2147483647),_rF=function(_rG,_rH){while(1){var _rI=E(_rG);if(!_rI._){var _rJ=_rI.a,_rK=E(_rH);if(!_rK._){var _rL=_rK.a,_rM=addC(_rJ,_rL);if(!E(_rM.b)){return new T1(0,_rM.a);}else{_rG=new T1(1,I_fromInt(_rJ));_rH=new T1(1,I_fromInt(_rL));continue;}}else{_rG=new T1(1,I_fromInt(_rJ));_rH=_rK;continue;}}else{var _rN=E(_rH);if(!_rN._){_rG=_rI;_rH=new T1(1,I_fromInt(_rN.a));continue;}else{return new T1(1,I_add(_rI.a,_rN.a));}}}},_rO=new T(function(){return B(_rF(_rE,_rD));}),_rP=function(_rQ){var _rR=E(_rQ);if(!_rR._){var _rS=E(_rR.a);return (_rS==( -2147483648))?E(_rO):new T1(0, -_rS);}else{return new T1(1,I_negate(_rR.a));}},_rT=function(_rU,_rV){if(!E(_rU)){return new F(function(){return _rP(B(_rA(_rV)));});}else{return new F(function(){return _rA(_rV);});}},_rW=1420103680,_rX=465,_rY=new T2(1,_rX,_v),_rZ=new T2(1,_rW,_rY),_s0=new T(function(){return B(_rT(_5Q,_rZ));}),_s1=function(_s2){return E(_s0);},_s3=0,_s4=function(_s5,_s6){var _s7=E(_s6);switch(_s7){case  -1:return E(_s3);case 0:return E(_rf);default:return new F(function(){return _pT(E(_s5),_s7);});}},_s8=new T(function(){return B(unCStr("s"));}),_s9=function(_sa,_sb){while(1){var _sc=E(_sa);if(!_sc._){return E(_sb);}else{_sa=_sc.b;_sb=_sc.a;continue;}}},_sd=function(_se,_sf,_sg){return new F(function(){return _s9(_sf,_se);});},_sh=new T1(0,1),_si=new T1(0,1),_sj=function(_sk,_sl){var _sm=E(_sk);return new T2(0,_sm,new T(function(){var _sn=B(_sj(B(_rF(_sm,_sl)),_sl));return new T2(1,_sn.a,_sn.b);}));},_so=function(_sp){var _sq=B(_sj(_sp,_si));return new T2(1,_sq.a,_sq.b);},_sr=function(_ss,_st){while(1){var _su=E(_ss);if(!_su._){var _sv=_su.a,_sw=E(_st);if(!_sw._){var _sx=_sw.a,_sy=subC(_sv,_sx);if(!E(_sy.b)){return new T1(0,_sy.a);}else{_ss=new T1(1,I_fromInt(_sv));_st=new T1(1,I_fromInt(_sx));continue;}}else{_ss=new T1(1,I_fromInt(_sv));_st=_sw;continue;}}else{var _sz=E(_st);if(!_sz._){_ss=_su;_st=new T1(1,I_fromInt(_sz.a));continue;}else{return new T1(1,I_sub(_su.a,_sz.a));}}}},_sA=function(_sB,_sC){var _sD=B(_sj(_sB,new T(function(){return B(_sr(_sC,_sB));})));return new T2(1,_sD.a,_sD.b);},_sE=new T1(0,0),_sF=function(_sG,_sH){var _sI=E(_sG);if(!_sI._){var _sJ=_sI.a,_sK=E(_sH);return (_sK._==0)?_sJ>=_sK.a:I_compareInt(_sK.a,_sJ)<=0;}else{var _sL=_sI.a,_sM=E(_sH);return (_sM._==0)?I_compareInt(_sL,_sM.a)>=0:I_compare(_sL,_sM.a)>=0;}},_sN=function(_sO,_sP){var _sQ=E(_sO);if(!_sQ._){var _sR=_sQ.a,_sS=E(_sP);return (_sS._==0)?_sR>_sS.a:I_compareInt(_sS.a,_sR)<0;}else{var _sT=_sQ.a,_sU=E(_sP);return (_sU._==0)?I_compareInt(_sT,_sU.a)>0:I_compare(_sT,_sU.a)>0;}},_sV=function(_sW,_sX){var _sY=E(_sW);if(!_sY._){var _sZ=_sY.a,_t0=E(_sX);return (_t0._==0)?_sZ<_t0.a:I_compareInt(_t0.a,_sZ)>0;}else{var _t1=_sY.a,_t2=E(_sX);return (_t2._==0)?I_compareInt(_t1,_t2.a)<0:I_compare(_t1,_t2.a)<0;}},_t3=function(_t4,_t5,_t6){if(!B(_sF(_t5,_sE))){var _t7=function(_t8){return (!B(_sV(_t8,_t6)))?new T2(1,_t8,new T(function(){return B(_t7(B(_rF(_t8,_t5))));})):__Z;};return new F(function(){return _t7(_t4);});}else{var _t9=function(_ta){return (!B(_sN(_ta,_t6)))?new T2(1,_ta,new T(function(){return B(_t9(B(_rF(_ta,_t5))));})):__Z;};return new F(function(){return _t9(_t4);});}},_tb=function(_tc,_td,_te){return new F(function(){return _t3(_tc,B(_sr(_td,_tc)),_te);});},_tf=function(_tg,_th){return new F(function(){return _t3(_tg,_si,_th);});},_ti=function(_tj){var _tk=E(_tj);if(!_tk._){return E(_tk.a);}else{return new F(function(){return I_toInt(_tk.a);});}},_tl=function(_tm){return new F(function(){return _ti(_tm);});},_tn=function(_to){return new F(function(){return _sr(_to,_si);});},_tp=function(_tq){return new F(function(){return _rF(_tq,_si);});},_tr=function(_ts){return new T1(0,_ts);},_tt=function(_tu){return new F(function(){return _tr(E(_tu));});},_tv={_:0,a:_tp,b:_tn,c:_tt,d:_tl,e:_so,f:_sA,g:_tf,h:_tb},_tw=function(_tx,_ty){while(1){var _tz=E(_tx);if(!_tz._){var _tA=E(_tz.a);if(_tA==( -2147483648)){_tx=new T1(1,I_fromInt( -2147483648));continue;}else{var _tB=E(_ty);if(!_tB._){return new T1(0,B(_pC(_tA,_tB.a)));}else{_tx=new T1(1,I_fromInt(_tA));_ty=_tB;continue;}}}else{var _tC=_tz.a,_tD=E(_ty);return (_tD._==0)?new T1(1,I_div(_tC,I_fromInt(_tD.a))):new T1(1,I_div(_tC,_tD.a));}}},_tE=function(_tF,_tG){var _tH=E(_tF);if(!_tH._){var _tI=_tH.a,_tJ=E(_tG);return (_tJ._==0)?_tI==_tJ.a:(I_compareInt(_tJ.a,_tI)==0)?true:false;}else{var _tK=_tH.a,_tL=E(_tG);return (_tL._==0)?(I_compareInt(_tK,_tL.a)==0)?true:false:(I_compare(_tK,_tL.a)==0)?true:false;}},_tM=new T1(0,0),_tN=function(_tO,_tP){if(!B(_tE(_tP,_tM))){return new F(function(){return _tw(_tO,_tP);});}else{return E(_rf);}},_tQ=function(_tR,_tS){while(1){var _tT=E(_tR);if(!_tT._){var _tU=E(_tT.a);if(_tU==( -2147483648)){_tR=new T1(1,I_fromInt( -2147483648));continue;}else{var _tV=E(_tS);if(!_tV._){var _tW=_tV.a;return new T2(0,new T1(0,B(_pC(_tU,_tW))),new T1(0,B(_pT(_tU,_tW))));}else{_tR=new T1(1,I_fromInt(_tU));_tS=_tV;continue;}}}else{var _tX=E(_tS);if(!_tX._){_tR=_tT;_tS=new T1(1,I_fromInt(_tX.a));continue;}else{var _tY=I_divMod(_tT.a,_tX.a);return new T2(0,new T1(1,_tY.a),new T1(1,_tY.b));}}}},_tZ=function(_u0,_u1){if(!B(_tE(_u1,_tM))){var _u2=B(_tQ(_u0,_u1));return new T2(0,_u2.a,_u2.b);}else{return E(_rf);}},_u3=function(_u4,_u5){while(1){var _u6=E(_u4);if(!_u6._){var _u7=E(_u6.a);if(_u7==( -2147483648)){_u4=new T1(1,I_fromInt( -2147483648));continue;}else{var _u8=E(_u5);if(!_u8._){return new T1(0,B(_pT(_u7,_u8.a)));}else{_u4=new T1(1,I_fromInt(_u7));_u5=_u8;continue;}}}else{var _u9=_u6.a,_ua=E(_u5);return (_ua._==0)?new T1(1,I_mod(_u9,I_fromInt(_ua.a))):new T1(1,I_mod(_u9,_ua.a));}}},_ub=function(_uc,_ud){if(!B(_tE(_ud,_tM))){return new F(function(){return _u3(_uc,_ud);});}else{return E(_rf);}},_ue=function(_uf,_ug){while(1){var _uh=E(_uf);if(!_uh._){var _ui=E(_uh.a);if(_ui==( -2147483648)){_uf=new T1(1,I_fromInt( -2147483648));continue;}else{var _uj=E(_ug);if(!_uj._){return new T1(0,quot(_ui,_uj.a));}else{_uf=new T1(1,I_fromInt(_ui));_ug=_uj;continue;}}}else{var _uk=_uh.a,_ul=E(_ug);return (_ul._==0)?new T1(0,I_toInt(I_quot(_uk,I_fromInt(_ul.a)))):new T1(1,I_quot(_uk,_ul.a));}}},_um=function(_un,_uo){if(!B(_tE(_uo,_tM))){return new F(function(){return _ue(_un,_uo);});}else{return E(_rf);}},_up=function(_uq,_ur){while(1){var _us=E(_uq);if(!_us._){var _ut=E(_us.a);if(_ut==( -2147483648)){_uq=new T1(1,I_fromInt( -2147483648));continue;}else{var _uu=E(_ur);if(!_uu._){var _uv=_uu.a;return new T2(0,new T1(0,quot(_ut,_uv)),new T1(0,_ut%_uv));}else{_uq=new T1(1,I_fromInt(_ut));_ur=_uu;continue;}}}else{var _uw=E(_ur);if(!_uw._){_uq=_us;_ur=new T1(1,I_fromInt(_uw.a));continue;}else{var _ux=I_quotRem(_us.a,_uw.a);return new T2(0,new T1(1,_ux.a),new T1(1,_ux.b));}}}},_uy=function(_uz,_uA){if(!B(_tE(_uA,_tM))){var _uB=B(_up(_uz,_uA));return new T2(0,_uB.a,_uB.b);}else{return E(_rf);}},_uC=function(_uD,_uE){while(1){var _uF=E(_uD);if(!_uF._){var _uG=E(_uF.a);if(_uG==( -2147483648)){_uD=new T1(1,I_fromInt( -2147483648));continue;}else{var _uH=E(_uE);if(!_uH._){return new T1(0,_uG%_uH.a);}else{_uD=new T1(1,I_fromInt(_uG));_uE=_uH;continue;}}}else{var _uI=_uF.a,_uJ=E(_uE);return (_uJ._==0)?new T1(1,I_rem(_uI,I_fromInt(_uJ.a))):new T1(1,I_rem(_uI,_uJ.a));}}},_uK=function(_uL,_uM){if(!B(_tE(_uM,_tM))){return new F(function(){return _uC(_uL,_uM);});}else{return E(_rf);}},_uN=function(_uO){return E(_uO);},_uP=function(_uQ){return E(_uQ);},_uR=function(_uS){var _uT=E(_uS);if(!_uT._){var _uU=E(_uT.a);return (_uU==( -2147483648))?E(_rO):(_uU<0)?new T1(0, -_uU):E(_uT);}else{var _uV=_uT.a;return (I_compareInt(_uV,0)>=0)?E(_uT):new T1(1,I_negate(_uV));}},_uW=new T1(0, -1),_uX=function(_uY){var _uZ=E(_uY);if(!_uZ._){var _v0=_uZ.a;return (_v0>=0)?(E(_v0)==0)?E(_ro):E(_rD):E(_uW);}else{var _v1=I_compareInt(_uZ.a,0);return (_v1<=0)?(E(_v1)==0)?E(_ro):E(_uW):E(_rD);}},_v2=function(_v3,_v4){while(1){var _v5=E(_v3);if(!_v5._){var _v6=_v5.a,_v7=E(_v4);if(!_v7._){var _v8=_v7.a;if(!(imul(_v6,_v8)|0)){return new T1(0,imul(_v6,_v8)|0);}else{_v3=new T1(1,I_fromInt(_v6));_v4=new T1(1,I_fromInt(_v8));continue;}}else{_v3=new T1(1,I_fromInt(_v6));_v4=_v7;continue;}}else{var _v9=E(_v4);if(!_v9._){_v3=_v5;_v4=new T1(1,I_fromInt(_v9.a));continue;}else{return new T1(1,I_mul(_v5.a,_v9.a));}}}},_va={_:0,a:_rF,b:_sr,c:_v2,d:_rP,e:_uR,f:_uX,g:_uP},_vb=function(_vc,_vd){var _ve=E(_vc);if(!_ve._){var _vf=_ve.a,_vg=E(_vd);return (_vg._==0)?_vf!=_vg.a:(I_compareInt(_vg.a,_vf)==0)?false:true;}else{var _vh=_ve.a,_vi=E(_vd);return (_vi._==0)?(I_compareInt(_vh,_vi.a)==0)?false:true:(I_compare(_vh,_vi.a)==0)?false:true;}},_vj=new T2(0,_tE,_vb),_vk=function(_vl,_vm){var _vn=E(_vl);if(!_vn._){var _vo=_vn.a,_vp=E(_vm);return (_vp._==0)?_vo<=_vp.a:I_compareInt(_vp.a,_vo)>=0;}else{var _vq=_vn.a,_vr=E(_vm);return (_vr._==0)?I_compareInt(_vq,_vr.a)<=0:I_compare(_vq,_vr.a)<=0;}},_vs=function(_vt,_vu){return (!B(_vk(_vt,_vu)))?E(_vt):E(_vu);},_vv=function(_vw,_vx){return (!B(_vk(_vw,_vx)))?E(_vx):E(_vw);},_vy=function(_vz,_vA){var _vB=E(_vz);if(!_vB._){var _vC=_vB.a,_vD=E(_vA);if(!_vD._){var _vE=_vD.a;return (_vC!=_vE)?(_vC>_vE)?2:0:1;}else{var _vF=I_compareInt(_vD.a,_vC);return (_vF<=0)?(_vF>=0)?1:2:0;}}else{var _vG=_vB.a,_vH=E(_vA);if(!_vH._){var _vI=I_compareInt(_vG,_vH.a);return (_vI>=0)?(_vI<=0)?1:2:0;}else{var _vJ=I_compare(_vG,_vH.a);return (_vJ>=0)?(_vJ<=0)?1:2:0;}}},_vK={_:0,a:_vj,b:_vy,c:_sV,d:_vk,e:_sN,f:_sF,g:_vs,h:_vv},_vL=function(_vM){return new T2(0,E(_vM),E(_sh));},_vN=new T3(0,_va,_vK,_vL),_vO={_:0,a:_vN,b:_tv,c:_um,d:_uK,e:_tN,f:_ub,g:_uy,h:_tZ,i:_uN},_vP=new T1(0,0),_vQ=function(_vR,_vS,_vT){var _vU=B(A1(_vR,_vS));if(!B(_tE(_vU,_vP))){return new F(function(){return _tw(B(_v2(_vS,_vT)),_vU);});}else{return E(_rf);}},_vV=function(_vW,_vX){while(1){if(!B(_tE(_vX,_tM))){var _vY=_vX,_vZ=B(_uK(_vW,_vX));_vW=_vY;_vX=_vZ;continue;}else{return E(_vW);}}},_w0=5,_w1=new T(function(){return B(_rc(_w0));}),_w2=new T(function(){return die(_w1);}),_w3=function(_w4,_w5){if(!B(_tE(_w5,_tM))){var _w6=B(_vV(B(_uR(_w4)),B(_uR(_w5))));return (!B(_tE(_w6,_tM)))?new T2(0,B(_ue(_w4,_w6)),B(_ue(_w5,_w6))):E(_rf);}else{return E(_w2);}},_w7=function(_w8,_w9,_wa,_wb){var _wc=B(_v2(_w9,_wa));return new F(function(){return _w3(B(_v2(B(_v2(_w8,_wb)),B(_uX(_wc)))),B(_uR(_wc)));});},_wd=function(_we){return E(E(_we).a);},_wf=function(_wg){return E(E(_wg).a);},_wh=function(_wi){return E(E(_wi).g);},_wj=function(_wk,_wl,_wm){var _wn=new T(function(){if(!B(_tE(_wm,_tM))){var _wo=B(_up(_wl,_wm));return new T2(0,_wo.a,_wo.b);}else{return E(_rf);}}),_wp=new T(function(){return B(A2(_wh,B(_wf(B(_wd(_wk)))),new T(function(){return E(E(_wn).a);})));});return new T2(0,_wp,new T(function(){return new T2(0,E(E(_wn).b),E(_wm));}));},_wq=function(_wr){return E(E(_wr).b);},_ws=function(_wt,_wu,_wv){var _ww=B(_wj(_wt,_wu,_wv)),_wx=_ww.a,_wy=E(_ww.b);if(!B(_sV(B(_v2(_wy.a,_sh)),B(_v2(_tM,_wy.b))))){return E(_wx);}else{var _wz=B(_wf(B(_wd(_wt))));return new F(function(){return A3(_wq,_wz,_wx,new T(function(){return B(A2(_wh,_wz,_sh));}));});}},_wA=479723520,_wB=40233135,_wC=new T2(1,_wB,_v),_wD=new T2(1,_wA,_wC),_wE=new T(function(){return B(_rT(_5Q,_wD));}),_wF=new T1(0,40587),_wG=function(_wH){var _wI=new T(function(){var _wJ=B(_w7(_wH,_sh,_s0,_sh)),_wK=B(_w7(_wE,_sh,_s0,_sh)),_wL=B(_w7(_wJ.a,_wJ.b,_wK.a,_wK.b));return B(_ws(_vO,_wL.a,_wL.b));});return new T2(0,new T(function(){return B(_rF(_wF,_wI));}),new T(function(){return B(_sr(_wH,B(_vQ(_s1,B(_v2(_wI,_s0)),_wE))));}));},_wM=function(_wN,_wO){var _wP=E(_wO);if(!_wP._){return __Z;}else{var _wQ=_wP.a,_wR=E(_wN);return (_wR==1)?new T2(1,_wQ,_v):new T2(1,_wQ,new T(function(){return B(_wM(_wR-1|0,_wP.b));}));}},_wS=function(_wT,_){var _wU=__get(_wT,0),_wV=__get(_wT,1),_wW=Number(_wU),_wX=jsTrunc(_wW),_wY=Number(_wV),_wZ=jsTrunc(_wY);return new T2(0,_wX,_wZ);},_x0=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_x1=660865024,_x2=465661287,_x3=new T2(1,_x2,_v),_x4=new T2(1,_x1,_x3),_x5=new T(function(){return B(_rT(_5Q,_x4));}),_x6=function(_){var _x7=__app0(E(_x0)),_x8=B(_wS(_x7,_));return new T(function(){var _x9=E(_x8);if(!B(_tE(_x5,_vP))){return B(_rF(B(_v2(B(_tr(E(_x9.a))),_s0)),B(_tw(B(_v2(B(_v2(B(_tr(E(_x9.b))),_s0)),_s0)),_x5))));}else{return E(_rf);}});},_xa=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_xb=new T(function(){return B(err(_xa));}),_xc=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_xd=new T(function(){return B(err(_xc));}),_xe=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_xf=function(_xg){return new F(function(){return _bc(new T1(0,new T(function(){return B(_bq(_xg,_xe));})),_aW);});},_xh=new T(function(){return B(_xf("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_xi=function(_xj,_xk){while(1){var _xl=B((function(_xm,_xn){var _xo=E(_xm);switch(_xo._){case 0:var _xp=E(_xn);if(!_xp._){return __Z;}else{_xj=B(A1(_xo.a,_xp.a));_xk=_xp.b;return __continue;}break;case 1:var _xq=B(A1(_xo.a,_xn)),_xr=_xn;_xj=_xq;_xk=_xr;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_xo.a,_xn),new T(function(){return B(_xi(_xo.b,_xn));}));default:return E(_xo.a);}})(_xj,_xk));if(_xl!=__continue){return _xl;}}},_xs=function(_xt,_xu){var _xv=function(_xw){var _xx=E(_xu);if(_xx._==3){return new T2(3,_xx.a,new T(function(){return B(_xs(_xt,_xx.b));}));}else{var _xy=E(_xt);if(_xy._==2){return E(_xx);}else{var _xz=E(_xx);if(_xz._==2){return E(_xy);}else{var _xA=function(_xB){var _xC=E(_xz);if(_xC._==4){var _xD=function(_xE){return new T1(4,new T(function(){return B(_3(B(_xi(_xy,_xE)),_xC.a));}));};return new T1(1,_xD);}else{var _xF=E(_xy);if(_xF._==1){var _xG=_xF.a,_xH=E(_xC);if(!_xH._){return new T1(1,function(_xI){return new F(function(){return _xs(B(A1(_xG,_xI)),_xH);});});}else{var _xJ=function(_xK){return new F(function(){return _xs(B(A1(_xG,_xK)),new T(function(){return B(A1(_xH.a,_xK));}));});};return new T1(1,_xJ);}}else{var _xL=E(_xC);if(!_xL._){return E(_xh);}else{var _xM=function(_xN){return new F(function(){return _xs(_xF,new T(function(){return B(A1(_xL.a,_xN));}));});};return new T1(1,_xM);}}}},_xO=E(_xy);switch(_xO._){case 1:var _xP=E(_xz);if(_xP._==4){var _xQ=function(_xR){return new T1(4,new T(function(){return B(_3(B(_xi(B(A1(_xO.a,_xR)),_xR)),_xP.a));}));};return new T1(1,_xQ);}else{return new F(function(){return _xA(_);});}break;case 4:var _xS=_xO.a,_xT=E(_xz);switch(_xT._){case 0:var _xU=function(_xV){var _xW=new T(function(){return B(_3(_xS,new T(function(){return B(_xi(_xT,_xV));},1)));});return new T1(4,_xW);};return new T1(1,_xU);case 1:var _xX=function(_xY){var _xZ=new T(function(){return B(_3(_xS,new T(function(){return B(_xi(B(A1(_xT.a,_xY)),_xY));},1)));});return new T1(4,_xZ);};return new T1(1,_xX);default:return new T1(4,new T(function(){return B(_3(_xS,_xT.a));}));}break;default:return new F(function(){return _xA(_);});}}}}},_y0=E(_xt);switch(_y0._){case 0:var _y1=E(_xu);if(!_y1._){var _y2=function(_y3){return new F(function(){return _xs(B(A1(_y0.a,_y3)),new T(function(){return B(A1(_y1.a,_y3));}));});};return new T1(0,_y2);}else{return new F(function(){return _xv(_);});}break;case 3:return new T2(3,_y0.a,new T(function(){return B(_xs(_y0.b,_xu));}));default:return new F(function(){return _xv(_);});}},_y4=new T(function(){return B(unCStr("("));}),_y5=new T(function(){return B(unCStr(")"));}),_y6=function(_y7,_y8){return (!B(_7z(_y7,_y8)))?true:false;},_y9=new T2(0,_7z,_y6),_ya=function(_yb,_yc){var _yd=E(_yb);switch(_yd._){case 0:return new T1(0,function(_ye){return new F(function(){return _ya(B(A1(_yd.a,_ye)),_yc);});});case 1:return new T1(1,function(_yf){return new F(function(){return _ya(B(A1(_yd.a,_yf)),_yc);});});case 2:return new T0(2);case 3:return new F(function(){return _xs(B(A1(_yc,_yd.a)),new T(function(){return B(_ya(_yd.b,_yc));}));});break;default:var _yg=function(_yh){var _yi=E(_yh);if(!_yi._){return __Z;}else{var _yj=E(_yi.a);return new F(function(){return _3(B(_xi(B(A1(_yc,_yj.a)),_yj.b)),new T(function(){return B(_yg(_yi.b));},1));});}},_yk=B(_yg(_yd.a));return (_yk._==0)?new T0(2):new T1(4,_yk);}},_yl=new T0(2),_ym=function(_yn){return new T2(3,_yn,_yl);},_yo=function(_yp,_yq){var _yr=E(_yp);if(!_yr){return new F(function(){return A1(_yq,_5L);});}else{var _ys=new T(function(){return B(_yo(_yr-1|0,_yq));});return new T1(0,function(_yt){return E(_ys);});}},_yu=function(_yv,_yw,_yx){var _yy=new T(function(){return B(A1(_yv,_ym));}),_yz=function(_yA,_yB,_yC,_yD){while(1){var _yE=B((function(_yF,_yG,_yH,_yI){var _yJ=E(_yF);switch(_yJ._){case 0:var _yK=E(_yG);if(!_yK._){return new F(function(){return A1(_yw,_yI);});}else{var _yL=_yH+1|0,_yM=_yI;_yA=B(A1(_yJ.a,_yK.a));_yB=_yK.b;_yC=_yL;_yD=_yM;return __continue;}break;case 1:var _yN=B(A1(_yJ.a,_yG)),_yO=_yG,_yL=_yH,_yM=_yI;_yA=_yN;_yB=_yO;_yC=_yL;_yD=_yM;return __continue;case 2:return new F(function(){return A1(_yw,_yI);});break;case 3:var _yP=new T(function(){return B(_ya(_yJ,_yI));});return new F(function(){return _yo(_yH,function(_yQ){return E(_yP);});});break;default:return new F(function(){return _ya(_yJ,_yI);});}})(_yA,_yB,_yC,_yD));if(_yE!=__continue){return _yE;}}};return function(_yR){return new F(function(){return _yz(_yy,_yR,0,_yx);});};},_yS=function(_yT){return new F(function(){return A1(_yT,_v);});},_yU=function(_yV,_yW){var _yX=function(_yY){var _yZ=E(_yY);if(!_yZ._){return E(_yS);}else{var _z0=_yZ.a;if(!B(A1(_yV,_z0))){return E(_yS);}else{var _z1=new T(function(){return B(_yX(_yZ.b));}),_z2=function(_z3){var _z4=new T(function(){return B(A1(_z1,function(_z5){return new F(function(){return A1(_z3,new T2(1,_z0,_z5));});}));});return new T1(0,function(_z6){return E(_z4);});};return E(_z2);}}};return function(_z7){return new F(function(){return A2(_yX,_z7,_yW);});};},_z8=new T0(6),_z9=new T(function(){return B(unCStr("valDig: Bad base"));}),_za=new T(function(){return B(err(_z9));}),_zb=function(_zc,_zd){var _ze=function(_zf,_zg){var _zh=E(_zf);if(!_zh._){var _zi=new T(function(){return B(A1(_zg,_v));});return function(_zj){return new F(function(){return A1(_zj,_zi);});};}else{var _zk=E(_zh.a),_zl=function(_zm){var _zn=new T(function(){return B(_ze(_zh.b,function(_zo){return new F(function(){return A1(_zg,new T2(1,_zm,_zo));});}));}),_zp=function(_zq){var _zr=new T(function(){return B(A1(_zn,_zq));});return new T1(0,function(_zs){return E(_zr);});};return E(_zp);};switch(E(_zc)){case 8:if(48>_zk){var _zt=new T(function(){return B(A1(_zg,_v));});return function(_zu){return new F(function(){return A1(_zu,_zt);});};}else{if(_zk>55){var _zv=new T(function(){return B(A1(_zg,_v));});return function(_zw){return new F(function(){return A1(_zw,_zv);});};}else{return new F(function(){return _zl(_zk-48|0);});}}break;case 10:if(48>_zk){var _zx=new T(function(){return B(A1(_zg,_v));});return function(_zy){return new F(function(){return A1(_zy,_zx);});};}else{if(_zk>57){var _zz=new T(function(){return B(A1(_zg,_v));});return function(_zA){return new F(function(){return A1(_zA,_zz);});};}else{return new F(function(){return _zl(_zk-48|0);});}}break;case 16:if(48>_zk){if(97>_zk){if(65>_zk){var _zB=new T(function(){return B(A1(_zg,_v));});return function(_zC){return new F(function(){return A1(_zC,_zB);});};}else{if(_zk>70){var _zD=new T(function(){return B(A1(_zg,_v));});return function(_zE){return new F(function(){return A1(_zE,_zD);});};}else{return new F(function(){return _zl((_zk-65|0)+10|0);});}}}else{if(_zk>102){if(65>_zk){var _zF=new T(function(){return B(A1(_zg,_v));});return function(_zG){return new F(function(){return A1(_zG,_zF);});};}else{if(_zk>70){var _zH=new T(function(){return B(A1(_zg,_v));});return function(_zI){return new F(function(){return A1(_zI,_zH);});};}else{return new F(function(){return _zl((_zk-65|0)+10|0);});}}}else{return new F(function(){return _zl((_zk-97|0)+10|0);});}}}else{if(_zk>57){if(97>_zk){if(65>_zk){var _zJ=new T(function(){return B(A1(_zg,_v));});return function(_zK){return new F(function(){return A1(_zK,_zJ);});};}else{if(_zk>70){var _zL=new T(function(){return B(A1(_zg,_v));});return function(_zM){return new F(function(){return A1(_zM,_zL);});};}else{return new F(function(){return _zl((_zk-65|0)+10|0);});}}}else{if(_zk>102){if(65>_zk){var _zN=new T(function(){return B(A1(_zg,_v));});return function(_zO){return new F(function(){return A1(_zO,_zN);});};}else{if(_zk>70){var _zP=new T(function(){return B(A1(_zg,_v));});return function(_zQ){return new F(function(){return A1(_zQ,_zP);});};}else{return new F(function(){return _zl((_zk-65|0)+10|0);});}}}else{return new F(function(){return _zl((_zk-97|0)+10|0);});}}}else{return new F(function(){return _zl(_zk-48|0);});}}break;default:return E(_za);}}},_zR=function(_zS){var _zT=E(_zS);if(!_zT._){return new T0(2);}else{return new F(function(){return A1(_zd,_zT);});}};return function(_zU){return new F(function(){return A3(_ze,_zU,_5x,_zR);});};},_zV=16,_zW=8,_zX=function(_zY){var _zZ=function(_A0){return new F(function(){return A1(_zY,new T1(5,new T2(0,_zW,_A0)));});},_A1=function(_A2){return new F(function(){return A1(_zY,new T1(5,new T2(0,_zV,_A2)));});},_A3=function(_A4){switch(E(_A4)){case 79:return new T1(1,B(_zb(_zW,_zZ)));case 88:return new T1(1,B(_zb(_zV,_A1)));case 111:return new T1(1,B(_zb(_zW,_zZ)));case 120:return new T1(1,B(_zb(_zV,_A1)));default:return new T0(2);}};return function(_A5){return (E(_A5)==48)?E(new T1(0,_A3)):new T0(2);};},_A6=function(_A7){return new T1(0,B(_zX(_A7)));},_A8=function(_A9){return new F(function(){return A1(_A9,_2q);});},_Aa=function(_Ab){return new F(function(){return A1(_Ab,_2q);});},_Ac=10,_Ad=new T1(0,10),_Ae=function(_Af){return new F(function(){return _tr(E(_Af));});},_Ag=new T(function(){return B(unCStr("this should not happen"));}),_Ah=new T(function(){return B(err(_Ag));}),_Ai=function(_Aj,_Ak){var _Al=E(_Ak);if(!_Al._){return __Z;}else{var _Am=E(_Al.b);return (_Am._==0)?E(_Ah):new T2(1,B(_rF(B(_v2(_Al.a,_Aj)),_Am.a)),new T(function(){return B(_Ai(_Aj,_Am.b));}));}},_An=new T1(0,0),_Ao=function(_Ap,_Aq,_Ar){while(1){var _As=B((function(_At,_Au,_Av){var _Aw=E(_Av);if(!_Aw._){return E(_An);}else{if(!E(_Aw.b)._){return E(_Aw.a);}else{var _Ax=E(_Au);if(_Ax<=40){var _Ay=function(_Az,_AA){while(1){var _AB=E(_AA);if(!_AB._){return E(_Az);}else{var _AC=B(_rF(B(_v2(_Az,_At)),_AB.a));_Az=_AC;_AA=_AB.b;continue;}}};return new F(function(){return _Ay(_An,_Aw);});}else{var _AD=B(_v2(_At,_At));if(!(_Ax%2)){var _AE=B(_Ai(_At,_Aw));_Ap=_AD;_Aq=quot(_Ax+1|0,2);_Ar=_AE;return __continue;}else{var _AE=B(_Ai(_At,new T2(1,_An,_Aw)));_Ap=_AD;_Aq=quot(_Ax+1|0,2);_Ar=_AE;return __continue;}}}}})(_Ap,_Aq,_Ar));if(_As!=__continue){return _As;}}},_AF=function(_AG,_AH){return new F(function(){return _Ao(_AG,new T(function(){return B(_9X(_AH,0));},1),B(_df(_Ae,_AH)));});},_AI=function(_AJ){var _AK=new T(function(){var _AL=new T(function(){var _AM=function(_AN){return new F(function(){return A1(_AJ,new T1(1,new T(function(){return B(_AF(_Ad,_AN));})));});};return new T1(1,B(_zb(_Ac,_AM)));}),_AO=function(_AP){if(E(_AP)==43){var _AQ=function(_AR){return new F(function(){return A1(_AJ,new T1(1,new T(function(){return B(_AF(_Ad,_AR));})));});};return new T1(1,B(_zb(_Ac,_AQ)));}else{return new T0(2);}},_AS=function(_AT){if(E(_AT)==45){var _AU=function(_AV){return new F(function(){return A1(_AJ,new T1(1,new T(function(){return B(_rP(B(_AF(_Ad,_AV))));})));});};return new T1(1,B(_zb(_Ac,_AU)));}else{return new T0(2);}};return B(_xs(B(_xs(new T1(0,_AS),new T1(0,_AO))),_AL));});return new F(function(){return _xs(new T1(0,function(_AW){return (E(_AW)==101)?E(_AK):new T0(2);}),new T1(0,function(_AX){return (E(_AX)==69)?E(_AK):new T0(2);}));});},_AY=function(_AZ){var _B0=function(_B1){return new F(function(){return A1(_AZ,new T1(1,_B1));});};return function(_B2){return (E(_B2)==46)?new T1(1,B(_zb(_Ac,_B0))):new T0(2);};},_B3=function(_B4){return new T1(0,B(_AY(_B4)));},_B5=function(_B6){var _B7=function(_B8){var _B9=function(_Ba){return new T1(1,B(_yu(_AI,_A8,function(_Bb){return new F(function(){return A1(_B6,new T1(5,new T3(1,_B8,_Ba,_Bb)));});})));};return new T1(1,B(_yu(_B3,_Aa,_B9)));};return new F(function(){return _zb(_Ac,_B7);});},_Bc=function(_Bd){return new T1(1,B(_B5(_Bd)));},_Be=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_Bf=function(_Bg){return new F(function(){return _4d(_f3,_Bg,_Be);});},_Bh=function(_Bi){var _Bj=new T(function(){return B(A1(_Bi,_zW));}),_Bk=new T(function(){return B(A1(_Bi,_zV));});return function(_Bl){switch(E(_Bl)){case 79:return E(_Bj);case 88:return E(_Bk);case 111:return E(_Bj);case 120:return E(_Bk);default:return new T0(2);}};},_Bm=function(_Bn){return new T1(0,B(_Bh(_Bn)));},_Bo=function(_Bp){return new F(function(){return A1(_Bp,_Ac);});},_Bq=function(_Br){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_d(9,_Br,_v));}))));});},_Bs=function(_Bt){return new T0(2);},_Bu=function(_Bv){var _Bw=E(_Bv);if(!_Bw._){return E(_Bs);}else{var _Bx=_Bw.a,_By=E(_Bw.b);if(!_By._){return E(_Bx);}else{var _Bz=new T(function(){return B(_Bu(_By));}),_BA=function(_BB){return new F(function(){return _xs(B(A1(_Bx,_BB)),new T(function(){return B(A1(_Bz,_BB));}));});};return E(_BA);}}},_BC=function(_BD,_BE){var _BF=function(_BG,_BH,_BI){var _BJ=E(_BG);if(!_BJ._){return new F(function(){return A1(_BI,_BD);});}else{var _BK=E(_BH);if(!_BK._){return new T0(2);}else{if(E(_BJ.a)!=E(_BK.a)){return new T0(2);}else{var _BL=new T(function(){return B(_BF(_BJ.b,_BK.b,_BI));});return new T1(0,function(_BM){return E(_BL);});}}}};return function(_BN){return new F(function(){return _BF(_BD,_BN,_BE);});};},_BO=new T(function(){return B(unCStr("SO"));}),_BP=14,_BQ=function(_BR){var _BS=new T(function(){return B(A1(_BR,_BP));});return new T1(1,B(_BC(_BO,function(_BT){return E(_BS);})));},_BU=new T(function(){return B(unCStr("SOH"));}),_BV=1,_BW=function(_BX){var _BY=new T(function(){return B(A1(_BX,_BV));});return new T1(1,B(_BC(_BU,function(_BZ){return E(_BY);})));},_C0=function(_C1){return new T1(1,B(_yu(_BW,_BQ,_C1)));},_C2=new T(function(){return B(unCStr("NUL"));}),_C3=0,_C4=function(_C5){var _C6=new T(function(){return B(A1(_C5,_C3));});return new T1(1,B(_BC(_C2,function(_C7){return E(_C6);})));},_C8=new T(function(){return B(unCStr("STX"));}),_C9=2,_Ca=function(_Cb){var _Cc=new T(function(){return B(A1(_Cb,_C9));});return new T1(1,B(_BC(_C8,function(_Cd){return E(_Cc);})));},_Ce=new T(function(){return B(unCStr("ETX"));}),_Cf=3,_Cg=function(_Ch){var _Ci=new T(function(){return B(A1(_Ch,_Cf));});return new T1(1,B(_BC(_Ce,function(_Cj){return E(_Ci);})));},_Ck=new T(function(){return B(unCStr("EOT"));}),_Cl=4,_Cm=function(_Cn){var _Co=new T(function(){return B(A1(_Cn,_Cl));});return new T1(1,B(_BC(_Ck,function(_Cp){return E(_Co);})));},_Cq=new T(function(){return B(unCStr("ENQ"));}),_Cr=5,_Cs=function(_Ct){var _Cu=new T(function(){return B(A1(_Ct,_Cr));});return new T1(1,B(_BC(_Cq,function(_Cv){return E(_Cu);})));},_Cw=new T(function(){return B(unCStr("ACK"));}),_Cx=6,_Cy=function(_Cz){var _CA=new T(function(){return B(A1(_Cz,_Cx));});return new T1(1,B(_BC(_Cw,function(_CB){return E(_CA);})));},_CC=new T(function(){return B(unCStr("BEL"));}),_CD=7,_CE=function(_CF){var _CG=new T(function(){return B(A1(_CF,_CD));});return new T1(1,B(_BC(_CC,function(_CH){return E(_CG);})));},_CI=new T(function(){return B(unCStr("BS"));}),_CJ=8,_CK=function(_CL){var _CM=new T(function(){return B(A1(_CL,_CJ));});return new T1(1,B(_BC(_CI,function(_CN){return E(_CM);})));},_CO=new T(function(){return B(unCStr("HT"));}),_CP=9,_CQ=function(_CR){var _CS=new T(function(){return B(A1(_CR,_CP));});return new T1(1,B(_BC(_CO,function(_CT){return E(_CS);})));},_CU=new T(function(){return B(unCStr("LF"));}),_CV=10,_CW=function(_CX){var _CY=new T(function(){return B(A1(_CX,_CV));});return new T1(1,B(_BC(_CU,function(_CZ){return E(_CY);})));},_D0=new T(function(){return B(unCStr("VT"));}),_D1=11,_D2=function(_D3){var _D4=new T(function(){return B(A1(_D3,_D1));});return new T1(1,B(_BC(_D0,function(_D5){return E(_D4);})));},_D6=new T(function(){return B(unCStr("FF"));}),_D7=12,_D8=function(_D9){var _Da=new T(function(){return B(A1(_D9,_D7));});return new T1(1,B(_BC(_D6,function(_Db){return E(_Da);})));},_Dc=new T(function(){return B(unCStr("CR"));}),_Dd=13,_De=function(_Df){var _Dg=new T(function(){return B(A1(_Df,_Dd));});return new T1(1,B(_BC(_Dc,function(_Dh){return E(_Dg);})));},_Di=new T(function(){return B(unCStr("SI"));}),_Dj=15,_Dk=function(_Dl){var _Dm=new T(function(){return B(A1(_Dl,_Dj));});return new T1(1,B(_BC(_Di,function(_Dn){return E(_Dm);})));},_Do=new T(function(){return B(unCStr("DLE"));}),_Dp=16,_Dq=function(_Dr){var _Ds=new T(function(){return B(A1(_Dr,_Dp));});return new T1(1,B(_BC(_Do,function(_Dt){return E(_Ds);})));},_Du=new T(function(){return B(unCStr("DC1"));}),_Dv=17,_Dw=function(_Dx){var _Dy=new T(function(){return B(A1(_Dx,_Dv));});return new T1(1,B(_BC(_Du,function(_Dz){return E(_Dy);})));},_DA=new T(function(){return B(unCStr("DC2"));}),_DB=18,_DC=function(_DD){var _DE=new T(function(){return B(A1(_DD,_DB));});return new T1(1,B(_BC(_DA,function(_DF){return E(_DE);})));},_DG=new T(function(){return B(unCStr("DC3"));}),_DH=19,_DI=function(_DJ){var _DK=new T(function(){return B(A1(_DJ,_DH));});return new T1(1,B(_BC(_DG,function(_DL){return E(_DK);})));},_DM=new T(function(){return B(unCStr("DC4"));}),_DN=20,_DO=function(_DP){var _DQ=new T(function(){return B(A1(_DP,_DN));});return new T1(1,B(_BC(_DM,function(_DR){return E(_DQ);})));},_DS=new T(function(){return B(unCStr("NAK"));}),_DT=21,_DU=function(_DV){var _DW=new T(function(){return B(A1(_DV,_DT));});return new T1(1,B(_BC(_DS,function(_DX){return E(_DW);})));},_DY=new T(function(){return B(unCStr("SYN"));}),_DZ=22,_E0=function(_E1){var _E2=new T(function(){return B(A1(_E1,_DZ));});return new T1(1,B(_BC(_DY,function(_E3){return E(_E2);})));},_E4=new T(function(){return B(unCStr("ETB"));}),_E5=23,_E6=function(_E7){var _E8=new T(function(){return B(A1(_E7,_E5));});return new T1(1,B(_BC(_E4,function(_E9){return E(_E8);})));},_Ea=new T(function(){return B(unCStr("CAN"));}),_Eb=24,_Ec=function(_Ed){var _Ee=new T(function(){return B(A1(_Ed,_Eb));});return new T1(1,B(_BC(_Ea,function(_Ef){return E(_Ee);})));},_Eg=new T(function(){return B(unCStr("EM"));}),_Eh=25,_Ei=function(_Ej){var _Ek=new T(function(){return B(A1(_Ej,_Eh));});return new T1(1,B(_BC(_Eg,function(_El){return E(_Ek);})));},_Em=new T(function(){return B(unCStr("SUB"));}),_En=26,_Eo=function(_Ep){var _Eq=new T(function(){return B(A1(_Ep,_En));});return new T1(1,B(_BC(_Em,function(_Er){return E(_Eq);})));},_Es=new T(function(){return B(unCStr("ESC"));}),_Et=27,_Eu=function(_Ev){var _Ew=new T(function(){return B(A1(_Ev,_Et));});return new T1(1,B(_BC(_Es,function(_Ex){return E(_Ew);})));},_Ey=new T(function(){return B(unCStr("FS"));}),_Ez=28,_EA=function(_EB){var _EC=new T(function(){return B(A1(_EB,_Ez));});return new T1(1,B(_BC(_Ey,function(_ED){return E(_EC);})));},_EE=new T(function(){return B(unCStr("GS"));}),_EF=29,_EG=function(_EH){var _EI=new T(function(){return B(A1(_EH,_EF));});return new T1(1,B(_BC(_EE,function(_EJ){return E(_EI);})));},_EK=new T(function(){return B(unCStr("RS"));}),_EL=30,_EM=function(_EN){var _EO=new T(function(){return B(A1(_EN,_EL));});return new T1(1,B(_BC(_EK,function(_EP){return E(_EO);})));},_EQ=new T(function(){return B(unCStr("US"));}),_ER=31,_ES=function(_ET){var _EU=new T(function(){return B(A1(_ET,_ER));});return new T1(1,B(_BC(_EQ,function(_EV){return E(_EU);})));},_EW=new T(function(){return B(unCStr("SP"));}),_EX=32,_EY=function(_EZ){var _F0=new T(function(){return B(A1(_EZ,_EX));});return new T1(1,B(_BC(_EW,function(_F1){return E(_F0);})));},_F2=new T(function(){return B(unCStr("DEL"));}),_F3=127,_F4=function(_F5){var _F6=new T(function(){return B(A1(_F5,_F3));});return new T1(1,B(_BC(_F2,function(_F7){return E(_F6);})));},_F8=new T2(1,_F4,_v),_F9=new T2(1,_EY,_F8),_Fa=new T2(1,_ES,_F9),_Fb=new T2(1,_EM,_Fa),_Fc=new T2(1,_EG,_Fb),_Fd=new T2(1,_EA,_Fc),_Fe=new T2(1,_Eu,_Fd),_Ff=new T2(1,_Eo,_Fe),_Fg=new T2(1,_Ei,_Ff),_Fh=new T2(1,_Ec,_Fg),_Fi=new T2(1,_E6,_Fh),_Fj=new T2(1,_E0,_Fi),_Fk=new T2(1,_DU,_Fj),_Fl=new T2(1,_DO,_Fk),_Fm=new T2(1,_DI,_Fl),_Fn=new T2(1,_DC,_Fm),_Fo=new T2(1,_Dw,_Fn),_Fp=new T2(1,_Dq,_Fo),_Fq=new T2(1,_Dk,_Fp),_Fr=new T2(1,_De,_Fq),_Fs=new T2(1,_D8,_Fr),_Ft=new T2(1,_D2,_Fs),_Fu=new T2(1,_CW,_Ft),_Fv=new T2(1,_CQ,_Fu),_Fw=new T2(1,_CK,_Fv),_Fx=new T2(1,_CE,_Fw),_Fy=new T2(1,_Cy,_Fx),_Fz=new T2(1,_Cs,_Fy),_FA=new T2(1,_Cm,_Fz),_FB=new T2(1,_Cg,_FA),_FC=new T2(1,_Ca,_FB),_FD=new T2(1,_C4,_FC),_FE=new T2(1,_C0,_FD),_FF=new T(function(){return B(_Bu(_FE));}),_FG=34,_FH=new T1(0,1114111),_FI=92,_FJ=39,_FK=function(_FL){var _FM=new T(function(){return B(A1(_FL,_CD));}),_FN=new T(function(){return B(A1(_FL,_CJ));}),_FO=new T(function(){return B(A1(_FL,_CP));}),_FP=new T(function(){return B(A1(_FL,_CV));}),_FQ=new T(function(){return B(A1(_FL,_D1));}),_FR=new T(function(){return B(A1(_FL,_D7));}),_FS=new T(function(){return B(A1(_FL,_Dd));}),_FT=new T(function(){return B(A1(_FL,_FI));}),_FU=new T(function(){return B(A1(_FL,_FJ));}),_FV=new T(function(){return B(A1(_FL,_FG));}),_FW=new T(function(){var _FX=function(_FY){var _FZ=new T(function(){return B(_tr(E(_FY)));}),_G0=function(_G1){var _G2=B(_AF(_FZ,_G1));if(!B(_vk(_G2,_FH))){return new T0(2);}else{return new F(function(){return A1(_FL,new T(function(){var _G3=B(_ti(_G2));if(_G3>>>0>1114111){return B(_Bq(_G3));}else{return _G3;}}));});}};return new T1(1,B(_zb(_FY,_G0)));},_G4=new T(function(){var _G5=new T(function(){return B(A1(_FL,_ER));}),_G6=new T(function(){return B(A1(_FL,_EL));}),_G7=new T(function(){return B(A1(_FL,_EF));}),_G8=new T(function(){return B(A1(_FL,_Ez));}),_G9=new T(function(){return B(A1(_FL,_Et));}),_Ga=new T(function(){return B(A1(_FL,_En));}),_Gb=new T(function(){return B(A1(_FL,_Eh));}),_Gc=new T(function(){return B(A1(_FL,_Eb));}),_Gd=new T(function(){return B(A1(_FL,_E5));}),_Ge=new T(function(){return B(A1(_FL,_DZ));}),_Gf=new T(function(){return B(A1(_FL,_DT));}),_Gg=new T(function(){return B(A1(_FL,_DN));}),_Gh=new T(function(){return B(A1(_FL,_DH));}),_Gi=new T(function(){return B(A1(_FL,_DB));}),_Gj=new T(function(){return B(A1(_FL,_Dv));}),_Gk=new T(function(){return B(A1(_FL,_Dp));}),_Gl=new T(function(){return B(A1(_FL,_Dj));}),_Gm=new T(function(){return B(A1(_FL,_BP));}),_Gn=new T(function(){return B(A1(_FL,_Cx));}),_Go=new T(function(){return B(A1(_FL,_Cr));}),_Gp=new T(function(){return B(A1(_FL,_Cl));}),_Gq=new T(function(){return B(A1(_FL,_Cf));}),_Gr=new T(function(){return B(A1(_FL,_C9));}),_Gs=new T(function(){return B(A1(_FL,_BV));}),_Gt=new T(function(){return B(A1(_FL,_C3));}),_Gu=function(_Gv){switch(E(_Gv)){case 64:return E(_Gt);case 65:return E(_Gs);case 66:return E(_Gr);case 67:return E(_Gq);case 68:return E(_Gp);case 69:return E(_Go);case 70:return E(_Gn);case 71:return E(_FM);case 72:return E(_FN);case 73:return E(_FO);case 74:return E(_FP);case 75:return E(_FQ);case 76:return E(_FR);case 77:return E(_FS);case 78:return E(_Gm);case 79:return E(_Gl);case 80:return E(_Gk);case 81:return E(_Gj);case 82:return E(_Gi);case 83:return E(_Gh);case 84:return E(_Gg);case 85:return E(_Gf);case 86:return E(_Ge);case 87:return E(_Gd);case 88:return E(_Gc);case 89:return E(_Gb);case 90:return E(_Ga);case 91:return E(_G9);case 92:return E(_G8);case 93:return E(_G7);case 94:return E(_G6);case 95:return E(_G5);default:return new T0(2);}};return B(_xs(new T1(0,function(_Gw){return (E(_Gw)==94)?E(new T1(0,_Gu)):new T0(2);}),new T(function(){return B(A1(_FF,_FL));})));});return B(_xs(new T1(1,B(_yu(_Bm,_Bo,_FX))),_G4));});return new F(function(){return _xs(new T1(0,function(_Gx){switch(E(_Gx)){case 34:return E(_FV);case 39:return E(_FU);case 92:return E(_FT);case 97:return E(_FM);case 98:return E(_FN);case 102:return E(_FR);case 110:return E(_FP);case 114:return E(_FS);case 116:return E(_FO);case 118:return E(_FQ);default:return new T0(2);}}),_FW);});},_Gy=function(_Gz){return new F(function(){return A1(_Gz,_5L);});},_GA=function(_GB){var _GC=E(_GB);if(!_GC._){return E(_Gy);}else{var _GD=E(_GC.a),_GE=_GD>>>0,_GF=new T(function(){return B(_GA(_GC.b));});if(_GE>887){var _GG=u_iswspace(_GD);if(!E(_GG)){return E(_Gy);}else{var _GH=function(_GI){var _GJ=new T(function(){return B(A1(_GF,_GI));});return new T1(0,function(_GK){return E(_GJ);});};return E(_GH);}}else{var _GL=E(_GE);if(_GL==32){var _GM=function(_GN){var _GO=new T(function(){return B(A1(_GF,_GN));});return new T1(0,function(_GP){return E(_GO);});};return E(_GM);}else{if(_GL-9>>>0>4){if(E(_GL)==160){var _GQ=function(_GR){var _GS=new T(function(){return B(A1(_GF,_GR));});return new T1(0,function(_GT){return E(_GS);});};return E(_GQ);}else{return E(_Gy);}}else{var _GU=function(_GV){var _GW=new T(function(){return B(A1(_GF,_GV));});return new T1(0,function(_GX){return E(_GW);});};return E(_GU);}}}}},_GY=function(_GZ){var _H0=new T(function(){return B(_GY(_GZ));}),_H1=function(_H2){return (E(_H2)==92)?E(_H0):new T0(2);},_H3=function(_H4){return E(new T1(0,_H1));},_H5=new T1(1,function(_H6){return new F(function(){return A2(_GA,_H6,_H3);});}),_H7=new T(function(){return B(_FK(function(_H8){return new F(function(){return A1(_GZ,new T2(0,_H8,_5Q));});}));}),_H9=function(_Ha){var _Hb=E(_Ha);if(_Hb==38){return E(_H0);}else{var _Hc=_Hb>>>0;if(_Hc>887){var _Hd=u_iswspace(_Hb);return (E(_Hd)==0)?new T0(2):E(_H5);}else{var _He=E(_Hc);return (_He==32)?E(_H5):(_He-9>>>0>4)?(E(_He)==160)?E(_H5):new T0(2):E(_H5);}}};return new F(function(){return _xs(new T1(0,function(_Hf){return (E(_Hf)==92)?E(new T1(0,_H9)):new T0(2);}),new T1(0,function(_Hg){var _Hh=E(_Hg);if(E(_Hh)==92){return E(_H7);}else{return new F(function(){return A1(_GZ,new T2(0,_Hh,_5N));});}}));});},_Hi=function(_Hj,_Hk){var _Hl=new T(function(){return B(A1(_Hk,new T1(1,new T(function(){return B(A1(_Hj,_v));}))));}),_Hm=function(_Hn){var _Ho=E(_Hn),_Hp=E(_Ho.a);if(E(_Hp)==34){if(!E(_Ho.b)){return E(_Hl);}else{return new F(function(){return _Hi(function(_Hq){return new F(function(){return A1(_Hj,new T2(1,_Hp,_Hq));});},_Hk);});}}else{return new F(function(){return _Hi(function(_Hr){return new F(function(){return A1(_Hj,new T2(1,_Hp,_Hr));});},_Hk);});}};return new F(function(){return _GY(_Hm);});},_Hs=new T(function(){return B(unCStr("_\'"));}),_Ht=function(_Hu){var _Hv=u_iswalnum(_Hu);if(!E(_Hv)){return new F(function(){return _4d(_f3,_Hu,_Hs);});}else{return true;}},_Hw=function(_Hx){return new F(function(){return _Ht(E(_Hx));});},_Hy=new T(function(){return B(unCStr(",;()[]{}`"));}),_Hz=new T(function(){return B(unCStr("=>"));}),_HA=new T2(1,_Hz,_v),_HB=new T(function(){return B(unCStr("~"));}),_HC=new T2(1,_HB,_HA),_HD=new T(function(){return B(unCStr("@"));}),_HE=new T2(1,_HD,_HC),_HF=new T(function(){return B(unCStr("->"));}),_HG=new T2(1,_HF,_HE),_HH=new T(function(){return B(unCStr("<-"));}),_HI=new T2(1,_HH,_HG),_HJ=new T(function(){return B(unCStr("|"));}),_HK=new T2(1,_HJ,_HI),_HL=new T(function(){return B(unCStr("\\"));}),_HM=new T2(1,_HL,_HK),_HN=new T(function(){return B(unCStr("="));}),_HO=new T2(1,_HN,_HM),_HP=new T(function(){return B(unCStr("::"));}),_HQ=new T2(1,_HP,_HO),_HR=new T(function(){return B(unCStr(".."));}),_HS=new T2(1,_HR,_HQ),_HT=function(_HU){var _HV=new T(function(){return B(A1(_HU,_z8));}),_HW=new T(function(){var _HX=new T(function(){var _HY=function(_HZ){var _I0=new T(function(){return B(A1(_HU,new T1(0,_HZ)));});return new T1(0,function(_I1){return (E(_I1)==39)?E(_I0):new T0(2);});};return B(_FK(_HY));}),_I2=function(_I3){var _I4=E(_I3);switch(E(_I4)){case 39:return new T0(2);case 92:return E(_HX);default:var _I5=new T(function(){return B(A1(_HU,new T1(0,_I4)));});return new T1(0,function(_I6){return (E(_I6)==39)?E(_I5):new T0(2);});}},_I7=new T(function(){var _I8=new T(function(){return B(_Hi(_5x,_HU));}),_I9=new T(function(){var _Ia=new T(function(){var _Ib=new T(function(){var _Ic=function(_Id){var _Ie=E(_Id),_If=u_iswalpha(_Ie);return (E(_If)==0)?(E(_Ie)==95)?new T1(1,B(_yU(_Hw,function(_Ig){return new F(function(){return A1(_HU,new T1(3,new T2(1,_Ie,_Ig)));});}))):new T0(2):new T1(1,B(_yU(_Hw,function(_Ih){return new F(function(){return A1(_HU,new T1(3,new T2(1,_Ie,_Ih)));});})));};return B(_xs(new T1(0,_Ic),new T(function(){return new T1(1,B(_yu(_A6,_Bc,_HU)));})));}),_Ii=function(_Ij){return (!B(_4d(_f3,_Ij,_Be)))?new T0(2):new T1(1,B(_yU(_Bf,function(_Ik){var _Il=new T2(1,_Ij,_Ik);if(!B(_4d(_y9,_Il,_HS))){return new F(function(){return A1(_HU,new T1(4,_Il));});}else{return new F(function(){return A1(_HU,new T1(2,_Il));});}})));};return B(_xs(new T1(0,_Ii),_Ib));});return B(_xs(new T1(0,function(_Im){if(!B(_4d(_f3,_Im,_Hy))){return new T0(2);}else{return new F(function(){return A1(_HU,new T1(2,new T2(1,_Im,_v)));});}}),_Ia));});return B(_xs(new T1(0,function(_In){return (E(_In)==34)?E(_I8):new T0(2);}),_I9));});return B(_xs(new T1(0,function(_Io){return (E(_Io)==39)?E(new T1(0,_I2)):new T0(2);}),_I7));});return new F(function(){return _xs(new T1(1,function(_Ip){return (E(_Ip)._==0)?E(_HV):new T0(2);}),_HW);});},_Iq=0,_Ir=function(_Is,_It){var _Iu=new T(function(){var _Iv=new T(function(){var _Iw=function(_Ix){var _Iy=new T(function(){var _Iz=new T(function(){return B(A1(_It,_Ix));});return B(_HT(function(_IA){var _IB=E(_IA);return (_IB._==2)?(!B(_97(_IB.a,_y5)))?new T0(2):E(_Iz):new T0(2);}));}),_IC=function(_ID){return E(_Iy);};return new T1(1,function(_IE){return new F(function(){return A2(_GA,_IE,_IC);});});};return B(A2(_Is,_Iq,_Iw));});return B(_HT(function(_IF){var _IG=E(_IF);return (_IG._==2)?(!B(_97(_IG.a,_y4)))?new T0(2):E(_Iv):new T0(2);}));}),_IH=function(_II){return E(_Iu);};return function(_IJ){return new F(function(){return A2(_GA,_IJ,_IH);});};},_IK=function(_IL,_IM){var _IN=function(_IO){var _IP=new T(function(){return B(A1(_IL,_IO));}),_IQ=function(_IR){return new F(function(){return _xs(B(A1(_IP,_IR)),new T(function(){return new T1(1,B(_Ir(_IN,_IR)));}));});};return E(_IQ);},_IS=new T(function(){return B(A1(_IL,_IM));}),_IT=function(_IU){return new F(function(){return _xs(B(A1(_IS,_IU)),new T(function(){return new T1(1,B(_Ir(_IN,_IU)));}));});};return E(_IT);},_IV=function(_IW,_IX){var _IY=function(_IZ,_J0){var _J1=function(_J2){return new F(function(){return A1(_J0,new T(function(){return  -E(_J2);}));});},_J3=new T(function(){return B(_HT(function(_J4){return new F(function(){return A3(_IW,_J4,_IZ,_J1);});}));}),_J5=function(_J6){return E(_J3);},_J7=function(_J8){return new F(function(){return A2(_GA,_J8,_J5);});},_J9=new T(function(){return B(_HT(function(_Ja){var _Jb=E(_Ja);if(_Jb._==4){var _Jc=E(_Jb.a);if(!_Jc._){return new F(function(){return A3(_IW,_Jb,_IZ,_J0);});}else{if(E(_Jc.a)==45){if(!E(_Jc.b)._){return E(new T1(1,_J7));}else{return new F(function(){return A3(_IW,_Jb,_IZ,_J0);});}}else{return new F(function(){return A3(_IW,_Jb,_IZ,_J0);});}}}else{return new F(function(){return A3(_IW,_Jb,_IZ,_J0);});}}));}),_Jd=function(_Je){return E(_J9);};return new T1(1,function(_Jf){return new F(function(){return A2(_GA,_Jf,_Jd);});});};return new F(function(){return _IK(_IY,_IX);});},_Jg=function(_Jh){var _Ji=E(_Jh);if(!_Ji._){var _Jj=_Ji.b,_Jk=new T(function(){return B(_Ao(new T(function(){return B(_tr(E(_Ji.a)));}),new T(function(){return B(_9X(_Jj,0));},1),B(_df(_Ae,_Jj))));});return new T1(1,_Jk);}else{return (E(_Ji.b)._==0)?(E(_Ji.c)._==0)?new T1(1,new T(function(){return B(_AF(_Ad,_Ji.a));})):__Z:__Z;}},_Jl=function(_Jm,_Jn){return new T0(2);},_Jo=function(_Jp){var _Jq=E(_Jp);if(_Jq._==5){var _Jr=B(_Jg(_Jq.a));if(!_Jr._){return E(_Jl);}else{var _Js=new T(function(){return B(_ti(_Jr.a));});return function(_Jt,_Ju){return new F(function(){return A1(_Ju,_Js);});};}}else{return E(_Jl);}},_Jv=function(_Jw){var _Jx=function(_Jy){return E(new T2(3,_Jw,_yl));};return new T1(1,function(_Jz){return new F(function(){return A2(_GA,_Jz,_Jx);});});},_JA=new T(function(){return B(A3(_IV,_Jo,_Iq,_Jv));}),_JB=function(_JC){while(1){var _JD=B((function(_JE){var _JF=E(_JE);if(!_JF._){return __Z;}else{var _JG=_JF.b,_JH=E(_JF.a);if(!E(_JH.b)._){return new T2(1,_JH.a,new T(function(){return B(_JB(_JG));}));}else{_JC=_JG;return __continue;}}})(_JC));if(_JD!=__continue){return _JD;}}},_JI=function(_JJ,_JK,_JL){var _JM=E(_JL);if(!_JM._){return new T2(0,new T2(1,_JK,_v),_v);}else{var _JN=E(_JK),_JO=new T(function(){var _JP=B(_JI(_JJ,_JM.a,_JM.b));return new T2(0,_JP.a,_JP.b);});return (_JJ!=_JN)?new T2(0,new T2(1,_JN,new T(function(){return E(E(_JO).a);})),new T(function(){return E(E(_JO).b);})):new T2(0,_v,new T2(1,new T(function(){return E(E(_JO).a);}),new T(function(){return E(E(_JO).b);})));}},_JQ=new T1(0,1),_JR=new T1(0,10),_JS=function(_JT){while(1){var _JU=E(_JT);if(!_JU._){_JT=new T1(1,I_fromInt(_JU.a));continue;}else{return new F(function(){return I_toString(_JU.a);});}}},_JV=function(_JW,_JX){return new F(function(){return _3(fromJSStr(B(_JS(_JW))),_JX);});},_JY=new T1(0,0),_JZ=function(_K0,_K1,_K2){if(_K0<=6){return new F(function(){return _JV(_K1,_K2);});}else{if(!B(_sV(_K1,_JY))){return new F(function(){return _JV(_K1,_K2);});}else{return new T2(1,_c,new T(function(){return B(_3(fromJSStr(B(_JS(_K1))),new T2(1,_b,_K2)));}));}}},_K3=function(_K4,_K5,_K6){while(1){if(!(_K5%2)){var _K7=B(_v2(_K4,_K4)),_K8=quot(_K5,2);_K4=_K7;_K5=_K8;continue;}else{var _K9=E(_K5);if(_K9==1){return new F(function(){return _v2(_K4,_K6);});}else{var _K7=B(_v2(_K4,_K4)),_Ka=B(_v2(_K4,_K6));_K4=_K7;_K5=quot(_K9-1|0,2);_K6=_Ka;continue;}}}},_Kb=function(_Kc,_Kd){while(1){if(!(_Kd%2)){var _Ke=B(_v2(_Kc,_Kc)),_Kf=quot(_Kd,2);_Kc=_Ke;_Kd=_Kf;continue;}else{var _Kg=E(_Kd);if(_Kg==1){return E(_Kc);}else{return new F(function(){return _K3(B(_v2(_Kc,_Kc)),quot(_Kg-1|0,2),_Kc);});}}}},_Kh=new T(function(){return B(unCStr("Negative exponent"));}),_Ki=new T(function(){return B(err(_Kh));}),_Kj=function(_Kk){return new F(function(){return _JZ(0,_Kk,_v);});},_Kl=new T(function(){return B(_tE(_JR,_vP));}),_Km=function(_Kn){while(1){if(!B(_tE(_Kn,_vP))){if(!E(_Kl)){if(!B(_tE(B(_u3(_Kn,_JR)),_vP))){return new F(function(){return _Kj(_Kn);});}else{var _Ko=B(_tw(_Kn,_JR));_Kn=_Ko;continue;}}else{return E(_rf);}}else{return __Z;}}},_Kp=function(_Kq){var _Kr=E(_Kq);if(!_Kr._){return _Kr.a;}else{return new F(function(){return I_toNumber(_Kr.a);});}},_Ks=46,_Kt=48,_Ku=function(_Kv,_Kw,_Kx){if(!B(_sV(_Kx,_vP))){var _Ky=B(A1(_Kv,_Kx));if(!B(_tE(_Ky,_vP))){var _Kz=B(_tQ(_Kx,_Ky)),_KA=_Kz.b,_KB=new T(function(){var _KC=Math.log(B(_Kp(_Ky)))/Math.log(10),_KD=_KC&4294967295,_KE=function(_KF){if(_KF>=0){var _KG=E(_KF);if(!_KG){var _KH=B(_tw(B(_sr(B(_rF(B(_v2(_KA,_sh)),_Ky)),_JQ)),_Ky));}else{var _KH=B(_tw(B(_sr(B(_rF(B(_v2(_KA,B(_Kb(_JR,_KG)))),_Ky)),_JQ)),_Ky));}var _KI=function(_KJ){var _KK=B(_JZ(0,_KH,_v)),_KL=_KF-B(_9X(_KK,0))|0;if(0>=_KL){if(!E(_Kw)){return E(_KK);}else{return new F(function(){return _Km(_KH);});}}else{var _KM=new T(function(){if(!E(_Kw)){return E(_KK);}else{return B(_Km(_KH));}}),_KN=function(_KO){var _KP=E(_KO);return (_KP==1)?E(new T2(1,_Kt,_KM)):new T2(1,_Kt,new T(function(){return B(_KN(_KP-1|0));}));};return new F(function(){return _KN(_KL);});}};if(!E(_Kw)){var _KQ=B(_KI(_));return (_KQ._==0)?__Z:new T2(1,_Ks,_KQ);}else{if(!B(_tE(_KH,_vP))){var _KR=B(_KI(_));return (_KR._==0)?__Z:new T2(1,_Ks,_KR);}else{return __Z;}}}else{return E(_Ki);}};if(_KD>=_KC){return B(_KE(_KD));}else{return B(_KE(_KD+1|0));}},1);return new F(function(){return _3(B(_JZ(0,_Kz.a,_v)),_KB);});}else{return E(_rf);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_Ku(_Kv,_Kw,B(_rP(_Kx))));}));});}},_KS=function(_KT,_KU,_){var _KV=B(_x6(_)),_KW=new T(function(){var _KX=new T(function(){var _KY=new T(function(){var _KZ=B(_3(B(_Ku(_s1,_5Q,B(_wG(_KV)).b)),_s8));if(!_KZ._){return E(_aF);}else{var _L0=B(_ax(_KZ.a,_KZ.b));if(!_L0._){return B(_sd(_v,_v,_aH));}else{var _L1=_L0.a,_L2=E(_L0.b);if(!_L2._){return B(_sd(new T2(1,_L1,_v),_v,_aH));}else{var _L3=E(_L1),_L4=new T(function(){var _L5=B(_JI(46,_L2.a,_L2.b));return new T2(0,_L5.a,_L5.b);});if(E(_L3)==46){return B(_sd(_v,new T2(1,new T(function(){return E(E(_L4).a);}),new T(function(){return E(E(_L4).b);})),_aH));}else{return B(_sd(new T2(1,_L3,new T(function(){return E(E(_L4).a);})),new T(function(){return E(E(_L4).b);}),_aH));}}}}}),_L6=B(_JB(B(_xi(_JA,_KY))));if(!_L6._){return E(_xd);}else{if(!E(_L6.b)._){return B(_wM(3,B(_d(0,E(_L6.a)+(imul(E(_KU),E(_KT)-1|0)|0)|0,_v))));}else{return E(_xb);}}}),_L7=B(_JB(B(_xi(_JA,_KX))));if(!_L7._){return E(_xd);}else{if(!E(_L7.b)._){return E(_L7.a);}else{return E(_xb);}}});return new T2(0,new T(function(){return B(_s4(_KW,_KT));}),_KW);},_L8=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_L9=new T(function(){return B(err(_L8));}),_La=function(_Lb,_Lc){while(1){var _Ld=E(_Lc);if(!_Ld._){return __Z;}else{var _Le=_Ld.b,_Lf=E(_Lb);if(_Lf==1){return E(_Le);}else{_Lb=_Lf-1|0;_Lc=_Le;continue;}}}},_Lg=function(_Lh,_Li){if(B(_9X(_Li,0))>=(_Lh+1|0)){var _Lj=new T(function(){var _Lk=_Lh+1|0;if(_Lk>0){return B(_La(_Lk,_Li));}else{return E(_Li);}});if(0>=_Lh){return E(_Lj);}else{var _Ll=function(_Lm,_Ln){var _Lo=E(_Lm);if(!_Lo._){return E(_Lj);}else{var _Lp=_Lo.a,_Lq=E(_Ln);return (_Lq==1)?new T2(1,_Lp,_Lj):new T2(1,_Lp,new T(function(){return B(_Ll(_Lo.b,_Lq-1|0));}));}};return new F(function(){return _Ll(_Li,_Lh);});}}else{return E(_Li);}},_Lr=function(_Ls,_Lt){return new F(function(){return _Lg(E(_Ls),_Lt);});},_Lu=function(_Lv){return E(E(_Lv).a);},_Lw=function(_Lx){return new F(function(){return _d(0,E(_Lx),_v);});},_Ly=function(_Lz,_LA,_LB){return new F(function(){return _d(E(_Lz),E(_LA),_LB);});},_LC=function(_LD,_LE){return new F(function(){return _d(0,E(_LD),_LE);});},_LF=function(_LG,_LH){return new F(function(){return _28(_LC,_LG,_LH);});},_LI=new T3(0,_Ly,_Lw,_LF),_LJ=0,_LK=function(_LL,_LM,_LN){return new F(function(){return A1(_LL,new T2(1,_25,new T(function(){return B(A1(_LM,_LN));})));});},_LO=new T(function(){return B(unCStr("foldr1"));}),_LP=new T(function(){return B(_aC(_LO));}),_LQ=function(_LR,_LS){var _LT=E(_LS);if(!_LT._){return E(_LP);}else{var _LU=_LT.a,_LV=E(_LT.b);if(!_LV._){return E(_LU);}else{return new F(function(){return A2(_LR,_LU,new T(function(){return B(_LQ(_LR,_LV));}));});}}},_LW=new T(function(){return B(unCStr(" out of range "));}),_LX=new T(function(){return B(unCStr("}.index: Index "));}),_LY=new T(function(){return B(unCStr("Ix{"));}),_LZ=new T2(1,_b,_v),_M0=new T2(1,_b,_LZ),_M1=0,_M2=function(_M3){return E(E(_M3).a);},_M4=function(_M5,_M6,_M7,_M8,_M9){var _Ma=new T(function(){var _Mb=new T(function(){var _Mc=new T(function(){var _Md=new T(function(){var _Me=new T(function(){return B(A3(_LQ,_LK,new T2(1,new T(function(){return B(A3(_M2,_M7,_M1,_M8));}),new T2(1,new T(function(){return B(A3(_M2,_M7,_M1,_M9));}),_v)),_M0));});return B(_3(_LW,new T2(1,_c,new T2(1,_c,_Me))));});return B(A(_M2,[_M7,_LJ,_M6,new T2(1,_b,_Md)]));});return B(_3(_LX,new T2(1,_c,_Mc)));},1);return B(_3(_M5,_Mb));},1);return new F(function(){return err(B(_3(_LY,_Ma)));});},_Mf=function(_Mg,_Mh,_Mi,_Mj,_Mk){return new F(function(){return _M4(_Mg,_Mh,_Mk,_Mi,_Mj);});},_Ml=function(_Mm,_Mn,_Mo,_Mp){var _Mq=E(_Mo);return new F(function(){return _Mf(_Mm,_Mn,_Mq.a,_Mq.b,_Mp);});},_Mr=function(_Ms,_Mt,_Mu,_Mv){return new F(function(){return _Ml(_Mv,_Mu,_Mt,_Ms);});},_Mw=new T(function(){return B(unCStr("Int"));}),_Mx=function(_My,_Mz,_MA){return new F(function(){return _Mr(_LI,new T2(0,_Mz,_MA),_My,_Mw);});},_MB=0,_MC=new T(function(){return B(unCStr("Negative range size"));}),_MD=new T(function(){return B(err(_MC));}),_ME=function(_MF){var _MG=B(A1(_MF,_));return E(_MG);},_MH=function(_MI,_MJ,_MK,_){var _ML=E(_MI);if(!_ML){return new T2(0,_v,_MJ);}else{var _MM=new T(function(){return B(_9X(_MK,0))-1|0;}),_MN=B(_KS(new T(function(){return E(_MM)+1|0;}),_MJ,_)),_MO=E(_MN),_MP=_MO.a,_MQ=_MO.b,_MR=B(_MH(_ML-1|0,_MQ,new T(function(){return B(_Lr(_MP,_MK));}),_)),_MS=new T(function(){var _MT=function(_){var _MU=E(_MM),_MV=function(_MW){if(_MW>=0){var _MX=newArr(_MW,_L9),_MY=_MX,_MZ=E(_MW);if(!_MZ){return new T4(0,E(_MB),E(_MU),0,_MY);}else{var _N0=function(_N1,_N2,_){while(1){var _N3=E(_N1);if(!_N3._){return E(_);}else{var _=_MY[_N2]=_N3.a;if(_N2!=(_MZ-1|0)){var _N4=_N2+1|0;_N1=_N3.b;_N2=_N4;continue;}else{return E(_);}}}},_=B(_N0(_MK,0,_));return new T4(0,E(_MB),E(_MU),_MZ,_MY);}}else{return E(_MD);}};if(0>_MU){return new F(function(){return _MV(0);});}else{return new F(function(){return _MV(_MU+1|0);});}},_N5=B(_ME(_MT)),_N6=E(_N5.a),_N7=E(_N5.b),_N8=E(_MP);if(_N6>_N8){return B(_Mx(_N8,_N6,_N7));}else{if(_N8>_N7){return B(_Mx(_N8,_N6,_N7));}else{return E(_N5.d[_N8-_N6|0]);}}});return new T2(0,new T2(1,_MS,new T(function(){return B(_Lu(_MR));})),_MQ);}},_N9=function(_Na){var _Nb=E(_Na);if(!_Nb._){return new T2(0,_v,_v);}else{var _Nc=E(_Nb.a),_Nd=new T(function(){var _Ne=B(_N9(_Nb.b));return new T2(0,_Ne.a,_Ne.b);});return new T2(0,new T2(1,_Nc.a,new T(function(){return E(E(_Nd).a);})),new T2(1,_Nc.b,new T(function(){return E(E(_Nd).b);})));}},_Nf=function(_Ng){return new T2(1,_Ng,_v);},_Nh=new T(function(){return B(unCStr("\u3042\u304b\u306f\u306a\u307e\u3044\u304d\u3072\u306b\u307f\u3046\u304f\u3075\u306c\u3080\u3048\u3051\u3078\u306d\u3081\u304a\u3053\u307b\u306e\u3082\u3068\u308d\u305d\u3088\u3092\u3066\u308c\u305b\u3091\u3064\u308b\u3059\u3086\u3093\u3061\u308a\u3057\u3090\u305f\u3089\u3055\u3084\u308f"));}),_Ni=function(_Nj,_Nk,_){var _Nl=new T(function(){var _Nm=E(_Nk);return 4+B(_rj(_Nm,8-B(_pC(_Nm,8))|0))|0;}),_Nn=B(_KS(_Nl,_Nj,_)),_No=E(_Nn),_Np=new T(function(){return B(_kt(_pK,new T(function(){var _Nq=E(_Nk)+3|0;if(0>=_Nq){return __Z;}else{return B(_wM(_Nq,_Nh));}},1)));}),_Nr=B(_MH(E(_Nl),_No.b,_Np,_)),_Ns=E(_Nr);return new T2(0,new T(function(){var _Nt=B(_N9(_Ns.a));return new T3(0,E(B(_df(_Nf,_Nt.b))),E(_Nt.a),E(_No.a));}),_Ns.b);},_Nu=function(_Nv){return E(_Nv).e;},_Nw=function(_Nx,_Ny,_Nz,_NA,_){var _NB=B(_Ni(new T(function(){return B(_Nu(_NA));},1),_Nz,_)),_NC=E(_NB),_ND=E(_NC.a),_NE=_ND.b,_NF=_ND.c,_NG=B(A3(_eB,_5z,B(_78(_Ny,B(_78(_NE,_NF)))).a,_));return new T(function(){var _NH=E(_NA),_NI=E(_Nx),_NJ=B(_q6(_NI.a,_NI.b,_ND.a,_NE,_NF));return {_:0,a:E(_NH.a),b:E(new T1(1,_ND)),c:E(_NH.c),d:E(new T2(1,_NJ.a,_NJ.b)),e:E(_NC.b),f:E(_NH.f),g:E(_NH.g)};});},_NK=function(_NL,_NM,_NN,_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_){var _O2=function(_,_O3,_O4,_O5,_O6,_O7,_O8,_O9,_Oa,_Ob,_Oc,_Od){var _Oe=function(_){var _Of=E(_O5);if(!_Of._){return {_:0,a:E(_O3),b:E(_O4),c:E(_2q),d:E(_O6),e:_O7,f:E(new T5(0,E(_O8),E(_O9),E(_Oa),E(_Ob),E(_Oc))),g:E(_Od)};}else{var _Og=B(A3(_eB,_5z,B(_78(_NP,E(_Of.a))).a,_));return {_:0,a:E(_O3),b:E(_O4),c:E(_2q),d:E(_O6),e:_O7,f:E(new T5(0,E(_O8),E(_O9),E(_Oa),E(_Ob),E(_Oc))),g:E(_Od)};}};if(!B(_9c(_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_O3,_O4,_O5,_O6,_O7,_O8,_O9,_Oa,_Ob,_Oc,_Od))){var _Oh=E(_NL),_Oi=__app1(E(_eM),_Oh.b),_Oj=B(A2(_eW,_Oh.a,_)),_Ok=B(_ky(_Oh,new T2(0,_NM,_pw),_NN,_O6,_));return new F(function(){return _Oe(_);});}else{return new F(function(){return _Oe(_);});}},_Ol=E(_NQ);if(_Ol==( -1)){return new F(function(){return _O2(_,_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1);});}else{var _Om=B(_6R(_Ol,_NU));if(!_Om._){return new F(function(){return _O2(_,_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1);});}else{var _On=E(E(_Om.a).o);switch(_On._){case 0:return new F(function(){return _O2(_,_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1);});break;case 1:var _Oo=E(_On.a);if(!_Oo._){var _Op=B(_Nw(_NM,_NO,_Oo.a,{_:0,a:E(new T1(1,_Oo)),b:E(_NS),c:E(_NT),d:E(_NU),e:_NV,f:E(new T5(0,E(_NW),E(_NX),E(_NY),E(_NZ),E(_O0))),g:E(_O1)},_)),_Oq=E(_Op),_Or=E(_Oq.f);return new F(function(){return _O2(_,_Oq.a,_Oq.b,_Oq.c,_Oq.d,_Oq.e,_Or.a,_Or.b,_Or.c,_Or.d,_Or.e,_Oq.g);});}else{return E(_pB);}break;case 2:var _Os=B(_dj(_NM,new T(function(){return B(_9X(_NU,0));},1),_On.a,_NR,_NS,_NT,_NU,_NV,new T5(0,E(_NW),E(_NX),E(_NY),E(_NZ),E(_O0)),_O1)),_Ot=E(_Os.f);return new F(function(){return _O2(_,_Os.a,_Os.b,_Os.c,_Os.d,_Os.e,_Ot.a,_Ot.b,_Ot.c,_Ot.d,_Ot.e,_Os.g);});break;default:var _Ou=B(_bU(_NM,E(_On.a),_NR,_NS,_NT,_NU,_NV,new T5(0,E(_NW),E(_NX),E(_NY),E(_NZ),E(_O0)),_O1)),_Ov=E(_Ou.f);return new F(function(){return _O2(_,_Ou.a,_Ou.b,_Ou.c,_Ou.d,_Ou.e,_Ov.a,_Ov.b,_Ov.c,_Ov.d,_Ov.e,_Ou.g);});}}}},_Ow=function(_Ox,_Oy){while(1){var _Oz=E(_Ox);if(!_Oz._){return E(_Oy);}else{var _OA=new T2(1,_Oz.a,_Oy);_Ox=_Oz.b;_Oy=_OA;continue;}}},_OB=function(_OC,_OD,_OE,_OF,_OG,_OH,_OI,_){var _OJ=E(_OD),_OK=_OJ.a,_OL=E(_OF),_OM=E(_OI),_ON=_OM.d,_OO=function(_OP){var _OQ=E(_OM.f);return new F(function(){return _NK(_OC,_OK,_OE,_OL.a,_OL.b,_OP,_OM.a,_OM.b,_OM.c,_ON,_OM.e,_OQ.a,_OQ.b,_OQ.c,_OQ.d,_OQ.e,_OM.g,_);});},_OR=B(_Ow(_ON,_v));if(!_OR._){return new F(function(){return _OO( -1);});}else{var _OS=_OR.b,_OT=E(_OK),_OU=_OT.b,_OV=E(_OJ.b),_OW=_OV.b,_OX=E(_OG)*(E(_OT.a)/E(_OV.a)),_OY=E(_OR.a),_OZ=E(_OY.b),_P0=E(_OZ.a);if(_OX<=_P0){return new F(function(){return _OO(B(_6G(_OX,new T(function(){return E(_OH)*(E(_OU)/E(_OW));},1),_OS)));});}else{if(_OX>=_P0+E(_OZ.c)){return new F(function(){return _OO(B(_6G(_OX,new T(function(){return E(_OH)*(E(_OU)/E(_OW));},1),_OS)));});}else{var _P1=E(_OH)*(E(_OU)/E(_OW)),_P2=E(_OZ.b);if(_P1<=_P2){return new F(function(){return _OO(B(_6w(_OX,_P1,_OS)));});}else{if(_P1>=_P2+E(_OZ.d)){return new F(function(){return _OO(B(_6w(_OX,_P1,_OS)));});}else{return new F(function(){return _OO(_OY.a);});}}}}}},_P3=function(_P4){return E(E(_P4).a);},_P5=function(_P6){return E(E(_P6).b);},_P7=function(_P8){return E(E(_P8).a);},_P9=function(_){return new F(function(){return nMV(_2q);});},_Pa=new T(function(){return B(_2J(_P9));}),_Pb=function(_Pc){return E(E(_Pc).b);},_Pd=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_Pe=function(_Pf){return E(E(_Pf).d);},_Pg=function(_Ph,_Pi,_Pj,_Pk,_Pl,_Pm){var _Pn=B(_P3(_Ph)),_Po=B(_dK(_Pn)),_Pp=new T(function(){return B(_5U(_Pn));}),_Pq=new T(function(){return B(_Pe(_Po));}),_Pr=new T(function(){return B(A1(_Pi,_Pk));}),_Ps=new T(function(){return B(A2(_P7,_Pj,_Pl));}),_Pt=function(_Pu){return new F(function(){return A1(_Pq,new T3(0,_Ps,_Pr,_Pu));});},_Pv=function(_Pw){var _Px=new T(function(){var _Py=new T(function(){var _Pz=__createJSFunc(2,function(_PA,_){var _PB=B(A2(E(_Pw),_PA,_));return _2N;}),_PC=_Pz;return function(_){return new F(function(){return __app3(E(_Pd),E(_Pr),E(_Ps),_PC);});};});return B(A1(_Pp,_Py));});return new F(function(){return A3(_ev,_Po,_Px,_Pt);});},_PD=new T(function(){var _PE=new T(function(){return B(_5U(_Pn));}),_PF=function(_PG){var _PH=new T(function(){return B(A1(_PE,function(_){var _=wMV(E(_Pa),new T1(1,_PG));return new F(function(){return A(_P5,[_Pj,_Pl,_PG,_]);});}));});return new F(function(){return A3(_ev,_Po,_PH,_Pm);});};return B(A2(_Pb,_Ph,_PF));});return new F(function(){return A3(_ev,_Po,_PD,_Pv);});},_PI=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_PJ=function(_){var _PK=rMV(E(_Pa)),_PL=E(_PK);if(!_PL._){var _PM=__app1(E(_PI),E(_2N));return new F(function(){return _dH(_);});}else{var _PN=__app1(E(_PI),E(_PL.a));return new F(function(){return _dH(_);});}},_PO=new T(function(){return B(unCStr("\u4eca\u65e5\u3082\u6700\u9ad8\u306e\u4e00\u65e5\u306b\u306a\u308b\u3088\uff01\n\u30f2\u30b7\u30c6\u3092\u5b78\u3093\u3067\u3044\u304b\u3046\u3088\uff01\n\u304a\u3082\u3057\u308d\u3044\u3053\u3068\u306b\u306a\u3063\u3066\u304d\u305f\u306d\uff01\n\u3059\u3066\u304d\u306a \u51fa\u6703\u3072\u304c \u3042\u3063\u3066 \u3046\u308c\u3057\u3044\u306d\uff01\n\u5fc3\u306e\u6e96\u5099\u306f\u3067\u304d\u3066\u308b\uff1f\n\u3055\u3042 \u306f\u3058\u3081\u3084\u3046\u304b\uff01"));}),_PP=function(_PQ,_PR){var _PS=E(_PR);if(!_PS._){return new T2(0,_v,_v);}else{var _PT=_PS.a;if(!B(A1(_PQ,_PT))){var _PU=new T(function(){var _PV=B(_PP(_PQ,_PS.b));return new T2(0,_PV.a,_PV.b);});return new T2(0,new T2(1,_PT,new T(function(){return E(E(_PU).a);})),new T(function(){return E(E(_PU).b);}));}else{return new T2(0,_v,_PS);}}},_PW=function(_PX){return (E(_PX)==10)?true:false;},_PY=function(_PZ){var _Q0=E(_PZ);if(!_Q0._){return __Z;}else{var _Q1=new T(function(){var _Q2=B(_PP(_PW,_Q0));return new T2(0,_Q2.a,new T(function(){var _Q3=E(_Q2.b);if(!_Q3._){return __Z;}else{return B(_PY(_Q3.b));}}));});return new T2(1,new T(function(){return E(E(_Q1).a);}),new T(function(){return E(E(_Q1).b);}));}},_Q4=new T(function(){return B(_PY(_PO));}),_Q5=function(_Q6,_Q7){while(1){var _Q8=E(_Q6);if(!_Q8._){return E(_Q7);}else{_Q6=_Q8.b;_Q7=_Q8.a;continue;}}},_Q9=function(_Qa,_Qb,_Qc,_Qd,_){var _Qe=B(_MH(1,new T(function(){return E(_Qd).e;}),_Q4,_));return new F(function(){return _ky(_Qa,_Qb,_Qc,new T2(1,{_:0,a:0,b:E(_6d),c:E(_62),d:0,e:5,f:E(_69),g:E(_v),h:E(_6k),i:E(_6i),j:E(new T2(1,new T(function(){return B(_Q5(E(_Qe).a,_aH));}),_v)),k:E(_6f),l:E(_v),m:E(_v),n:E(_2q),o:E(_65)},_v),_);});},_Qf=new T(function(){return B(unCStr("vaw"));}),_Qg=new T(function(){return B(unCStr("ggo"));}),_Qh=new T(function(){return B(unCStr("3pm"));}),_Qi=0,_Qj=1,_Qk=2,_Ql=function(_Qm){var _Qn=B(_wM(3,B(_Ow(fromJSStr(_Qm),_v))));return (!B(_97(_Qn,_Qh)))?(!B(_97(_Qn,_Qg)))?(!B(_97(_Qn,_Qf)))?__Z:new T1(1,new T2(0,E(_Qk),_Qm)):new T1(1,new T2(0,E(_Qj),_Qm)):new T1(1,new T2(0,E(_Qi),_Qm));},_Qo=new T(function(){return B(_bB("Browser.hs:84:7-34|Just adSrc"));}),_Qp=2,_Qq=new T6(0,E(_5N),E(_5N),E(_5N),E(_Qp),E(_5N),1),_Qr=new T(function(){return B(unCStr(".mp3"));}),_Qs=function(_Qt){return new T1(1,E(_Qt));},_Qu=function(_Qv,_Qw){return new F(function(){return A2(_Pe,B(_dK(_Qv)),new T1(1,_Qw));});},_Qx=new T2(0,_5x,_Qu),_Qy="auto",_Qz="metadata",_QA="none",_QB=new T(function(){return new T1(0,"preload");}),_QC=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_QD=function(_){return new F(function(){return __app1(E(_QC),"source");});},_QE=new T(function(){return new T1(0,"src");}),_QF="audio/wav",_QG="audio/ogg",_QH="audio/mpeg",_QI=new T(function(){return new T1(0,"type");}),_QJ=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_QK=function(_QL){return E(E(_QL).a);},_QM=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_QN=new T(function(){return eval("(function(e,p,v){e.style[p] = v;})");}),_QO=function(_QP,_QQ,_QR,_QS){var _QT=new T(function(){return B(A2(_QK,_QP,_QR));}),_QU=function(_QV,_){var _QW=E(_QV);if(!_QW._){return _5L;}else{var _QX=E(_QT),_QY=E(_QJ),_QZ=__app2(_QY,E(_QW.a),_QX),_R0=function(_R1,_){while(1){var _R2=E(_R1);if(!_R2._){return _5L;}else{var _R3=__app2(_QY,E(_R2.a),_QX);_R1=_R2.b;continue;}}};return new F(function(){return _R0(_QW.b,_);});}},_R4=function(_R5,_){while(1){var _R6=B((function(_R7,_){var _R8=E(_R7);if(!_R8._){return _5L;}else{var _R9=_R8.b,_Ra=E(_R8.a);if(!_Ra._){var _Rb=_Ra.b,_Rc=E(_Ra.a);switch(_Rc._){case 0:var _Rd=E(_QT),_Re=E(_fY),_Rf=__app3(_Re,_Rd,_Rc.a,_Rb),_Rg=function(_Rh,_){while(1){var _Ri=E(_Rh);if(!_Ri._){return _5L;}else{var _Rj=_Ri.b,_Rk=E(_Ri.a);if(!_Rk._){var _Rl=_Rk.b,_Rm=E(_Rk.a);switch(_Rm._){case 0:var _Rn=__app3(_Re,_Rd,_Rm.a,_Rl);_Rh=_Rj;continue;case 1:var _Ro=__app3(E(_QN),_Rd,_Rm.a,_Rl);_Rh=_Rj;continue;default:var _Rp=__app3(E(_QM),_Rd,_Rm.a,_Rl);_Rh=_Rj;continue;}}else{var _Rq=B(_QU(_Rk.a,_));_Rh=_Rj;continue;}}}};return new F(function(){return _Rg(_R9,_);});break;case 1:var _Rr=E(_QT),_Rs=E(_QN),_Rt=__app3(_Rs,_Rr,_Rc.a,_Rb),_Ru=function(_Rv,_){while(1){var _Rw=E(_Rv);if(!_Rw._){return _5L;}else{var _Rx=_Rw.b,_Ry=E(_Rw.a);if(!_Ry._){var _Rz=_Ry.b,_RA=E(_Ry.a);switch(_RA._){case 0:var _RB=__app3(E(_fY),_Rr,_RA.a,_Rz);_Rv=_Rx;continue;case 1:var _RC=__app3(_Rs,_Rr,_RA.a,_Rz);_Rv=_Rx;continue;default:var _RD=__app3(E(_QM),_Rr,_RA.a,_Rz);_Rv=_Rx;continue;}}else{var _RE=B(_QU(_Ry.a,_));_Rv=_Rx;continue;}}}};return new F(function(){return _Ru(_R9,_);});break;default:var _RF=E(_QT),_RG=E(_QM),_RH=__app3(_RG,_RF,_Rc.a,_Rb),_RI=function(_RJ,_){while(1){var _RK=E(_RJ);if(!_RK._){return _5L;}else{var _RL=_RK.b,_RM=E(_RK.a);if(!_RM._){var _RN=_RM.b,_RO=E(_RM.a);switch(_RO._){case 0:var _RP=__app3(E(_fY),_RF,_RO.a,_RN);_RJ=_RL;continue;case 1:var _RQ=__app3(E(_QN),_RF,_RO.a,_RN);_RJ=_RL;continue;default:var _RR=__app3(_RG,_RF,_RO.a,_RN);_RJ=_RL;continue;}}else{var _RS=B(_QU(_RM.a,_));_RJ=_RL;continue;}}}};return new F(function(){return _RI(_R9,_);});}}else{var _RT=B(_QU(_Ra.a,_));_R5=_R9;return __continue;}}})(_R5,_));if(_R6!=__continue){return _R6;}}};return new F(function(){return A2(_5U,_QQ,function(_){return new F(function(){return _R4(_QS,_);});});});},_RU=function(_RV,_RW,_RX,_RY){var _RZ=B(_dK(_RW)),_S0=function(_S1){return new F(function(){return A3(_et,_RZ,new T(function(){return B(_QO(_RV,_RW,_S1,_RY));}),new T(function(){return B(A2(_Pe,_RZ,_S1));}));});};return new F(function(){return A3(_ev,_RZ,_RX,_S0);});},_S2=function(_S3,_){var _S4=E(_S3);if(!_S4._){return _v;}else{var _S5=E(_S4.a),_S6=B(A(_RU,[_Qx,_5z,_QD,new T2(1,new T(function(){var _S7=E(_QI);switch(E(_S5.a)){case 0:return new T2(0,E(_S7),E(_QH));break;case 1:return new T2(0,E(_S7),E(_QG));break;default:return new T2(0,E(_S7),E(_QF));}}),new T2(1,new T(function(){return new T2(0,E(_QE),_S5.b);}),_v)),_])),_S8=B(_S2(_S4.b,_));return new T2(1,_S6,_S8);}},_S9=new T(function(){return new T1(0,"volume");}),_Sa=new T(function(){return new T1(0,"muted");}),_Sb=new T(function(){return new T1(0,"loop");}),_Sc=new T(function(){return new T1(0,"autoplay");}),_Sd="true",_Se=new T(function(){return toJSStr(_v);}),_Sf=new T(function(){return new T1(0,"controls");}),_Sg=function(_){return new F(function(){return __app1(E(_QC),"audio");});},_Sh=function(_Si,_Sj,_Sk){var _Sl=function(_){var _Sm=B(_S2(_Sk,_)),_Sn=B(A(_RU,[_Qx,_5z,_Sg,new T2(1,new T(function(){var _So=E(_Sf);if(!E(E(_Sj).a)){return new T2(0,E(_So),E(_Se));}else{return new T2(0,E(_So),E(_Sd));}}),new T2(1,new T(function(){var _Sp=E(_Sc);if(!E(E(_Sj).b)){return new T2(0,E(_Sp),E(_Se));}else{return new T2(0,E(_Sp),E(_Sd));}}),new T2(1,new T(function(){var _Sq=E(_Sb);if(!E(E(_Sj).c)){return new T2(0,E(_Sq),E(_Se));}else{return new T2(0,E(_Sq),E(_Sd));}}),new T2(1,new T(function(){var _Sr=E(_Sa);if(!E(E(_Sj).e)){return new T2(0,E(_Sr),E(_Se));}else{return new T2(0,E(_Sr),E(_Sd));}}),new T2(1,new T(function(){var _Ss=String(E(_Sj).f);return new T2(0,E(_S9),_Ss);}),new T2(1,new T(function(){var _St=E(_QB);switch(E(E(_Sj).d)){case 0:return new T2(0,E(_St),E(_QA));break;case 1:return new T2(0,E(_St),E(_Qz));break;default:return new T2(0,E(_St),E(_Qy));}}),new T2(1,new T(function(){return B(_Qs(_Sm));}),_v))))))),_]));return new T1(0,_Sn);};return new F(function(){return A2(_5U,_Si,_Sl);});},_Su=function(_Sv,_Sw){var _Sx=E(_Sv);if(_Sx==( -1)){return __Z;}else{var _Sy=new T(function(){var _Sz=new T(function(){var _SA=B(_Ql(toJSStr(B(_3(_Sw,new T(function(){return B(_3(B(_d(0,_Sx,_v)),_Qr));},1))))));if(!_SA._){return E(_Qo);}else{return E(_SA.a);}});return B(_Sh(_5z,_Qq,new T2(1,_Sz,_v)));});return new F(function(){return _3(B(_Su(_Sx-1|0,_Sw)),new T2(1,_Sy,_v));});}},_SB=new T(function(){return B(unCStr("Audio/se"));}),_SC=new T(function(){return B(_Su(3,_SB));}),_SD=function(_SE,_){var _SF=E(_SE);if(!_SF._){return _v;}else{var _SG=B(A1(_SF.a,_)),_SH=B(_SD(_SF.b,_));return new T2(1,_SG,_SH);}},_SI=new T(function(){return B(unCStr("Audio/os"));}),_SJ=new T(function(){return B(_Su(47,_SI));}),_SK=function(_SL,_){var _SM=E(_SL);if(!_SM._){return _v;}else{var _SN=B(A1(_SM.a,_)),_SO=B(_SK(_SM.b,_));return new T2(1,_SN,_SO);}},_SP="src",_SQ=new T(function(){return B(unCStr("img"));}),_SR=function(_SS,_ST){return new F(function(){return A2(_5U,_SS,function(_){var _SU=__app1(E(_QC),toJSStr(E(_SQ))),_SV=__app3(E(_fY),_SU,E(_SP),E(_ST));return _SU;});});},_SW=new T(function(){return B(unCStr(".png"));}),_SX=function(_SY,_SZ){var _T0=E(_SY);if(_T0==( -1)){return __Z;}else{var _T1=new T(function(){var _T2=new T(function(){return toJSStr(B(_3(_SZ,new T(function(){return B(_3(B(_d(0,_T0,_v)),_SW));},1))));});return B(_SR(_5z,_T2));});return new F(function(){return _3(B(_SX(_T0-1|0,_SZ)),new T2(1,_T1,_v));});}},_T3=new T(function(){return B(unCStr("Images/Wst/wst"));}),_T4=new T(function(){return B(_SX(120,_T3));}),_T5=function(_T6,_){var _T7=E(_T6);if(!_T7._){return _v;}else{var _T8=B(A1(_T7.a,_)),_T9=B(_T5(_T7.b,_));return new T2(1,_T8,_T9);}},_Ta=new T(function(){return B(unCStr("Images/img"));}),_Tb=new T(function(){return B(_SX(5,_Ta));}),_Tc=function(_Td,_){var _Te=E(_Td);if(!_Te._){return _v;}else{var _Tf=B(A1(_Te.a,_)),_Tg=B(_Tc(_Te.b,_));return new T2(1,_Tf,_Tg);}},_Th=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_Ti=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_Tj=function(_Tk,_Tl,_Tm){var _Tn=B(_P3(_Tk)),_To=new T(function(){return B(_5U(_Tn));}),_Tp=function(_Tq){var _Tr=function(_){var _Ts=E(_Tl);if(!_Ts._){var _Tt=B(A1(_Tq,_5L)),_Tu=__createJSFunc(0,function(_){var _Tv=B(A1(_Tt,_));return _2N;}),_Tw=__app2(E(_Ti),_Ts.a,_Tu);return new T(function(){var _Tx=Number(_Tw),_Ty=jsTrunc(_Tx);return new T2(0,_Ty,E(_Ts));});}else{var _Tz=B(A1(_Tq,_5L)),_TA=__createJSFunc(0,function(_){var _TB=B(A1(_Tz,_));return _2N;}),_TC=__app2(E(_Th),_Ts.a,_TA);return new T(function(){var _TD=Number(_TC),_TE=jsTrunc(_TD);return new T2(0,_TE,E(_Ts));});}};return new F(function(){return A1(_To,_Tr);});},_TF=new T(function(){return B(A2(_Pb,_Tk,function(_TG){return E(_Tm);}));});return new F(function(){return A3(_ev,B(_dK(_Tn)),_TF,_Tp);});},_TH=function(_){var _TI=B(_Tc(_Tb,_)),_TJ=B(_T5(_T4,_)),_TK=B(_SK(_SJ,_)),_TL=_TK,_TM=B(_SD(_SC,_)),_TN=_TM,_TO=__app1(E(_5R),"canvas"),_TP=__eq(_TO,E(_2N));if(!E(_TP)){var _TQ=__isUndef(_TO);if(!E(_TQ)){var _TR=B(A3(_5W,_5z,_TO,_)),_TS=E(_TR);if(!_TS._){return new F(function(){return die(_6v);});}else{var _TT=E(_TS.a),_TU=B(_5F(_TT.b,_)),_TV=_TU,_TW=nMV(_6o),_TX=_TW,_TY=new T2(0,_TI,_TJ),_TZ=B(_Q9(_TT,_TV,_TY,_6o,_)),_U0=B(A(_Pg,[_5A,_3g,_3f,_TO,_5M,function(_U1,_){var _U2=E(E(_U1).a),_U3=rMV(_TX),_U4=B(_OB(_TT,_TV,_TY,new T2(0,_TL,_TN),_U2.a,_U2.b,_U3,_)),_=wMV(_TX,_U4);return _5L;},_])),_U5=B(A(_Pg,[_5A,_3g,_4P,_TO,_5P,function(_U6,_){var _U7=E(_U6),_U8=rMV(_TX),_U9=E(_U8);if(!E(E(_U9.f).c)){var _=wMV(_TX,_U9);return _5L;}else{var _Ua=B(_PJ(_)),_=wMV(_TX,_U9);return _5L;}},_])),_Ub=function(_){var _Uc=rMV(_TX),_=wMV(_TX,new T(function(){var _Ud=E(_Uc),_Ue=E(_Ud.f);return {_:0,a:E(_Ud.a),b:E(_Ud.b),c:E(_Ud.c),d:E(_Ud.d),e:_Ud.e,f:E(new T5(0,E(_Ue.a),E(_Ue.b),E(_5N),E(_Ue.d),E(_Ue.e))),g:E(_Ud.g)};}));return _5L;},_Uf=function(_Ug,_){var _Uh=E(_Ug),_Ui=rMV(_TX),_=wMV(_TX,new T(function(){var _Uj=E(_Ui),_Uk=E(_Uj.f);return {_:0,a:E(_Uj.a),b:E(_Uj.b),c:E(_Uj.c),d:E(_Uj.d),e:_Uj.e,f:E(new T5(0,E(_Uk.a),E(_Uk.b),E(_5Q),E(_Uk.d),E(_Uk.e))),g:E(_Uj.g)};})),_Ul=B(A(_Tj,[_5A,_6p,_Ub,_]));return _5L;},_Um=B(A(_Pg,[_5A,_3g,_4P,_TO,_5O,_Uf,_]));return _5L;}}else{return new F(function(){return die(_6s);});}}else{return new F(function(){return die(_6s);});}},_Un=function(_){return new F(function(){return _TH(_);});};
var hasteMain = function() {B(A(_Un, [0]));};window.onload = hasteMain;