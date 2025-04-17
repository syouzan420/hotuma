"use strict";
var __haste_prog_id = 'f8847e5c48d49e7b702eae06bba411a8094fdfcd5a94db4003152ee578b18605';
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

var _0="deltaZ",_1="deltaY",_2="deltaX",_3=function(_4,_5){var _6=E(_4);return (_6._==0)?E(_5):new T2(1,_6.a,new T(function(){return B(_3(_6.b,_5));}));},_7=function(_8,_9){var _a=jsShowI(_8);return new F(function(){return _3(fromJSStr(_a),_9);});},_b=41,_c=40,_d=function(_e,_f,_g){if(_f>=0){return new F(function(){return _7(_f,_g);});}else{if(_e<=6){return new F(function(){return _7(_f,_g);});}else{return new T2(1,_c,new T(function(){var _h=jsShowI(_f);return B(_3(fromJSStr(_h),new T2(1,_b,_g)));}));}}},_i=new T(function(){return B(unCStr(")"));}),_j=new T(function(){return B(_d(0,2,_i));}),_k=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_j));}),_l=function(_m){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_d(0,_m,_k));}))));});},_n=function(_o,_){return new T(function(){var _p=Number(E(_o)),_q=jsTrunc(_p);if(_q<0){return B(_l(_q));}else{if(_q>2){return B(_l(_q));}else{return _q;}}});},_r=0,_s=new T3(0,_r,_r,_r),_t="button",_u=new T(function(){return eval("jsGetMouseCoords");}),_v=__Z,_w=function(_x,_){var _y=E(_x);if(!_y._){return _v;}else{var _z=B(_w(_y.b,_));return new T2(1,new T(function(){var _A=Number(E(_y.a));return jsTrunc(_A);}),_z);}},_B=function(_C,_){var _D=__arr2lst(0,_C);return new F(function(){return _w(_D,_);});},_E=function(_F,_){return new F(function(){return _B(E(_F),_);});},_G=function(_H,_){return new T(function(){var _I=Number(E(_H));return jsTrunc(_I);});},_J=new T2(0,_G,_E),_K=function(_L,_){var _M=E(_L);if(!_M._){return _v;}else{var _N=B(_K(_M.b,_));return new T2(1,_M.a,_N);}},_O=new T(function(){return B(unCStr("base"));}),_P=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Q=new T(function(){return B(unCStr("IOException"));}),_R=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_O,_P,_Q),_S=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_R,_v,_v),_T=function(_U){return E(_S);},_V=function(_W){return E(E(_W).a);},_X=function(_Y,_Z,_10){var _11=B(A1(_Y,_)),_12=B(A1(_Z,_)),_13=hs_eqWord64(_11.a,_12.a);if(!_13){return __Z;}else{var _14=hs_eqWord64(_11.b,_12.b);return (!_14)?__Z:new T1(1,_10);}},_15=function(_16){var _17=E(_16);return new F(function(){return _X(B(_V(_17.a)),_T,_17.b);});},_18=new T(function(){return B(unCStr(": "));}),_19=new T(function(){return B(unCStr(")"));}),_1a=new T(function(){return B(unCStr(" ("));}),_1b=new T(function(){return B(unCStr("interrupted"));}),_1c=new T(function(){return B(unCStr("system error"));}),_1d=new T(function(){return B(unCStr("unsatisified constraints"));}),_1e=new T(function(){return B(unCStr("user error"));}),_1f=new T(function(){return B(unCStr("permission denied"));}),_1g=new T(function(){return B(unCStr("illegal operation"));}),_1h=new T(function(){return B(unCStr("end of file"));}),_1i=new T(function(){return B(unCStr("resource exhausted"));}),_1j=new T(function(){return B(unCStr("resource busy"));}),_1k=new T(function(){return B(unCStr("does not exist"));}),_1l=new T(function(){return B(unCStr("already exists"));}),_1m=new T(function(){return B(unCStr("resource vanished"));}),_1n=new T(function(){return B(unCStr("timeout"));}),_1o=new T(function(){return B(unCStr("unsupported operation"));}),_1p=new T(function(){return B(unCStr("hardware fault"));}),_1q=new T(function(){return B(unCStr("inappropriate type"));}),_1r=new T(function(){return B(unCStr("invalid argument"));}),_1s=new T(function(){return B(unCStr("failed"));}),_1t=new T(function(){return B(unCStr("protocol error"));}),_1u=function(_1v,_1w){switch(E(_1v)){case 0:return new F(function(){return _3(_1l,_1w);});break;case 1:return new F(function(){return _3(_1k,_1w);});break;case 2:return new F(function(){return _3(_1j,_1w);});break;case 3:return new F(function(){return _3(_1i,_1w);});break;case 4:return new F(function(){return _3(_1h,_1w);});break;case 5:return new F(function(){return _3(_1g,_1w);});break;case 6:return new F(function(){return _3(_1f,_1w);});break;case 7:return new F(function(){return _3(_1e,_1w);});break;case 8:return new F(function(){return _3(_1d,_1w);});break;case 9:return new F(function(){return _3(_1c,_1w);});break;case 10:return new F(function(){return _3(_1t,_1w);});break;case 11:return new F(function(){return _3(_1s,_1w);});break;case 12:return new F(function(){return _3(_1r,_1w);});break;case 13:return new F(function(){return _3(_1q,_1w);});break;case 14:return new F(function(){return _3(_1p,_1w);});break;case 15:return new F(function(){return _3(_1o,_1w);});break;case 16:return new F(function(){return _3(_1n,_1w);});break;case 17:return new F(function(){return _3(_1m,_1w);});break;default:return new F(function(){return _3(_1b,_1w);});}},_1x=new T(function(){return B(unCStr("}"));}),_1y=new T(function(){return B(unCStr("{handle: "));}),_1z=function(_1A,_1B,_1C,_1D,_1E,_1F){var _1G=new T(function(){var _1H=new T(function(){var _1I=new T(function(){var _1J=E(_1D);if(!_1J._){return E(_1F);}else{var _1K=new T(function(){return B(_3(_1J,new T(function(){return B(_3(_19,_1F));},1)));},1);return B(_3(_1a,_1K));}},1);return B(_1u(_1B,_1I));}),_1L=E(_1C);if(!_1L._){return E(_1H);}else{return B(_3(_1L,new T(function(){return B(_3(_18,_1H));},1)));}}),_1M=E(_1E);if(!_1M._){var _1N=E(_1A);if(!_1N._){return E(_1G);}else{var _1O=E(_1N.a);if(!_1O._){var _1P=new T(function(){var _1Q=new T(function(){return B(_3(_1x,new T(function(){return B(_3(_18,_1G));},1)));},1);return B(_3(_1O.a,_1Q));},1);return new F(function(){return _3(_1y,_1P);});}else{var _1R=new T(function(){var _1S=new T(function(){return B(_3(_1x,new T(function(){return B(_3(_18,_1G));},1)));},1);return B(_3(_1O.a,_1S));},1);return new F(function(){return _3(_1y,_1R);});}}}else{return new F(function(){return _3(_1M.a,new T(function(){return B(_3(_18,_1G));},1));});}},_1T=function(_1U){var _1V=E(_1U);return new F(function(){return _1z(_1V.a,_1V.b,_1V.c,_1V.d,_1V.f,_v);});},_1W=function(_1X,_1Y,_1Z){var _20=E(_1Y);return new F(function(){return _1z(_20.a,_20.b,_20.c,_20.d,_20.f,_1Z);});},_21=function(_22,_23){var _24=E(_22);return new F(function(){return _1z(_24.a,_24.b,_24.c,_24.d,_24.f,_23);});},_25=44,_26=93,_27=91,_28=function(_29,_2a,_2b){var _2c=E(_2a);if(!_2c._){return new F(function(){return unAppCStr("[]",_2b);});}else{var _2d=new T(function(){var _2e=new T(function(){var _2f=function(_2g){var _2h=E(_2g);if(!_2h._){return E(new T2(1,_26,_2b));}else{var _2i=new T(function(){return B(A2(_29,_2h.a,new T(function(){return B(_2f(_2h.b));})));});return new T2(1,_25,_2i);}};return B(_2f(_2c.b));});return B(A2(_29,_2c.a,_2e));});return new T2(1,_27,_2d);}},_2j=function(_2k,_2l){return new F(function(){return _28(_21,_2k,_2l);});},_2m=new T3(0,_1W,_1T,_2j),_2n=new T(function(){return new T5(0,_T,_2m,_2o,_15,_1T);}),_2o=function(_2p){return new T2(0,_2n,_2p);},_2q=__Z,_2r=7,_2s=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2t=new T6(0,_2q,_2r,_v,_2s,_2q,_2q),_2u=new T(function(){return B(_2o(_2t));}),_2v=function(_){return new F(function(){return die(_2u);});},_2w=function(_2x){return E(E(_2x).a);},_2y=function(_2z,_2A,_2B,_){var _2C=__arr2lst(0,_2B),_2D=B(_K(_2C,_)),_2E=E(_2D);if(!_2E._){return new F(function(){return _2v(_);});}else{var _2F=E(_2E.b);if(!_2F._){return new F(function(){return _2v(_);});}else{if(!E(_2F.b)._){var _2G=B(A3(_2w,_2z,_2E.a,_)),_2H=B(A3(_2w,_2A,_2F.a,_));return new T2(0,_2G,_2H);}else{return new F(function(){return _2v(_);});}}}},_2I=function(_){return new F(function(){return __jsNull();});},_2J=function(_2K){var _2L=B(A1(_2K,_));return E(_2L);},_2M=new T(function(){return B(_2J(_2I));}),_2N=new T(function(){return E(_2M);}),_2O=function(_2P,_2Q,_){if(E(_2P)==7){var _2R=__app1(E(_u),_2Q),_2S=B(_2y(_J,_J,_2R,_)),_2T=__get(_2Q,E(_2)),_2U=__get(_2Q,E(_1)),_2V=__get(_2Q,E(_0));return new T(function(){return new T3(0,E(_2S),E(_2q),E(new T3(0,_2T,_2U,_2V)));});}else{var _2W=__app1(E(_u),_2Q),_2X=B(_2y(_J,_J,_2W,_)),_2Y=__get(_2Q,E(_t)),_2Z=__eq(_2Y,E(_2N));if(!E(_2Z)){var _30=__isUndef(_2Y);if(!E(_30)){var _31=B(_n(_2Y,_));return new T(function(){return new T3(0,E(_2X),E(new T1(1,_31)),E(_s));});}else{return new T(function(){return new T3(0,E(_2X),E(_2q),E(_s));});}}else{return new T(function(){return new T3(0,E(_2X),E(_2q),E(_s));});}}},_32=function(_33,_34,_){return new F(function(){return _2O(_33,E(_34),_);});},_35="mouseout",_36="mouseover",_37="mousemove",_38="mouseup",_39="mousedown",_3a="dblclick",_3b="click",_3c="wheel",_3d=function(_3e){switch(E(_3e)){case 0:return E(_3b);case 1:return E(_3a);case 2:return E(_39);case 3:return E(_38);case 4:return E(_37);case 5:return E(_36);case 6:return E(_35);default:return E(_3c);}},_3f=new T2(0,_3d,_32),_3g=function(_3h){return E(_3h);},_3i=function(_3j,_3k){return E(_3j)==E(_3k);},_3l=function(_3m,_3n){return E(_3m)!=E(_3n);},_3o=new T2(0,_3i,_3l),_3p="screenY",_3q="screenX",_3r="clientY",_3s="clientX",_3t="pageY",_3u="pageX",_3v="target",_3w="identifier",_3x=function(_3y,_){var _3z=__get(_3y,E(_3w)),_3A=__get(_3y,E(_3v)),_3B=__get(_3y,E(_3u)),_3C=__get(_3y,E(_3t)),_3D=__get(_3y,E(_3s)),_3E=__get(_3y,E(_3r)),_3F=__get(_3y,E(_3q)),_3G=__get(_3y,E(_3p));return new T(function(){var _3H=Number(_3z),_3I=jsTrunc(_3H);return new T5(0,_3I,_3A,E(new T2(0,new T(function(){var _3J=Number(_3B);return jsTrunc(_3J);}),new T(function(){var _3K=Number(_3C);return jsTrunc(_3K);}))),E(new T2(0,new T(function(){var _3L=Number(_3D);return jsTrunc(_3L);}),new T(function(){var _3M=Number(_3E);return jsTrunc(_3M);}))),E(new T2(0,new T(function(){var _3N=Number(_3F);return jsTrunc(_3N);}),new T(function(){var _3O=Number(_3G);return jsTrunc(_3O);}))));});},_3P=function(_3Q,_){var _3R=E(_3Q);if(!_3R._){return _v;}else{var _3S=B(_3x(E(_3R.a),_)),_3T=B(_3P(_3R.b,_));return new T2(1,_3S,_3T);}},_3U="touches",_3V=function(_3W){return E(E(_3W).b);},_3X=function(_3Y,_3Z,_){var _40=__arr2lst(0,_3Z),_41=new T(function(){return B(_3V(_3Y));}),_42=function(_43,_){var _44=E(_43);if(!_44._){return _v;}else{var _45=B(A2(_41,_44.a,_)),_46=B(_42(_44.b,_));return new T2(1,_45,_46);}};return new F(function(){return _42(_40,_);});},_47=function(_48,_){return new F(function(){return _3X(_J,E(_48),_);});},_49=new T2(0,_E,_47),_4a=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4b=function(_4c){return E(E(_4c).a);},_4d=function(_4e,_4f,_4g){while(1){var _4h=E(_4g);if(!_4h._){return false;}else{if(!B(A3(_4b,_4e,_4f,_4h.a))){_4g=_4h.b;continue;}else{return true;}}}},_4i=function(_4j,_4k){while(1){var _4l=B((function(_4m,_4n){var _4o=E(_4n);if(!_4o._){return __Z;}else{var _4p=_4o.a,_4q=_4o.b;if(!B(A1(_4m,_4p))){var _4r=_4m;_4j=_4r;_4k=_4q;return __continue;}else{return new T2(1,_4p,new T(function(){return B(_4i(_4m,_4q));}));}}})(_4j,_4k));if(_4l!=__continue){return _4l;}}},_4s=function(_4t,_){var _4u=__get(_4t,E(_3U)),_4v=__arr2lst(0,_4u),_4w=B(_3P(_4v,_)),_4x=__app1(E(_4a),_4t),_4y=B(_2y(_49,_49,_4x,_)),_4z=E(_4y),_4A=new T(function(){var _4B=function(_4C){return new F(function(){return _4d(_3o,new T(function(){return E(_4C).a;}),_4z.a);});};return B(_4i(_4B,_4w));}),_4D=new T(function(){var _4E=function(_4F){return new F(function(){return _4d(_3o,new T(function(){return E(_4F).a;}),_4z.b);});};return B(_4i(_4E,_4w));});return new T3(0,_4w,_4D,_4A);},_4G=function(_4H,_4I,_){return new F(function(){return _4s(E(_4I),_);});},_4J="touchcancel",_4K="touchend",_4L="touchmove",_4M="touchstart",_4N=function(_4O){switch(E(_4O)){case 0:return E(_4M);case 1:return E(_4L);case 2:return E(_4K);default:return E(_4J);}},_4P=new T2(0,_4N,_4G),_4Q=function(_4R,_4S,_){var _4T=B(A1(_4R,_)),_4U=B(A1(_4S,_));return _4T;},_4V=function(_4W,_4X,_){var _4Y=B(A1(_4W,_)),_4Z=B(A1(_4X,_));return new T(function(){return B(A1(_4Y,_4Z));});},_50=function(_51,_52,_){var _53=B(A1(_52,_));return _51;},_54=function(_55,_56,_){var _57=B(A1(_56,_));return new T(function(){return B(A1(_55,_57));});},_58=new T2(0,_54,_50),_59=function(_5a,_){return _5a;},_5b=function(_5c,_5d,_){var _5e=B(A1(_5c,_));return new F(function(){return A1(_5d,_);});},_5f=new T5(0,_58,_59,_4V,_5b,_4Q),_5g=new T(function(){return E(_2n);}),_5h=function(_5i){return E(E(_5i).c);},_5j=function(_5k){return new T6(0,_2q,_2r,_v,_5k,_2q,_2q);},_5l=function(_5m,_){var _5n=new T(function(){return B(A2(_5h,_5g,new T(function(){return B(A1(_5j,_5m));})));});return new F(function(){return die(_5n);});},_5o=function(_5p,_){return new F(function(){return _5l(_5p,_);});},_5q=function(_5r){return new F(function(){return A1(_5o,_5r);});},_5s=function(_5t,_5u,_){var _5v=B(A1(_5t,_));return new F(function(){return A2(_5u,_5v,_);});},_5w=new T5(0,_5f,_5s,_5b,_59,_5q),_5x=function(_5y){return E(_5y);},_5z=new T2(0,_5w,_5x),_5A=new T2(0,_5z,_59),_5B=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_5C=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_5D=new T(function(){return eval("(function(cv){return cv.height})");}),_5E=new T(function(){return eval("(function(cv){return cv.width})");}),_5F=function(_5G,_){var _5H=__app1(E(_5E),_5G),_5I=__app1(E(_5D),_5G),_5J=__app1(E(_5C),_5G),_5K=__app1(E(_5B),_5G);return new T2(0,new T2(0,_5H,_5I),new T2(0,_5J,_5K));},_5L=0,_5M=0,_5N=false,_5O=2,_5P=0,_5Q=true,_5R=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_5S=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_5T=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_5U=function(_5V){return E(E(_5V).b);},_5W=function(_5X,_5Y){return new F(function(){return A2(_5U,_5X,function(_){var _5Z=E(_5Y),_60=__app1(E(_5T),_5Z);if(!_60){return _2q;}else{var _61=__app1(E(_5S),_5Z);return new T1(1,new T2(0,_61,_5Z));}});});},_62=2,_63=1,_64=new T1(0,_63),_65=new T1(1,_64),_66=30,_67=100,_68=new T2(0,_67,_66),_69=new T2(1,_68,_v),_6a=370,_6b=200,_6c=80,_6d=new T4(0,_6c,_67,_6b,_6a),_6e=0,_6f=new T2(1,_6e,_v),_6g=new T(function(){return B(unCStr("\u3053\u3093\u306b\u3061\u306f\n\u5143\u6c23\u3067\u3059\u304b\uff1f"));}),_6h=new T2(1,_6g,_v),_6i=new T2(1,_63,_v),_6j=20,_6k=new T2(1,_6j,_v),_6l={_:0,a:0,b:E(_6d),c:E(_62),d:0,e:5,f:E(_69),g:E(_v),h:E(_6k),i:E(_6i),j:E(_6h),k:E(_6f),l:E(_v),m:E(_v),n:E(_2q),o:E(_65)},_6m=new T2(1,_6l,_v),_6n=new T5(0,E(_5N),E(_5N),E(_5N),E(_5N),E(_5N)),_6o=new T6(0,E(_2q),E(_2q),E(_6m),0,E(_6n),E(_v)),_6p=new T1(0,100),_6q=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:16:3-9"));}),_6r=new T6(0,_2q,_2r,_v,_6q,_2q,_2q),_6s=new T(function(){return B(_2o(_6r));}),_6t=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:17:3-8"));}),_6u=new T6(0,_2q,_2r,_v,_6t,_2q,_2q),_6v=new T(function(){return B(_2o(_6u));}),_6w=function(_6x,_6y,_6z){while(1){var _6A=E(_6z);if(!_6A._){return  -1;}else{var _6B=_6A.b,_6C=E(_6A.a),_6D=E(_6C.b),_6E=E(_6D.a);if(_6x<=_6E){_6z=_6B;continue;}else{if(_6x>=_6E+E(_6D.c)){_6z=_6B;continue;}else{var _6F=E(_6D.b);if(_6y<=_6F){_6z=_6B;continue;}else{if(_6y>=_6F+E(_6D.d)){_6z=_6B;continue;}else{return E(_6C.a);}}}}}}},_6G=function(_6H,_6I,_6J){while(1){var _6K=E(_6J);if(!_6K._){return  -1;}else{var _6L=_6K.b,_6M=E(_6K.a),_6N=E(_6M.b),_6O=E(_6N.a);if(_6H<=_6O){_6J=_6L;continue;}else{if(_6H>=_6O+E(_6N.c)){_6J=_6L;continue;}else{var _6P=E(_6I),_6Q=E(_6N.b);if(_6P<=_6Q){return new F(function(){return _6w(_6H,_6P,_6L);});}else{if(_6P>=_6Q+E(_6N.d)){return new F(function(){return _6w(_6H,_6P,_6L);});}else{return E(_6M.a);}}}}}}},_6R=function(_6S,_6T){while(1){var _6U=E(_6T);if(!_6U._){return __Z;}else{var _6V=E(_6U.a);if(_6S!=_6V.a){_6T=_6U.b;continue;}else{return new T1(1,_6V);}}}},_6W=function(_6X,_6Y){var _6Z=E(_6X);if(!_6Z._){var _70=E(_6Y);if(!_70._){return new F(function(){return _3i(_6Z.a,_70.a);});}else{return false;}}else{var _71=E(_6Y);if(!_71._){return false;}else{return new F(function(){return _3i(_6Z.a,_71.a);});}}},_72=function(_73,_74){return (E(_73)==0)?(E(_74)==0)?false:true:(E(_74)==0)?true:false;},_75=function(_76,_77){return (E(_76)==0)?(E(_77)==0)?true:false:(E(_77)==0)?false:true;},_78=new T2(0,_75,_72),_79=function(_7a,_7b,_7c){while(1){var _7d=E(_7b);if(!_7d._){return (E(_7c)._==0)?true:false;}else{var _7e=E(_7c);if(!_7e._){return false;}else{if(!B(A3(_4b,_7a,_7d.a,_7e.a))){return false;}else{_7b=_7d.b;_7c=_7e.b;continue;}}}}},_7f=function(_7g,_7h){while(1){var _7i=E(_7g);if(!_7i._){return (E(_7h)._==0)?true:false;}else{var _7j=E(_7h);if(!_7j._){return false;}else{if(E(_7i.a)!=E(_7j.a)){return false;}else{_7g=_7i.b;_7h=_7j.b;continue;}}}}},_7k=function(_7l,_7m){while(1){var _7n=E(_7l);if(!_7n._){return (E(_7m)._==0)?true:false;}else{var _7o=E(_7m);if(!_7o._){return false;}else{if(E(_7n.a)!=E(_7o.a)){return false;}else{_7l=_7n.b;_7m=_7o.b;continue;}}}}},_7p=function(_7q,_7r){while(1){var _7s=E(_7q);if(!_7s._){return (E(_7r)._==0)?true:false;}else{var _7t=E(_7r);if(!_7t._){return false;}else{if(!B(_7k(_7s.a,_7t.a))){return false;}else{_7q=_7s.b;_7r=_7t.b;continue;}}}}},_7u=function(_7v,_7w,_7x,_7y){return (_7v!=_7x)?true:(E(_7w)!=E(_7y))?true:false;},_7z=function(_7A,_7B){var _7C=E(_7A),_7D=E(_7B);return new F(function(){return _7u(E(_7C.a),_7C.b,E(_7D.a),_7D.b);});},_7E=function(_7F,_7G){return E(_7F)==E(_7G);},_7H=function(_7I,_7J,_7K,_7L){if(_7I!=_7K){return false;}else{return new F(function(){return _7E(_7J,_7L);});}},_7M=function(_7N,_7O){var _7P=E(_7N),_7Q=E(_7O);return new F(function(){return _7H(E(_7P.a),_7P.b,E(_7Q.a),_7Q.b);});},_7R=new T2(0,_7M,_7z),_7S=function(_7T,_7U,_7V,_7W,_7X,_7Y,_7Z,_80,_81,_82,_83,_84,_85,_86,_87,_88,_89,_8a,_8b,_8c,_8d,_8e,_8f,_8g,_8h,_8i,_8j,_8k,_8l,_8m,_8n,_8o,_8p,_8q,_8r,_8s){if(_7T!=_8b){return false;}else{if(E(_7U)!=E(_8c)){return false;}else{if(E(_7V)!=E(_8d)){return false;}else{if(E(_7W)!=E(_8e)){return false;}else{if(E(_7X)!=E(_8f)){return false;}else{var _8t=function(_8u){if(!B(_79(_7R,_81,_8j))){return false;}else{if(!B(_79(_7R,_82,_8k))){return false;}else{if(!B(_7f(_83,_8l))){return false;}else{if(!B(_7f(_84,_8m))){return false;}else{if(!B(_7p(_85,_8n))){return false;}else{if(!B(_79(_78,_86,_8o))){return false;}else{if(!B(_79(_7R,_87,_8p))){return false;}else{if(!B(_7f(_88,_8q))){return false;}else{var _8v=function(_8w){var _8x=E(_8a);switch(_8x._){case 0:return (E(_8s)._==0)?true:false;case 1:var _8y=E(_8s);if(_8y._==1){return new F(function(){return _6W(_8x.a,_8y.a);});}else{return false;}break;case 2:var _8z=E(_8s);if(_8z._==2){return new F(function(){return _3i(_8x.a,_8z.a);});}else{return false;}break;default:var _8A=E(_8s);if(_8A._==3){return new F(function(){return _3i(_8x.a,_8A.a);});}else{return false;}}},_8B=E(_89);if(!_8B._){if(!E(_8r)._){return new F(function(){return _8v(_);});}else{return false;}}else{var _8C=E(_8r);if(!_8C._){return false;}else{if(E(_8B.a)!=E(_8C.a)){return false;}else{return new F(function(){return _8v(_);});}}}}}}}}}}}};switch(E(_7Y)){case 0:if(!E(_8g)){if(_7Z!=_8h){return false;}else{if(_80!=_8i){return false;}else{return new F(function(){return _8t(_);});}}}else{return false;}break;case 1:if(E(_8g)==1){if(_7Z!=_8h){return false;}else{if(_80!=_8i){return false;}else{return new F(function(){return _8t(_);});}}}else{return false;}break;default:if(E(_8g)==2){if(_7Z!=_8h){return false;}else{if(_80!=_8i){return false;}else{return new F(function(){return _8t(_);});}}}else{return false;}}}}}}}},_8D=function(_8E,_8F){var _8G=E(_8E),_8H=E(_8G.b),_8I=E(_8F),_8J=E(_8I.b);return (!B(_7S(_8G.a,_8H.a,_8H.b,_8H.c,_8H.d,_8G.c,_8G.d,_8G.e,_8G.f,_8G.g,_8G.h,_8G.i,_8G.j,_8G.k,_8G.l,_8G.m,_8G.n,_8G.o,_8I.a,_8J.a,_8J.b,_8J.c,_8J.d,_8I.c,_8I.d,_8I.e,_8I.f,_8I.g,_8I.h,_8I.i,_8I.j,_8I.k,_8I.l,_8I.m,_8I.n,_8I.o)))?true:false;},_8K=function(_8L,_8M){var _8N=E(_8L),_8O=E(_8N.b),_8P=E(_8M),_8Q=E(_8P.b);return new F(function(){return _7S(_8N.a,_8O.a,_8O.b,_8O.c,_8O.d,_8N.c,_8N.d,_8N.e,_8N.f,_8N.g,_8N.h,_8N.i,_8N.j,_8N.k,_8N.l,_8N.m,_8N.n,_8N.o,_8P.a,_8Q.a,_8Q.b,_8Q.c,_8Q.d,_8P.c,_8P.d,_8P.e,_8P.f,_8P.g,_8P.h,_8P.i,_8P.j,_8P.k,_8P.l,_8P.m,_8P.n,_8P.o);});},_8R=new T2(0,_8K,_8D),_8S=function(_8T,_8U){while(1){var _8V=E(_8T);if(!_8V._){return (E(_8U)._==0)?true:false;}else{var _8W=E(_8U);if(!_8W._){return false;}else{if(E(_8V.a)!=E(_8W.a)){return false;}else{_8T=_8V.b;_8U=_8W.b;continue;}}}}},_8X=function(_8Y,_8Z,_90,_91,_92,_93,_94,_95,_96,_97,_98,_99,_9a,_9b,_9c,_9d,_9e,_9f,_9g,_9h){var _9i=function(_9j){var _9k=function(_9l){if(_91!=_9b){return false;}else{var _9m=function(_9n){var _9o=function(_9p){var _9q=function(_9r){return (!E(_95))?(!E(_9f))?(!E(_96))?(!E(_9g))?true:false:E(_9g):false:(!E(_9f))?false:(!E(_96))?(!E(_9g))?true:false:E(_9g);};if(!E(_94)){if(!E(_9e)){return new F(function(){return _9q(_);});}else{return false;}}else{if(!E(_9e)){return false;}else{return new F(function(){return _9q(_);});}}};if(!E(_93)){if(!E(_9d)){return new F(function(){return _9o(_);});}else{return false;}}else{if(!E(_9d)){return false;}else{return new F(function(){return _9o(_);});}}};if(!E(_92)){if(!E(_9c)){if(!B(_9m(_))){return false;}else{return new F(function(){return _8S(_97,_9h);});}}else{return false;}}else{if(!E(_9c)){return false;}else{if(!B(_9m(_))){return false;}else{return new F(function(){return _8S(_97,_9h);});}}}}},_9s=E(_8Z);if(!_9s._){if(!E(_99)._){if(!B(_79(_8R,_90,_9a))){return false;}else{return new F(function(){return _9k(_);});}}else{return false;}}else{var _9t=E(_99);if(!_9t._){return false;}else{var _9u=E(_9s.a),_9v=E(_9t.a);if(!B(_7p(_9u.a,_9v.a))){return false;}else{if(!B(_7f(_9u.b,_9v.b))){return false;}else{if(_9u.c!=_9v.c){return false;}else{if(!B(_79(_8R,_90,_9a))){return false;}else{return new F(function(){return _9k(_);});}}}}}}},_9w=E(_8Y);if(!_9w._){if(!E(_98)._){return new F(function(){return _9i(_);});}else{return false;}}else{var _9x=E(_98);if(!_9x._){return false;}else{var _9y=_9x.a,_9z=E(_9w.a);if(!_9z._){var _9A=E(_9y);if(!_9A._){if(E(_9z.a)!=E(_9A.a)){return false;}else{return new F(function(){return _9i(_);});}}else{return false;}}else{var _9B=E(_9y);if(!_9B._){return false;}else{if(E(_9z.a)!=E(_9B.a)){return false;}else{return new F(function(){return _9i(_);});}}}}}},_9C=function(_9D,_9E){while(1){var _9F=E(_9D);if(!_9F._){return E(_9E);}else{var _9G=_9E+1|0;_9D=_9F.b;_9E=_9G;continue;}}},_9H=function(_9I,_9J){while(1){var _9K=E(_9I);if(!_9K._){return E(_9J);}else{_9I=_9K.b;_9J=_9K.a;continue;}}},_9L=function(_9M,_9N,_9O){return new F(function(){return _9H(_9N,_9M);});},_9P=new T(function(){return B(unCStr("!!: negative index"));}),_9Q=new T(function(){return B(unCStr("Prelude."));}),_9R=new T(function(){return B(_3(_9Q,_9P));}),_9S=new T(function(){return B(err(_9R));}),_9T=new T(function(){return B(unCStr("!!: index too large"));}),_9U=new T(function(){return B(_3(_9Q,_9T));}),_9V=new T(function(){return B(err(_9U));}),_9W=function(_9X,_9Y){while(1){var _9Z=E(_9X);if(!_9Z._){return E(_9V);}else{var _a0=E(_9Y);if(!_a0){return E(_9Z.a);}else{_9X=_9Z.b;_9Y=_a0-1|0;continue;}}}},_a1=function(_a2,_a3){if(_a3>=0){return new F(function(){return _9W(_a2,_a3);});}else{return E(_9S);}},_a4=function(_a5,_a6){while(1){var _a7=E(_a6);if(!_a7._){return __Z;}else{var _a8=_a7.b,_a9=E(_a5);if(_a9==1){return E(_a8);}else{_a5=_a9-1|0;_a6=_a8;continue;}}}},_aa=function(_ab,_ac,_ad){var _ae=new T2(1,_ab,new T(function(){var _af=_ac+1|0;if(_af>0){return B(_a4(_af,_ad));}else{return E(_ad);}}));if(0>=_ac){return E(_ae);}else{var _ag=function(_ah,_ai){var _aj=E(_ah);if(!_aj._){return E(_ae);}else{var _ak=_aj.a,_al=E(_ai);return (_al==1)?new T2(1,_ak,_ae):new T2(1,_ak,new T(function(){return B(_ag(_aj.b,_al-1|0));}));}};return new F(function(){return _ag(_ad,_ac);});}},_am=__Z,_an=function(_ao,_ap){while(1){var _aq=E(_ao);if(!_aq._){return E(_ap);}else{_ao=_aq.b;_ap=_aq.a;continue;}}},_ar=function(_as,_at){var _au=E(_at);return (_au._==0)?__Z:new T2(1,_as,new T(function(){return B(_ar(_au.a,_au.b));}));},_av=new T(function(){return B(unCStr(": empty list"));}),_aw=function(_ax){return new F(function(){return err(B(_3(_9Q,new T(function(){return B(_3(_ax,_av));},1))));});},_ay=new T(function(){return B(unCStr("init"));}),_az=new T(function(){return B(_aw(_ay));}),_aA=new T(function(){return B(unCStr("last"));}),_aB=new T(function(){return B(_aw(_aA));}),_aC=new T(function(){return B(unCStr("base"));}),_aD=new T(function(){return B(unCStr("Control.Exception.Base"));}),_aE=new T(function(){return B(unCStr("PatternMatchFail"));}),_aF=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_aC,_aD,_aE),_aG=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_aF,_v,_v),_aH=function(_aI){return E(_aG);},_aJ=function(_aK){var _aL=E(_aK);return new F(function(){return _X(B(_V(_aL.a)),_aH,_aL.b);});},_aM=function(_aN){return E(E(_aN).a);},_aO=function(_aP){return new T2(0,_aQ,_aP);},_aR=function(_aS,_aT){return new F(function(){return _3(E(_aS).a,_aT);});},_aU=function(_aV,_aW){return new F(function(){return _28(_aR,_aV,_aW);});},_aX=function(_aY,_aZ,_b0){return new F(function(){return _3(E(_aZ).a,_b0);});},_b1=new T3(0,_aX,_aM,_aU),_aQ=new T(function(){return new T5(0,_aH,_b1,_aO,_aJ,_aM);}),_b2=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_b3=function(_b4,_b5){return new F(function(){return die(new T(function(){return B(A2(_5h,_b5,_b4));}));});},_b6=function(_b7,_b8){return new F(function(){return _b3(_b7,_b8);});},_b9=function(_ba,_bb){var _bc=E(_bb);if(!_bc._){return new T2(0,_v,_v);}else{var _bd=_bc.a;if(!B(A1(_ba,_bd))){return new T2(0,_v,_bc);}else{var _be=new T(function(){var _bf=B(_b9(_ba,_bc.b));return new T2(0,_bf.a,_bf.b);});return new T2(0,new T2(1,_bd,new T(function(){return E(E(_be).a);})),new T(function(){return E(E(_be).b);}));}}},_bg=32,_bh=new T(function(){return B(unCStr("\n"));}),_bi=function(_bj){return (E(_bj)==124)?false:true;},_bk=function(_bl,_bm){var _bn=B(_b9(_bi,B(unCStr(_bl)))),_bo=_bn.a,_bp=function(_bq,_br){var _bs=new T(function(){var _bt=new T(function(){return B(_3(_bm,new T(function(){return B(_3(_br,_bh));},1)));});return B(unAppCStr(": ",_bt));},1);return new F(function(){return _3(_bq,_bs);});},_bu=E(_bn.b);if(!_bu._){return new F(function(){return _bp(_bo,_v);});}else{if(E(_bu.a)==124){return new F(function(){return _bp(_bo,new T2(1,_bg,_bu.b));});}else{return new F(function(){return _bp(_bo,_v);});}}},_bv=function(_bw){return new F(function(){return _b6(new T1(0,new T(function(){return B(_bk(_bw,_b2));})),_aQ);});},_bx=new T(function(){return B(_bv("Events.hs:80:7-27|(hco : tlCos)"));}),_by=40,_bz=new T2(1,_by,_v),_bA=new T(function(){return B(unCStr("\u305b\u3044\u304b\u3044\uff01"));}),_bB=new T2(1,_bA,_v),_bC=1,_bD=new T1(0,_bC),_bE=new T(function(){return B(unCStr("\u306f"));}),_bF=new T(function(){return B(unCStr("\u3065"));}),_bG=new T(function(){return B(unCStr("\u308c"));}),_bH=new T2(1,_bG,_v),_bI=new T2(1,_bF,_bH),_bJ=new T2(1,_bE,_bI),_bK=120,_bL=function(_bM,_bN,_bO,_bP,_bQ,_bR,_bS,_bT){var _bU=function(_bV){if(_bV!=_bN){var _bW=new T(function(){var _bX=E(_bQ);if(!_bX._){return E(_bx);}else{return new T2(0,_bX.a,_bX.b);}}),_bY=new T(function(){var _bZ=function(_c0){var _c1=new T(function(){return E(E(_bW).b);}),_c2=new T(function(){var _c3=B(_an(_c1,_aB));return {_:0,a:_c3.a,b:E(_c3.b),c:E(_c3.c),d:_c3.d,e:_c3.e,f:E(_c3.f),g:E(_c3.g),h:E(_c3.h),i:E(_c3.i),j:E(_bJ),k:E(_c3.k),l:E(_c3.l),m:E(_c3.m),n:E(_c3.n),o:E(new T1(1,new T(function(){var _c4=E(_bO);if(!_c4._){return E(_bD);}else{return E(_c4.a);}})))};}),_c5=function(_c6){var _c7=E(_c6);return (_c7._==0)?E(new T2(1,_c2,_v)):new T2(1,new T(function(){var _c8=E(_c7.a);return {_:0,a:_c8.a,b:E(_c8.b),c:E(_c8.c),d:_c8.d,e:_c8.e,f:E(_c8.f),g:E(_c8.g),h:E(_c8.h),i:E(_c8.i),j:E(_c8.j),k:E(_c8.k),l:E(_c8.l),m:E(_c8.m),n:E(_c8.n),o:E(_am)};}),new T(function(){return B(_c5(_c7.b));}));},_c9=new T(function(){var _ca=E(_c1);if(!_ca._){return E(_az);}else{return B(_ar(_ca.a,_ca.b));}}),_cb=new T(function(){return B(_aa(new T(function(){var _cc=B(_a1(_c9,_bN));return {_:0,a:_cc.a,b:E(_cc.b),c:E(_cc.c),d:3,e:_cc.e,f:E(_cc.f),g:E(_cc.g),h:E(_cc.h),i:E(_cc.i),j:E(_cc.j),k:E(_cc.k),l:E(_cc.l),m:E(_cc.m),n:E(_cc.n),o:E(_cc.o)};}),_bN,_c9));});return new F(function(){return _c5(B(_aa(new T(function(){var _cd=B(_a1(_c9,_c0));return {_:0,a:_cd.a,b:E(_cd.b),c:E(_cd.c),d:4,e:_cd.e,f:E(_cd.f),g:E(_cd.g),h:E(_cd.h),i:E(_cd.i),j:E(_cd.j),k:E(_cd.k),l:E(_cd.l),m:E(_cd.m),n:E(_cd.n),o:E(_cd.o)};}),_c0,_cb)));});},_ce=E(_bP);if(!_ce._){return B(_bZ(0));}else{return B(_bZ(E(_ce.a).c));}});return new T6(0,_bO,_bP,new T2(1,new T(function(){return E(E(_bW).a);}),_bY),_bR,_bS,_bT);}else{var _cf=E(_bM),_cg=_cf.a,_ch=_cf.b,_ci=E(_bQ);if(!_ci._){var _cj=E(_az);}else{var _ck=_ci.a,_cl=_ci.b,_cm=new T(function(){var _cn=B(_9L(_ck,_cl,_aB)),_co=new T(function(){return E(_cg)/3;}),_cp=new T(function(){return E(_ch)/6;}),_cq=new T(function(){var _cr=E(_bO);if(!_cr._){return E(_bD);}else{var _cs=E(_cr.a);if(!_cs._){return new T1(0,new T(function(){return E(_cs.a)+1|0;}));}else{return new T1(1,new T(function(){return E(_cs.a)+1|0;}));}}});return {_:0,a:_cn.a,b:E(new T4(0,_co,_cp,new T(function(){var _ct=E(_co);return E(_cg)-(_ct+_ct);}),new T(function(){var _cu=E(_cp);return E(_ch)-(_cu+_cu);}))),c:E(_cn.c),d:_cn.d,e:_cn.e,f:E(new T2(1,new T2(0,new T(function(){return E(_cg)/2-E(_co)-20;}),_bK),_v)),g:E(_cn.g),h:E(_bz),i:E(_cn.i),j:E(_bB),k:E(_cn.k),l:E(_cn.l),m:E(_cn.m),n:E(_cn.n),o:E(new T1(1,_cq))};}),_cv=function(_cw){var _cx=E(_cw);return (_cx._==0)?E(new T2(1,_cm,_v)):new T2(1,new T(function(){var _cy=E(_cx.a);return {_:0,a:_cy.a,b:E(_cy.b),c:E(_cy.c),d:_cy.d,e:_cy.e,f:E(_cy.f),g:E(_cy.g),h:E(_cy.h),i:E(_cy.i),j:E(_cy.j),k:E(_cy.k),l:E(_cy.l),m:E(_cy.m),n:E(_cy.n),o:E(_am)};}),new T(function(){return B(_cv(_cx.b));}));},_cj=B(_cv(B(_ar(_ck,_cl))));}return new T6(0,_bO,_bP,_cj,_bR,_bS,_bT);}},_cz=E(_bP);if(!_cz._){return new F(function(){return _bU(0);});}else{return new F(function(){return _bU(E(_cz.a).c);});}},_cA=new T2(1,_6e,_v),_cB=new T2(1,_6e,_cA),_cC=new T2(1,_6e,_cB),_cD=5,_cE=new T2(1,_cD,_v),_cF=new T2(1,_cD,_cE),_cG=new T2(1,_cD,_cF),_cH=50,_cI=new T2(1,_cH,_v),_cJ=new T2(1,_cH,_cI),_cK=new T2(1,_cH,_cJ),_cL=new T(function(){return B(unCStr("\u3075"));}),_cM=new T2(1,_cL,_v),_cN=new T(function(){return B(unCStr("\u305f"));}),_cO=new T2(1,_cN,_cM),_cP=new T(function(){return B(unCStr("\u3053"));}),_cQ=new T2(1,_cP,_cO),_cR=50,_cS=function(_cT,_cU,_cV,_cW){var _cX=new T(function(){return E(_cT)/8*3-20;}),_cY=new T(function(){return E(_cT)/8;});return {_:0,a:_cV,b:E(new T4(0,_cY,new T(function(){var _cZ=E(_cU);return _cZ-_cZ/6;}),new T(function(){var _d0=E(_cY);return E(_cT)-(_d0+_d0);}),new T(function(){return E(_cU)/8;}))),c:E(_62),d:1,e:6,f:E(new T2(1,new T2(0,new T(function(){return E(_cX)-50;}),_cR),new T2(1,new T2(0,_cX,_cR),new T2(1,new T2(0,new T(function(){return E(_cX)+50;}),_cR),_v)))),g:E(_v),h:E(_cK),i:E(_cG),j:E(_cQ),k:E(_cC),l:E(_v),m:E(_v),n:E(_2q),o:E(new T1(3,_cW))};},_d1=function(_d2){var _d3=E(_d2);return {_:0,a:_d3.a,b:E(_d3.b),c:E(_d3.c),d:0,e:_d3.e,f:E(_d3.f),g:E(_d3.g),h:E(_d3.h),i:E(_d3.i),j:E(_d3.j),k:E(_d3.k),l:E(_d3.l),m:E(_d3.m),n:E(_d3.n),o:E(_d3.o)};},_d4=new T(function(){return B(_bv("Events.hs:27:7-27|(hco : chCos)"));}),_d5=function(_d6,_d7){var _d8=E(_d7);return (_d8._==0)?__Z:new T2(1,new T(function(){return B(A1(_d6,_d8.a));}),new T(function(){return B(_d5(_d6,_d8.b));}));},_d9=function(_da,_db,_dc,_dd,_de,_df,_dg,_dh,_di){var _dj=new T(function(){var _dk=E(_df);if(!_dk._){return E(_d4);}else{return new T2(0,_dk.a,_dk.b);}}),_dl=new T(function(){var _dm=function(_dn){var _do=E(_dc),_dp=new T(function(){return E(E(_dj).b);}),_dq=B(_aa(new T(function(){var _dr=B(_a1(_dp,_do));return {_:0,a:_dr.a,b:E(_dr.b),c:E(_dr.c),d:4,e:_dr.e,f:E(_dr.f),g:E(_dr.g),h:E(_dr.h),i:E(_dr.i),j:E(_dr.j),k:E(_dr.k),l:E(_dr.l),m:E(_dr.m),n:E(_dr.n),o:E(_dr.o)};}),_do,new T(function(){return B(_d5(_d1,_dp));})));if((_dn+1|0)!=E(_db)){var _ds=E(_dq);if(!_ds._){return E(_az);}else{return new F(function(){return _3(B(_ar(_ds.a,_ds.b)),new T2(1,new T(function(){var _dt=E(_da);return B(_cS(_dt.a,_dt.b,_dn+1|0,_do));}),_v));});}}else{return new F(function(){return _3(_dq,new T2(1,new T(function(){var _du=E(_da);return B(_cS(_du.a,_du.b,_dn+1|0,_do));}),_v));});}},_dv=E(_de);if(!_dv._){return B(_dm(0));}else{return B(_dm(B(_9C(E(_dv.a).a,0))));}});return new T6(0,_dd,_de,new T2(1,new T(function(){return E(E(_dj).a);}),_dl),_dg,_dh,_di);},_dw=new T(function(){return eval("(function(e){e.width = e.width;})");}),_dx=function(_){return _5L;},_dy=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_dz=function(_dA,_dB,_dC){var _dD=new T(function(){return toJSStr(E(_dC));});return function(_dE,_){var _dF=__app4(E(_dy),E(_dE),E(_dD),E(_dA),E(_dB));return new F(function(){return _dx(_);});};},_dG=0,_dH=new T(function(){return B(_dz(_dG,_dG,_v));}),_dI=function(_dJ,_dK){return E(_dJ)!=E(_dK);},_dL=function(_dM,_dN){return E(_dM)==E(_dN);},_dO=new T2(0,_dL,_dI),_dP=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_dQ=new T(function(){return eval("(function(ctx){ctx.save();})");}),_dR=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_dS=function(_dT,_dU,_dV,_){var _dW=__app1(E(_dQ),_dV),_dX=__app2(E(_dR),_dV,E(_dT)),_dY=B(A2(_dU,_dV,_)),_dZ=__app1(E(_dP),_dV);return new F(function(){return _dx(_);});},_e0=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_e1=function(_e2,_e3,_e4,_e5,_){var _e6=__app1(E(_dQ),_e5),_e7=__app3(E(_e0),_e5,E(_e2),E(_e3)),_e8=B(A2(_e4,_e5,_)),_e9=__app1(E(_dP),_e5);return new F(function(){return _dx(_);});},_ea=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_eb=function(_ec,_ed,_ee,_ef,_){var _eg=__app1(E(_dQ),_ef),_eh=__app3(E(_ea),_ef,E(_ec),E(_ed)),_ei=B(A2(_ee,_ef,_)),_ej=__app1(E(_dP),_ef);return new F(function(){return _dx(_);});},_ek=new T(function(){return eval("(function(ctx,i,x,y){ctx.drawImage(i,x,y);})");}),_el=function(_em,_en,_eo,_ep,_){var _eq=__app4(E(_ek),_ep,_em,_en,_eo);return new F(function(){return _dx(_);});},_er=function(_es,_et,_eu){var _ev=E(_eu);return (_ev._==0)?0:(!B(A3(_4b,_es,_et,_ev.a)))?1+B(_er(_es,_et,_ev.b))|0:0;},_ew=",",_ex="rgba(",_ey=new T(function(){return toJSStr(_v);}),_ez="rgb(",_eA=")",_eB=new T2(1,_eA,_v),_eC=function(_eD){var _eE=E(_eD);if(!_eE._){var _eF=jsCat(new T2(1,_ez,new T2(1,new T(function(){return String(_eE.a);}),new T2(1,_ew,new T2(1,new T(function(){return String(_eE.b);}),new T2(1,_ew,new T2(1,new T(function(){return String(_eE.c);}),_eB)))))),E(_ey));return E(_eF);}else{var _eG=jsCat(new T2(1,_ex,new T2(1,new T(function(){return String(_eE.a);}),new T2(1,_ew,new T2(1,new T(function(){return String(_eE.b);}),new T2(1,_ew,new T2(1,new T(function(){return String(_eE.c);}),new T2(1,_ew,new T2(1,new T(function(){return String(_eE.d);}),_eB)))))))),E(_ey));return E(_eG);}},_eH="strokeStyle",_eI="fillStyle",_eJ=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_eK=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_eL=function(_eM,_eN){var _eO=new T(function(){return B(_eC(_eM));});return function(_eP,_){var _eQ=E(_eP),_eR=E(_eI),_eS=E(_eJ),_eT=__app2(_eS,_eQ,_eR),_eU=E(_eH),_eV=__app2(_eS,_eQ,_eU),_eW=E(_eO),_eX=E(_eK),_eY=__app3(_eX,_eQ,_eR,_eW),_eZ=__app3(_eX,_eQ,_eU,_eW),_f0=B(A2(_eN,_eQ,_)),_f1=String(_eT),_f2=__app3(_eX,_eQ,_eR,_f1),_f3=String(_eV),_f4=__app3(_eX,_eQ,_eU,_f3);return new F(function(){return _dx(_);});};},_f5="font",_f6=function(_f7,_f8){var _f9=new T(function(){return toJSStr(E(_f7));});return function(_fa,_){var _fb=E(_fa),_fc=E(_f5),_fd=__app2(E(_eJ),_fb,_fc),_fe=E(_eK),_ff=__app3(_fe,_fb,_fc,E(_f9)),_fg=B(A2(_f8,_fb,_)),_fh=String(_fd),_fi=__app3(_fe,_fb,_fc,_fh);return new F(function(){return _dx(_);});};},_fj=0,_fk=new T(function(){return B(unCStr("px IPAGothic"));}),_fl=new T(function(){return B(unCStr("\u3042\u3044\u3046\u3048\u304axkhnmtrsy \u304b\u306f\u306a\u307e\u304d\u3072\u306b\u307f\u304f\u3075\u306c\u3080\u3051\u3078\u306d\u3081\u3053\u307b\u306e\u3082\u3068\u308d\u305d\u3088\u3092\u3066\u308c\u305b\u3091\u3064\u308b\u3059\u3086\u3093\u3061\u308a\u3057\u3090\u305f\u3089\u3055\u3084\u308f\u309b\u963f\u548c\u5b87\u543e\u4ed8\u9808\u88ab\u610f\u767e\u96c4\u9593\u6ce2\u304c9\u7a42\u305e\u8a71\u8449\u3056\u3050\u3073\u7dd2\u30693\u305a\u3070\u3076\u304e\u3079\u88dc\u82bd1\u5e9c\u5834\u3058\u500b\u6211\u3054\u56f3\u6642\u66fe\u706b\u65e5\u3060\u5ea7\u7fbd4\u99ac\u90e8\u7956\u7089\u5177\u8a9e\u3065\u5f8c\u5b50\u7537\u3067\u305c\u51fa\u88f3\u7f8e"));}),_fm=function(_fn,_fo,_fp,_fq,_fr,_fs,_ft,_fu,_fv,_fw,_){var _fx=E(_fw);if(!_fx._){return _5L;}else{var _fy=_fx.b,_fz=E(_fs),_fA=_fz.b,_fB=E(_fv),_fC=_fB.a,_fD=_fB.b,_fE=E(_fx.a),_fF=new T(function(){return E(_fr);});if(E(_fE)==13){return new F(function(){return _fG(_fn,_fo,_fp,_fq,_fr,_fz.a,_fA,_ft,0,new T(function(){return E(_fC)-E(_fF)*1.2;}),_ft,_fy,_);});}else{var _fH=function(_){var _fI=new T(function(){return E(_fF)*1.1;}),_fJ=new T(function(){var _fK=E(_fu),_fL=E(_fA)/E(_fI),_fM=_fL&4294967295;if(_fL>=_fM){return (_fK+1|0)>(_fM-2|0);}else{return (_fK+1|0)>((_fM-1|0)-2|0);}});return new F(function(){return _fm(_fn,_fo,_fp,_fq,_fr,_fz,_ft,new T(function(){if(!E(_fJ)){return E(_fu)+1|0;}else{return E(_fj);}}),new T2(0,new T(function(){if(!E(_fJ)){return E(_fC);}else{return E(_fC)-E(_fF)*1.2;}}),new T(function(){if(!E(_fJ)){return E(_fD)+E(_fI);}else{return E(_ft);}})),_fy,_);});};if(!E(_fq)){var _fN=new T(function(){var _fO=new T(function(){return B(_dz(_dG,_dG,new T2(1,_fE,_v)));}),_fP=function(_fQ,_){return new F(function(){return _dS(_dG,_fO,E(_fQ),_);});};return B(_f6(new T(function(){return B(_3(B(_d(0,E(_fr),_v)),_fk));},1),function(_fR,_){return new F(function(){return _eb(_fC,_fD,_fP,E(_fR),_);});}));}),_fS=B(A(_eL,[_fp,_fN,E(_fn).a,_]));return new F(function(){return _fH(_);});}else{var _fT=new T(function(){return E(_fr)/20;}),_fU=function(_fV,_){return new F(function(){return _e1(_fT,_fT,function(_fW,_){if(!B(_4d(_dO,_fE,_fl))){return new F(function(){return _el(B(_a1(_fo,14)),0,0,E(_fW),_);});}else{return new F(function(){return _el(B(_a1(_fo,B(_er(_dO,_fE,_fl)))),0,0,E(_fW),_);});}},E(_fV),_);});},_fX=B(_eb(new T(function(){return E(_fC)-E(_fF)/6;},1),new T(function(){return E(_fD)-E(_fF)*3/4;},1),_fU,E(_fn).a,_));return new F(function(){return _fH(_);});}}}},_fG=function(_fY,_fZ,_g0,_g1,_g2,_g3,_g4,_g5,_g6,_g7,_g8,_g9,_){while(1){var _ga=B((function(_gb,_gc,_gd,_ge,_gf,_gg,_gh,_gi,_gj,_gk,_gl,_gm,_){var _gn=E(_gm);if(!_gn._){return _5L;}else{var _go=_gn.b,_gp=E(_gn.a),_gq=new T(function(){return E(_gf);});if(E(_gp)==13){var _gr=_gb,_gs=_gc,_gt=_gd,_gu=_ge,_gv=_gf,_gw=_gg,_gx=_gh,_gy=_gi,_gz=_gi;_fY=_gr;_fZ=_gs;_g0=_gt;_g1=_gu;_g2=_gv;_g3=_gw;_g4=_gx;_g5=_gy;_g6=0;_g7=new T(function(){return E(_gk)-E(_gq)*1.2;});_g8=_gz;_g9=_go;return __continue;}else{var _gA=function(_){var _gB=new T(function(){return E(_gq)*1.1;}),_gC=new T(function(){var _gD=E(_gh)/E(_gB),_gE=_gD&4294967295;if(_gD>=_gE){return (_gj+1|0)>(_gE-2|0);}else{return (_gj+1|0)>((_gE-1|0)-2|0);}});return new F(function(){return _fm(_gb,_gc,_gd,_ge,_gf,new T2(0,_gg,_gh),_gi,new T(function(){if(!E(_gC)){return _gj+1|0;}else{return E(_fj);}}),new T2(0,new T(function(){if(!E(_gC)){return E(_gk);}else{return E(_gk)-E(_gq)*1.2;}}),new T(function(){if(!E(_gC)){return E(_gl)+E(_gB);}else{return E(_gi);}})),_go,_);});};if(!E(_ge)){var _gF=new T(function(){var _gG=new T(function(){return B(_dz(_dG,_dG,new T2(1,_gp,_v)));}),_gH=function(_gI,_){return new F(function(){return _dS(_dG,_gG,E(_gI),_);});};return B(_f6(new T(function(){return B(_3(B(_d(0,E(_gf),_v)),_fk));},1),function(_gJ,_){return new F(function(){return _eb(_gk,_gl,_gH,E(_gJ),_);});}));}),_gK=B(A(_eL,[_gd,_gF,E(_gb).a,_]));return new F(function(){return _gA(_);});}else{var _gL=new T(function(){return E(_gf)/20;}),_gM=function(_gN,_){return new F(function(){return _e1(_gL,_gL,function(_gO,_){if(!B(_4d(_dO,_gp,_fl))){return new F(function(){return _el(B(_a1(_gc,14)),0,0,E(_gO),_);});}else{return new F(function(){return _el(B(_a1(_gc,B(_er(_dO,_gp,_fl)))),0,0,E(_gO),_);});}},E(_gN),_);});},_gP=B(_eb(new T(function(){return E(_gk)-E(_gq)/6;},1),new T(function(){return E(_gl)-E(_gq)*3/4;},1),_gM,E(_gb).a,_));return new F(function(){return _gA(_);});}}}})(_fY,_fZ,_g0,_g1,_g2,_g3,_g4,_g5,_g6,_g7,_g8,_g9,_));if(_ga!=__continue){return _ga;}}},_gQ=function(_gR,_gS,_gT,_gU,_gV,_gW,_gX,_gY,_gZ,_h0,_h1,_h2,_h3,_){while(1){var _h4=B((function(_h5,_h6,_h7,_h8,_h9,_ha,_hb,_hc,_hd,_he,_hf,_hg,_hh,_){var _hi=E(_hh);if(!_hi._){return _5L;}else{var _hj=_hi.b,_hk=E(_hi.a),_hl=new T(function(){return E(_ha);});if(E(_hk)==13){var _hm=_h5,_hn=_h6,_ho=_h7,_hp=_h8,_hq=_h9,_hr=_ha,_hs=_hb,_ht=_hc,_hu=_hd,_hv=_hd;_gR=_hm;_gS=_hn;_gT=_ho;_gU=_hp;_gV=_hq;_gW=_hr;_gX=_hs;_gY=_ht;_gZ=_hu;_h0=0;_h1=new T(function(){return E(_hf)-E(_hl)*1.2;});_h2=_hv;_h3=_hj;return __continue;}else{var _hw=function(_){var _hx=new T(function(){return E(_hl)*1.1;}),_hy=new T(function(){var _hz=E(_hc)/E(_hx),_hA=_hz&4294967295;if(_hz>=_hA){return (_he+1|0)>(_hA-2|0);}else{return (_he+1|0)>((_hA-1|0)-2|0);}});return new F(function(){return _fm(new T2(0,_h5,_h6),_h7,_h8,_h9,_ha,new T2(0,_hb,_hc),_hd,new T(function(){if(!E(_hy)){return _he+1|0;}else{return E(_fj);}}),new T2(0,new T(function(){if(!E(_hy)){return E(_hf);}else{return E(_hf)-E(_hl)*1.2;}}),new T(function(){if(!E(_hy)){return E(_hg)+E(_hx);}else{return E(_hd);}})),_hj,_);});};if(!E(_h9)){var _hB=new T(function(){var _hC=new T(function(){return B(_dz(_dG,_dG,new T2(1,_hk,_v)));}),_hD=function(_hE,_){return new F(function(){return _dS(_dG,_hC,E(_hE),_);});};return B(_f6(new T(function(){return B(_3(B(_d(0,E(_ha),_v)),_fk));},1),function(_hF,_){return new F(function(){return _eb(_hf,_hg,_hD,E(_hF),_);});}));}),_hG=B(A(_eL,[_h8,_hB,_h5,_]));return new F(function(){return _hw(_);});}else{var _hH=new T(function(){return E(_ha)/20;}),_hI=function(_hJ,_){return new F(function(){return _e1(_hH,_hH,function(_hK,_){if(!B(_4d(_dO,_hk,_fl))){return new F(function(){return _el(B(_a1(_h7,14)),0,0,E(_hK),_);});}else{return new F(function(){return _el(B(_a1(_h7,B(_er(_dO,_hk,_fl)))),0,0,E(_hK),_);});}},E(_hJ),_);});},_hL=B(_eb(new T(function(){return E(_hf)-E(_hl)/6;},1),new T(function(){return E(_hg)-E(_hl)*3/4;},1),_hI,_h5,_));return new F(function(){return _hw(_);});}}}})(_gR,_gS,_gT,_gU,_gV,_gW,_gX,_gY,_gZ,_h0,_h1,_h2,_h3,_));if(_h4!=__continue){return _h4;}}},_hM=new T(function(){return eval("(function(ctx, x, y, radius, fromAngle, toAngle){ctx.arc(x, y, radius, fromAngle, toAngle);})");}),_hN=function(_hO,_hP,_hQ,_hR,_hS,_hT,_){var _hU=__apply(E(_hM),new T2(1,_hS,new T2(1,_hR,new T2(1,_hQ,new T2(1,_hP,new T2(1,_hO,new T2(1,_hT,_v)))))));return new F(function(){return _dx(_);});},_hV=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_hW=new T(function(){return eval("(function(ctx,x,y){ctx.lineTo(x,y);})");}),_hX=function(_hY,_hZ,_){var _i0=E(_hY);if(!_i0._){return _5L;}else{var _i1=E(_i0.a),_i2=E(_hZ),_i3=__app3(E(_hV),_i2,E(_i1.a),E(_i1.b)),_i4=E(_i0.b);if(!_i4._){return _5L;}else{var _i5=E(_i4.a),_i6=E(_hW),_i7=__app3(_i6,_i2,E(_i5.a),E(_i5.b)),_i8=function(_i9,_){while(1){var _ia=E(_i9);if(!_ia._){return _5L;}else{var _ib=E(_ia.a),_ic=__app3(_i6,_i2,E(_ib.a),E(_ib.b));_i9=_ia.b;continue;}}};return new F(function(){return _i8(_i4.b,_);});}}},_id=function(_ie,_if,_ig,_ih,_ii,_){var _ij=B(_hN(_ie+_ig-10,_if+_ih-10,10,0,1.5707963267948966,_ii,_)),_ik=B(_hN(_ie+10,_if+_ih-10,10,1.5707963267948966,3.141592653589793,_ii,_)),_il=B(_hN(_ie+10,_if+10,10,3.141592653589793,4.71238898038469,_ii,_)),_im=B(_hN(_ie+_ig-10,_if+10,10,4.71238898038469,6.283185307179586,_ii,_));return new F(function(){return _hX(new T2(1,new T2(0,_ie+_ig,_if+_ih-10),new T2(1,new T2(0,_ie+_ig,_if+10),_v)),_ii,_);});},_in=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_io=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_ip=function(_iq,_ir,_){var _is=__app1(E(_in),_ir),_it=B(A2(_iq,_ir,_)),_iu=__app1(E(_io),_ir);return new F(function(){return _dx(_);});},_iv=function(_iw,_ix,_iy,_iz,_iA,_){return new F(function(){return _hX(new T2(1,new T2(0,_iw,_ix),new T2(1,new T2(0,_iy,_ix),new T2(1,new T2(0,_iy,_iz),new T2(1,new T2(0,_iw,_iz),new T2(1,new T2(0,_iw,_ix),_v))))),_iA,_);});},_iB=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_iC=function(_iD,_iE,_){var _iF=__app1(E(_in),_iE),_iG=B(A2(_iD,_iE,_)),_iH=__app1(E(_iB),_iE);return new F(function(){return _dx(_);});},_iI=new T3(0,200,255,200),_iJ=new T3(0,255,204,153),_iK=new T3(0,255,153,204),_iL=new T3(0,153,255,255),_iM=new T3(0,0,128,128),_iN=new T3(0,0,0,0),_iO=new T2(1,_iN,_v),_iP=new T3(0,255,255,100),_iQ=new T2(1,_iP,_iO),_iR=new T2(1,_iM,_iQ),_iS=new T2(1,_iL,_iR),_iT=new T2(1,_iK,_iS),_iU=new T2(1,_iJ,_iT),_iV=new T2(1,_iI,_iU),_iW=new T3(0,200,200,180),_iX=new T2(1,_iW,_iV),_iY="lineWidth",_iZ=function(_j0,_j1){var _j2=new T(function(){return String(E(_j0));});return function(_j3,_){var _j4=E(_j3),_j5=E(_iY),_j6=__app2(E(_eJ),_j4,_j5),_j7=E(_eK),_j8=__app3(_j7,_j4,_j5,E(_j2)),_j9=B(A2(_j1,_j4,_)),_ja=String(_j6),_jb=__app3(_j7,_j4,_j5,_ja);return new F(function(){return _dx(_);});};},_jc=3,_jd=function(_je,_jf){var _jg=E(_je);if(!_jg._){return __Z;}else{var _jh=E(_jf);return (_jh._==0)?__Z:new T2(1,new T2(0,_jg.a,_jh.a),new T(function(){return B(_jd(_jg.b,_jh.b));}));}},_ji=function(_jj,_jk,_jl,_jm,_){var _jn=E(_jm);if(!_jn._){return _5L;}else{var _jo=E(E(_jk).a),_jp=new T(function(){return E(E(_jl).b);}),_jq=function(_jr,_){while(1){var _js=B((function(_jt,_){var _ju=E(_jt);if(!_ju._){return _5L;}else{var _jv=_ju.b,_jw=E(_ju.a),_jx=_jw.d,_jy=E(_jw.b),_jz=_jy.a,_jA=_jy.b,_jB=_jy.c,_jC=_jy.d,_jD=function(_){var _jE=function(_jF,_jG,_jH,_){while(1){var _jI=B((function(_jJ,_jK,_jL,_){var _jM=E(_jJ);if(!_jM._){return _5L;}else{var _jN=E(_jK);if(!_jN._){return _5L;}else{var _jO=E(_jL);if(!_jO._){return _5L;}else{var _jP=E(_jO.a),_jQ=E(_jP.a),_jR=E(_jP.b),_jS=new T(function(){return E(_jQ.b)+E(_jA);}),_jT=B(_fG(_jj,_jp,new T(function(){return B(_a1(_iX,E(_jR.b)));}),_jN.a,_jR.a,_jB,_jC,_jS,0,new T(function(){return E(_jQ.a)+E(_jz);}),_jS,_jM.a,_));_jF=_jM.b;_jG=_jN.b;_jH=_jO.b;return __continue;}}}})(_jF,_jG,_jH,_));if(_jI!=__continue){return _jI;}}},_jU=new T(function(){return B(_jd(_jw.f,new T(function(){return B(_jd(_jw.h,_jw.i));},1)));},1);return new F(function(){return _jE(_jw.j,_jw.k,_jU,_);});};switch(E(_jw.c)){case 0:var _jV=B(_jD(_));_jr=_jv;return __continue;case 1:var _jW=E(_jj),_jX=_jW.a,_jY=new T(function(){return E(_jz)+E(_jB);}),_jZ=new T(function(){return E(_jA)+E(_jC);}),_k0=function(_k1,_){return new F(function(){return _iv(_jz,_jA,_jY,_jZ,_k1,_);});},_k2=B(A(_eL,[new T(function(){return B(_a1(_iX,_jx));},1),function(_k3,_){return new F(function(){return _iC(_k0,E(_k3),_);});},_jX,_])),_k4=B(_jD(_)),_k5=function(_k6,_){while(1){var _k7=B((function(_k8,_){var _k9=E(_k8);if(!_k9._){return _5L;}else{var _ka=_k9.b,_kb=E(_k9.a),_kc=_kb.d,_kd=E(_kb.b),_ke=_kd.a,_kf=_kd.b,_kg=_kd.c,_kh=_kd.d,_ki=function(_){var _kj=function(_kk,_kl,_km,_){while(1){var _kn=B((function(_ko,_kp,_kq,_){var _kr=E(_ko);if(!_kr._){return _5L;}else{var _ks=E(_kp);if(!_ks._){return _5L;}else{var _kt=E(_kq);if(!_kt._){return _5L;}else{var _ku=E(_kt.a),_kv=E(_ku.a),_kw=E(_ku.b),_kx=new T(function(){return E(_kv.b)+E(_kf);}),_ky=B(_gQ(_jX,_jW.b,_jp,new T(function(){return B(_a1(_iX,E(_kw.b)));}),_ks.a,_kw.a,_kg,_kh,_kx,0,new T(function(){return E(_kv.a)+E(_ke);}),_kx,_kr.a,_));_kk=_kr.b;_kl=_ks.b;_km=_kt.b;return __continue;}}}})(_kk,_kl,_km,_));if(_kn!=__continue){return _kn;}}},_kz=new T(function(){return B(_jd(_kb.f,new T(function(){return B(_jd(_kb.h,_kb.i));},1)));},1);return new F(function(){return _kj(_kb.j,_kb.k,_kz,_);});};switch(E(_kb.c)){case 0:var _kA=B(_ki(_));_k6=_ka;return __continue;case 1:var _kB=new T(function(){return E(_ke)+E(_kg);}),_kC=new T(function(){return E(_kf)+E(_kh);}),_kD=function(_kE,_){return new F(function(){return _iv(_ke,_kf,_kB,_kC,_kE,_);});},_kF=B(A(_eL,[new T(function(){return B(_a1(_iX,_kc));},1),function(_kG,_){return new F(function(){return _iC(_kD,E(_kG),_);});},_jX,_])),_kH=B(_ki(_));_k6=_ka;return __continue;default:var _kI=function(_kJ,_){return new F(function(){return _id(E(_ke),E(_kf),E(_kg),E(_kh),E(_kJ),_);});},_kK=B(A(_eL,[new T(function(){return B(_a1(_iX,_kb.e));},1),function(_kL,_){return new F(function(){return _ip(_kI,E(_kL),_);});},_jX,_])),_kM=new T(function(){var _kN=function(_kO,_){return new F(function(){return _id(E(_ke),E(_kf),E(_kg),E(_kh),E(_kO),_);});};return B(_iZ(_jc,function(_kP,_){return new F(function(){return _iC(_kN,E(_kP),_);});}));}),_kQ=B(A(_eL,[new T(function(){return B(_a1(_iX,_kc));},1),_kM,_jX,_])),_kR=B(_ki(_));_k6=_ka;return __continue;}}})(_k6,_));if(_k7!=__continue){return _k7;}}};return new F(function(){return _k5(_jv,_);});break;default:var _kS=E(_jj),_kT=_kS.a,_kU=function(_kV,_){return new F(function(){return _id(E(_jz),E(_jA),E(_jB),E(_jC),E(_kV),_);});},_kW=B(A(_eL,[new T(function(){return B(_a1(_iX,_jw.e));},1),function(_kX,_){return new F(function(){return _ip(_kU,E(_kX),_);});},_kT,_])),_kY=new T(function(){var _kZ=function(_l0,_){return new F(function(){return _id(E(_jz),E(_jA),E(_jB),E(_jC),E(_l0),_);});};return B(_iZ(_jc,function(_l1,_){return new F(function(){return _iC(_kZ,E(_l1),_);});}));}),_l2=B(A(_eL,[new T(function(){return B(_a1(_iX,_jx));},1),_kY,_kT,_])),_l3=B(_jD(_)),_l4=function(_l5,_){while(1){var _l6=B((function(_l7,_){var _l8=E(_l7);if(!_l8._){return _5L;}else{var _l9=_l8.b,_la=E(_l8.a),_lb=_la.d,_lc=E(_la.b),_ld=_lc.a,_le=_lc.b,_lf=_lc.c,_lg=_lc.d,_lh=function(_){var _li=function(_lj,_lk,_ll,_){while(1){var _lm=B((function(_ln,_lo,_lp,_){var _lq=E(_ln);if(!_lq._){return _5L;}else{var _lr=E(_lo);if(!_lr._){return _5L;}else{var _ls=E(_lp);if(!_ls._){return _5L;}else{var _lt=E(_ls.a),_lu=E(_lt.a),_lv=E(_lt.b),_lw=new T(function(){return E(_lu.b)+E(_le);}),_lx=B(_gQ(_kT,_kS.b,_jp,new T(function(){return B(_a1(_iX,E(_lv.b)));}),_lr.a,_lv.a,_lf,_lg,_lw,0,new T(function(){return E(_lu.a)+E(_ld);}),_lw,_lq.a,_));_lj=_lq.b;_lk=_lr.b;_ll=_ls.b;return __continue;}}}})(_lj,_lk,_ll,_));if(_lm!=__continue){return _lm;}}},_ly=new T(function(){return B(_jd(_la.f,new T(function(){return B(_jd(_la.h,_la.i));},1)));},1);return new F(function(){return _li(_la.j,_la.k,_ly,_);});};switch(E(_la.c)){case 0:var _lz=B(_lh(_));_l5=_l9;return __continue;case 1:var _lA=new T(function(){return E(_ld)+E(_lf);}),_lB=new T(function(){return E(_le)+E(_lg);}),_lC=function(_lD,_){return new F(function(){return _iv(_ld,_le,_lA,_lB,_lD,_);});},_lE=B(A(_eL,[new T(function(){return B(_a1(_iX,_lb));},1),function(_lF,_){return new F(function(){return _iC(_lC,E(_lF),_);});},_kT,_])),_lG=B(_lh(_));_l5=_l9;return __continue;default:var _lH=function(_lI,_){return new F(function(){return _id(E(_ld),E(_le),E(_lf),E(_lg),E(_lI),_);});},_lJ=B(A(_eL,[new T(function(){return B(_a1(_iX,_la.e));},1),function(_lK,_){return new F(function(){return _ip(_lH,E(_lK),_);});},_kT,_])),_lL=new T(function(){var _lM=function(_lN,_){return new F(function(){return _id(E(_ld),E(_le),E(_lf),E(_lg),E(_lN),_);});};return B(_iZ(_jc,function(_lO,_){return new F(function(){return _iC(_lM,E(_lO),_);});}));}),_lP=B(A(_eL,[new T(function(){return B(_a1(_iX,_lb));},1),_lL,_kT,_])),_lQ=B(_lh(_));_l5=_l9;return __continue;}}})(_l5,_));if(_l6!=__continue){return _l6;}}};return new F(function(){return _l4(_jv,_);});}}})(_jr,_));if(_js!=__continue){return _js;}}},_lR=_jn.a,_lS=_jn.b,_lT=E(_lR),_lU=_lT.d,_lV=E(_lT.b),_lW=_lV.a,_lX=_lV.b,_lY=_lV.c,_lZ=_lV.d,_m0=function(_){var _m1=function(_m2,_m3,_m4,_){while(1){var _m5=B((function(_m6,_m7,_m8,_){var _m9=E(_m6);if(!_m9._){return _5L;}else{var _ma=E(_m7);if(!_ma._){return _5L;}else{var _mb=E(_m8);if(!_mb._){return _5L;}else{var _mc=E(_mb.a),_md=E(_mc.a),_me=E(_mc.b),_mf=new T(function(){return E(_md.b)+E(_lX);}),_mg=B(_fG(_jj,_jp,new T(function(){return B(_a1(_iX,E(_me.b)));}),_ma.a,_me.a,_lY,_lZ,_mf,0,new T(function(){return E(_md.a)+E(_lW);}),_mf,_m9.a,_));_m2=_m9.b;_m3=_ma.b;_m4=_mb.b;return __continue;}}}})(_m2,_m3,_m4,_));if(_m5!=__continue){return _m5;}}},_mh=new T(function(){return B(_jd(_lT.f,new T(function(){return B(_jd(_lT.h,_lT.i));},1)));},1);return new F(function(){return _m1(_lT.j,_lT.k,_mh,_);});};switch(E(_lT.c)){case 0:var _mi=B(_m0(_));return new F(function(){return _jq(_lS,_);});break;case 1:var _mj=E(_jj),_mk=_mj.a,_ml=new T(function(){return E(_lW)+E(_lY);}),_mm=new T(function(){return E(_lX)+E(_lZ);}),_mn=function(_mo,_){return new F(function(){return _iv(_lW,_lX,_ml,_mm,_mo,_);});},_mp=B(A(_eL,[new T(function(){return B(_a1(_iX,_lU));},1),function(_mq,_){return new F(function(){return _iC(_mn,E(_mq),_);});},_mk,_])),_mr=B(_m0(_)),_ms=function(_mt,_){while(1){var _mu=B((function(_mv,_){var _mw=E(_mv);if(!_mw._){return _5L;}else{var _mx=_mw.b,_my=E(_mw.a),_mz=_my.d,_mA=E(_my.b),_mB=_mA.a,_mC=_mA.b,_mD=_mA.c,_mE=_mA.d,_mF=function(_){var _mG=function(_mH,_mI,_mJ,_){while(1){var _mK=B((function(_mL,_mM,_mN,_){var _mO=E(_mL);if(!_mO._){return _5L;}else{var _mP=E(_mM);if(!_mP._){return _5L;}else{var _mQ=E(_mN);if(!_mQ._){return _5L;}else{var _mR=E(_mQ.a),_mS=E(_mR.a),_mT=E(_mR.b),_mU=new T(function(){return E(_mS.b)+E(_mC);}),_mV=B(_gQ(_mk,_mj.b,_jp,new T(function(){return B(_a1(_iX,E(_mT.b)));}),_mP.a,_mT.a,_mD,_mE,_mU,0,new T(function(){return E(_mS.a)+E(_mB);}),_mU,_mO.a,_));_mH=_mO.b;_mI=_mP.b;_mJ=_mQ.b;return __continue;}}}})(_mH,_mI,_mJ,_));if(_mK!=__continue){return _mK;}}},_mW=new T(function(){return B(_jd(_my.f,new T(function(){return B(_jd(_my.h,_my.i));},1)));},1);return new F(function(){return _mG(_my.j,_my.k,_mW,_);});};switch(E(_my.c)){case 0:var _mX=B(_mF(_));_mt=_mx;return __continue;case 1:var _mY=new T(function(){return E(_mB)+E(_mD);}),_mZ=new T(function(){return E(_mC)+E(_mE);}),_n0=function(_n1,_){return new F(function(){return _iv(_mB,_mC,_mY,_mZ,_n1,_);});},_n2=B(A(_eL,[new T(function(){return B(_a1(_iX,_mz));},1),function(_n3,_){return new F(function(){return _iC(_n0,E(_n3),_);});},_mk,_])),_n4=B(_mF(_));_mt=_mx;return __continue;default:var _n5=function(_n6,_){return new F(function(){return _id(E(_mB),E(_mC),E(_mD),E(_mE),E(_n6),_);});},_n7=B(A(_eL,[new T(function(){return B(_a1(_iX,_my.e));},1),function(_n8,_){return new F(function(){return _ip(_n5,E(_n8),_);});},_mk,_])),_n9=new T(function(){var _na=function(_nb,_){return new F(function(){return _id(E(_mB),E(_mC),E(_mD),E(_mE),E(_nb),_);});};return B(_iZ(_jc,function(_nc,_){return new F(function(){return _iC(_na,E(_nc),_);});}));}),_nd=B(A(_eL,[new T(function(){return B(_a1(_iX,_mz));},1),_n9,_mk,_])),_ne=B(_mF(_));_mt=_mx;return __continue;}}})(_mt,_));if(_mu!=__continue){return _mu;}}};return new F(function(){return _ms(_lS,_);});break;default:var _nf=E(_jj),_ng=_nf.a,_nh=function(_ni,_){return new F(function(){return _id(E(_lW),E(_lX),E(_lY),E(_lZ),E(_ni),_);});},_nj=B(A(_eL,[new T(function(){return B(_a1(_iX,_lT.e));},1),function(_nk,_){return new F(function(){return _ip(_nh,E(_nk),_);});},_ng,_])),_nl=new T(function(){var _nm=function(_nn,_){return new F(function(){return _id(E(_lW),E(_lX),E(_lY),E(_lZ),E(_nn),_);});};return B(_iZ(_jc,function(_no,_){return new F(function(){return _iC(_nm,E(_no),_);});}));}),_np=B(A(_eL,[new T(function(){return B(_a1(_iX,_lU));},1),_nl,_ng,_])),_nq=B(_m0(_)),_nr=function(_ns,_){while(1){var _nt=B((function(_nu,_){var _nv=E(_nu);if(!_nv._){return _5L;}else{var _nw=_nv.b,_nx=E(_nv.a),_ny=_nx.d,_nz=E(_nx.b),_nA=_nz.a,_nB=_nz.b,_nC=_nz.c,_nD=_nz.d,_nE=function(_){var _nF=function(_nG,_nH,_nI,_){while(1){var _nJ=B((function(_nK,_nL,_nM,_){var _nN=E(_nK);if(!_nN._){return _5L;}else{var _nO=E(_nL);if(!_nO._){return _5L;}else{var _nP=E(_nM);if(!_nP._){return _5L;}else{var _nQ=E(_nP.a),_nR=E(_nQ.a),_nS=E(_nQ.b),_nT=new T(function(){return E(_nR.b)+E(_nB);}),_nU=B(_gQ(_ng,_nf.b,_jp,new T(function(){return B(_a1(_iX,E(_nS.b)));}),_nO.a,_nS.a,_nC,_nD,_nT,0,new T(function(){return E(_nR.a)+E(_nA);}),_nT,_nN.a,_));_nG=_nN.b;_nH=_nO.b;_nI=_nP.b;return __continue;}}}})(_nG,_nH,_nI,_));if(_nJ!=__continue){return _nJ;}}},_nV=new T(function(){return B(_jd(_nx.f,new T(function(){return B(_jd(_nx.h,_nx.i));},1)));},1);return new F(function(){return _nF(_nx.j,_nx.k,_nV,_);});};switch(E(_nx.c)){case 0:var _nW=B(_nE(_));_ns=_nw;return __continue;case 1:var _nX=new T(function(){return E(_nA)+E(_nC);}),_nY=new T(function(){return E(_nB)+E(_nD);}),_nZ=function(_o0,_){return new F(function(){return _iv(_nA,_nB,_nX,_nY,_o0,_);});},_o1=B(A(_eL,[new T(function(){return B(_a1(_iX,_ny));},1),function(_o2,_){return new F(function(){return _iC(_nZ,E(_o2),_);});},_ng,_])),_o3=B(_nE(_));_ns=_nw;return __continue;default:var _o4=function(_o5,_){return new F(function(){return _id(E(_nA),E(_nB),E(_nC),E(_nD),E(_o5),_);});},_o6=B(A(_eL,[new T(function(){return B(_a1(_iX,_nx.e));},1),function(_o7,_){return new F(function(){return _ip(_o4,E(_o7),_);});},_ng,_])),_o8=new T(function(){var _o9=function(_oa,_){return new F(function(){return _id(E(_nA),E(_nB),E(_nC),E(_nD),E(_oa),_);});};return B(_iZ(_jc,function(_ob,_){return new F(function(){return _iC(_o9,E(_ob),_);});}));}),_oc=B(A(_eL,[new T(function(){return B(_a1(_iX,_ny));},1),_o8,_ng,_])),_od=B(_nE(_));_ns=_nw;return __continue;}}})(_ns,_));if(_nt!=__continue){return _nt;}}};return new F(function(){return _nr(_lS,_);});}}},_oe=function(_of){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_of));}))));});},_og=new T(function(){return B(_oe("ww_sb48 (Double, Double)"));}),_oh=new T(function(){return B(unCStr("Prelude.undefined"));}),_oi=new T(function(){return B(err(_oh));}),_oj=function(_ok){return E(_oi);},_ol=new T(function(){return B(_oj(_));}),_om=function(_on,_oo){if(_on<=_oo){var _op=function(_oq){return new T2(1,_oq,new T(function(){if(_oq!=_oo){return B(_op(_oq+1|0));}else{return __Z;}}));};return new F(function(){return _op(_on);});}else{return __Z;}},_or=new T(function(){return B(_om(0,2147483647));}),_os=1,_ot=new T2(1,_os,_v),_ou=1,_ov=new T2(1,_ou,_v),_ow=60,_ox=40,_oy=new T2(0,_ox,_ow),_oz=new T2(1,_oy,_v),_oA=function(_oB,_oC,_oD){var _oE=E(_oC);if(!_oE._){return __Z;}else{var _oF=E(_oD);return (_oF._==0)?__Z:new T2(1,new T(function(){return B(A2(_oB,_oE.a,_oF.a));}),new T(function(){return B(_oA(_oB,_oE.b,_oF.b));}));}},_oG=function(_oH,_oI,_oJ,_oK,_oL){var _oM=new T(function(){var _oN=new T(function(){if(B(_9C(_oJ,0))==4){var _oO=new T(function(){return E(_oI)/5;}),_oP=new T(function(){var _oQ=E(_oI);return _oQ/4+_oQ/10;}),_oR=new T(function(){return E(_oO)+E(_oP)+E(_oH)/20;}),_oS=new T(function(){return E(_oH)/3;}),_oT=new T(function(){return E(_oH)/8;}),_oU=new T(function(){return E(_oT)+E(_oS)+E(_oH)/16;});return new T2(1,new T4(0,_oT,_oP,_oS,_oO),new T2(1,new T4(0,_oU,_oP,_oS,_oO),new T2(1,new T4(0,_oT,_oR,_oS,_oO),new T2(1,new T4(0,_oU,_oR,_oS,_oO),_v))));}else{return __Z;}},1),_oV=function(_oW,_oX){var _oY=E(_oW);return {_:0,a:_oY+1|0,b:E(_oX),c:E(_62),d:0,e:7,f:E(_oz),g:E(_v),h:E(_cI),i:E(_ov),j:E(new T2(1,new T(function(){return B(_a1(_oJ,_oY));}),_v)),k:E(_ot),l:E(_v),m:E(_v),n:E(new T1(1,new T(function(){return B(_a1(_oK,_oY));}))),o:E(new T1(2,_oY))};};return B(_oA(_oV,_or,_oN));});return new T2(0,{_:0,a:0,b:E(new T4(0,new T(function(){return E(_oH)/8;}),new T(function(){return E(_oI)/10;}),new T(function(){return E(_oH)/3;}),new T(function(){return E(_oI)/5;}))),c:E(_62),d:0,e:5,f:E(_oz),g:E(_v),h:E(_cI),i:E(_ov),j:E(new T2(1,new T(function(){return B(_a1(_oJ,_oL));}),_v)),k:E(_cA),l:E(_v),m:E(_v),n:E(new T1(1,new T(function(){return B(_a1(_oK,_oL));}))),o:E(_am)},_oM);},_oZ=function(_p0){return E(E(_p0).a);},_p1=function(_p2){return E(E(_p2).a);},_p3=new T1(1,_5N),_p4="false",_p5=new T1(1,_5Q),_p6="true",_p7=function(_p8){var _p9=strEq(_p8,E(_p6));if(!E(_p9)){var _pa=strEq(_p8,E(_p4));return (E(_pa)==0)?__Z:E(_p3);}else{return E(_p5);}},_pb=2,_pc="paused",_pd="ended",_pe=function(_pf,_pg){var _ph=function(_){var _pi=E(_pg),_pj=E(_eJ),_pk=__app2(_pj,_pi,E(_pd)),_pl=String(_pk),_pm=function(_pn){var _po=__app2(_pj,_pi,E(_pc));return new T(function(){var _pp=String(_po),_pq=B(_p7(_pp));if(!_pq._){return 0;}else{if(!E(_pq.a)){return 0;}else{return 1;}}});},_pr=B(_p7(_pl));if(!_pr._){return new F(function(){return _pm(_);});}else{if(!E(_pr.a)){return new F(function(){return _pm(_);});}else{return _pb;}}};return new F(function(){return A2(_5U,_pf,_ph);});},_ps="duration",_pt=new T(function(){return eval("(function(e,t) {e.currentTime = t;})");}),_pu=function(_pv,_pw,_px){var _py=new T(function(){var _pz=E(_px);switch(_pz._){case 0:return function(_){var _pA=__app2(E(_pt),E(_pw),0);return new F(function(){return _dx(_);});};break;case 1:return function(_){var _pB=E(_pw),_pC=__app2(E(_eJ),_pB,E(_ps)),_pD=String(_pC),_pE=Number(_pD),_pF=isDoubleNaN(_pE);if(!E(_pF)){var _pG=__app2(E(_pt),_pB,_pE);return new F(function(){return _dx(_);});}else{var _pH=__app2(E(_pt),_pB,0);return new F(function(){return _dx(_);});}};break;default:return function(_){var _pI=__app2(E(_pt),E(_pw),E(_pz.a));return new F(function(){return _dx(_);});};}});return new F(function(){return A2(_5U,_pv,_py);});},_pJ=function(_pK){return E(E(_pK).c);},_pL=function(_pM){return E(E(_pM).b);},_pN=__Z,_pO=new T(function(){return eval("(function(x){x.play();})");}),_pP=function(_pQ){return E(E(_pQ).b);},_pR=function(_pS,_pT){var _pU=new T(function(){return B(_pu(_pS,_pT,_pN));}),_pV=B(_p1(_pS)),_pW=new T(function(){return B(A2(_pP,B(_oZ(_pV)),_5L));}),_pX=new T(function(){var _pY=function(_){var _pZ=__app1(E(_pO),E(_pT));return new F(function(){return _dx(_);});};return B(A2(_5U,_pS,_pY));}),_q0=function(_q1){return new F(function(){return A3(_pJ,_pV,new T(function(){if(E(_q1)==2){return E(_pU);}else{return E(_pW);}}),_pX);});};return new F(function(){return A3(_pL,_pV,new T(function(){return B(_pe(_pS,_pT));}),_q0);});},_q2=function(_q3,_q4){if(_q3<=0){if(_q3>=0){return new F(function(){return quot(_q3,_q4);});}else{if(_q4<=0){return new F(function(){return quot(_q3,_q4);});}else{return quot(_q3+1|0,_q4)-1|0;}}}else{if(_q4>=0){if(_q3>=0){return new F(function(){return quot(_q3,_q4);});}else{if(_q4<=0){return new F(function(){return quot(_q3,_q4);});}else{return quot(_q3+1|0,_q4)-1|0;}}}else{return quot(_q3-1|0,_q4)-1|0;}}},_q5=new T(function(){return B(unCStr("base"));}),_q6=new T(function(){return B(unCStr("GHC.Exception"));}),_q7=new T(function(){return B(unCStr("ArithException"));}),_q8=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_q5,_q6,_q7),_q9=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_q8,_v,_v),_qa=function(_qb){return E(_q9);},_qc=function(_qd){var _qe=E(_qd);return new F(function(){return _X(B(_V(_qe.a)),_qa,_qe.b);});},_qf=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_qg=new T(function(){return B(unCStr("denormal"));}),_qh=new T(function(){return B(unCStr("divide by zero"));}),_qi=new T(function(){return B(unCStr("loss of precision"));}),_qj=new T(function(){return B(unCStr("arithmetic underflow"));}),_qk=new T(function(){return B(unCStr("arithmetic overflow"));}),_ql=function(_qm,_qn){switch(E(_qm)){case 0:return new F(function(){return _3(_qk,_qn);});break;case 1:return new F(function(){return _3(_qj,_qn);});break;case 2:return new F(function(){return _3(_qi,_qn);});break;case 3:return new F(function(){return _3(_qh,_qn);});break;case 4:return new F(function(){return _3(_qg,_qn);});break;default:return new F(function(){return _3(_qf,_qn);});}},_qo=function(_qp){return new F(function(){return _ql(_qp,_v);});},_qq=function(_qr,_qs,_qt){return new F(function(){return _ql(_qs,_qt);});},_qu=function(_qv,_qw){return new F(function(){return _28(_ql,_qv,_qw);});},_qx=new T3(0,_qq,_qo,_qu),_qy=new T(function(){return new T5(0,_qa,_qx,_qz,_qc,_qo);}),_qz=function(_b8){return new T2(0,_qy,_b8);},_qA=3,_qB=new T(function(){return B(_qz(_qA));}),_qC=new T(function(){return die(_qB);}),_qD=0,_qE=new T(function(){return B(_qz(_qD));}),_qF=new T(function(){return die(_qE);}),_qG=function(_qH,_qI){var _qJ=E(_qI);switch(_qJ){case  -1:var _qK=E(_qH);if(_qK==( -2147483648)){return E(_qF);}else{return new F(function(){return _q2(_qK, -1);});}break;case 0:return E(_qC);default:return new F(function(){return _q2(_qH,_qJ);});}},_qL=new T1(0,0),_qM=function(_qN,_qO){while(1){var _qP=E(_qN);if(!_qP._){var _qQ=_qP.a,_qR=E(_qO);if(!_qR._){return new T1(0,(_qQ>>>0|_qR.a>>>0)>>>0&4294967295);}else{_qN=new T1(1,I_fromInt(_qQ));_qO=_qR;continue;}}else{var _qS=E(_qO);if(!_qS._){_qN=_qP;_qO=new T1(1,I_fromInt(_qS.a));continue;}else{return new T1(1,I_or(_qP.a,_qS.a));}}}},_qT=function(_qU,_qV){while(1){var _qW=E(_qU);if(!_qW._){_qU=new T1(1,I_fromInt(_qW.a));continue;}else{return new T1(1,I_shiftLeft(_qW.a,_qV));}}},_qX=function(_qY){var _qZ=E(_qY);if(!_qZ._){return E(_qL);}else{return new F(function(){return _qM(new T1(0,E(_qZ.a)),B(_qT(B(_qX(_qZ.b)),31)));});}},_r0=new T1(0,1),_r1=new T1(0,2147483647),_r2=function(_r3,_r4){while(1){var _r5=E(_r3);if(!_r5._){var _r6=_r5.a,_r7=E(_r4);if(!_r7._){var _r8=_r7.a,_r9=addC(_r6,_r8);if(!E(_r9.b)){return new T1(0,_r9.a);}else{_r3=new T1(1,I_fromInt(_r6));_r4=new T1(1,I_fromInt(_r8));continue;}}else{_r3=new T1(1,I_fromInt(_r6));_r4=_r7;continue;}}else{var _ra=E(_r4);if(!_ra._){_r3=_r5;_r4=new T1(1,I_fromInt(_ra.a));continue;}else{return new T1(1,I_add(_r5.a,_ra.a));}}}},_rb=new T(function(){return B(_r2(_r1,_r0));}),_rc=function(_rd){var _re=E(_rd);if(!_re._){var _rf=E(_re.a);return (_rf==( -2147483648))?E(_rb):new T1(0, -_rf);}else{return new T1(1,I_negate(_re.a));}},_rg=function(_rh,_ri){if(!E(_rh)){return new F(function(){return _rc(B(_qX(_ri)));});}else{return new F(function(){return _qX(_ri);});}},_rj=1420103680,_rk=465,_rl=new T2(1,_rk,_v),_rm=new T2(1,_rj,_rl),_rn=new T(function(){return B(_rg(_5Q,_rm));}),_ro=function(_rp){return E(_rn);},_rq=0,_rr=function(_rs,_rt){var _ru=_rs%_rt;if(_rs<=0){if(_rs>=0){return E(_ru);}else{if(_rt<=0){return E(_ru);}else{var _rv=E(_ru);return (_rv==0)?0:_rv+_rt|0;}}}else{if(_rt>=0){if(_rs>=0){return E(_ru);}else{if(_rt<=0){return E(_ru);}else{var _rw=E(_ru);return (_rw==0)?0:_rw+_rt|0;}}}else{var _rx=E(_ru);return (_rx==0)?0:_rx+_rt|0;}}},_ry=function(_rz,_rA){var _rB=E(_rA);switch(_rB){case  -1:return E(_rq);case 0:return E(_qC);default:return new F(function(){return _rr(E(_rz),_rB);});}},_rC=new T(function(){return B(unCStr("s"));}),_rD=function(_rE,_rF){while(1){var _rG=E(_rE);if(!_rG._){return E(_rF);}else{_rE=_rG.b;_rF=_rG.a;continue;}}},_rH=function(_rI,_rJ,_rK){return new F(function(){return _rD(_rJ,_rI);});},_rL=new T1(0,1),_rM=new T1(0,1),_rN=function(_rO,_rP){var _rQ=E(_rO);return new T2(0,_rQ,new T(function(){var _rR=B(_rN(B(_r2(_rQ,_rP)),_rP));return new T2(1,_rR.a,_rR.b);}));},_rS=function(_rT){var _rU=B(_rN(_rT,_rM));return new T2(1,_rU.a,_rU.b);},_rV=function(_rW,_rX){while(1){var _rY=E(_rW);if(!_rY._){var _rZ=_rY.a,_s0=E(_rX);if(!_s0._){var _s1=_s0.a,_s2=subC(_rZ,_s1);if(!E(_s2.b)){return new T1(0,_s2.a);}else{_rW=new T1(1,I_fromInt(_rZ));_rX=new T1(1,I_fromInt(_s1));continue;}}else{_rW=new T1(1,I_fromInt(_rZ));_rX=_s0;continue;}}else{var _s3=E(_rX);if(!_s3._){_rW=_rY;_rX=new T1(1,I_fromInt(_s3.a));continue;}else{return new T1(1,I_sub(_rY.a,_s3.a));}}}},_s4=function(_s5,_s6){var _s7=B(_rN(_s5,new T(function(){return B(_rV(_s6,_s5));})));return new T2(1,_s7.a,_s7.b);},_s8=new T1(0,0),_s9=function(_sa,_sb){var _sc=E(_sa);if(!_sc._){var _sd=_sc.a,_se=E(_sb);return (_se._==0)?_sd>=_se.a:I_compareInt(_se.a,_sd)<=0;}else{var _sf=_sc.a,_sg=E(_sb);return (_sg._==0)?I_compareInt(_sf,_sg.a)>=0:I_compare(_sf,_sg.a)>=0;}},_sh=function(_si,_sj){var _sk=E(_si);if(!_sk._){var _sl=_sk.a,_sm=E(_sj);return (_sm._==0)?_sl>_sm.a:I_compareInt(_sm.a,_sl)<0;}else{var _sn=_sk.a,_so=E(_sj);return (_so._==0)?I_compareInt(_sn,_so.a)>0:I_compare(_sn,_so.a)>0;}},_sp=function(_sq,_sr){var _ss=E(_sq);if(!_ss._){var _st=_ss.a,_su=E(_sr);return (_su._==0)?_st<_su.a:I_compareInt(_su.a,_st)>0;}else{var _sv=_ss.a,_sw=E(_sr);return (_sw._==0)?I_compareInt(_sv,_sw.a)<0:I_compare(_sv,_sw.a)<0;}},_sx=function(_sy,_sz,_sA){if(!B(_s9(_sz,_s8))){var _sB=function(_sC){return (!B(_sp(_sC,_sA)))?new T2(1,_sC,new T(function(){return B(_sB(B(_r2(_sC,_sz))));})):__Z;};return new F(function(){return _sB(_sy);});}else{var _sD=function(_sE){return (!B(_sh(_sE,_sA)))?new T2(1,_sE,new T(function(){return B(_sD(B(_r2(_sE,_sz))));})):__Z;};return new F(function(){return _sD(_sy);});}},_sF=function(_sG,_sH,_sI){return new F(function(){return _sx(_sG,B(_rV(_sH,_sG)),_sI);});},_sJ=function(_sK,_sL){return new F(function(){return _sx(_sK,_rM,_sL);});},_sM=function(_sN){var _sO=E(_sN);if(!_sO._){return E(_sO.a);}else{return new F(function(){return I_toInt(_sO.a);});}},_sP=function(_sQ){return new F(function(){return _sM(_sQ);});},_sR=function(_sS){return new F(function(){return _rV(_sS,_rM);});},_sT=function(_sU){return new F(function(){return _r2(_sU,_rM);});},_sV=function(_sW){return new T1(0,_sW);},_sX=function(_sY){return new F(function(){return _sV(E(_sY));});},_sZ={_:0,a:_sT,b:_sR,c:_sX,d:_sP,e:_rS,f:_s4,g:_sJ,h:_sF},_t0=function(_t1,_t2){while(1){var _t3=E(_t1);if(!_t3._){var _t4=E(_t3.a);if(_t4==( -2147483648)){_t1=new T1(1,I_fromInt( -2147483648));continue;}else{var _t5=E(_t2);if(!_t5._){return new T1(0,B(_q2(_t4,_t5.a)));}else{_t1=new T1(1,I_fromInt(_t4));_t2=_t5;continue;}}}else{var _t6=_t3.a,_t7=E(_t2);return (_t7._==0)?new T1(1,I_div(_t6,I_fromInt(_t7.a))):new T1(1,I_div(_t6,_t7.a));}}},_t8=function(_t9,_ta){var _tb=E(_t9);if(!_tb._){var _tc=_tb.a,_td=E(_ta);return (_td._==0)?_tc==_td.a:(I_compareInt(_td.a,_tc)==0)?true:false;}else{var _te=_tb.a,_tf=E(_ta);return (_tf._==0)?(I_compareInt(_te,_tf.a)==0)?true:false:(I_compare(_te,_tf.a)==0)?true:false;}},_tg=new T1(0,0),_th=function(_ti,_tj){if(!B(_t8(_tj,_tg))){return new F(function(){return _t0(_ti,_tj);});}else{return E(_qC);}},_tk=function(_tl,_tm){while(1){var _tn=E(_tl);if(!_tn._){var _to=E(_tn.a);if(_to==( -2147483648)){_tl=new T1(1,I_fromInt( -2147483648));continue;}else{var _tp=E(_tm);if(!_tp._){var _tq=_tp.a;return new T2(0,new T1(0,B(_q2(_to,_tq))),new T1(0,B(_rr(_to,_tq))));}else{_tl=new T1(1,I_fromInt(_to));_tm=_tp;continue;}}}else{var _tr=E(_tm);if(!_tr._){_tl=_tn;_tm=new T1(1,I_fromInt(_tr.a));continue;}else{var _ts=I_divMod(_tn.a,_tr.a);return new T2(0,new T1(1,_ts.a),new T1(1,_ts.b));}}}},_tt=function(_tu,_tv){if(!B(_t8(_tv,_tg))){var _tw=B(_tk(_tu,_tv));return new T2(0,_tw.a,_tw.b);}else{return E(_qC);}},_tx=function(_ty,_tz){while(1){var _tA=E(_ty);if(!_tA._){var _tB=E(_tA.a);if(_tB==( -2147483648)){_ty=new T1(1,I_fromInt( -2147483648));continue;}else{var _tC=E(_tz);if(!_tC._){return new T1(0,B(_rr(_tB,_tC.a)));}else{_ty=new T1(1,I_fromInt(_tB));_tz=_tC;continue;}}}else{var _tD=_tA.a,_tE=E(_tz);return (_tE._==0)?new T1(1,I_mod(_tD,I_fromInt(_tE.a))):new T1(1,I_mod(_tD,_tE.a));}}},_tF=function(_tG,_tH){if(!B(_t8(_tH,_tg))){return new F(function(){return _tx(_tG,_tH);});}else{return E(_qC);}},_tI=function(_tJ,_tK){while(1){var _tL=E(_tJ);if(!_tL._){var _tM=E(_tL.a);if(_tM==( -2147483648)){_tJ=new T1(1,I_fromInt( -2147483648));continue;}else{var _tN=E(_tK);if(!_tN._){return new T1(0,quot(_tM,_tN.a));}else{_tJ=new T1(1,I_fromInt(_tM));_tK=_tN;continue;}}}else{var _tO=_tL.a,_tP=E(_tK);return (_tP._==0)?new T1(0,I_toInt(I_quot(_tO,I_fromInt(_tP.a)))):new T1(1,I_quot(_tO,_tP.a));}}},_tQ=function(_tR,_tS){if(!B(_t8(_tS,_tg))){return new F(function(){return _tI(_tR,_tS);});}else{return E(_qC);}},_tT=function(_tU,_tV){while(1){var _tW=E(_tU);if(!_tW._){var _tX=E(_tW.a);if(_tX==( -2147483648)){_tU=new T1(1,I_fromInt( -2147483648));continue;}else{var _tY=E(_tV);if(!_tY._){var _tZ=_tY.a;return new T2(0,new T1(0,quot(_tX,_tZ)),new T1(0,_tX%_tZ));}else{_tU=new T1(1,I_fromInt(_tX));_tV=_tY;continue;}}}else{var _u0=E(_tV);if(!_u0._){_tU=_tW;_tV=new T1(1,I_fromInt(_u0.a));continue;}else{var _u1=I_quotRem(_tW.a,_u0.a);return new T2(0,new T1(1,_u1.a),new T1(1,_u1.b));}}}},_u2=function(_u3,_u4){if(!B(_t8(_u4,_tg))){var _u5=B(_tT(_u3,_u4));return new T2(0,_u5.a,_u5.b);}else{return E(_qC);}},_u6=function(_u7,_u8){while(1){var _u9=E(_u7);if(!_u9._){var _ua=E(_u9.a);if(_ua==( -2147483648)){_u7=new T1(1,I_fromInt( -2147483648));continue;}else{var _ub=E(_u8);if(!_ub._){return new T1(0,_ua%_ub.a);}else{_u7=new T1(1,I_fromInt(_ua));_u8=_ub;continue;}}}else{var _uc=_u9.a,_ud=E(_u8);return (_ud._==0)?new T1(1,I_rem(_uc,I_fromInt(_ud.a))):new T1(1,I_rem(_uc,_ud.a));}}},_ue=function(_uf,_ug){if(!B(_t8(_ug,_tg))){return new F(function(){return _u6(_uf,_ug);});}else{return E(_qC);}},_uh=function(_ui){return E(_ui);},_uj=function(_uk){return E(_uk);},_ul=function(_um){var _un=E(_um);if(!_un._){var _uo=E(_un.a);return (_uo==( -2147483648))?E(_rb):(_uo<0)?new T1(0, -_uo):E(_un);}else{var _up=_un.a;return (I_compareInt(_up,0)>=0)?E(_un):new T1(1,I_negate(_up));}},_uq=new T1(0, -1),_ur=function(_us){var _ut=E(_us);if(!_ut._){var _uu=_ut.a;return (_uu>=0)?(E(_uu)==0)?E(_qL):E(_r0):E(_uq);}else{var _uv=I_compareInt(_ut.a,0);return (_uv<=0)?(E(_uv)==0)?E(_qL):E(_uq):E(_r0);}},_uw=function(_ux,_uy){while(1){var _uz=E(_ux);if(!_uz._){var _uA=_uz.a,_uB=E(_uy);if(!_uB._){var _uC=_uB.a;if(!(imul(_uA,_uC)|0)){return new T1(0,imul(_uA,_uC)|0);}else{_ux=new T1(1,I_fromInt(_uA));_uy=new T1(1,I_fromInt(_uC));continue;}}else{_ux=new T1(1,I_fromInt(_uA));_uy=_uB;continue;}}else{var _uD=E(_uy);if(!_uD._){_ux=_uz;_uy=new T1(1,I_fromInt(_uD.a));continue;}else{return new T1(1,I_mul(_uz.a,_uD.a));}}}},_uE={_:0,a:_r2,b:_rV,c:_uw,d:_rc,e:_ul,f:_ur,g:_uj},_uF=function(_uG,_uH){var _uI=E(_uG);if(!_uI._){var _uJ=_uI.a,_uK=E(_uH);return (_uK._==0)?_uJ!=_uK.a:(I_compareInt(_uK.a,_uJ)==0)?false:true;}else{var _uL=_uI.a,_uM=E(_uH);return (_uM._==0)?(I_compareInt(_uL,_uM.a)==0)?false:true:(I_compare(_uL,_uM.a)==0)?false:true;}},_uN=new T2(0,_t8,_uF),_uO=function(_uP,_uQ){var _uR=E(_uP);if(!_uR._){var _uS=_uR.a,_uT=E(_uQ);return (_uT._==0)?_uS<=_uT.a:I_compareInt(_uT.a,_uS)>=0;}else{var _uU=_uR.a,_uV=E(_uQ);return (_uV._==0)?I_compareInt(_uU,_uV.a)<=0:I_compare(_uU,_uV.a)<=0;}},_uW=function(_uX,_uY){return (!B(_uO(_uX,_uY)))?E(_uX):E(_uY);},_uZ=function(_v0,_v1){return (!B(_uO(_v0,_v1)))?E(_v1):E(_v0);},_v2=function(_v3,_v4){var _v5=E(_v3);if(!_v5._){var _v6=_v5.a,_v7=E(_v4);if(!_v7._){var _v8=_v7.a;return (_v6!=_v8)?(_v6>_v8)?2:0:1;}else{var _v9=I_compareInt(_v7.a,_v6);return (_v9<=0)?(_v9>=0)?1:2:0;}}else{var _va=_v5.a,_vb=E(_v4);if(!_vb._){var _vc=I_compareInt(_va,_vb.a);return (_vc>=0)?(_vc<=0)?1:2:0;}else{var _vd=I_compare(_va,_vb.a);return (_vd>=0)?(_vd<=0)?1:2:0;}}},_ve={_:0,a:_uN,b:_v2,c:_sp,d:_uO,e:_sh,f:_s9,g:_uW,h:_uZ},_vf=function(_vg){return new T2(0,E(_vg),E(_rL));},_vh=new T3(0,_uE,_ve,_vf),_vi={_:0,a:_vh,b:_sZ,c:_tQ,d:_ue,e:_th,f:_tF,g:_u2,h:_tt,i:_uh},_vj=new T1(0,0),_vk=function(_vl,_vm,_vn){var _vo=B(A1(_vl,_vm));if(!B(_t8(_vo,_vj))){return new F(function(){return _t0(B(_uw(_vm,_vn)),_vo);});}else{return E(_qC);}},_vp=function(_vq,_vr){while(1){if(!B(_t8(_vr,_tg))){var _vs=_vr,_vt=B(_ue(_vq,_vr));_vq=_vs;_vr=_vt;continue;}else{return E(_vq);}}},_vu=5,_vv=new T(function(){return B(_qz(_vu));}),_vw=new T(function(){return die(_vv);}),_vx=function(_vy,_vz){if(!B(_t8(_vz,_tg))){var _vA=B(_vp(B(_ul(_vy)),B(_ul(_vz))));return (!B(_t8(_vA,_tg)))?new T2(0,B(_tI(_vy,_vA)),B(_tI(_vz,_vA))):E(_qC);}else{return E(_vw);}},_vB=function(_vC,_vD,_vE,_vF){var _vG=B(_uw(_vD,_vE));return new F(function(){return _vx(B(_uw(B(_uw(_vC,_vF)),B(_ur(_vG)))),B(_ul(_vG)));});},_vH=function(_vI){return E(E(_vI).a);},_vJ=function(_vK){return E(E(_vK).a);},_vL=function(_vM){return E(E(_vM).g);},_vN=function(_vO,_vP,_vQ){var _vR=new T(function(){if(!B(_t8(_vQ,_tg))){var _vS=B(_tT(_vP,_vQ));return new T2(0,_vS.a,_vS.b);}else{return E(_qC);}}),_vT=new T(function(){return B(A2(_vL,B(_vJ(B(_vH(_vO)))),new T(function(){return E(E(_vR).a);})));});return new T2(0,_vT,new T(function(){return new T2(0,E(E(_vR).b),E(_vQ));}));},_vU=function(_vV){return E(E(_vV).b);},_vW=function(_vX,_vY,_vZ){var _w0=B(_vN(_vX,_vY,_vZ)),_w1=_w0.a,_w2=E(_w0.b);if(!B(_sp(B(_uw(_w2.a,_rL)),B(_uw(_tg,_w2.b))))){return E(_w1);}else{var _w3=B(_vJ(B(_vH(_vX))));return new F(function(){return A3(_vU,_w3,_w1,new T(function(){return B(A2(_vL,_w3,_rL));}));});}},_w4=479723520,_w5=40233135,_w6=new T2(1,_w5,_v),_w7=new T2(1,_w4,_w6),_w8=new T(function(){return B(_rg(_5Q,_w7));}),_w9=new T1(0,40587),_wa=function(_wb){var _wc=new T(function(){var _wd=B(_vB(_wb,_rL,_rn,_rL)),_we=B(_vB(_w8,_rL,_rn,_rL)),_wf=B(_vB(_wd.a,_wd.b,_we.a,_we.b));return B(_vW(_vi,_wf.a,_wf.b));});return new T2(0,new T(function(){return B(_r2(_w9,_wc));}),new T(function(){return B(_rV(_wb,B(_vk(_ro,B(_uw(_wc,_rn)),_w8))));}));},_wg=function(_wh,_wi){var _wj=E(_wi);if(!_wj._){return __Z;}else{var _wk=_wj.a,_wl=E(_wh);return (_wl==1)?new T2(1,_wk,_v):new T2(1,_wk,new T(function(){return B(_wg(_wl-1|0,_wj.b));}));}},_wm=function(_wn,_){var _wo=__get(_wn,0),_wp=__get(_wn,1),_wq=Number(_wo),_wr=jsTrunc(_wq),_ws=Number(_wp),_wt=jsTrunc(_ws);return new T2(0,_wr,_wt);},_wu=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_wv=660865024,_ww=465661287,_wx=new T2(1,_ww,_v),_wy=new T2(1,_wv,_wx),_wz=new T(function(){return B(_rg(_5Q,_wy));}),_wA=function(_){var _wB=__app0(E(_wu)),_wC=B(_wm(_wB,_));return new T(function(){var _wD=E(_wC);if(!B(_t8(_wz,_vj))){return B(_r2(B(_uw(B(_sV(E(_wD.a))),_rn)),B(_t0(B(_uw(B(_uw(B(_sV(E(_wD.b))),_rn)),_rn)),_wz))));}else{return E(_qC);}});},_wE=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_wF=new T(function(){return B(err(_wE));}),_wG=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_wH=new T(function(){return B(err(_wG));}),_wI=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_wJ=function(_wK){return new F(function(){return _b6(new T1(0,new T(function(){return B(_bk(_wK,_wI));})),_aQ);});},_wL=new T(function(){return B(_wJ("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_wM=function(_wN,_wO){while(1){var _wP=B((function(_wQ,_wR){var _wS=E(_wQ);switch(_wS._){case 0:var _wT=E(_wR);if(!_wT._){return __Z;}else{_wN=B(A1(_wS.a,_wT.a));_wO=_wT.b;return __continue;}break;case 1:var _wU=B(A1(_wS.a,_wR)),_wV=_wR;_wN=_wU;_wO=_wV;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_wS.a,_wR),new T(function(){return B(_wM(_wS.b,_wR));}));default:return E(_wS.a);}})(_wN,_wO));if(_wP!=__continue){return _wP;}}},_wW=function(_wX,_wY){var _wZ=function(_x0){var _x1=E(_wY);if(_x1._==3){return new T2(3,_x1.a,new T(function(){return B(_wW(_wX,_x1.b));}));}else{var _x2=E(_wX);if(_x2._==2){return E(_x1);}else{var _x3=E(_x1);if(_x3._==2){return E(_x2);}else{var _x4=function(_x5){var _x6=E(_x3);if(_x6._==4){var _x7=function(_x8){return new T1(4,new T(function(){return B(_3(B(_wM(_x2,_x8)),_x6.a));}));};return new T1(1,_x7);}else{var _x9=E(_x2);if(_x9._==1){var _xa=_x9.a,_xb=E(_x6);if(!_xb._){return new T1(1,function(_xc){return new F(function(){return _wW(B(A1(_xa,_xc)),_xb);});});}else{var _xd=function(_xe){return new F(function(){return _wW(B(A1(_xa,_xe)),new T(function(){return B(A1(_xb.a,_xe));}));});};return new T1(1,_xd);}}else{var _xf=E(_x6);if(!_xf._){return E(_wL);}else{var _xg=function(_xh){return new F(function(){return _wW(_x9,new T(function(){return B(A1(_xf.a,_xh));}));});};return new T1(1,_xg);}}}},_xi=E(_x2);switch(_xi._){case 1:var _xj=E(_x3);if(_xj._==4){var _xk=function(_xl){return new T1(4,new T(function(){return B(_3(B(_wM(B(A1(_xi.a,_xl)),_xl)),_xj.a));}));};return new T1(1,_xk);}else{return new F(function(){return _x4(_);});}break;case 4:var _xm=_xi.a,_xn=E(_x3);switch(_xn._){case 0:var _xo=function(_xp){var _xq=new T(function(){return B(_3(_xm,new T(function(){return B(_wM(_xn,_xp));},1)));});return new T1(4,_xq);};return new T1(1,_xo);case 1:var _xr=function(_xs){var _xt=new T(function(){return B(_3(_xm,new T(function(){return B(_wM(B(A1(_xn.a,_xs)),_xs));},1)));});return new T1(4,_xt);};return new T1(1,_xr);default:return new T1(4,new T(function(){return B(_3(_xm,_xn.a));}));}break;default:return new F(function(){return _x4(_);});}}}}},_xu=E(_wX);switch(_xu._){case 0:var _xv=E(_wY);if(!_xv._){var _xw=function(_xx){return new F(function(){return _wW(B(A1(_xu.a,_xx)),new T(function(){return B(A1(_xv.a,_xx));}));});};return new T1(0,_xw);}else{return new F(function(){return _wZ(_);});}break;case 3:return new T2(3,_xu.a,new T(function(){return B(_wW(_xu.b,_wY));}));default:return new F(function(){return _wZ(_);});}},_xy=new T(function(){return B(unCStr("("));}),_xz=new T(function(){return B(unCStr(")"));}),_xA=function(_xB,_xC){return (!B(_7k(_xB,_xC)))?true:false;},_xD=new T2(0,_7k,_xA),_xE=function(_xF,_xG){var _xH=E(_xF);switch(_xH._){case 0:return new T1(0,function(_xI){return new F(function(){return _xE(B(A1(_xH.a,_xI)),_xG);});});case 1:return new T1(1,function(_xJ){return new F(function(){return _xE(B(A1(_xH.a,_xJ)),_xG);});});case 2:return new T0(2);case 3:return new F(function(){return _wW(B(A1(_xG,_xH.a)),new T(function(){return B(_xE(_xH.b,_xG));}));});break;default:var _xK=function(_xL){var _xM=E(_xL);if(!_xM._){return __Z;}else{var _xN=E(_xM.a);return new F(function(){return _3(B(_wM(B(A1(_xG,_xN.a)),_xN.b)),new T(function(){return B(_xK(_xM.b));},1));});}},_xO=B(_xK(_xH.a));return (_xO._==0)?new T0(2):new T1(4,_xO);}},_xP=new T0(2),_xQ=function(_xR){return new T2(3,_xR,_xP);},_xS=function(_xT,_xU){var _xV=E(_xT);if(!_xV){return new F(function(){return A1(_xU,_5L);});}else{var _xW=new T(function(){return B(_xS(_xV-1|0,_xU));});return new T1(0,function(_xX){return E(_xW);});}},_xY=function(_xZ,_y0,_y1){var _y2=new T(function(){return B(A1(_xZ,_xQ));}),_y3=function(_y4,_y5,_y6,_y7){while(1){var _y8=B((function(_y9,_ya,_yb,_yc){var _yd=E(_y9);switch(_yd._){case 0:var _ye=E(_ya);if(!_ye._){return new F(function(){return A1(_y0,_yc);});}else{var _yf=_yb+1|0,_yg=_yc;_y4=B(A1(_yd.a,_ye.a));_y5=_ye.b;_y6=_yf;_y7=_yg;return __continue;}break;case 1:var _yh=B(A1(_yd.a,_ya)),_yi=_ya,_yf=_yb,_yg=_yc;_y4=_yh;_y5=_yi;_y6=_yf;_y7=_yg;return __continue;case 2:return new F(function(){return A1(_y0,_yc);});break;case 3:var _yj=new T(function(){return B(_xE(_yd,_yc));});return new F(function(){return _xS(_yb,function(_yk){return E(_yj);});});break;default:return new F(function(){return _xE(_yd,_yc);});}})(_y4,_y5,_y6,_y7));if(_y8!=__continue){return _y8;}}};return function(_yl){return new F(function(){return _y3(_y2,_yl,0,_y1);});};},_ym=function(_yn){return new F(function(){return A1(_yn,_v);});},_yo=function(_yp,_yq){var _yr=function(_ys){var _yt=E(_ys);if(!_yt._){return E(_ym);}else{var _yu=_yt.a;if(!B(A1(_yp,_yu))){return E(_ym);}else{var _yv=new T(function(){return B(_yr(_yt.b));}),_yw=function(_yx){var _yy=new T(function(){return B(A1(_yv,function(_yz){return new F(function(){return A1(_yx,new T2(1,_yu,_yz));});}));});return new T1(0,function(_yA){return E(_yy);});};return E(_yw);}}};return function(_yB){return new F(function(){return A2(_yr,_yB,_yq);});};},_yC=new T0(6),_yD=new T(function(){return B(unCStr("valDig: Bad base"));}),_yE=new T(function(){return B(err(_yD));}),_yF=function(_yG,_yH){var _yI=function(_yJ,_yK){var _yL=E(_yJ);if(!_yL._){var _yM=new T(function(){return B(A1(_yK,_v));});return function(_yN){return new F(function(){return A1(_yN,_yM);});};}else{var _yO=E(_yL.a),_yP=function(_yQ){var _yR=new T(function(){return B(_yI(_yL.b,function(_yS){return new F(function(){return A1(_yK,new T2(1,_yQ,_yS));});}));}),_yT=function(_yU){var _yV=new T(function(){return B(A1(_yR,_yU));});return new T1(0,function(_yW){return E(_yV);});};return E(_yT);};switch(E(_yG)){case 8:if(48>_yO){var _yX=new T(function(){return B(A1(_yK,_v));});return function(_yY){return new F(function(){return A1(_yY,_yX);});};}else{if(_yO>55){var _yZ=new T(function(){return B(A1(_yK,_v));});return function(_z0){return new F(function(){return A1(_z0,_yZ);});};}else{return new F(function(){return _yP(_yO-48|0);});}}break;case 10:if(48>_yO){var _z1=new T(function(){return B(A1(_yK,_v));});return function(_z2){return new F(function(){return A1(_z2,_z1);});};}else{if(_yO>57){var _z3=new T(function(){return B(A1(_yK,_v));});return function(_z4){return new F(function(){return A1(_z4,_z3);});};}else{return new F(function(){return _yP(_yO-48|0);});}}break;case 16:if(48>_yO){if(97>_yO){if(65>_yO){var _z5=new T(function(){return B(A1(_yK,_v));});return function(_z6){return new F(function(){return A1(_z6,_z5);});};}else{if(_yO>70){var _z7=new T(function(){return B(A1(_yK,_v));});return function(_z8){return new F(function(){return A1(_z8,_z7);});};}else{return new F(function(){return _yP((_yO-65|0)+10|0);});}}}else{if(_yO>102){if(65>_yO){var _z9=new T(function(){return B(A1(_yK,_v));});return function(_za){return new F(function(){return A1(_za,_z9);});};}else{if(_yO>70){var _zb=new T(function(){return B(A1(_yK,_v));});return function(_zc){return new F(function(){return A1(_zc,_zb);});};}else{return new F(function(){return _yP((_yO-65|0)+10|0);});}}}else{return new F(function(){return _yP((_yO-97|0)+10|0);});}}}else{if(_yO>57){if(97>_yO){if(65>_yO){var _zd=new T(function(){return B(A1(_yK,_v));});return function(_ze){return new F(function(){return A1(_ze,_zd);});};}else{if(_yO>70){var _zf=new T(function(){return B(A1(_yK,_v));});return function(_zg){return new F(function(){return A1(_zg,_zf);});};}else{return new F(function(){return _yP((_yO-65|0)+10|0);});}}}else{if(_yO>102){if(65>_yO){var _zh=new T(function(){return B(A1(_yK,_v));});return function(_zi){return new F(function(){return A1(_zi,_zh);});};}else{if(_yO>70){var _zj=new T(function(){return B(A1(_yK,_v));});return function(_zk){return new F(function(){return A1(_zk,_zj);});};}else{return new F(function(){return _yP((_yO-65|0)+10|0);});}}}else{return new F(function(){return _yP((_yO-97|0)+10|0);});}}}else{return new F(function(){return _yP(_yO-48|0);});}}break;default:return E(_yE);}}},_zl=function(_zm){var _zn=E(_zm);if(!_zn._){return new T0(2);}else{return new F(function(){return A1(_yH,_zn);});}};return function(_zo){return new F(function(){return A3(_yI,_zo,_5x,_zl);});};},_zp=16,_zq=8,_zr=function(_zs){var _zt=function(_zu){return new F(function(){return A1(_zs,new T1(5,new T2(0,_zq,_zu)));});},_zv=function(_zw){return new F(function(){return A1(_zs,new T1(5,new T2(0,_zp,_zw)));});},_zx=function(_zy){switch(E(_zy)){case 79:return new T1(1,B(_yF(_zq,_zt)));case 88:return new T1(1,B(_yF(_zp,_zv)));case 111:return new T1(1,B(_yF(_zq,_zt)));case 120:return new T1(1,B(_yF(_zp,_zv)));default:return new T0(2);}};return function(_zz){return (E(_zz)==48)?E(new T1(0,_zx)):new T0(2);};},_zA=function(_zB){return new T1(0,B(_zr(_zB)));},_zC=function(_zD){return new F(function(){return A1(_zD,_2q);});},_zE=function(_zF){return new F(function(){return A1(_zF,_2q);});},_zG=10,_zH=new T1(0,10),_zI=function(_zJ){return new F(function(){return _sV(E(_zJ));});},_zK=new T(function(){return B(unCStr("this should not happen"));}),_zL=new T(function(){return B(err(_zK));}),_zM=function(_zN,_zO){var _zP=E(_zO);if(!_zP._){return __Z;}else{var _zQ=E(_zP.b);return (_zQ._==0)?E(_zL):new T2(1,B(_r2(B(_uw(_zP.a,_zN)),_zQ.a)),new T(function(){return B(_zM(_zN,_zQ.b));}));}},_zR=new T1(0,0),_zS=function(_zT,_zU,_zV){while(1){var _zW=B((function(_zX,_zY,_zZ){var _A0=E(_zZ);if(!_A0._){return E(_zR);}else{if(!E(_A0.b)._){return E(_A0.a);}else{var _A1=E(_zY);if(_A1<=40){var _A2=function(_A3,_A4){while(1){var _A5=E(_A4);if(!_A5._){return E(_A3);}else{var _A6=B(_r2(B(_uw(_A3,_zX)),_A5.a));_A3=_A6;_A4=_A5.b;continue;}}};return new F(function(){return _A2(_zR,_A0);});}else{var _A7=B(_uw(_zX,_zX));if(!(_A1%2)){var _A8=B(_zM(_zX,_A0));_zT=_A7;_zU=quot(_A1+1|0,2);_zV=_A8;return __continue;}else{var _A8=B(_zM(_zX,new T2(1,_zR,_A0)));_zT=_A7;_zU=quot(_A1+1|0,2);_zV=_A8;return __continue;}}}}})(_zT,_zU,_zV));if(_zW!=__continue){return _zW;}}},_A9=function(_Aa,_Ab){return new F(function(){return _zS(_Aa,new T(function(){return B(_9C(_Ab,0));},1),B(_d5(_zI,_Ab)));});},_Ac=function(_Ad){var _Ae=new T(function(){var _Af=new T(function(){var _Ag=function(_Ah){return new F(function(){return A1(_Ad,new T1(1,new T(function(){return B(_A9(_zH,_Ah));})));});};return new T1(1,B(_yF(_zG,_Ag)));}),_Ai=function(_Aj){if(E(_Aj)==43){var _Ak=function(_Al){return new F(function(){return A1(_Ad,new T1(1,new T(function(){return B(_A9(_zH,_Al));})));});};return new T1(1,B(_yF(_zG,_Ak)));}else{return new T0(2);}},_Am=function(_An){if(E(_An)==45){var _Ao=function(_Ap){return new F(function(){return A1(_Ad,new T1(1,new T(function(){return B(_rc(B(_A9(_zH,_Ap))));})));});};return new T1(1,B(_yF(_zG,_Ao)));}else{return new T0(2);}};return B(_wW(B(_wW(new T1(0,_Am),new T1(0,_Ai))),_Af));});return new F(function(){return _wW(new T1(0,function(_Aq){return (E(_Aq)==101)?E(_Ae):new T0(2);}),new T1(0,function(_Ar){return (E(_Ar)==69)?E(_Ae):new T0(2);}));});},_As=function(_At){var _Au=function(_Av){return new F(function(){return A1(_At,new T1(1,_Av));});};return function(_Aw){return (E(_Aw)==46)?new T1(1,B(_yF(_zG,_Au))):new T0(2);};},_Ax=function(_Ay){return new T1(0,B(_As(_Ay)));},_Az=function(_AA){var _AB=function(_AC){var _AD=function(_AE){return new T1(1,B(_xY(_Ac,_zC,function(_AF){return new F(function(){return A1(_AA,new T1(5,new T3(1,_AC,_AE,_AF)));});})));};return new T1(1,B(_xY(_Ax,_zE,_AD)));};return new F(function(){return _yF(_zG,_AB);});},_AG=function(_AH){return new T1(1,B(_Az(_AH)));},_AI=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_AJ=function(_AK){return new F(function(){return _4d(_dO,_AK,_AI);});},_AL=function(_AM){var _AN=new T(function(){return B(A1(_AM,_zq));}),_AO=new T(function(){return B(A1(_AM,_zp));});return function(_AP){switch(E(_AP)){case 79:return E(_AN);case 88:return E(_AO);case 111:return E(_AN);case 120:return E(_AO);default:return new T0(2);}};},_AQ=function(_AR){return new T1(0,B(_AL(_AR)));},_AS=function(_AT){return new F(function(){return A1(_AT,_zG);});},_AU=function(_AV){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_d(9,_AV,_v));}))));});},_AW=function(_AX){return new T0(2);},_AY=function(_AZ){var _B0=E(_AZ);if(!_B0._){return E(_AW);}else{var _B1=_B0.a,_B2=E(_B0.b);if(!_B2._){return E(_B1);}else{var _B3=new T(function(){return B(_AY(_B2));}),_B4=function(_B5){return new F(function(){return _wW(B(A1(_B1,_B5)),new T(function(){return B(A1(_B3,_B5));}));});};return E(_B4);}}},_B6=function(_B7,_B8){var _B9=function(_Ba,_Bb,_Bc){var _Bd=E(_Ba);if(!_Bd._){return new F(function(){return A1(_Bc,_B7);});}else{var _Be=E(_Bb);if(!_Be._){return new T0(2);}else{if(E(_Bd.a)!=E(_Be.a)){return new T0(2);}else{var _Bf=new T(function(){return B(_B9(_Bd.b,_Be.b,_Bc));});return new T1(0,function(_Bg){return E(_Bf);});}}}};return function(_Bh){return new F(function(){return _B9(_B7,_Bh,_B8);});};},_Bi=new T(function(){return B(unCStr("SO"));}),_Bj=14,_Bk=function(_Bl){var _Bm=new T(function(){return B(A1(_Bl,_Bj));});return new T1(1,B(_B6(_Bi,function(_Bn){return E(_Bm);})));},_Bo=new T(function(){return B(unCStr("SOH"));}),_Bp=1,_Bq=function(_Br){var _Bs=new T(function(){return B(A1(_Br,_Bp));});return new T1(1,B(_B6(_Bo,function(_Bt){return E(_Bs);})));},_Bu=function(_Bv){return new T1(1,B(_xY(_Bq,_Bk,_Bv)));},_Bw=new T(function(){return B(unCStr("NUL"));}),_Bx=0,_By=function(_Bz){var _BA=new T(function(){return B(A1(_Bz,_Bx));});return new T1(1,B(_B6(_Bw,function(_BB){return E(_BA);})));},_BC=new T(function(){return B(unCStr("STX"));}),_BD=2,_BE=function(_BF){var _BG=new T(function(){return B(A1(_BF,_BD));});return new T1(1,B(_B6(_BC,function(_BH){return E(_BG);})));},_BI=new T(function(){return B(unCStr("ETX"));}),_BJ=3,_BK=function(_BL){var _BM=new T(function(){return B(A1(_BL,_BJ));});return new T1(1,B(_B6(_BI,function(_BN){return E(_BM);})));},_BO=new T(function(){return B(unCStr("EOT"));}),_BP=4,_BQ=function(_BR){var _BS=new T(function(){return B(A1(_BR,_BP));});return new T1(1,B(_B6(_BO,function(_BT){return E(_BS);})));},_BU=new T(function(){return B(unCStr("ENQ"));}),_BV=5,_BW=function(_BX){var _BY=new T(function(){return B(A1(_BX,_BV));});return new T1(1,B(_B6(_BU,function(_BZ){return E(_BY);})));},_C0=new T(function(){return B(unCStr("ACK"));}),_C1=6,_C2=function(_C3){var _C4=new T(function(){return B(A1(_C3,_C1));});return new T1(1,B(_B6(_C0,function(_C5){return E(_C4);})));},_C6=new T(function(){return B(unCStr("BEL"));}),_C7=7,_C8=function(_C9){var _Ca=new T(function(){return B(A1(_C9,_C7));});return new T1(1,B(_B6(_C6,function(_Cb){return E(_Ca);})));},_Cc=new T(function(){return B(unCStr("BS"));}),_Cd=8,_Ce=function(_Cf){var _Cg=new T(function(){return B(A1(_Cf,_Cd));});return new T1(1,B(_B6(_Cc,function(_Ch){return E(_Cg);})));},_Ci=new T(function(){return B(unCStr("HT"));}),_Cj=9,_Ck=function(_Cl){var _Cm=new T(function(){return B(A1(_Cl,_Cj));});return new T1(1,B(_B6(_Ci,function(_Cn){return E(_Cm);})));},_Co=new T(function(){return B(unCStr("LF"));}),_Cp=10,_Cq=function(_Cr){var _Cs=new T(function(){return B(A1(_Cr,_Cp));});return new T1(1,B(_B6(_Co,function(_Ct){return E(_Cs);})));},_Cu=new T(function(){return B(unCStr("VT"));}),_Cv=11,_Cw=function(_Cx){var _Cy=new T(function(){return B(A1(_Cx,_Cv));});return new T1(1,B(_B6(_Cu,function(_Cz){return E(_Cy);})));},_CA=new T(function(){return B(unCStr("FF"));}),_CB=12,_CC=function(_CD){var _CE=new T(function(){return B(A1(_CD,_CB));});return new T1(1,B(_B6(_CA,function(_CF){return E(_CE);})));},_CG=new T(function(){return B(unCStr("CR"));}),_CH=13,_CI=function(_CJ){var _CK=new T(function(){return B(A1(_CJ,_CH));});return new T1(1,B(_B6(_CG,function(_CL){return E(_CK);})));},_CM=new T(function(){return B(unCStr("SI"));}),_CN=15,_CO=function(_CP){var _CQ=new T(function(){return B(A1(_CP,_CN));});return new T1(1,B(_B6(_CM,function(_CR){return E(_CQ);})));},_CS=new T(function(){return B(unCStr("DLE"));}),_CT=16,_CU=function(_CV){var _CW=new T(function(){return B(A1(_CV,_CT));});return new T1(1,B(_B6(_CS,function(_CX){return E(_CW);})));},_CY=new T(function(){return B(unCStr("DC1"));}),_CZ=17,_D0=function(_D1){var _D2=new T(function(){return B(A1(_D1,_CZ));});return new T1(1,B(_B6(_CY,function(_D3){return E(_D2);})));},_D4=new T(function(){return B(unCStr("DC2"));}),_D5=18,_D6=function(_D7){var _D8=new T(function(){return B(A1(_D7,_D5));});return new T1(1,B(_B6(_D4,function(_D9){return E(_D8);})));},_Da=new T(function(){return B(unCStr("DC3"));}),_Db=19,_Dc=function(_Dd){var _De=new T(function(){return B(A1(_Dd,_Db));});return new T1(1,B(_B6(_Da,function(_Df){return E(_De);})));},_Dg=new T(function(){return B(unCStr("DC4"));}),_Dh=20,_Di=function(_Dj){var _Dk=new T(function(){return B(A1(_Dj,_Dh));});return new T1(1,B(_B6(_Dg,function(_Dl){return E(_Dk);})));},_Dm=new T(function(){return B(unCStr("NAK"));}),_Dn=21,_Do=function(_Dp){var _Dq=new T(function(){return B(A1(_Dp,_Dn));});return new T1(1,B(_B6(_Dm,function(_Dr){return E(_Dq);})));},_Ds=new T(function(){return B(unCStr("SYN"));}),_Dt=22,_Du=function(_Dv){var _Dw=new T(function(){return B(A1(_Dv,_Dt));});return new T1(1,B(_B6(_Ds,function(_Dx){return E(_Dw);})));},_Dy=new T(function(){return B(unCStr("ETB"));}),_Dz=23,_DA=function(_DB){var _DC=new T(function(){return B(A1(_DB,_Dz));});return new T1(1,B(_B6(_Dy,function(_DD){return E(_DC);})));},_DE=new T(function(){return B(unCStr("CAN"));}),_DF=24,_DG=function(_DH){var _DI=new T(function(){return B(A1(_DH,_DF));});return new T1(1,B(_B6(_DE,function(_DJ){return E(_DI);})));},_DK=new T(function(){return B(unCStr("EM"));}),_DL=25,_DM=function(_DN){var _DO=new T(function(){return B(A1(_DN,_DL));});return new T1(1,B(_B6(_DK,function(_DP){return E(_DO);})));},_DQ=new T(function(){return B(unCStr("SUB"));}),_DR=26,_DS=function(_DT){var _DU=new T(function(){return B(A1(_DT,_DR));});return new T1(1,B(_B6(_DQ,function(_DV){return E(_DU);})));},_DW=new T(function(){return B(unCStr("ESC"));}),_DX=27,_DY=function(_DZ){var _E0=new T(function(){return B(A1(_DZ,_DX));});return new T1(1,B(_B6(_DW,function(_E1){return E(_E0);})));},_E2=new T(function(){return B(unCStr("FS"));}),_E3=28,_E4=function(_E5){var _E6=new T(function(){return B(A1(_E5,_E3));});return new T1(1,B(_B6(_E2,function(_E7){return E(_E6);})));},_E8=new T(function(){return B(unCStr("GS"));}),_E9=29,_Ea=function(_Eb){var _Ec=new T(function(){return B(A1(_Eb,_E9));});return new T1(1,B(_B6(_E8,function(_Ed){return E(_Ec);})));},_Ee=new T(function(){return B(unCStr("RS"));}),_Ef=30,_Eg=function(_Eh){var _Ei=new T(function(){return B(A1(_Eh,_Ef));});return new T1(1,B(_B6(_Ee,function(_Ej){return E(_Ei);})));},_Ek=new T(function(){return B(unCStr("US"));}),_El=31,_Em=function(_En){var _Eo=new T(function(){return B(A1(_En,_El));});return new T1(1,B(_B6(_Ek,function(_Ep){return E(_Eo);})));},_Eq=new T(function(){return B(unCStr("SP"));}),_Er=32,_Es=function(_Et){var _Eu=new T(function(){return B(A1(_Et,_Er));});return new T1(1,B(_B6(_Eq,function(_Ev){return E(_Eu);})));},_Ew=new T(function(){return B(unCStr("DEL"));}),_Ex=127,_Ey=function(_Ez){var _EA=new T(function(){return B(A1(_Ez,_Ex));});return new T1(1,B(_B6(_Ew,function(_EB){return E(_EA);})));},_EC=new T2(1,_Ey,_v),_ED=new T2(1,_Es,_EC),_EE=new T2(1,_Em,_ED),_EF=new T2(1,_Eg,_EE),_EG=new T2(1,_Ea,_EF),_EH=new T2(1,_E4,_EG),_EI=new T2(1,_DY,_EH),_EJ=new T2(1,_DS,_EI),_EK=new T2(1,_DM,_EJ),_EL=new T2(1,_DG,_EK),_EM=new T2(1,_DA,_EL),_EN=new T2(1,_Du,_EM),_EO=new T2(1,_Do,_EN),_EP=new T2(1,_Di,_EO),_EQ=new T2(1,_Dc,_EP),_ER=new T2(1,_D6,_EQ),_ES=new T2(1,_D0,_ER),_ET=new T2(1,_CU,_ES),_EU=new T2(1,_CO,_ET),_EV=new T2(1,_CI,_EU),_EW=new T2(1,_CC,_EV),_EX=new T2(1,_Cw,_EW),_EY=new T2(1,_Cq,_EX),_EZ=new T2(1,_Ck,_EY),_F0=new T2(1,_Ce,_EZ),_F1=new T2(1,_C8,_F0),_F2=new T2(1,_C2,_F1),_F3=new T2(1,_BW,_F2),_F4=new T2(1,_BQ,_F3),_F5=new T2(1,_BK,_F4),_F6=new T2(1,_BE,_F5),_F7=new T2(1,_By,_F6),_F8=new T2(1,_Bu,_F7),_F9=new T(function(){return B(_AY(_F8));}),_Fa=34,_Fb=new T1(0,1114111),_Fc=92,_Fd=39,_Fe=function(_Ff){var _Fg=new T(function(){return B(A1(_Ff,_C7));}),_Fh=new T(function(){return B(A1(_Ff,_Cd));}),_Fi=new T(function(){return B(A1(_Ff,_Cj));}),_Fj=new T(function(){return B(A1(_Ff,_Cp));}),_Fk=new T(function(){return B(A1(_Ff,_Cv));}),_Fl=new T(function(){return B(A1(_Ff,_CB));}),_Fm=new T(function(){return B(A1(_Ff,_CH));}),_Fn=new T(function(){return B(A1(_Ff,_Fc));}),_Fo=new T(function(){return B(A1(_Ff,_Fd));}),_Fp=new T(function(){return B(A1(_Ff,_Fa));}),_Fq=new T(function(){var _Fr=function(_Fs){var _Ft=new T(function(){return B(_sV(E(_Fs)));}),_Fu=function(_Fv){var _Fw=B(_A9(_Ft,_Fv));if(!B(_uO(_Fw,_Fb))){return new T0(2);}else{return new F(function(){return A1(_Ff,new T(function(){var _Fx=B(_sM(_Fw));if(_Fx>>>0>1114111){return B(_AU(_Fx));}else{return _Fx;}}));});}};return new T1(1,B(_yF(_Fs,_Fu)));},_Fy=new T(function(){var _Fz=new T(function(){return B(A1(_Ff,_El));}),_FA=new T(function(){return B(A1(_Ff,_Ef));}),_FB=new T(function(){return B(A1(_Ff,_E9));}),_FC=new T(function(){return B(A1(_Ff,_E3));}),_FD=new T(function(){return B(A1(_Ff,_DX));}),_FE=new T(function(){return B(A1(_Ff,_DR));}),_FF=new T(function(){return B(A1(_Ff,_DL));}),_FG=new T(function(){return B(A1(_Ff,_DF));}),_FH=new T(function(){return B(A1(_Ff,_Dz));}),_FI=new T(function(){return B(A1(_Ff,_Dt));}),_FJ=new T(function(){return B(A1(_Ff,_Dn));}),_FK=new T(function(){return B(A1(_Ff,_Dh));}),_FL=new T(function(){return B(A1(_Ff,_Db));}),_FM=new T(function(){return B(A1(_Ff,_D5));}),_FN=new T(function(){return B(A1(_Ff,_CZ));}),_FO=new T(function(){return B(A1(_Ff,_CT));}),_FP=new T(function(){return B(A1(_Ff,_CN));}),_FQ=new T(function(){return B(A1(_Ff,_Bj));}),_FR=new T(function(){return B(A1(_Ff,_C1));}),_FS=new T(function(){return B(A1(_Ff,_BV));}),_FT=new T(function(){return B(A1(_Ff,_BP));}),_FU=new T(function(){return B(A1(_Ff,_BJ));}),_FV=new T(function(){return B(A1(_Ff,_BD));}),_FW=new T(function(){return B(A1(_Ff,_Bp));}),_FX=new T(function(){return B(A1(_Ff,_Bx));}),_FY=function(_FZ){switch(E(_FZ)){case 64:return E(_FX);case 65:return E(_FW);case 66:return E(_FV);case 67:return E(_FU);case 68:return E(_FT);case 69:return E(_FS);case 70:return E(_FR);case 71:return E(_Fg);case 72:return E(_Fh);case 73:return E(_Fi);case 74:return E(_Fj);case 75:return E(_Fk);case 76:return E(_Fl);case 77:return E(_Fm);case 78:return E(_FQ);case 79:return E(_FP);case 80:return E(_FO);case 81:return E(_FN);case 82:return E(_FM);case 83:return E(_FL);case 84:return E(_FK);case 85:return E(_FJ);case 86:return E(_FI);case 87:return E(_FH);case 88:return E(_FG);case 89:return E(_FF);case 90:return E(_FE);case 91:return E(_FD);case 92:return E(_FC);case 93:return E(_FB);case 94:return E(_FA);case 95:return E(_Fz);default:return new T0(2);}};return B(_wW(new T1(0,function(_G0){return (E(_G0)==94)?E(new T1(0,_FY)):new T0(2);}),new T(function(){return B(A1(_F9,_Ff));})));});return B(_wW(new T1(1,B(_xY(_AQ,_AS,_Fr))),_Fy));});return new F(function(){return _wW(new T1(0,function(_G1){switch(E(_G1)){case 34:return E(_Fp);case 39:return E(_Fo);case 92:return E(_Fn);case 97:return E(_Fg);case 98:return E(_Fh);case 102:return E(_Fl);case 110:return E(_Fj);case 114:return E(_Fm);case 116:return E(_Fi);case 118:return E(_Fk);default:return new T0(2);}}),_Fq);});},_G2=function(_G3){return new F(function(){return A1(_G3,_5L);});},_G4=function(_G5){var _G6=E(_G5);if(!_G6._){return E(_G2);}else{var _G7=E(_G6.a),_G8=_G7>>>0,_G9=new T(function(){return B(_G4(_G6.b));});if(_G8>887){var _Ga=u_iswspace(_G7);if(!E(_Ga)){return E(_G2);}else{var _Gb=function(_Gc){var _Gd=new T(function(){return B(A1(_G9,_Gc));});return new T1(0,function(_Ge){return E(_Gd);});};return E(_Gb);}}else{var _Gf=E(_G8);if(_Gf==32){var _Gg=function(_Gh){var _Gi=new T(function(){return B(A1(_G9,_Gh));});return new T1(0,function(_Gj){return E(_Gi);});};return E(_Gg);}else{if(_Gf-9>>>0>4){if(E(_Gf)==160){var _Gk=function(_Gl){var _Gm=new T(function(){return B(A1(_G9,_Gl));});return new T1(0,function(_Gn){return E(_Gm);});};return E(_Gk);}else{return E(_G2);}}else{var _Go=function(_Gp){var _Gq=new T(function(){return B(A1(_G9,_Gp));});return new T1(0,function(_Gr){return E(_Gq);});};return E(_Go);}}}}},_Gs=function(_Gt){var _Gu=new T(function(){return B(_Gs(_Gt));}),_Gv=function(_Gw){return (E(_Gw)==92)?E(_Gu):new T0(2);},_Gx=function(_Gy){return E(new T1(0,_Gv));},_Gz=new T1(1,function(_GA){return new F(function(){return A2(_G4,_GA,_Gx);});}),_GB=new T(function(){return B(_Fe(function(_GC){return new F(function(){return A1(_Gt,new T2(0,_GC,_5Q));});}));}),_GD=function(_GE){var _GF=E(_GE);if(_GF==38){return E(_Gu);}else{var _GG=_GF>>>0;if(_GG>887){var _GH=u_iswspace(_GF);return (E(_GH)==0)?new T0(2):E(_Gz);}else{var _GI=E(_GG);return (_GI==32)?E(_Gz):(_GI-9>>>0>4)?(E(_GI)==160)?E(_Gz):new T0(2):E(_Gz);}}};return new F(function(){return _wW(new T1(0,function(_GJ){return (E(_GJ)==92)?E(new T1(0,_GD)):new T0(2);}),new T1(0,function(_GK){var _GL=E(_GK);if(E(_GL)==92){return E(_GB);}else{return new F(function(){return A1(_Gt,new T2(0,_GL,_5N));});}}));});},_GM=function(_GN,_GO){var _GP=new T(function(){return B(A1(_GO,new T1(1,new T(function(){return B(A1(_GN,_v));}))));}),_GQ=function(_GR){var _GS=E(_GR),_GT=E(_GS.a);if(E(_GT)==34){if(!E(_GS.b)){return E(_GP);}else{return new F(function(){return _GM(function(_GU){return new F(function(){return A1(_GN,new T2(1,_GT,_GU));});},_GO);});}}else{return new F(function(){return _GM(function(_GV){return new F(function(){return A1(_GN,new T2(1,_GT,_GV));});},_GO);});}};return new F(function(){return _Gs(_GQ);});},_GW=new T(function(){return B(unCStr("_\'"));}),_GX=function(_GY){var _GZ=u_iswalnum(_GY);if(!E(_GZ)){return new F(function(){return _4d(_dO,_GY,_GW);});}else{return true;}},_H0=function(_H1){return new F(function(){return _GX(E(_H1));});},_H2=new T(function(){return B(unCStr(",;()[]{}`"));}),_H3=new T(function(){return B(unCStr("=>"));}),_H4=new T2(1,_H3,_v),_H5=new T(function(){return B(unCStr("~"));}),_H6=new T2(1,_H5,_H4),_H7=new T(function(){return B(unCStr("@"));}),_H8=new T2(1,_H7,_H6),_H9=new T(function(){return B(unCStr("->"));}),_Ha=new T2(1,_H9,_H8),_Hb=new T(function(){return B(unCStr("<-"));}),_Hc=new T2(1,_Hb,_Ha),_Hd=new T(function(){return B(unCStr("|"));}),_He=new T2(1,_Hd,_Hc),_Hf=new T(function(){return B(unCStr("\\"));}),_Hg=new T2(1,_Hf,_He),_Hh=new T(function(){return B(unCStr("="));}),_Hi=new T2(1,_Hh,_Hg),_Hj=new T(function(){return B(unCStr("::"));}),_Hk=new T2(1,_Hj,_Hi),_Hl=new T(function(){return B(unCStr(".."));}),_Hm=new T2(1,_Hl,_Hk),_Hn=function(_Ho){var _Hp=new T(function(){return B(A1(_Ho,_yC));}),_Hq=new T(function(){var _Hr=new T(function(){var _Hs=function(_Ht){var _Hu=new T(function(){return B(A1(_Ho,new T1(0,_Ht)));});return new T1(0,function(_Hv){return (E(_Hv)==39)?E(_Hu):new T0(2);});};return B(_Fe(_Hs));}),_Hw=function(_Hx){var _Hy=E(_Hx);switch(E(_Hy)){case 39:return new T0(2);case 92:return E(_Hr);default:var _Hz=new T(function(){return B(A1(_Ho,new T1(0,_Hy)));});return new T1(0,function(_HA){return (E(_HA)==39)?E(_Hz):new T0(2);});}},_HB=new T(function(){var _HC=new T(function(){return B(_GM(_5x,_Ho));}),_HD=new T(function(){var _HE=new T(function(){var _HF=new T(function(){var _HG=function(_HH){var _HI=E(_HH),_HJ=u_iswalpha(_HI);return (E(_HJ)==0)?(E(_HI)==95)?new T1(1,B(_yo(_H0,function(_HK){return new F(function(){return A1(_Ho,new T1(3,new T2(1,_HI,_HK)));});}))):new T0(2):new T1(1,B(_yo(_H0,function(_HL){return new F(function(){return A1(_Ho,new T1(3,new T2(1,_HI,_HL)));});})));};return B(_wW(new T1(0,_HG),new T(function(){return new T1(1,B(_xY(_zA,_AG,_Ho)));})));}),_HM=function(_HN){return (!B(_4d(_dO,_HN,_AI)))?new T0(2):new T1(1,B(_yo(_AJ,function(_HO){var _HP=new T2(1,_HN,_HO);if(!B(_4d(_xD,_HP,_Hm))){return new F(function(){return A1(_Ho,new T1(4,_HP));});}else{return new F(function(){return A1(_Ho,new T1(2,_HP));});}})));};return B(_wW(new T1(0,_HM),_HF));});return B(_wW(new T1(0,function(_HQ){if(!B(_4d(_dO,_HQ,_H2))){return new T0(2);}else{return new F(function(){return A1(_Ho,new T1(2,new T2(1,_HQ,_v)));});}}),_HE));});return B(_wW(new T1(0,function(_HR){return (E(_HR)==34)?E(_HC):new T0(2);}),_HD));});return B(_wW(new T1(0,function(_HS){return (E(_HS)==39)?E(new T1(0,_Hw)):new T0(2);}),_HB));});return new F(function(){return _wW(new T1(1,function(_HT){return (E(_HT)._==0)?E(_Hp):new T0(2);}),_Hq);});},_HU=0,_HV=function(_HW,_HX){var _HY=new T(function(){var _HZ=new T(function(){var _I0=function(_I1){var _I2=new T(function(){var _I3=new T(function(){return B(A1(_HX,_I1));});return B(_Hn(function(_I4){var _I5=E(_I4);return (_I5._==2)?(!B(_8S(_I5.a,_xz)))?new T0(2):E(_I3):new T0(2);}));}),_I6=function(_I7){return E(_I2);};return new T1(1,function(_I8){return new F(function(){return A2(_G4,_I8,_I6);});});};return B(A2(_HW,_HU,_I0));});return B(_Hn(function(_I9){var _Ia=E(_I9);return (_Ia._==2)?(!B(_8S(_Ia.a,_xy)))?new T0(2):E(_HZ):new T0(2);}));}),_Ib=function(_Ic){return E(_HY);};return function(_Id){return new F(function(){return A2(_G4,_Id,_Ib);});};},_Ie=function(_If,_Ig){var _Ih=function(_Ii){var _Ij=new T(function(){return B(A1(_If,_Ii));}),_Ik=function(_Il){return new F(function(){return _wW(B(A1(_Ij,_Il)),new T(function(){return new T1(1,B(_HV(_Ih,_Il)));}));});};return E(_Ik);},_Im=new T(function(){return B(A1(_If,_Ig));}),_In=function(_Io){return new F(function(){return _wW(B(A1(_Im,_Io)),new T(function(){return new T1(1,B(_HV(_Ih,_Io)));}));});};return E(_In);},_Ip=function(_Iq,_Ir){var _Is=function(_It,_Iu){var _Iv=function(_Iw){return new F(function(){return A1(_Iu,new T(function(){return  -E(_Iw);}));});},_Ix=new T(function(){return B(_Hn(function(_Iy){return new F(function(){return A3(_Iq,_Iy,_It,_Iv);});}));}),_Iz=function(_IA){return E(_Ix);},_IB=function(_IC){return new F(function(){return A2(_G4,_IC,_Iz);});},_ID=new T(function(){return B(_Hn(function(_IE){var _IF=E(_IE);if(_IF._==4){var _IG=E(_IF.a);if(!_IG._){return new F(function(){return A3(_Iq,_IF,_It,_Iu);});}else{if(E(_IG.a)==45){if(!E(_IG.b)._){return E(new T1(1,_IB));}else{return new F(function(){return A3(_Iq,_IF,_It,_Iu);});}}else{return new F(function(){return A3(_Iq,_IF,_It,_Iu);});}}}else{return new F(function(){return A3(_Iq,_IF,_It,_Iu);});}}));}),_IH=function(_II){return E(_ID);};return new T1(1,function(_IJ){return new F(function(){return A2(_G4,_IJ,_IH);});});};return new F(function(){return _Ie(_Is,_Ir);});},_IK=function(_IL){var _IM=E(_IL);if(!_IM._){var _IN=_IM.b,_IO=new T(function(){return B(_zS(new T(function(){return B(_sV(E(_IM.a)));}),new T(function(){return B(_9C(_IN,0));},1),B(_d5(_zI,_IN))));});return new T1(1,_IO);}else{return (E(_IM.b)._==0)?(E(_IM.c)._==0)?new T1(1,new T(function(){return B(_A9(_zH,_IM.a));})):__Z:__Z;}},_IP=function(_IQ,_IR){return new T0(2);},_IS=function(_IT){var _IU=E(_IT);if(_IU._==5){var _IV=B(_IK(_IU.a));if(!_IV._){return E(_IP);}else{var _IW=new T(function(){return B(_sM(_IV.a));});return function(_IX,_IY){return new F(function(){return A1(_IY,_IW);});};}}else{return E(_IP);}},_IZ=function(_J0){var _J1=function(_J2){return E(new T2(3,_J0,_xP));};return new T1(1,function(_J3){return new F(function(){return A2(_G4,_J3,_J1);});});},_J4=new T(function(){return B(A3(_Ip,_IS,_HU,_IZ));}),_J5=function(_J6){while(1){var _J7=B((function(_J8){var _J9=E(_J8);if(!_J9._){return __Z;}else{var _Ja=_J9.b,_Jb=E(_J9.a);if(!E(_Jb.b)._){return new T2(1,_Jb.a,new T(function(){return B(_J5(_Ja));}));}else{_J6=_Ja;return __continue;}}})(_J6));if(_J7!=__continue){return _J7;}}},_Jc=function(_Jd,_Je,_Jf){var _Jg=E(_Jf);if(!_Jg._){return new T2(0,new T2(1,_Je,_v),_v);}else{var _Jh=E(_Je),_Ji=new T(function(){var _Jj=B(_Jc(_Jd,_Jg.a,_Jg.b));return new T2(0,_Jj.a,_Jj.b);});return (_Jd!=_Jh)?new T2(0,new T2(1,_Jh,new T(function(){return E(E(_Ji).a);})),new T(function(){return E(E(_Ji).b);})):new T2(0,_v,new T2(1,new T(function(){return E(E(_Ji).a);}),new T(function(){return E(E(_Ji).b);})));}},_Jk=new T1(0,1),_Jl=new T1(0,10),_Jm=function(_Jn){while(1){var _Jo=E(_Jn);if(!_Jo._){_Jn=new T1(1,I_fromInt(_Jo.a));continue;}else{return new F(function(){return I_toString(_Jo.a);});}}},_Jp=function(_Jq,_Jr){return new F(function(){return _3(fromJSStr(B(_Jm(_Jq))),_Jr);});},_Js=new T1(0,0),_Jt=function(_Ju,_Jv,_Jw){if(_Ju<=6){return new F(function(){return _Jp(_Jv,_Jw);});}else{if(!B(_sp(_Jv,_Js))){return new F(function(){return _Jp(_Jv,_Jw);});}else{return new T2(1,_c,new T(function(){return B(_3(fromJSStr(B(_Jm(_Jv))),new T2(1,_b,_Jw)));}));}}},_Jx=function(_Jy,_Jz,_JA){while(1){if(!(_Jz%2)){var _JB=B(_uw(_Jy,_Jy)),_JC=quot(_Jz,2);_Jy=_JB;_Jz=_JC;continue;}else{var _JD=E(_Jz);if(_JD==1){return new F(function(){return _uw(_Jy,_JA);});}else{var _JB=B(_uw(_Jy,_Jy)),_JE=B(_uw(_Jy,_JA));_Jy=_JB;_Jz=quot(_JD-1|0,2);_JA=_JE;continue;}}}},_JF=function(_JG,_JH){while(1){if(!(_JH%2)){var _JI=B(_uw(_JG,_JG)),_JJ=quot(_JH,2);_JG=_JI;_JH=_JJ;continue;}else{var _JK=E(_JH);if(_JK==1){return E(_JG);}else{return new F(function(){return _Jx(B(_uw(_JG,_JG)),quot(_JK-1|0,2),_JG);});}}}},_JL=new T(function(){return B(unCStr("Negative exponent"));}),_JM=new T(function(){return B(err(_JL));}),_JN=function(_JO){return new F(function(){return _Jt(0,_JO,_v);});},_JP=new T(function(){return B(_t8(_Jl,_vj));}),_JQ=function(_JR){while(1){if(!B(_t8(_JR,_vj))){if(!E(_JP)){if(!B(_t8(B(_tx(_JR,_Jl)),_vj))){return new F(function(){return _JN(_JR);});}else{var _JS=B(_t0(_JR,_Jl));_JR=_JS;continue;}}else{return E(_qC);}}else{return __Z;}}},_JT=function(_JU){var _JV=E(_JU);if(!_JV._){return _JV.a;}else{return new F(function(){return I_toNumber(_JV.a);});}},_JW=46,_JX=48,_JY=function(_JZ,_K0,_K1){if(!B(_sp(_K1,_vj))){var _K2=B(A1(_JZ,_K1));if(!B(_t8(_K2,_vj))){var _K3=B(_tk(_K1,_K2)),_K4=_K3.b,_K5=new T(function(){var _K6=Math.log(B(_JT(_K2)))/Math.log(10),_K7=_K6&4294967295,_K8=function(_K9){if(_K9>=0){var _Ka=E(_K9);if(!_Ka){var _Kb=B(_t0(B(_rV(B(_r2(B(_uw(_K4,_rL)),_K2)),_Jk)),_K2));}else{var _Kb=B(_t0(B(_rV(B(_r2(B(_uw(_K4,B(_JF(_Jl,_Ka)))),_K2)),_Jk)),_K2));}var _Kc=function(_Kd){var _Ke=B(_Jt(0,_Kb,_v)),_Kf=_K9-B(_9C(_Ke,0))|0;if(0>=_Kf){if(!E(_K0)){return E(_Ke);}else{return new F(function(){return _JQ(_Kb);});}}else{var _Kg=new T(function(){if(!E(_K0)){return E(_Ke);}else{return B(_JQ(_Kb));}}),_Kh=function(_Ki){var _Kj=E(_Ki);return (_Kj==1)?E(new T2(1,_JX,_Kg)):new T2(1,_JX,new T(function(){return B(_Kh(_Kj-1|0));}));};return new F(function(){return _Kh(_Kf);});}};if(!E(_K0)){var _Kk=B(_Kc(_));return (_Kk._==0)?__Z:new T2(1,_JW,_Kk);}else{if(!B(_t8(_Kb,_vj))){var _Kl=B(_Kc(_));return (_Kl._==0)?__Z:new T2(1,_JW,_Kl);}else{return __Z;}}}else{return E(_JM);}};if(_K7>=_K6){return B(_K8(_K7));}else{return B(_K8(_K7+1|0));}},1);return new F(function(){return _3(B(_Jt(0,_K3.a,_v)),_K5);});}else{return E(_qC);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_JY(_JZ,_K0,B(_rc(_K1))));}));});}},_Km=function(_Kn,_Ko,_){var _Kp=B(_wA(_)),_Kq=new T(function(){var _Kr=new T(function(){var _Ks=new T(function(){var _Kt=B(_3(B(_JY(_ro,_5Q,B(_wa(_Kp)).b)),_rC));if(!_Kt._){return E(_az);}else{var _Ku=B(_ar(_Kt.a,_Kt.b));if(!_Ku._){return B(_rH(_v,_v,_aB));}else{var _Kv=_Ku.a,_Kw=E(_Ku.b);if(!_Kw._){return B(_rH(new T2(1,_Kv,_v),_v,_aB));}else{var _Kx=E(_Kv),_Ky=new T(function(){var _Kz=B(_Jc(46,_Kw.a,_Kw.b));return new T2(0,_Kz.a,_Kz.b);});if(E(_Kx)==46){return B(_rH(_v,new T2(1,new T(function(){return E(E(_Ky).a);}),new T(function(){return E(E(_Ky).b);})),_aB));}else{return B(_rH(new T2(1,_Kx,new T(function(){return E(E(_Ky).a);})),new T(function(){return E(E(_Ky).b);}),_aB));}}}}}),_KA=B(_J5(B(_wM(_J4,_Ks))));if(!_KA._){return E(_wH);}else{if(!E(_KA.b)._){return B(_wg(3,B(_d(0,E(_KA.a)+(imul(E(_Ko),E(_Kn)-1|0)|0)|0,_v))));}else{return E(_wF);}}}),_KB=B(_J5(B(_wM(_J4,_Kr))));if(!_KB._){return E(_wH);}else{if(!E(_KB.b)._){return E(_KB.a);}else{return E(_wF);}}});return new T2(0,new T(function(){return B(_ry(_Kq,_Kn));}),_Kq);},_KC=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_KD=new T(function(){return B(err(_KC));}),_KE=function(_KF,_KG){while(1){var _KH=E(_KG);if(!_KH._){return __Z;}else{var _KI=_KH.b,_KJ=E(_KF);if(_KJ==1){return E(_KI);}else{_KF=_KJ-1|0;_KG=_KI;continue;}}}},_KK=function(_KL,_KM){if(B(_9C(_KM,0))>=(_KL+1|0)){var _KN=new T(function(){var _KO=_KL+1|0;if(_KO>0){return B(_KE(_KO,_KM));}else{return E(_KM);}});if(0>=_KL){return E(_KN);}else{var _KP=function(_KQ,_KR){var _KS=E(_KQ);if(!_KS._){return E(_KN);}else{var _KT=_KS.a,_KU=E(_KR);return (_KU==1)?new T2(1,_KT,_KN):new T2(1,_KT,new T(function(){return B(_KP(_KS.b,_KU-1|0));}));}};return new F(function(){return _KP(_KM,_KL);});}}else{return E(_KM);}},_KV=function(_KW,_KX){return new F(function(){return _KK(E(_KW),_KX);});},_KY=function(_KZ){return E(E(_KZ).a);},_L0=function(_L1){return new F(function(){return _d(0,E(_L1),_v);});},_L2=function(_L3,_L4,_L5){return new F(function(){return _d(E(_L3),E(_L4),_L5);});},_L6=function(_L7,_L8){return new F(function(){return _d(0,E(_L7),_L8);});},_L9=function(_La,_Lb){return new F(function(){return _28(_L6,_La,_Lb);});},_Lc=new T3(0,_L2,_L0,_L9),_Ld=0,_Le=function(_Lf,_Lg,_Lh){return new F(function(){return A1(_Lf,new T2(1,_25,new T(function(){return B(A1(_Lg,_Lh));})));});},_Li=new T(function(){return B(unCStr("foldr1"));}),_Lj=new T(function(){return B(_aw(_Li));}),_Lk=function(_Ll,_Lm){var _Ln=E(_Lm);if(!_Ln._){return E(_Lj);}else{var _Lo=_Ln.a,_Lp=E(_Ln.b);if(!_Lp._){return E(_Lo);}else{return new F(function(){return A2(_Ll,_Lo,new T(function(){return B(_Lk(_Ll,_Lp));}));});}}},_Lq=new T(function(){return B(unCStr(" out of range "));}),_Lr=new T(function(){return B(unCStr("}.index: Index "));}),_Ls=new T(function(){return B(unCStr("Ix{"));}),_Lt=new T2(1,_b,_v),_Lu=new T2(1,_b,_Lt),_Lv=0,_Lw=function(_Lx){return E(E(_Lx).a);},_Ly=function(_Lz,_LA,_LB,_LC,_LD){var _LE=new T(function(){var _LF=new T(function(){var _LG=new T(function(){var _LH=new T(function(){var _LI=new T(function(){return B(A3(_Lk,_Le,new T2(1,new T(function(){return B(A3(_Lw,_LB,_Lv,_LC));}),new T2(1,new T(function(){return B(A3(_Lw,_LB,_Lv,_LD));}),_v)),_Lu));});return B(_3(_Lq,new T2(1,_c,new T2(1,_c,_LI))));});return B(A(_Lw,[_LB,_Ld,_LA,new T2(1,_b,_LH)]));});return B(_3(_Lr,new T2(1,_c,_LG)));},1);return B(_3(_Lz,_LF));},1);return new F(function(){return err(B(_3(_Ls,_LE)));});},_LJ=function(_LK,_LL,_LM,_LN,_LO){return new F(function(){return _Ly(_LK,_LL,_LO,_LM,_LN);});},_LP=function(_LQ,_LR,_LS,_LT){var _LU=E(_LS);return new F(function(){return _LJ(_LQ,_LR,_LU.a,_LU.b,_LT);});},_LV=function(_LW,_LX,_LY,_LZ){return new F(function(){return _LP(_LZ,_LY,_LX,_LW);});},_M0=new T(function(){return B(unCStr("Int"));}),_M1=function(_M2,_M3,_M4){return new F(function(){return _LV(_Lc,new T2(0,_M3,_M4),_M2,_M0);});},_M5=0,_M6=new T(function(){return B(unCStr("Negative range size"));}),_M7=new T(function(){return B(err(_M6));}),_M8=function(_M9){var _Ma=B(A1(_M9,_));return E(_Ma);},_Mb=function(_Mc,_Md,_Me,_){var _Mf=E(_Mc);if(!_Mf){return new T2(0,_v,_Md);}else{var _Mg=new T(function(){return B(_9C(_Me,0))-1|0;}),_Mh=B(_Km(new T(function(){return E(_Mg)+1|0;}),_Md,_)),_Mi=E(_Mh),_Mj=_Mi.a,_Mk=_Mi.b,_Ml=B(_Mb(_Mf-1|0,_Mk,new T(function(){return B(_KV(_Mj,_Me));}),_)),_Mm=new T(function(){var _Mn=function(_){var _Mo=E(_Mg),_Mp=function(_Mq){if(_Mq>=0){var _Mr=newArr(_Mq,_KD),_Ms=_Mr,_Mt=E(_Mq);if(!_Mt){return new T4(0,E(_M5),E(_Mo),0,_Ms);}else{var _Mu=function(_Mv,_Mw,_){while(1){var _Mx=E(_Mv);if(!_Mx._){return E(_);}else{var _=_Ms[_Mw]=_Mx.a;if(_Mw!=(_Mt-1|0)){var _My=_Mw+1|0;_Mv=_Mx.b;_Mw=_My;continue;}else{return E(_);}}}},_=B(_Mu(_Me,0,_));return new T4(0,E(_M5),E(_Mo),_Mt,_Ms);}}else{return E(_M7);}};if(0>_Mo){return new F(function(){return _Mp(0);});}else{return new F(function(){return _Mp(_Mo+1|0);});}},_Mz=B(_M8(_Mn)),_MA=E(_Mz.a),_MB=E(_Mz.b),_MC=E(_Mj);if(_MA>_MC){return B(_M1(_MC,_MA,_MB));}else{if(_MC>_MB){return B(_M1(_MC,_MA,_MB));}else{return E(_Mz.d[_MC-_MA|0]);}}});return new T2(0,new T2(1,_Mm,new T(function(){return B(_KY(_Ml));})),_Mk);}},_MD=function(_ME){var _MF=E(_ME);if(!_MF._){return new T2(0,_v,_v);}else{var _MG=E(_MF.a),_MH=new T(function(){var _MI=B(_MD(_MF.b));return new T2(0,_MI.a,_MI.b);});return new T2(0,new T2(1,_MG.a,new T(function(){return E(E(_MH).a);})),new T2(1,_MG.b,new T(function(){return E(E(_MH).b);})));}},_MJ=function(_MK){return new T2(1,_MK,_v);},_ML=new T(function(){return B(unCStr("\u3042\u304b\u306f\u306a\u307e\u3044\u304d\u3072\u306b\u307f\u3046\u304f\u3075\u306c\u3080\u3048\u3051\u3078\u306d\u3081\u304a\u3053\u307b\u306e\u3082\u3068\u308d\u305d\u3088\u3092\u3066\u308c\u305b\u3091\u3064\u308b\u3059\u3086\u3093\u3061\u308a\u3057\u3090\u305f\u3089\u3055\u3084\u308f"));}),_MM=function(_MN,_MO,_){var _MP=new T(function(){var _MQ=E(_MO);return 4+B(_qG(_MQ,8-B(_q2(_MQ,8))|0))|0;}),_MR=B(_Km(_MP,_MN,_)),_MS=E(_MR),_MT=new T(function(){return B(_jd(_or,new T(function(){var _MU=E(_MO)+3|0;if(0>=_MU){return __Z;}else{return B(_wg(_MU,_ML));}},1)));}),_MV=B(_Mb(E(_MP),_MS.b,_MT,_)),_MW=E(_MV);return new T2(0,new T(function(){var _MX=B(_MD(_MW.a));return new T3(0,E(B(_d5(_MJ,_MX.b))),E(_MX.a),E(_MS.a));}),_MW.b);},_MY=function(_MZ){return E(_MZ).d;},_N0=function(_N1,_N2,_N3,_N4,_){var _N5=B(_MM(new T(function(){return B(_MY(_N4));},1),_N3,_)),_N6=E(_N5),_N7=E(_N6.a),_N8=_N7.b,_N9=_N7.c,_Na=B(A3(_pR,_5z,B(_a1(_N2,B(_a1(_N8,_N9)))).a,_));return new T(function(){var _Nb=E(_N4),_Nc=E(_N1),_Nd=B(_oG(_Nc.a,_Nc.b,_N7.a,_N8,_N9));return new T6(0,E(_Nb.a),E(new T1(1,_N7)),E(new T2(1,_Nd.a,_Nd.b)),E(_N6.b),E(_Nb.e),E(_Nb.f));});},_Ne=function(_Nf,_Ng,_Nh,_Ni,_Nj,_Nk,_Nl,_Nm,_Nn,_No,_Np,_Nq,_Nr,_Ns,_Nt,_){var _Nu=function(_,_Nv,_Nw,_Nx,_Ny,_Nz,_NA,_NB,_NC,_ND,_NE){if(!B(_8X(_Nk,_Nl,_Nm,_Nn,_No,_Np,_Nq,_Nr,_Ns,_Nt,_Nv,_Nw,_Nx,_Ny,_Nz,_NA,_NB,_NC,_ND,_NE))){var _NF=E(_Nf),_NG=__app1(E(_dw),_NF.b),_NH=B(A2(_dH,_NF.a,_)),_NI=B(_ji(_NF,new T2(0,_Ng,_og),_Nh,_Nx,_));return new T6(0,E(_Nv),E(_Nw),E(_Nx),_Ny,E(new T5(0,E(_Nz),E(_NA),E(_NB),E(_NC),E(_ND))),E(_NE));}else{return new T6(0,E(_Nv),E(_Nw),E(_Nx),_Ny,E(new T5(0,E(_Nz),E(_NA),E(_NB),E(_NC),E(_ND))),E(_NE));}},_NJ=E(_Nj);if(_NJ==( -1)){return new F(function(){return _Nu(_,_Nk,_Nl,_Nm,_Nn,_No,_Np,_Nq,_Nr,_Ns,_Nt);});}else{var _NK=B(_6R(_NJ,_Nm));if(!_NK._){return new F(function(){return _Nu(_,_Nk,_Nl,_Nm,_Nn,_No,_Np,_Nq,_Nr,_Ns,_Nt);});}else{var _NL=E(E(_NK.a).o);switch(_NL._){case 0:return new F(function(){return _Nu(_,_Nk,_Nl,_Nm,_Nn,_No,_Np,_Nq,_Nr,_Ns,_Nt);});break;case 1:var _NM=E(_NL.a);if(!_NM._){var _NN=B(_N0(_Ng,_Ni,_NM.a,new T6(0,E(new T1(1,_NM)),E(_Nl),E(_Nm),_Nn,E(new T5(0,E(_No),E(_Np),E(_Nq),E(_Nr),E(_Ns))),E(_Nt)),_)),_NO=E(_NN),_NP=E(_NO.e);return new F(function(){return _Nu(_,_NO.a,_NO.b,_NO.c,_NO.d,_NP.a,_NP.b,_NP.c,_NP.d,_NP.e,_NO.f);});}else{return E(_ol);}break;case 2:var _NQ=B(_d9(_Ng,new T(function(){return B(_9C(_Nm,0));},1),_NL.a,_Nk,_Nl,_Nm,_Nn,new T5(0,E(_No),E(_Np),E(_Nq),E(_Nr),E(_Ns)),_Nt)),_NR=E(_NQ.e);return new F(function(){return _Nu(_,_NQ.a,_NQ.b,_NQ.c,_NQ.d,_NR.a,_NR.b,_NR.c,_NR.d,_NR.e,_NQ.f);});break;default:var _NS=B(_bL(_Ng,E(_NL.a),_Nk,_Nl,_Nm,_Nn,new T5(0,E(_No),E(_Np),E(_Nq),E(_Nr),E(_Ns)),_Nt)),_NT=E(_NS.e);return new F(function(){return _Nu(_,_NS.a,_NS.b,_NS.c,_NS.d,_NT.a,_NT.b,_NT.c,_NT.d,_NT.e,_NS.f);});}}}},_NU=function(_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_){var _O2=E(_NW),_O3=_O2.a,_O4=E(_O1),_O5=_O4.c,_O6=function(_O7){var _O8=E(_O4.e);return new F(function(){return _Ne(_NV,_O3,_NX,_NY,_O7,_O4.a,_O4.b,_O5,_O4.d,_O8.a,_O8.b,_O8.c,_O8.d,_O8.e,_O4.f,_);});},_O9=E(_O5);if(!_O9._){return new F(function(){return _O6( -1);});}else{var _Oa=_O9.b,_Ob=E(_O3),_Oc=_Ob.b,_Od=E(_O2.b),_Oe=_Od.b,_Of=E(_NZ)*(E(_Ob.a)/E(_Od.a)),_Og=E(_O9.a),_Oh=E(_Og.b),_Oi=E(_Oh.a);if(_Of<=_Oi){return new F(function(){return _O6(B(_6G(_Of,new T(function(){return E(_O0)*(E(_Oc)/E(_Oe));},1),_Oa)));});}else{if(_Of>=_Oi+E(_Oh.c)){return new F(function(){return _O6(B(_6G(_Of,new T(function(){return E(_O0)*(E(_Oc)/E(_Oe));},1),_Oa)));});}else{var _Oj=E(_O0)*(E(_Oc)/E(_Oe)),_Ok=E(_Oh.b);if(_Oj<=_Ok){return new F(function(){return _O6(B(_6w(_Of,_Oj,_Oa)));});}else{if(_Oj>=_Ok+E(_Oh.d)){return new F(function(){return _O6(B(_6w(_Of,_Oj,_Oa)));});}else{return new F(function(){return _O6(_Og.a);});}}}}}},_Ol=function(_Om){return E(E(_Om).a);},_On=function(_Oo){return E(E(_Oo).b);},_Op=function(_Oq){return E(E(_Oq).a);},_Or=function(_){return new F(function(){return nMV(_2q);});},_Os=new T(function(){return B(_2J(_Or));}),_Ot=function(_Ou){return E(E(_Ou).b);},_Ov=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_Ow=function(_Ox){return E(E(_Ox).d);},_Oy=function(_Oz,_OA,_OB,_OC,_OD,_OE){var _OF=B(_Ol(_Oz)),_OG=B(_p1(_OF)),_OH=new T(function(){return B(_5U(_OF));}),_OI=new T(function(){return B(_Ow(_OG));}),_OJ=new T(function(){return B(A1(_OA,_OC));}),_OK=new T(function(){return B(A2(_Op,_OB,_OD));}),_OL=function(_OM){return new F(function(){return A1(_OI,new T3(0,_OK,_OJ,_OM));});},_ON=function(_OO){var _OP=new T(function(){var _OQ=new T(function(){var _OR=__createJSFunc(2,function(_OS,_){var _OT=B(A2(E(_OO),_OS,_));return _2N;}),_OU=_OR;return function(_){return new F(function(){return __app3(E(_Ov),E(_OJ),E(_OK),_OU);});};});return B(A1(_OH,_OQ));});return new F(function(){return A3(_pL,_OG,_OP,_OL);});},_OV=new T(function(){var _OW=new T(function(){return B(_5U(_OF));}),_OX=function(_OY){var _OZ=new T(function(){return B(A1(_OW,function(_){var _=wMV(E(_Os),new T1(1,_OY));return new F(function(){return A(_On,[_OB,_OD,_OY,_]);});}));});return new F(function(){return A3(_pL,_OG,_OZ,_OE);});};return B(A2(_Ot,_Oz,_OX));});return new F(function(){return A3(_pL,_OG,_OV,_ON);});},_P0=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_P1=function(_){var _P2=rMV(E(_Os)),_P3=E(_P2);if(!_P3._){var _P4=__app1(E(_P0),E(_2N));return new F(function(){return _dx(_);});}else{var _P5=__app1(E(_P0),E(_P3.a));return new F(function(){return _dx(_);});}},_P6=new T(function(){return B(unCStr("\u4eca\u65e5\u3082\u6700\u9ad8\u306e\u4e00\u65e5\u306b\u306a\u308b\u3088\uff01\n\u30f2\u30b7\u30c6\u3092\u5b78\u3093\u3067\u3044\u304b\u3046\u3088\uff01\n\u304a\u3082\u3057\u308d\u3044\u3053\u3068\u306b\u306a\u3063\u3066\u304d\u305f\u306d\uff01\n\u3059\u3066\u304d\u306a \u51fa\u6703\u3072\u304c \u3042\u3063\u3066 \u3046\u308c\u3057\u3044\u306d\uff01\n\u5fc3\u306e\u6e96\u5099\u306f\u3067\u304d\u3066\u308b\uff1f\n\u3055\u3042 \u306f\u3058\u3081\u3084\u3046\u304b\uff01"));}),_P7=function(_P8,_P9){var _Pa=E(_P9);if(!_Pa._){return new T2(0,_v,_v);}else{var _Pb=_Pa.a;if(!B(A1(_P8,_Pb))){var _Pc=new T(function(){var _Pd=B(_P7(_P8,_Pa.b));return new T2(0,_Pd.a,_Pd.b);});return new T2(0,new T2(1,_Pb,new T(function(){return E(E(_Pc).a);})),new T(function(){return E(E(_Pc).b);}));}else{return new T2(0,_v,_Pa);}}},_Pe=function(_Pf){return (E(_Pf)==10)?true:false;},_Pg=function(_Ph){var _Pi=E(_Ph);if(!_Pi._){return __Z;}else{var _Pj=new T(function(){var _Pk=B(_P7(_Pe,_Pi));return new T2(0,_Pk.a,new T(function(){var _Pl=E(_Pk.b);if(!_Pl._){return __Z;}else{return B(_Pg(_Pl.b));}}));});return new T2(1,new T(function(){return E(E(_Pj).a);}),new T(function(){return E(E(_Pj).b);}));}},_Pm=new T(function(){return B(_Pg(_P6));}),_Pn=function(_Po,_Pp){while(1){var _Pq=E(_Po);if(!_Pq._){return E(_Pp);}else{_Po=_Pq.b;_Pp=_Pq.a;continue;}}},_Pr=function(_Ps,_Pt,_Pu,_Pv,_){var _Pw=B(_Mb(1,new T(function(){return E(_Pv).d;}),_Pm,_));return new F(function(){return _ji(_Ps,_Pt,_Pu,new T2(1,{_:0,a:0,b:E(_6d),c:E(_62),d:0,e:5,f:E(_69),g:E(_v),h:E(_6k),i:E(_6i),j:E(new T2(1,new T(function(){return B(_Pn(E(_Pw).a,_aB));}),_v)),k:E(_6f),l:E(_v),m:E(_v),n:E(_2q),o:E(_65)},_v),_);});},_Px=new T1(0,0),_Py=new T(function(){return B(unCStr("vaw"));}),_Pz=new T(function(){return B(unCStr("ggo"));}),_PA=new T(function(){return B(unCStr("3pm"));}),_PB=0,_PC=1,_PD=2,_PE=function(_PF,_PG){while(1){var _PH=E(_PF);if(!_PH._){return E(_PG);}else{var _PI=new T2(1,_PH.a,_PG);_PF=_PH.b;_PG=_PI;continue;}}},_PJ=function(_PK){var _PL=B(_wg(3,B(_PE(fromJSStr(_PK),_v))));return (!B(_8S(_PL,_PA)))?(!B(_8S(_PL,_Pz)))?(!B(_8S(_PL,_Py)))?__Z:new T1(1,new T2(0,E(_PD),_PK)):new T1(1,new T2(0,E(_PC),_PK)):new T1(1,new T2(0,E(_PB),_PK));},_PM=new T(function(){return B(unCStr("Audio/"));}),_PN=new T1(0,1),_PO=new T1(0,7),_PP=2,_PQ=new T6(0,E(_5N),E(_5N),E(_5N),E(_PP),E(_5N),1),_PR=new T(function(){return B(_bv("Browser.hs:83:7-34|Just adSrc"));}),_PS=new T(function(){return B(unCStr(".mp3"));}),_PT=function(_PU){return new T1(1,E(_PU));},_PV=function(_PW,_PX){return new F(function(){return A2(_Ow,B(_p1(_PW)),new T1(1,_PX));});},_PY=new T2(0,_5x,_PV),_PZ="auto",_Q0="metadata",_Q1="none",_Q2=new T(function(){return new T1(0,"preload");}),_Q3=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_Q4=function(_){return new F(function(){return __app1(E(_Q3),"source");});},_Q5=new T(function(){return new T1(0,"src");}),_Q6="audio/wav",_Q7="audio/ogg",_Q8="audio/mpeg",_Q9=new T(function(){return new T1(0,"type");}),_Qa=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_Qb=function(_Qc){return E(E(_Qc).a);},_Qd=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_Qe=new T(function(){return eval("(function(e,p,v){e.style[p] = v;})");}),_Qf=function(_Qg,_Qh,_Qi,_Qj){var _Qk=new T(function(){return B(A2(_Qb,_Qg,_Qi));}),_Ql=function(_Qm,_){var _Qn=E(_Qm);if(!_Qn._){return _5L;}else{var _Qo=E(_Qk),_Qp=E(_Qa),_Qq=__app2(_Qp,E(_Qn.a),_Qo),_Qr=function(_Qs,_){while(1){var _Qt=E(_Qs);if(!_Qt._){return _5L;}else{var _Qu=__app2(_Qp,E(_Qt.a),_Qo);_Qs=_Qt.b;continue;}}};return new F(function(){return _Qr(_Qn.b,_);});}},_Qv=function(_Qw,_){while(1){var _Qx=B((function(_Qy,_){var _Qz=E(_Qy);if(!_Qz._){return _5L;}else{var _QA=_Qz.b,_QB=E(_Qz.a);if(!_QB._){var _QC=_QB.b,_QD=E(_QB.a);switch(_QD._){case 0:var _QE=E(_Qk),_QF=E(_eK),_QG=__app3(_QF,_QE,_QD.a,_QC),_QH=function(_QI,_){while(1){var _QJ=E(_QI);if(!_QJ._){return _5L;}else{var _QK=_QJ.b,_QL=E(_QJ.a);if(!_QL._){var _QM=_QL.b,_QN=E(_QL.a);switch(_QN._){case 0:var _QO=__app3(_QF,_QE,_QN.a,_QM);_QI=_QK;continue;case 1:var _QP=__app3(E(_Qe),_QE,_QN.a,_QM);_QI=_QK;continue;default:var _QQ=__app3(E(_Qd),_QE,_QN.a,_QM);_QI=_QK;continue;}}else{var _QR=B(_Ql(_QL.a,_));_QI=_QK;continue;}}}};return new F(function(){return _QH(_QA,_);});break;case 1:var _QS=E(_Qk),_QT=E(_Qe),_QU=__app3(_QT,_QS,_QD.a,_QC),_QV=function(_QW,_){while(1){var _QX=E(_QW);if(!_QX._){return _5L;}else{var _QY=_QX.b,_QZ=E(_QX.a);if(!_QZ._){var _R0=_QZ.b,_R1=E(_QZ.a);switch(_R1._){case 0:var _R2=__app3(E(_eK),_QS,_R1.a,_R0);_QW=_QY;continue;case 1:var _R3=__app3(_QT,_QS,_R1.a,_R0);_QW=_QY;continue;default:var _R4=__app3(E(_Qd),_QS,_R1.a,_R0);_QW=_QY;continue;}}else{var _R5=B(_Ql(_QZ.a,_));_QW=_QY;continue;}}}};return new F(function(){return _QV(_QA,_);});break;default:var _R6=E(_Qk),_R7=E(_Qd),_R8=__app3(_R7,_R6,_QD.a,_QC),_R9=function(_Ra,_){while(1){var _Rb=E(_Ra);if(!_Rb._){return _5L;}else{var _Rc=_Rb.b,_Rd=E(_Rb.a);if(!_Rd._){var _Re=_Rd.b,_Rf=E(_Rd.a);switch(_Rf._){case 0:var _Rg=__app3(E(_eK),_R6,_Rf.a,_Re);_Ra=_Rc;continue;case 1:var _Rh=__app3(E(_Qe),_R6,_Rf.a,_Re);_Ra=_Rc;continue;default:var _Ri=__app3(_R7,_R6,_Rf.a,_Re);_Ra=_Rc;continue;}}else{var _Rj=B(_Ql(_Rd.a,_));_Ra=_Rc;continue;}}}};return new F(function(){return _R9(_QA,_);});}}else{var _Rk=B(_Ql(_QB.a,_));_Qw=_QA;return __continue;}}})(_Qw,_));if(_Qx!=__continue){return _Qx;}}};return new F(function(){return A2(_5U,_Qh,function(_){return new F(function(){return _Qv(_Qj,_);});});});},_Rl=function(_Rm,_Rn,_Ro,_Rp){var _Rq=B(_p1(_Rn)),_Rr=function(_Rs){return new F(function(){return A3(_pJ,_Rq,new T(function(){return B(_Qf(_Rm,_Rn,_Rs,_Rp));}),new T(function(){return B(A2(_Ow,_Rq,_Rs));}));});};return new F(function(){return A3(_pL,_Rq,_Ro,_Rr);});},_Rt=function(_Ru,_){var _Rv=E(_Ru);if(!_Rv._){return _v;}else{var _Rw=E(_Rv.a),_Rx=B(A(_Rl,[_PY,_5z,_Q4,new T2(1,new T(function(){var _Ry=E(_Q9);switch(E(_Rw.a)){case 0:return new T2(0,E(_Ry),E(_Q8));break;case 1:return new T2(0,E(_Ry),E(_Q7));break;default:return new T2(0,E(_Ry),E(_Q6));}}),new T2(1,new T(function(){return new T2(0,E(_Q5),_Rw.b);}),_v)),_])),_Rz=B(_Rt(_Rv.b,_));return new T2(1,_Rx,_Rz);}},_RA=new T(function(){return new T1(0,"volume");}),_RB=new T(function(){return new T1(0,"muted");}),_RC=new T(function(){return new T1(0,"loop");}),_RD=new T(function(){return new T1(0,"autoplay");}),_RE="true",_RF=new T(function(){return toJSStr(_v);}),_RG=new T(function(){return new T1(0,"controls");}),_RH=function(_){return new F(function(){return __app1(E(_Q3),"audio");});},_RI=function(_RJ,_RK,_RL){var _RM=function(_){var _RN=B(_Rt(_RL,_)),_RO=B(A(_Rl,[_PY,_5z,_RH,new T2(1,new T(function(){var _RP=E(_RG);if(!E(E(_RK).a)){return new T2(0,E(_RP),E(_RF));}else{return new T2(0,E(_RP),E(_RE));}}),new T2(1,new T(function(){var _RQ=E(_RD);if(!E(E(_RK).b)){return new T2(0,E(_RQ),E(_RF));}else{return new T2(0,E(_RQ),E(_RE));}}),new T2(1,new T(function(){var _RR=E(_RC);if(!E(E(_RK).c)){return new T2(0,E(_RR),E(_RF));}else{return new T2(0,E(_RR),E(_RE));}}),new T2(1,new T(function(){var _RS=E(_RB);if(!E(E(_RK).e)){return new T2(0,E(_RS),E(_RF));}else{return new T2(0,E(_RS),E(_RE));}}),new T2(1,new T(function(){var _RT=String(E(_RK).f);return new T2(0,E(_RA),_RT);}),new T2(1,new T(function(){var _RU=E(_Q2);switch(E(E(_RK).d)){case 0:return new T2(0,E(_RU),E(_Q1));break;case 1:return new T2(0,E(_RU),E(_Q0));break;default:return new T2(0,E(_RU),E(_PZ));}}),new T2(1,new T(function(){return B(_PT(_RN));}),_v))))))),_]));return new T1(0,_RO);};return new F(function(){return A2(_5U,_RJ,_RM);});},_RV=function(_RW,_){if(!B(_sh(_RW,_PO))){var _RX=new T(function(){var _RY=new T(function(){return B(unAppCStr("os",new T(function(){return B(_3(B(_Jt(0,_RW,_v)),_PS));})));},1),_RZ=B(_PJ(toJSStr(B(_3(_PM,_RY)))));if(!_RZ._){return E(_PR);}else{return E(_RZ.a);}}),_S0=B(A(_RI,[_5z,_PQ,new T2(1,_RX,_v),_])),_S1=B(_RV(B(_r2(_RW,_PN)),_));return new T2(1,_S0,_S1);}else{return _v;}},_S2="src",_S3=new T(function(){return B(unCStr("img"));}),_S4=function(_S5,_S6){return new F(function(){return A2(_5U,_S5,function(_){var _S7=__app1(E(_Q3),toJSStr(E(_S3))),_S8=__app3(E(_eK),_S7,E(_S2),E(_S6));return _S7;});});},_S9=new T(function(){return B(unCStr(".png"));}),_Sa=function(_Sb,_Sc){var _Sd=E(_Sb);if(_Sd==( -1)){return __Z;}else{var _Se=new T(function(){var _Sf=new T(function(){return toJSStr(B(_3(_Sc,new T(function(){return B(_3(B(_d(0,_Sd,_v)),_S9));},1))));});return B(_S4(_5z,_Sf));});return new F(function(){return _3(B(_Sa(_Sd-1|0,_Sc)),new T2(1,_Se,_v));});}},_Sg=new T(function(){return B(unCStr("Images/Wst/wst"));}),_Sh=new T(function(){return B(_Sa(120,_Sg));}),_Si=function(_Sj,_){var _Sk=E(_Sj);if(!_Sk._){return _v;}else{var _Sl=B(A1(_Sk.a,_)),_Sm=B(_Si(_Sk.b,_));return new T2(1,_Sl,_Sm);}},_Sn=new T(function(){return B(unCStr("Images/img"));}),_So=new T(function(){return B(_Sa(5,_Sn));}),_Sp=function(_Sq,_){var _Sr=E(_Sq);if(!_Sr._){return _v;}else{var _Ss=B(A1(_Sr.a,_)),_St=B(_Sp(_Sr.b,_));return new T2(1,_Ss,_St);}},_Su=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_Sv=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_Sw=function(_Sx,_Sy,_Sz){var _SA=B(_Ol(_Sx)),_SB=new T(function(){return B(_5U(_SA));}),_SC=function(_SD){var _SE=function(_){var _SF=E(_Sy);if(!_SF._){var _SG=B(A1(_SD,_5L)),_SH=__createJSFunc(0,function(_){var _SI=B(A1(_SG,_));return _2N;}),_SJ=__app2(E(_Sv),_SF.a,_SH);return new T(function(){var _SK=Number(_SJ),_SL=jsTrunc(_SK);return new T2(0,_SL,E(_SF));});}else{var _SM=B(A1(_SD,_5L)),_SN=__createJSFunc(0,function(_){var _SO=B(A1(_SM,_));return _2N;}),_SP=__app2(E(_Su),_SF.a,_SN);return new T(function(){var _SQ=Number(_SP),_SR=jsTrunc(_SQ);return new T2(0,_SR,E(_SF));});}};return new F(function(){return A1(_SB,_SE);});},_SS=new T(function(){return B(A2(_Ot,_Sx,function(_ST){return E(_Sz);}));});return new F(function(){return A3(_pL,B(_p1(_SA)),_SS,_SC);});},_SU=function(_){var _SV=B(_Sp(_So,_)),_SW=B(_Si(_Sh,_)),_SX=B(_RV(_Px,_)),_SY=_SX,_SZ=__app1(E(_5R),"canvas"),_T0=__eq(_SZ,E(_2N));if(!E(_T0)){var _T1=__isUndef(_SZ);if(!E(_T1)){var _T2=B(A3(_5W,_5z,_SZ,_)),_T3=E(_T2);if(!_T3._){return new F(function(){return die(_6v);});}else{var _T4=E(_T3.a),_T5=B(_5F(_T4.b,_)),_T6=_T5,_T7=nMV(_6o),_T8=_T7,_T9=new T2(0,_SV,_SW),_Ta=B(_Pr(_T4,_T6,_T9,_6o,_)),_Tb=B(A(_Oy,[_5A,_3g,_3f,_SZ,_5M,function(_Tc,_){var _Td=E(E(_Tc).a),_Te=rMV(_T8),_Tf=B(_NU(_T4,_T6,_T9,_SY,_Td.a,_Td.b,_Te,_)),_=wMV(_T8,_Tf);return _5L;},_])),_Tg=B(A(_Oy,[_5A,_3g,_4P,_SZ,_5P,function(_Th,_){var _Ti=E(_Th),_Tj=rMV(_T8),_Tk=E(_Tj);if(!E(E(_Tk.e).c)){var _=wMV(_T8,_Tk);return _5L;}else{var _Tl=B(_P1(_)),_=wMV(_T8,_Tk);return _5L;}},_])),_Tm=function(_){var _Tn=rMV(_T8),_=wMV(_T8,new T(function(){var _To=E(_Tn),_Tp=E(_To.e);return new T6(0,E(_To.a),E(_To.b),E(_To.c),_To.d,E(new T5(0,E(_Tp.a),E(_Tp.b),E(_5N),E(_Tp.d),E(_Tp.e))),E(_To.f));}));return _5L;},_Tq=function(_Tr,_){var _Ts=E(_Tr),_Tt=rMV(_T8),_=wMV(_T8,new T(function(){var _Tu=E(_Tt),_Tv=E(_Tu.e);return new T6(0,E(_Tu.a),E(_Tu.b),E(_Tu.c),_Tu.d,E(new T5(0,E(_Tv.a),E(_Tv.b),E(_5Q),E(_Tv.d),E(_Tv.e))),E(_Tu.f));})),_Tw=B(A(_Sw,[_5A,_6p,_Tm,_]));return _5L;},_Tx=B(A(_Oy,[_5A,_3g,_4P,_SZ,_5O,_Tq,_]));return _5L;}}else{return new F(function(){return die(_6s);});}}else{return new F(function(){return die(_6s);});}},_Ty=function(_){return new F(function(){return _SU(_);});};
var hasteMain = function() {B(A(_Ty, [0]));};window.onload = hasteMain;