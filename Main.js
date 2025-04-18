"use strict";
var __haste_prog_id = 'd65e056c09df6f12044617d990e158b5dc288c40cea9de50ef19286fd853b00c';
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

var _0="deltaZ",_1="deltaY",_2="deltaX",_3=function(_4,_5){var _6=E(_4);return (_6._==0)?E(_5):new T2(1,_6.a,new T(function(){return B(_3(_6.b,_5));}));},_7=function(_8,_9){var _a=jsShowI(_8);return new F(function(){return _3(fromJSStr(_a),_9);});},_b=41,_c=40,_d=function(_e,_f,_g){if(_f>=0){return new F(function(){return _7(_f,_g);});}else{if(_e<=6){return new F(function(){return _7(_f,_g);});}else{return new T2(1,_c,new T(function(){var _h=jsShowI(_f);return B(_3(fromJSStr(_h),new T2(1,_b,_g)));}));}}},_i=new T(function(){return B(unCStr(")"));}),_j=new T(function(){return B(_d(0,2,_i));}),_k=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_j));}),_l=function(_m){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_d(0,_m,_k));}))));});},_n=function(_o,_){return new T(function(){var _p=Number(E(_o)),_q=jsTrunc(_p);if(_q<0){return B(_l(_q));}else{if(_q>2){return B(_l(_q));}else{return _q;}}});},_r=0,_s=new T3(0,_r,_r,_r),_t="button",_u=new T(function(){return eval("jsGetMouseCoords");}),_v=__Z,_w=function(_x,_){var _y=E(_x);if(!_y._){return _v;}else{var _z=B(_w(_y.b,_));return new T2(1,new T(function(){var _A=Number(E(_y.a));return jsTrunc(_A);}),_z);}},_B=function(_C,_){var _D=__arr2lst(0,_C);return new F(function(){return _w(_D,_);});},_E=function(_F,_){return new F(function(){return _B(E(_F),_);});},_G=function(_H,_){return new T(function(){var _I=Number(E(_H));return jsTrunc(_I);});},_J=new T2(0,_G,_E),_K=function(_L,_){var _M=E(_L);if(!_M._){return _v;}else{var _N=B(_K(_M.b,_));return new T2(1,_M.a,_N);}},_O=new T(function(){return B(unCStr("base"));}),_P=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Q=new T(function(){return B(unCStr("IOException"));}),_R=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_O,_P,_Q),_S=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_R,_v,_v),_T=function(_U){return E(_S);},_V=function(_W){return E(E(_W).a);},_X=function(_Y,_Z,_10){var _11=B(A1(_Y,_)),_12=B(A1(_Z,_)),_13=hs_eqWord64(_11.a,_12.a);if(!_13){return __Z;}else{var _14=hs_eqWord64(_11.b,_12.b);return (!_14)?__Z:new T1(1,_10);}},_15=function(_16){var _17=E(_16);return new F(function(){return _X(B(_V(_17.a)),_T,_17.b);});},_18=new T(function(){return B(unCStr(": "));}),_19=new T(function(){return B(unCStr(")"));}),_1a=new T(function(){return B(unCStr(" ("));}),_1b=new T(function(){return B(unCStr("interrupted"));}),_1c=new T(function(){return B(unCStr("system error"));}),_1d=new T(function(){return B(unCStr("unsatisified constraints"));}),_1e=new T(function(){return B(unCStr("user error"));}),_1f=new T(function(){return B(unCStr("permission denied"));}),_1g=new T(function(){return B(unCStr("illegal operation"));}),_1h=new T(function(){return B(unCStr("end of file"));}),_1i=new T(function(){return B(unCStr("resource exhausted"));}),_1j=new T(function(){return B(unCStr("resource busy"));}),_1k=new T(function(){return B(unCStr("does not exist"));}),_1l=new T(function(){return B(unCStr("already exists"));}),_1m=new T(function(){return B(unCStr("resource vanished"));}),_1n=new T(function(){return B(unCStr("timeout"));}),_1o=new T(function(){return B(unCStr("unsupported operation"));}),_1p=new T(function(){return B(unCStr("hardware fault"));}),_1q=new T(function(){return B(unCStr("inappropriate type"));}),_1r=new T(function(){return B(unCStr("invalid argument"));}),_1s=new T(function(){return B(unCStr("failed"));}),_1t=new T(function(){return B(unCStr("protocol error"));}),_1u=function(_1v,_1w){switch(E(_1v)){case 0:return new F(function(){return _3(_1l,_1w);});break;case 1:return new F(function(){return _3(_1k,_1w);});break;case 2:return new F(function(){return _3(_1j,_1w);});break;case 3:return new F(function(){return _3(_1i,_1w);});break;case 4:return new F(function(){return _3(_1h,_1w);});break;case 5:return new F(function(){return _3(_1g,_1w);});break;case 6:return new F(function(){return _3(_1f,_1w);});break;case 7:return new F(function(){return _3(_1e,_1w);});break;case 8:return new F(function(){return _3(_1d,_1w);});break;case 9:return new F(function(){return _3(_1c,_1w);});break;case 10:return new F(function(){return _3(_1t,_1w);});break;case 11:return new F(function(){return _3(_1s,_1w);});break;case 12:return new F(function(){return _3(_1r,_1w);});break;case 13:return new F(function(){return _3(_1q,_1w);});break;case 14:return new F(function(){return _3(_1p,_1w);});break;case 15:return new F(function(){return _3(_1o,_1w);});break;case 16:return new F(function(){return _3(_1n,_1w);});break;case 17:return new F(function(){return _3(_1m,_1w);});break;default:return new F(function(){return _3(_1b,_1w);});}},_1x=new T(function(){return B(unCStr("}"));}),_1y=new T(function(){return B(unCStr("{handle: "));}),_1z=function(_1A,_1B,_1C,_1D,_1E,_1F){var _1G=new T(function(){var _1H=new T(function(){var _1I=new T(function(){var _1J=E(_1D);if(!_1J._){return E(_1F);}else{var _1K=new T(function(){return B(_3(_1J,new T(function(){return B(_3(_19,_1F));},1)));},1);return B(_3(_1a,_1K));}},1);return B(_1u(_1B,_1I));}),_1L=E(_1C);if(!_1L._){return E(_1H);}else{return B(_3(_1L,new T(function(){return B(_3(_18,_1H));},1)));}}),_1M=E(_1E);if(!_1M._){var _1N=E(_1A);if(!_1N._){return E(_1G);}else{var _1O=E(_1N.a);if(!_1O._){var _1P=new T(function(){var _1Q=new T(function(){return B(_3(_1x,new T(function(){return B(_3(_18,_1G));},1)));},1);return B(_3(_1O.a,_1Q));},1);return new F(function(){return _3(_1y,_1P);});}else{var _1R=new T(function(){var _1S=new T(function(){return B(_3(_1x,new T(function(){return B(_3(_18,_1G));},1)));},1);return B(_3(_1O.a,_1S));},1);return new F(function(){return _3(_1y,_1R);});}}}else{return new F(function(){return _3(_1M.a,new T(function(){return B(_3(_18,_1G));},1));});}},_1T=function(_1U){var _1V=E(_1U);return new F(function(){return _1z(_1V.a,_1V.b,_1V.c,_1V.d,_1V.f,_v);});},_1W=function(_1X,_1Y,_1Z){var _20=E(_1Y);return new F(function(){return _1z(_20.a,_20.b,_20.c,_20.d,_20.f,_1Z);});},_21=function(_22,_23){var _24=E(_22);return new F(function(){return _1z(_24.a,_24.b,_24.c,_24.d,_24.f,_23);});},_25=44,_26=93,_27=91,_28=function(_29,_2a,_2b){var _2c=E(_2a);if(!_2c._){return new F(function(){return unAppCStr("[]",_2b);});}else{var _2d=new T(function(){var _2e=new T(function(){var _2f=function(_2g){var _2h=E(_2g);if(!_2h._){return E(new T2(1,_26,_2b));}else{var _2i=new T(function(){return B(A2(_29,_2h.a,new T(function(){return B(_2f(_2h.b));})));});return new T2(1,_25,_2i);}};return B(_2f(_2c.b));});return B(A2(_29,_2c.a,_2e));});return new T2(1,_27,_2d);}},_2j=function(_2k,_2l){return new F(function(){return _28(_21,_2k,_2l);});},_2m=new T3(0,_1W,_1T,_2j),_2n=new T(function(){return new T5(0,_T,_2m,_2o,_15,_1T);}),_2o=function(_2p){return new T2(0,_2n,_2p);},_2q=__Z,_2r=7,_2s=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2t=new T6(0,_2q,_2r,_v,_2s,_2q,_2q),_2u=new T(function(){return B(_2o(_2t));}),_2v=function(_){return new F(function(){return die(_2u);});},_2w=function(_2x){return E(E(_2x).a);},_2y=function(_2z,_2A,_2B,_){var _2C=__arr2lst(0,_2B),_2D=B(_K(_2C,_)),_2E=E(_2D);if(!_2E._){return new F(function(){return _2v(_);});}else{var _2F=E(_2E.b);if(!_2F._){return new F(function(){return _2v(_);});}else{if(!E(_2F.b)._){var _2G=B(A3(_2w,_2z,_2E.a,_)),_2H=B(A3(_2w,_2A,_2F.a,_));return new T2(0,_2G,_2H);}else{return new F(function(){return _2v(_);});}}}},_2I=function(_){return new F(function(){return __jsNull();});},_2J=function(_2K){var _2L=B(A1(_2K,_));return E(_2L);},_2M=new T(function(){return B(_2J(_2I));}),_2N=new T(function(){return E(_2M);}),_2O=function(_2P,_2Q,_){if(E(_2P)==7){var _2R=__app1(E(_u),_2Q),_2S=B(_2y(_J,_J,_2R,_)),_2T=__get(_2Q,E(_2)),_2U=__get(_2Q,E(_1)),_2V=__get(_2Q,E(_0));return new T(function(){return new T3(0,E(_2S),E(_2q),E(new T3(0,_2T,_2U,_2V)));});}else{var _2W=__app1(E(_u),_2Q),_2X=B(_2y(_J,_J,_2W,_)),_2Y=__get(_2Q,E(_t)),_2Z=__eq(_2Y,E(_2N));if(!E(_2Z)){var _30=__isUndef(_2Y);if(!E(_30)){var _31=B(_n(_2Y,_));return new T(function(){return new T3(0,E(_2X),E(new T1(1,_31)),E(_s));});}else{return new T(function(){return new T3(0,E(_2X),E(_2q),E(_s));});}}else{return new T(function(){return new T3(0,E(_2X),E(_2q),E(_s));});}}},_32=function(_33,_34,_){return new F(function(){return _2O(_33,E(_34),_);});},_35="mouseout",_36="mouseover",_37="mousemove",_38="mouseup",_39="mousedown",_3a="dblclick",_3b="click",_3c="wheel",_3d=function(_3e){switch(E(_3e)){case 0:return E(_3b);case 1:return E(_3a);case 2:return E(_39);case 3:return E(_38);case 4:return E(_37);case 5:return E(_36);case 6:return E(_35);default:return E(_3c);}},_3f=new T2(0,_3d,_32),_3g=function(_3h){return E(_3h);},_3i=function(_3j,_3k){return E(_3j)==E(_3k);},_3l=function(_3m,_3n){return E(_3m)!=E(_3n);},_3o=new T2(0,_3i,_3l),_3p="screenY",_3q="screenX",_3r="clientY",_3s="clientX",_3t="pageY",_3u="pageX",_3v="target",_3w="identifier",_3x=function(_3y,_){var _3z=__get(_3y,E(_3w)),_3A=__get(_3y,E(_3v)),_3B=__get(_3y,E(_3u)),_3C=__get(_3y,E(_3t)),_3D=__get(_3y,E(_3s)),_3E=__get(_3y,E(_3r)),_3F=__get(_3y,E(_3q)),_3G=__get(_3y,E(_3p));return new T(function(){var _3H=Number(_3z),_3I=jsTrunc(_3H);return new T5(0,_3I,_3A,E(new T2(0,new T(function(){var _3J=Number(_3B);return jsTrunc(_3J);}),new T(function(){var _3K=Number(_3C);return jsTrunc(_3K);}))),E(new T2(0,new T(function(){var _3L=Number(_3D);return jsTrunc(_3L);}),new T(function(){var _3M=Number(_3E);return jsTrunc(_3M);}))),E(new T2(0,new T(function(){var _3N=Number(_3F);return jsTrunc(_3N);}),new T(function(){var _3O=Number(_3G);return jsTrunc(_3O);}))));});},_3P=function(_3Q,_){var _3R=E(_3Q);if(!_3R._){return _v;}else{var _3S=B(_3x(E(_3R.a),_)),_3T=B(_3P(_3R.b,_));return new T2(1,_3S,_3T);}},_3U="touches",_3V=function(_3W){return E(E(_3W).b);},_3X=function(_3Y,_3Z,_){var _40=__arr2lst(0,_3Z),_41=new T(function(){return B(_3V(_3Y));}),_42=function(_43,_){var _44=E(_43);if(!_44._){return _v;}else{var _45=B(A2(_41,_44.a,_)),_46=B(_42(_44.b,_));return new T2(1,_45,_46);}};return new F(function(){return _42(_40,_);});},_47=function(_48,_){return new F(function(){return _3X(_J,E(_48),_);});},_49=new T2(0,_E,_47),_4a=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4b=function(_4c){return E(E(_4c).a);},_4d=function(_4e,_4f,_4g){while(1){var _4h=E(_4g);if(!_4h._){return false;}else{if(!B(A3(_4b,_4e,_4f,_4h.a))){_4g=_4h.b;continue;}else{return true;}}}},_4i=function(_4j,_4k){while(1){var _4l=B((function(_4m,_4n){var _4o=E(_4n);if(!_4o._){return __Z;}else{var _4p=_4o.a,_4q=_4o.b;if(!B(A1(_4m,_4p))){var _4r=_4m;_4j=_4r;_4k=_4q;return __continue;}else{return new T2(1,_4p,new T(function(){return B(_4i(_4m,_4q));}));}}})(_4j,_4k));if(_4l!=__continue){return _4l;}}},_4s=function(_4t,_){var _4u=__get(_4t,E(_3U)),_4v=__arr2lst(0,_4u),_4w=B(_3P(_4v,_)),_4x=__app1(E(_4a),_4t),_4y=B(_2y(_49,_49,_4x,_)),_4z=E(_4y),_4A=new T(function(){var _4B=function(_4C){return new F(function(){return _4d(_3o,new T(function(){return E(_4C).a;}),_4z.a);});};return B(_4i(_4B,_4w));}),_4D=new T(function(){var _4E=function(_4F){return new F(function(){return _4d(_3o,new T(function(){return E(_4F).a;}),_4z.b);});};return B(_4i(_4E,_4w));});return new T3(0,_4w,_4D,_4A);},_4G=function(_4H,_4I,_){return new F(function(){return _4s(E(_4I),_);});},_4J="touchcancel",_4K="touchend",_4L="touchmove",_4M="touchstart",_4N=function(_4O){switch(E(_4O)){case 0:return E(_4M);case 1:return E(_4L);case 2:return E(_4K);default:return E(_4J);}},_4P=new T2(0,_4N,_4G),_4Q=function(_4R,_4S,_){var _4T=B(A1(_4R,_)),_4U=B(A1(_4S,_));return _4T;},_4V=function(_4W,_4X,_){var _4Y=B(A1(_4W,_)),_4Z=B(A1(_4X,_));return new T(function(){return B(A1(_4Y,_4Z));});},_50=function(_51,_52,_){var _53=B(A1(_52,_));return _51;},_54=function(_55,_56,_){var _57=B(A1(_56,_));return new T(function(){return B(A1(_55,_57));});},_58=new T2(0,_54,_50),_59=function(_5a,_){return _5a;},_5b=function(_5c,_5d,_){var _5e=B(A1(_5c,_));return new F(function(){return A1(_5d,_);});},_5f=new T5(0,_58,_59,_4V,_5b,_4Q),_5g=new T(function(){return E(_2n);}),_5h=function(_5i){return E(E(_5i).c);},_5j=function(_5k){return new T6(0,_2q,_2r,_v,_5k,_2q,_2q);},_5l=function(_5m,_){var _5n=new T(function(){return B(A2(_5h,_5g,new T(function(){return B(A1(_5j,_5m));})));});return new F(function(){return die(_5n);});},_5o=function(_5p,_){return new F(function(){return _5l(_5p,_);});},_5q=function(_5r){return new F(function(){return A1(_5o,_5r);});},_5s=function(_5t,_5u,_){var _5v=B(A1(_5t,_));return new F(function(){return A2(_5u,_5v,_);});},_5w=new T5(0,_5f,_5s,_5b,_59,_5q),_5x=function(_5y){return E(_5y);},_5z=new T2(0,_5w,_5x),_5A=new T2(0,_5z,_59),_5B=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_5C=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_5D=new T(function(){return eval("(function(cv){return cv.height})");}),_5E=new T(function(){return eval("(function(cv){return cv.width})");}),_5F=function(_5G,_){var _5H=__app1(E(_5E),_5G),_5I=__app1(E(_5D),_5G),_5J=__app1(E(_5C),_5G),_5K=__app1(E(_5B),_5G);return new T2(0,new T2(0,_5H,_5I),new T2(0,_5J,_5K));},_5L=0,_5M=0,_5N=false,_5O=2,_5P=0,_5Q=true,_5R=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_5S=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_5T=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_5U=function(_5V){return E(E(_5V).b);},_5W=function(_5X,_5Y){return new F(function(){return A2(_5U,_5X,function(_){var _5Z=E(_5Y),_60=__app1(E(_5T),_5Z);if(!_60){return _2q;}else{var _61=__app1(E(_5S),_5Z);return new T1(1,new T2(0,_61,_5Z));}});});},_62=2,_63=1,_64=new T1(0,_63),_65=new T1(1,_64),_66=30,_67=100,_68=new T2(0,_67,_66),_69=new T2(1,_68,_v),_6a=370,_6b=200,_6c=80,_6d=new T4(0,_6c,_67,_6b,_6a),_6e=0,_6f=new T2(1,_6e,_v),_6g=new T(function(){return B(unCStr("\u3053\u3093\u306b\u3061\u306f\n\u5143\u6c23\u3067\u3059\u304b\uff1f"));}),_6h=new T2(1,_6g,_v),_6i=new T2(1,_63,_v),_6j=20,_6k=new T2(1,_6j,_v),_6l={_:0,a:0,b:E(_6d),c:E(_62),d:0,e:5,f:E(_69),g:E(_v),h:E(_6k),i:E(_6i),j:E(_6h),k:E(_6f),l:E(_v),m:E(_v),n:E(_2q),o:E(_65)},_6m=new T2(1,_6l,_v),_6n=new T5(0,E(_5N),E(_5N),E(_5N),E(_5N),E(_5N)),_6o=new T6(0,E(_2q),E(_2q),E(_6m),0,E(_6n),E(_v)),_6p=new T1(0,100),_6q=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:16:3-9"));}),_6r=new T6(0,_2q,_2r,_v,_6q,_2q,_2q),_6s=new T(function(){return B(_2o(_6r));}),_6t=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:17:3-8"));}),_6u=new T6(0,_2q,_2r,_v,_6t,_2q,_2q),_6v=new T(function(){return B(_2o(_6u));}),_6w=function(_6x,_6y,_6z){while(1){var _6A=E(_6z);if(!_6A._){return  -1;}else{var _6B=_6A.b,_6C=E(_6A.a),_6D=E(_6C.b),_6E=E(_6D.a);if(_6x<=_6E){_6z=_6B;continue;}else{if(_6x>=_6E+E(_6D.c)){_6z=_6B;continue;}else{var _6F=E(_6D.b);if(_6y<=_6F){_6z=_6B;continue;}else{if(_6y>=_6F+E(_6D.d)){_6z=_6B;continue;}else{return E(_6C.a);}}}}}}},_6G=function(_6H,_6I,_6J){while(1){var _6K=E(_6J);if(!_6K._){return  -1;}else{var _6L=_6K.b,_6M=E(_6K.a),_6N=E(_6M.b),_6O=E(_6N.a);if(_6H<=_6O){_6J=_6L;continue;}else{if(_6H>=_6O+E(_6N.c)){_6J=_6L;continue;}else{var _6P=E(_6I),_6Q=E(_6N.b);if(_6P<=_6Q){return new F(function(){return _6w(_6H,_6P,_6L);});}else{if(_6P>=_6Q+E(_6N.d)){return new F(function(){return _6w(_6H,_6P,_6L);});}else{return E(_6M.a);}}}}}}},_6R=function(_6S,_6T){while(1){var _6U=E(_6T);if(!_6U._){return __Z;}else{var _6V=E(_6U.a);if(_6S!=_6V.a){_6T=_6U.b;continue;}else{return new T1(1,_6V);}}}},_6W=function(_6X,_6Y){var _6Z=E(_6X);if(!_6Z._){var _70=E(_6Y);if(!_70._){return new F(function(){return _3i(_6Z.a,_70.a);});}else{return false;}}else{var _71=E(_6Y);if(!_71._){return false;}else{return new F(function(){return _3i(_6Z.a,_71.a);});}}},_72=function(_73,_74){return (E(_73)==0)?(E(_74)==0)?false:true:(E(_74)==0)?true:false;},_75=function(_76,_77){return (E(_76)==0)?(E(_77)==0)?true:false:(E(_77)==0)?false:true;},_78=new T2(0,_75,_72),_79=function(_7a,_7b,_7c){while(1){var _7d=E(_7b);if(!_7d._){return (E(_7c)._==0)?true:false;}else{var _7e=E(_7c);if(!_7e._){return false;}else{if(!B(A3(_4b,_7a,_7d.a,_7e.a))){return false;}else{_7b=_7d.b;_7c=_7e.b;continue;}}}}},_7f=function(_7g,_7h){while(1){var _7i=E(_7g);if(!_7i._){return (E(_7h)._==0)?true:false;}else{var _7j=E(_7h);if(!_7j._){return false;}else{if(E(_7i.a)!=E(_7j.a)){return false;}else{_7g=_7i.b;_7h=_7j.b;continue;}}}}},_7k=function(_7l,_7m){while(1){var _7n=E(_7l);if(!_7n._){return (E(_7m)._==0)?true:false;}else{var _7o=E(_7m);if(!_7o._){return false;}else{if(E(_7n.a)!=E(_7o.a)){return false;}else{_7l=_7n.b;_7m=_7o.b;continue;}}}}},_7p=function(_7q,_7r){while(1){var _7s=E(_7q);if(!_7s._){return (E(_7r)._==0)?true:false;}else{var _7t=E(_7r);if(!_7t._){return false;}else{if(!B(_7k(_7s.a,_7t.a))){return false;}else{_7q=_7s.b;_7r=_7t.b;continue;}}}}},_7u=function(_7v,_7w,_7x,_7y){return (_7v!=_7x)?true:(E(_7w)!=E(_7y))?true:false;},_7z=function(_7A,_7B){var _7C=E(_7A),_7D=E(_7B);return new F(function(){return _7u(E(_7C.a),_7C.b,E(_7D.a),_7D.b);});},_7E=function(_7F,_7G){return E(_7F)==E(_7G);},_7H=function(_7I,_7J,_7K,_7L){if(_7I!=_7K){return false;}else{return new F(function(){return _7E(_7J,_7L);});}},_7M=function(_7N,_7O){var _7P=E(_7N),_7Q=E(_7O);return new F(function(){return _7H(E(_7P.a),_7P.b,E(_7Q.a),_7Q.b);});},_7R=new T2(0,_7M,_7z),_7S=function(_7T,_7U,_7V,_7W,_7X,_7Y,_7Z,_80,_81,_82,_83,_84,_85,_86,_87,_88,_89,_8a,_8b,_8c,_8d,_8e,_8f,_8g,_8h,_8i,_8j,_8k,_8l,_8m,_8n,_8o,_8p,_8q,_8r,_8s){if(_7T!=_8b){return false;}else{if(E(_7U)!=E(_8c)){return false;}else{if(E(_7V)!=E(_8d)){return false;}else{if(E(_7W)!=E(_8e)){return false;}else{if(E(_7X)!=E(_8f)){return false;}else{var _8t=function(_8u){if(!B(_79(_7R,_81,_8j))){return false;}else{if(!B(_79(_7R,_82,_8k))){return false;}else{if(!B(_7f(_83,_8l))){return false;}else{if(!B(_7f(_84,_8m))){return false;}else{if(!B(_7p(_85,_8n))){return false;}else{if(!B(_79(_78,_86,_8o))){return false;}else{if(!B(_79(_7R,_87,_8p))){return false;}else{if(!B(_7f(_88,_8q))){return false;}else{var _8v=function(_8w){var _8x=E(_8a);switch(_8x._){case 0:return (E(_8s)._==0)?true:false;case 1:var _8y=E(_8s);if(_8y._==1){return new F(function(){return _6W(_8x.a,_8y.a);});}else{return false;}break;case 2:var _8z=E(_8s);if(_8z._==2){return new F(function(){return _3i(_8x.a,_8z.a);});}else{return false;}break;default:var _8A=E(_8s);if(_8A._==3){return new F(function(){return _3i(_8x.a,_8A.a);});}else{return false;}}},_8B=E(_89);if(!_8B._){if(!E(_8r)._){return new F(function(){return _8v(_);});}else{return false;}}else{var _8C=E(_8r);if(!_8C._){return false;}else{if(E(_8B.a)!=E(_8C.a)){return false;}else{return new F(function(){return _8v(_);});}}}}}}}}}}}};switch(E(_7Y)){case 0:if(!E(_8g)){if(_7Z!=_8h){return false;}else{if(_80!=_8i){return false;}else{return new F(function(){return _8t(_);});}}}else{return false;}break;case 1:if(E(_8g)==1){if(_7Z!=_8h){return false;}else{if(_80!=_8i){return false;}else{return new F(function(){return _8t(_);});}}}else{return false;}break;default:if(E(_8g)==2){if(_7Z!=_8h){return false;}else{if(_80!=_8i){return false;}else{return new F(function(){return _8t(_);});}}}else{return false;}}}}}}}},_8D=function(_8E,_8F){var _8G=E(_8E),_8H=E(_8G.b),_8I=E(_8F),_8J=E(_8I.b);return (!B(_7S(_8G.a,_8H.a,_8H.b,_8H.c,_8H.d,_8G.c,_8G.d,_8G.e,_8G.f,_8G.g,_8G.h,_8G.i,_8G.j,_8G.k,_8G.l,_8G.m,_8G.n,_8G.o,_8I.a,_8J.a,_8J.b,_8J.c,_8J.d,_8I.c,_8I.d,_8I.e,_8I.f,_8I.g,_8I.h,_8I.i,_8I.j,_8I.k,_8I.l,_8I.m,_8I.n,_8I.o)))?true:false;},_8K=function(_8L,_8M){var _8N=E(_8L),_8O=E(_8N.b),_8P=E(_8M),_8Q=E(_8P.b);return new F(function(){return _7S(_8N.a,_8O.a,_8O.b,_8O.c,_8O.d,_8N.c,_8N.d,_8N.e,_8N.f,_8N.g,_8N.h,_8N.i,_8N.j,_8N.k,_8N.l,_8N.m,_8N.n,_8N.o,_8P.a,_8Q.a,_8Q.b,_8Q.c,_8Q.d,_8P.c,_8P.d,_8P.e,_8P.f,_8P.g,_8P.h,_8P.i,_8P.j,_8P.k,_8P.l,_8P.m,_8P.n,_8P.o);});},_8R=new T2(0,_8K,_8D),_8S=function(_8T,_8U){while(1){var _8V=E(_8T);if(!_8V._){return (E(_8U)._==0)?true:false;}else{var _8W=E(_8U);if(!_8W._){return false;}else{if(E(_8V.a)!=E(_8W.a)){return false;}else{_8T=_8V.b;_8U=_8W.b;continue;}}}}},_8X=function(_8Y,_8Z,_90,_91,_92,_93,_94,_95,_96,_97,_98,_99,_9a,_9b,_9c,_9d,_9e,_9f,_9g,_9h){var _9i=function(_9j){var _9k=function(_9l){if(_91!=_9b){return false;}else{var _9m=function(_9n){var _9o=function(_9p){var _9q=function(_9r){return (!E(_95))?(!E(_9f))?(!E(_96))?(!E(_9g))?true:false:E(_9g):false:(!E(_9f))?false:(!E(_96))?(!E(_9g))?true:false:E(_9g);};if(!E(_94)){if(!E(_9e)){return new F(function(){return _9q(_);});}else{return false;}}else{if(!E(_9e)){return false;}else{return new F(function(){return _9q(_);});}}};if(!E(_93)){if(!E(_9d)){return new F(function(){return _9o(_);});}else{return false;}}else{if(!E(_9d)){return false;}else{return new F(function(){return _9o(_);});}}};if(!E(_92)){if(!E(_9c)){if(!B(_9m(_))){return false;}else{return new F(function(){return _8S(_97,_9h);});}}else{return false;}}else{if(!E(_9c)){return false;}else{if(!B(_9m(_))){return false;}else{return new F(function(){return _8S(_97,_9h);});}}}}},_9s=E(_8Z);if(!_9s._){if(!E(_99)._){if(!B(_79(_8R,_90,_9a))){return false;}else{return new F(function(){return _9k(_);});}}else{return false;}}else{var _9t=E(_99);if(!_9t._){return false;}else{var _9u=E(_9s.a),_9v=E(_9t.a);if(!B(_7p(_9u.a,_9v.a))){return false;}else{if(!B(_7f(_9u.b,_9v.b))){return false;}else{if(_9u.c!=_9v.c){return false;}else{if(!B(_79(_8R,_90,_9a))){return false;}else{return new F(function(){return _9k(_);});}}}}}}},_9w=E(_8Y);if(!_9w._){if(!E(_98)._){return new F(function(){return _9i(_);});}else{return false;}}else{var _9x=E(_98);if(!_9x._){return false;}else{var _9y=_9x.a,_9z=E(_9w.a);if(!_9z._){var _9A=E(_9y);if(!_9A._){if(E(_9z.a)!=E(_9A.a)){return false;}else{return new F(function(){return _9i(_);});}}else{return false;}}else{var _9B=E(_9y);if(!_9B._){return false;}else{if(E(_9z.a)!=E(_9B.a)){return false;}else{return new F(function(){return _9i(_);});}}}}}},_9C=function(_9D,_9E){while(1){var _9F=E(_9D);if(!_9F._){return E(_9E);}else{var _9G=_9E+1|0;_9D=_9F.b;_9E=_9G;continue;}}},_9H=function(_9I,_9J){while(1){var _9K=E(_9I);if(!_9K._){return E(_9J);}else{_9I=_9K.b;_9J=_9K.a;continue;}}},_9L=function(_9M,_9N,_9O){return new F(function(){return _9H(_9N,_9M);});},_9P=new T(function(){return B(unCStr("!!: negative index"));}),_9Q=new T(function(){return B(unCStr("Prelude."));}),_9R=new T(function(){return B(_3(_9Q,_9P));}),_9S=new T(function(){return B(err(_9R));}),_9T=new T(function(){return B(unCStr("!!: index too large"));}),_9U=new T(function(){return B(_3(_9Q,_9T));}),_9V=new T(function(){return B(err(_9U));}),_9W=function(_9X,_9Y){while(1){var _9Z=E(_9X);if(!_9Z._){return E(_9V);}else{var _a0=E(_9Y);if(!_a0){return E(_9Z.a);}else{_9X=_9Z.b;_9Y=_a0-1|0;continue;}}}},_a1=function(_a2,_a3){if(_a3>=0){return new F(function(){return _9W(_a2,_a3);});}else{return E(_9S);}},_a4=function(_a5,_a6){while(1){var _a7=E(_a6);if(!_a7._){return __Z;}else{var _a8=_a7.b,_a9=E(_a5);if(_a9==1){return E(_a8);}else{_a5=_a9-1|0;_a6=_a8;continue;}}}},_aa=function(_ab,_ac,_ad){var _ae=new T2(1,_ab,new T(function(){var _af=_ac+1|0;if(_af>0){return B(_a4(_af,_ad));}else{return E(_ad);}}));if(0>=_ac){return E(_ae);}else{var _ag=function(_ah,_ai){var _aj=E(_ah);if(!_aj._){return E(_ae);}else{var _ak=_aj.a,_al=E(_ai);return (_al==1)?new T2(1,_ak,_ae):new T2(1,_ak,new T(function(){return B(_ag(_aj.b,_al-1|0));}));}};return new F(function(){return _ag(_ad,_ac);});}},_am=__Z,_an=function(_ao,_ap){while(1){var _aq=E(_ao);if(!_aq._){return E(_ap);}else{_ao=_aq.b;_ap=_aq.a;continue;}}},_ar=function(_as,_at){var _au=E(_at);return (_au._==0)?__Z:new T2(1,_as,new T(function(){return B(_ar(_au.a,_au.b));}));},_av=new T(function(){return B(unCStr(": empty list"));}),_aw=function(_ax){return new F(function(){return err(B(_3(_9Q,new T(function(){return B(_3(_ax,_av));},1))));});},_ay=new T(function(){return B(unCStr("init"));}),_az=new T(function(){return B(_aw(_ay));}),_aA=new T(function(){return B(unCStr("last"));}),_aB=new T(function(){return B(_aw(_aA));}),_aC=new T(function(){return B(unCStr("base"));}),_aD=new T(function(){return B(unCStr("Control.Exception.Base"));}),_aE=new T(function(){return B(unCStr("PatternMatchFail"));}),_aF=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_aC,_aD,_aE),_aG=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_aF,_v,_v),_aH=function(_aI){return E(_aG);},_aJ=function(_aK){var _aL=E(_aK);return new F(function(){return _X(B(_V(_aL.a)),_aH,_aL.b);});},_aM=function(_aN){return E(E(_aN).a);},_aO=function(_aP){return new T2(0,_aQ,_aP);},_aR=function(_aS,_aT){return new F(function(){return _3(E(_aS).a,_aT);});},_aU=function(_aV,_aW){return new F(function(){return _28(_aR,_aV,_aW);});},_aX=function(_aY,_aZ,_b0){return new F(function(){return _3(E(_aZ).a,_b0);});},_b1=new T3(0,_aX,_aM,_aU),_aQ=new T(function(){return new T5(0,_aH,_b1,_aO,_aJ,_aM);}),_b2=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_b3=function(_b4,_b5){return new F(function(){return die(new T(function(){return B(A2(_5h,_b5,_b4));}));});},_b6=function(_b7,_b8){return new F(function(){return _b3(_b7,_b8);});},_b9=function(_ba,_bb){var _bc=E(_bb);if(!_bc._){return new T2(0,_v,_v);}else{var _bd=_bc.a;if(!B(A1(_ba,_bd))){return new T2(0,_v,_bc);}else{var _be=new T(function(){var _bf=B(_b9(_ba,_bc.b));return new T2(0,_bf.a,_bf.b);});return new T2(0,new T2(1,_bd,new T(function(){return E(E(_be).a);})),new T(function(){return E(E(_be).b);}));}}},_bg=32,_bh=new T(function(){return B(unCStr("\n"));}),_bi=function(_bj){return (E(_bj)==124)?false:true;},_bk=function(_bl,_bm){var _bn=B(_b9(_bi,B(unCStr(_bl)))),_bo=_bn.a,_bp=function(_bq,_br){var _bs=new T(function(){var _bt=new T(function(){return B(_3(_bm,new T(function(){return B(_3(_br,_bh));},1)));});return B(unAppCStr(": ",_bt));},1);return new F(function(){return _3(_bq,_bs);});},_bu=E(_bn.b);if(!_bu._){return new F(function(){return _bp(_bo,_v);});}else{if(E(_bu.a)==124){return new F(function(){return _bp(_bo,new T2(1,_bg,_bu.b));});}else{return new F(function(){return _bp(_bo,_v);});}}},_bv=function(_bw){return new F(function(){return _b6(new T1(0,new T(function(){return B(_bk(_bw,_b2));})),_aQ);});},_bx=new T(function(){return B(_bv("Events.hs:80:7-27|(hco : tlCos)"));}),_by=40,_bz=new T2(1,_by,_v),_bA=new T(function(){return B(unCStr("\u305b\u3044\u304b\u3044\uff01"));}),_bB=new T2(1,_bA,_v),_bC=1,_bD=new T1(0,_bC),_bE=new T(function(){return B(unCStr("\u306f"));}),_bF=new T(function(){return B(unCStr("\u3065"));}),_bG=new T(function(){return B(unCStr("\u308c"));}),_bH=new T2(1,_bG,_v),_bI=new T2(1,_bF,_bH),_bJ=new T2(1,_bE,_bI),_bK=120,_bL=function(_bM,_bN,_bO,_bP,_bQ,_bR,_bS,_bT){var _bU=function(_bV){if(_bV!=_bN){var _bW=new T(function(){var _bX=E(_bQ);if(!_bX._){return E(_bx);}else{return new T2(0,_bX.a,_bX.b);}}),_bY=new T(function(){var _bZ=function(_c0){var _c1=new T(function(){return E(E(_bW).b);}),_c2=new T(function(){var _c3=B(_an(_c1,_aB));return {_:0,a:_c3.a,b:E(_c3.b),c:E(_c3.c),d:_c3.d,e:_c3.e,f:E(_c3.f),g:E(_c3.g),h:E(_c3.h),i:E(_c3.i),j:E(_bJ),k:E(_c3.k),l:E(_c3.l),m:E(_c3.m),n:E(_c3.n),o:E(new T1(1,new T(function(){var _c4=E(_bO);if(!_c4._){return E(_bD);}else{return E(_c4.a);}})))};}),_c5=function(_c6){var _c7=E(_c6);return (_c7._==0)?E(new T2(1,_c2,_v)):new T2(1,new T(function(){var _c8=E(_c7.a);return {_:0,a:_c8.a,b:E(_c8.b),c:E(_c8.c),d:_c8.d,e:_c8.e,f:E(_c8.f),g:E(_c8.g),h:E(_c8.h),i:E(_c8.i),j:E(_c8.j),k:E(_c8.k),l:E(_c8.l),m:E(_c8.m),n:E(_c8.n),o:E(_am)};}),new T(function(){return B(_c5(_c7.b));}));},_c9=new T(function(){var _ca=E(_c1);if(!_ca._){return E(_az);}else{return B(_ar(_ca.a,_ca.b));}}),_cb=new T(function(){return B(_aa(new T(function(){var _cc=B(_a1(_c9,_bN));return {_:0,a:_cc.a,b:E(_cc.b),c:E(_cc.c),d:3,e:_cc.e,f:E(_cc.f),g:E(_cc.g),h:E(_cc.h),i:E(_cc.i),j:E(_cc.j),k:E(_cc.k),l:E(_cc.l),m:E(_cc.m),n:E(_cc.n),o:E(_cc.o)};}),_bN,_c9));});return new F(function(){return _c5(B(_aa(new T(function(){var _cd=B(_a1(_c9,_c0));return {_:0,a:_cd.a,b:E(_cd.b),c:E(_cd.c),d:4,e:_cd.e,f:E(_cd.f),g:E(_cd.g),h:E(_cd.h),i:E(_cd.i),j:E(_cd.j),k:E(_cd.k),l:E(_cd.l),m:E(_cd.m),n:E(_cd.n),o:E(_cd.o)};}),_c0,_cb)));});},_ce=E(_bP);if(!_ce._){return B(_bZ(0));}else{return B(_bZ(E(_ce.a).c));}});return new T6(0,_bO,_bP,new T2(1,new T(function(){return E(E(_bW).a);}),_bY),_bR,_bS,_bT);}else{var _cf=E(_bM),_cg=_cf.a,_ch=_cf.b,_ci=E(_bQ);if(!_ci._){var _cj=E(_az);}else{var _ck=_ci.a,_cl=_ci.b,_cm=new T(function(){var _cn=B(_9L(_ck,_cl,_aB)),_co=new T(function(){return E(_cg)/3;}),_cp=new T(function(){return E(_ch)/6;}),_cq=new T(function(){var _cr=E(_bO);if(!_cr._){return E(_bD);}else{var _cs=E(_cr.a);if(!_cs._){return new T1(0,new T(function(){return E(_cs.a)+1|0;}));}else{return new T1(1,new T(function(){return E(_cs.a)+1|0;}));}}});return {_:0,a:_cn.a,b:E(new T4(0,_co,_cp,new T(function(){var _ct=E(_co);return E(_cg)-(_ct+_ct);}),new T(function(){var _cu=E(_cp);return E(_ch)-(_cu+_cu);}))),c:E(_cn.c),d:_cn.d,e:_cn.e,f:E(new T2(1,new T2(0,new T(function(){return E(_cg)/2-E(_co)-20;}),_bK),_v)),g:E(_cn.g),h:E(_bz),i:E(_cn.i),j:E(_bB),k:E(_cn.k),l:E(_cn.l),m:E(_cn.m),n:E(_cn.n),o:E(new T1(1,_cq))};}),_cv=function(_cw){var _cx=E(_cw);return (_cx._==0)?E(new T2(1,_cm,_v)):new T2(1,new T(function(){var _cy=E(_cx.a);return {_:0,a:_cy.a,b:E(_cy.b),c:E(_cy.c),d:_cy.d,e:_cy.e,f:E(_cy.f),g:E(_cy.g),h:E(_cy.h),i:E(_cy.i),j:E(_cy.j),k:E(_cy.k),l:E(_cy.l),m:E(_cy.m),n:E(_cy.n),o:E(_am)};}),new T(function(){return B(_cv(_cx.b));}));},_cj=B(_cv(B(_ar(_ck,_cl))));}return new T6(0,_bO,_bP,_cj,_bR,_bS,_bT);}},_cz=E(_bP);if(!_cz._){return new F(function(){return _bU(0);});}else{return new F(function(){return _bU(E(_cz.a).c);});}},_cA=new T2(1,_6e,_v),_cB=new T2(1,_6e,_cA),_cC=new T2(1,_6e,_cB),_cD=5,_cE=new T2(1,_cD,_v),_cF=new T2(1,_cD,_cE),_cG=new T2(1,_cD,_cF),_cH=50,_cI=new T2(1,_cH,_v),_cJ=new T2(1,_cH,_cI),_cK=new T2(1,_cH,_cJ),_cL=new T(function(){return B(unCStr("\u3075"));}),_cM=new T2(1,_cL,_v),_cN=new T(function(){return B(unCStr("\u305f"));}),_cO=new T2(1,_cN,_cM),_cP=new T(function(){return B(unCStr("\u3053"));}),_cQ=new T2(1,_cP,_cO),_cR=50,_cS=function(_cT,_cU,_cV,_cW){var _cX=new T(function(){return E(_cT)/8*3-20;}),_cY=new T(function(){return E(_cT)/8;});return {_:0,a:_cV,b:E(new T4(0,_cY,new T(function(){var _cZ=E(_cU);return _cZ-_cZ/6;}),new T(function(){var _d0=E(_cY);return E(_cT)-(_d0+_d0);}),new T(function(){return E(_cU)/8;}))),c:E(_62),d:1,e:6,f:E(new T2(1,new T2(0,new T(function(){return E(_cX)-50;}),_cR),new T2(1,new T2(0,_cX,_cR),new T2(1,new T2(0,new T(function(){return E(_cX)+50;}),_cR),_v)))),g:E(_v),h:E(_cK),i:E(_cG),j:E(_cQ),k:E(_cC),l:E(_v),m:E(_v),n:E(_2q),o:E(new T1(3,_cW))};},_d1=function(_d2){var _d3=E(_d2);return {_:0,a:_d3.a,b:E(_d3.b),c:E(_d3.c),d:0,e:_d3.e,f:E(_d3.f),g:E(_d3.g),h:E(_d3.h),i:E(_d3.i),j:E(_d3.j),k:E(_d3.k),l:E(_d3.l),m:E(_d3.m),n:E(_d3.n),o:E(_d3.o)};},_d4=new T(function(){return B(_bv("Events.hs:27:7-27|(hco : chCos)"));}),_d5=function(_d6,_d7){var _d8=E(_d7);return (_d8._==0)?__Z:new T2(1,new T(function(){return B(A1(_d6,_d8.a));}),new T(function(){return B(_d5(_d6,_d8.b));}));},_d9=function(_da,_db,_dc,_dd,_de,_df,_dg,_dh,_di){var _dj=new T(function(){var _dk=E(_df);if(!_dk._){return E(_d4);}else{return new T2(0,_dk.a,_dk.b);}}),_dl=new T(function(){var _dm=function(_dn){var _do=E(_dc),_dp=new T(function(){return E(E(_dj).b);}),_dq=B(_aa(new T(function(){var _dr=B(_a1(_dp,_do));return {_:0,a:_dr.a,b:E(_dr.b),c:E(_dr.c),d:4,e:_dr.e,f:E(_dr.f),g:E(_dr.g),h:E(_dr.h),i:E(_dr.i),j:E(_dr.j),k:E(_dr.k),l:E(_dr.l),m:E(_dr.m),n:E(_dr.n),o:E(_dr.o)};}),_do,new T(function(){return B(_d5(_d1,_dp));})));if((_dn+1|0)!=E(_db)){var _ds=E(_dq);if(!_ds._){return E(_az);}else{return new F(function(){return _3(B(_ar(_ds.a,_ds.b)),new T2(1,new T(function(){var _dt=E(_da);return B(_cS(_dt.a,_dt.b,_dn+1|0,_do));}),_v));});}}else{return new F(function(){return _3(_dq,new T2(1,new T(function(){var _du=E(_da);return B(_cS(_du.a,_du.b,_dn+1|0,_do));}),_v));});}},_dv=E(_de);if(!_dv._){return B(_dm(0));}else{return B(_dm(B(_9C(E(_dv.a).a,0))));}});return new T6(0,_dd,_de,new T2(1,new T(function(){return E(E(_dj).a);}),_dl),_dg,_dh,_di);},_dw=new T(function(){return eval("(function(e){e.width = e.width;})");}),_dx=function(_){return _5L;},_dy=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_dz=function(_dA,_dB,_dC){var _dD=new T(function(){return toJSStr(E(_dC));});return function(_dE,_){var _dF=__app4(E(_dy),E(_dE),E(_dD),E(_dA),E(_dB));return new F(function(){return _dx(_);});};},_dG=0,_dH=new T(function(){return B(_dz(_dG,_dG,_v));}),_dI=function(_dJ,_dK){return E(_dJ)!=E(_dK);},_dL=function(_dM,_dN){return E(_dM)==E(_dN);},_dO=new T2(0,_dL,_dI),_dP=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_dQ=new T(function(){return eval("(function(ctx){ctx.save();})");}),_dR=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_dS=function(_dT,_dU,_dV,_){var _dW=__app1(E(_dQ),_dV),_dX=__app2(E(_dR),_dV,E(_dT)),_dY=B(A2(_dU,_dV,_)),_dZ=__app1(E(_dP),_dV);return new F(function(){return _dx(_);});},_e0=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_e1=function(_e2,_e3,_e4,_e5,_){var _e6=__app1(E(_dQ),_e5),_e7=__app3(E(_e0),_e5,E(_e2),E(_e3)),_e8=B(A2(_e4,_e5,_)),_e9=__app1(E(_dP),_e5);return new F(function(){return _dx(_);});},_ea=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_eb=function(_ec,_ed,_ee,_ef,_){var _eg=__app1(E(_dQ),_ef),_eh=__app3(E(_ea),_ef,E(_ec),E(_ed)),_ei=B(A2(_ee,_ef,_)),_ej=__app1(E(_dP),_ef);return new F(function(){return _dx(_);});},_ek=new T(function(){return eval("(function(ctx,i,x,y){ctx.drawImage(i,x,y);})");}),_el=function(_em,_en,_eo,_ep,_){var _eq=__app4(E(_ek),_ep,_em,_en,_eo);return new F(function(){return _dx(_);});},_er=function(_es,_et,_eu){var _ev=E(_eu);return (_ev._==0)?0:(!B(A3(_4b,_es,_et,_ev.a)))?1+B(_er(_es,_et,_ev.b))|0:0;},_ew=",",_ex="rgba(",_ey=new T(function(){return toJSStr(_v);}),_ez="rgb(",_eA=")",_eB=new T2(1,_eA,_v),_eC=function(_eD){var _eE=E(_eD);if(!_eE._){var _eF=jsCat(new T2(1,_ez,new T2(1,new T(function(){return String(_eE.a);}),new T2(1,_ew,new T2(1,new T(function(){return String(_eE.b);}),new T2(1,_ew,new T2(1,new T(function(){return String(_eE.c);}),_eB)))))),E(_ey));return E(_eF);}else{var _eG=jsCat(new T2(1,_ex,new T2(1,new T(function(){return String(_eE.a);}),new T2(1,_ew,new T2(1,new T(function(){return String(_eE.b);}),new T2(1,_ew,new T2(1,new T(function(){return String(_eE.c);}),new T2(1,_ew,new T2(1,new T(function(){return String(_eE.d);}),_eB)))))))),E(_ey));return E(_eG);}},_eH="strokeStyle",_eI="fillStyle",_eJ=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_eK=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_eL=function(_eM,_eN){var _eO=new T(function(){return B(_eC(_eM));});return function(_eP,_){var _eQ=E(_eP),_eR=E(_eI),_eS=E(_eJ),_eT=__app2(_eS,_eQ,_eR),_eU=E(_eH),_eV=__app2(_eS,_eQ,_eU),_eW=E(_eO),_eX=E(_eK),_eY=__app3(_eX,_eQ,_eR,_eW),_eZ=__app3(_eX,_eQ,_eU,_eW),_f0=B(A2(_eN,_eQ,_)),_f1=String(_eT),_f2=__app3(_eX,_eQ,_eR,_f1),_f3=String(_eV),_f4=__app3(_eX,_eQ,_eU,_f3);return new F(function(){return _dx(_);});};},_f5="font",_f6=function(_f7,_f8){var _f9=new T(function(){return toJSStr(E(_f7));});return function(_fa,_){var _fb=E(_fa),_fc=E(_f5),_fd=__app2(E(_eJ),_fb,_fc),_fe=E(_eK),_ff=__app3(_fe,_fb,_fc,E(_f9)),_fg=B(A2(_f8,_fb,_)),_fh=String(_fd),_fi=__app3(_fe,_fb,_fc,_fh);return new F(function(){return _dx(_);});};},_fj=0,_fk=new T(function(){return B(unCStr("px IPAGothic"));}),_fl=new T(function(){return B(unCStr("\u3042\u3044\u3046\u3048\u304axkhnmtrsy \u304b\u306f\u306a\u307e\u304d\u3072\u306b\u307f\u304f\u3075\u306c\u3080\u3051\u3078\u306d\u3081\u3053\u307b\u306e\u3082\u3068\u308d\u305d\u3088\u3092\u3066\u308c\u305b\u3091\u3064\u308b\u3059\u3086\u3093\u3061\u308a\u3057\u3090\u305f\u3089\u3055\u3084\u308f\u309b\u963f\u548c\u5b87\u543e\u4ed8\u9808\u88ab\u610f\u767e\u96c4\u9593\u6ce2\u304c9\u7a42\u305e\u8a71\u8449\u3056\u3050\u3073\u7dd2\u30693\u305a\u3070\u3076\u304e\u3079\u88dc\u82bd1\u5e9c\u5834\u3058\u500b\u6211\u3054\u56f3\u6642\u66fe\u706b\u65e5\u3060\u5ea7\u7fbd4\u99ac\u90e8\u7956\u7089\u5177\u8a9e\u3065\u5f8c\u5b50\u7537\u3067\u305c\u51fa\u88f3\u7f8e"));}),_fm=function(_fn,_fo,_fp,_fq,_fr,_fs,_ft,_fu,_fv,_fw,_){var _fx=E(_fw);if(!_fx._){return _5L;}else{var _fy=_fx.b,_fz=E(_fs),_fA=_fz.b,_fB=E(_fv),_fC=_fB.a,_fD=_fB.b,_fE=E(_fx.a),_fF=new T(function(){return E(_fr);});if(E(_fE)==13){return new F(function(){return _fG(_fn,_fo,_fp,_fq,_fr,_fz.a,_fA,_ft,0,new T(function(){return E(_fC)-E(_fF)*1.2;}),_ft,_fy,_);});}else{var _fH=function(_){var _fI=new T(function(){return E(_fF)*1.1;}),_fJ=new T(function(){var _fK=E(_fu),_fL=E(_fA)/E(_fI),_fM=_fL&4294967295;if(_fL>=_fM){return (_fK+1|0)>(_fM-2|0);}else{return (_fK+1|0)>((_fM-1|0)-2|0);}});return new F(function(){return _fm(_fn,_fo,_fp,_fq,_fr,_fz,_ft,new T(function(){if(!E(_fJ)){return E(_fu)+1|0;}else{return E(_fj);}}),new T2(0,new T(function(){if(!E(_fJ)){return E(_fC);}else{return E(_fC)-E(_fF)*1.2;}}),new T(function(){if(!E(_fJ)){return E(_fD)+E(_fI);}else{return E(_ft);}})),_fy,_);});};if(!E(_fq)){var _fN=new T(function(){var _fO=new T(function(){return B(_dz(_dG,_dG,new T2(1,_fE,_v)));}),_fP=function(_fQ,_){return new F(function(){return _dS(_dG,_fO,E(_fQ),_);});};return B(_f6(new T(function(){return B(_3(B(_d(0,E(_fr),_v)),_fk));},1),function(_fR,_){return new F(function(){return _eb(_fC,_fD,_fP,E(_fR),_);});}));}),_fS=B(A(_eL,[_fp,_fN,E(_fn).a,_]));return new F(function(){return _fH(_);});}else{var _fT=new T(function(){return E(_fr)/20;}),_fU=function(_fV,_){return new F(function(){return _e1(_fT,_fT,function(_fW,_){if(!B(_4d(_dO,_fE,_fl))){return new F(function(){return _el(B(_a1(_fo,14)),0,0,E(_fW),_);});}else{return new F(function(){return _el(B(_a1(_fo,B(_er(_dO,_fE,_fl)))),0,0,E(_fW),_);});}},E(_fV),_);});},_fX=B(_eb(new T(function(){return E(_fC)-E(_fF)/6;},1),new T(function(){return E(_fD)-E(_fF)*3/4;},1),_fU,E(_fn).a,_));return new F(function(){return _fH(_);});}}}},_fG=function(_fY,_fZ,_g0,_g1,_g2,_g3,_g4,_g5,_g6,_g7,_g8,_g9,_){while(1){var _ga=B((function(_gb,_gc,_gd,_ge,_gf,_gg,_gh,_gi,_gj,_gk,_gl,_gm,_){var _gn=E(_gm);if(!_gn._){return _5L;}else{var _go=_gn.b,_gp=E(_gn.a),_gq=new T(function(){return E(_gf);});if(E(_gp)==13){var _gr=_gb,_gs=_gc,_gt=_gd,_gu=_ge,_gv=_gf,_gw=_gg,_gx=_gh,_gy=_gi,_gz=_gi;_fY=_gr;_fZ=_gs;_g0=_gt;_g1=_gu;_g2=_gv;_g3=_gw;_g4=_gx;_g5=_gy;_g6=0;_g7=new T(function(){return E(_gk)-E(_gq)*1.2;});_g8=_gz;_g9=_go;return __continue;}else{var _gA=function(_){var _gB=new T(function(){return E(_gq)*1.1;}),_gC=new T(function(){var _gD=E(_gh)/E(_gB),_gE=_gD&4294967295;if(_gD>=_gE){return (_gj+1|0)>(_gE-2|0);}else{return (_gj+1|0)>((_gE-1|0)-2|0);}});return new F(function(){return _fm(_gb,_gc,_gd,_ge,_gf,new T2(0,_gg,_gh),_gi,new T(function(){if(!E(_gC)){return _gj+1|0;}else{return E(_fj);}}),new T2(0,new T(function(){if(!E(_gC)){return E(_gk);}else{return E(_gk)-E(_gq)*1.2;}}),new T(function(){if(!E(_gC)){return E(_gl)+E(_gB);}else{return E(_gi);}})),_go,_);});};if(!E(_ge)){var _gF=new T(function(){var _gG=new T(function(){return B(_dz(_dG,_dG,new T2(1,_gp,_v)));}),_gH=function(_gI,_){return new F(function(){return _dS(_dG,_gG,E(_gI),_);});};return B(_f6(new T(function(){return B(_3(B(_d(0,E(_gf),_v)),_fk));},1),function(_gJ,_){return new F(function(){return _eb(_gk,_gl,_gH,E(_gJ),_);});}));}),_gK=B(A(_eL,[_gd,_gF,E(_gb).a,_]));return new F(function(){return _gA(_);});}else{var _gL=new T(function(){return E(_gf)/20;}),_gM=function(_gN,_){return new F(function(){return _e1(_gL,_gL,function(_gO,_){if(!B(_4d(_dO,_gp,_fl))){return new F(function(){return _el(B(_a1(_gc,14)),0,0,E(_gO),_);});}else{return new F(function(){return _el(B(_a1(_gc,B(_er(_dO,_gp,_fl)))),0,0,E(_gO),_);});}},E(_gN),_);});},_gP=B(_eb(new T(function(){return E(_gk)-E(_gq)/6;},1),new T(function(){return E(_gl)-E(_gq)*3/4;},1),_gM,E(_gb).a,_));return new F(function(){return _gA(_);});}}}})(_fY,_fZ,_g0,_g1,_g2,_g3,_g4,_g5,_g6,_g7,_g8,_g9,_));if(_ga!=__continue){return _ga;}}},_gQ=function(_gR,_gS,_gT,_gU,_gV,_gW,_gX,_gY,_gZ,_h0,_h1,_h2,_h3,_){while(1){var _h4=B((function(_h5,_h6,_h7,_h8,_h9,_ha,_hb,_hc,_hd,_he,_hf,_hg,_hh,_){var _hi=E(_hh);if(!_hi._){return _5L;}else{var _hj=_hi.b,_hk=E(_hi.a),_hl=new T(function(){return E(_ha);});if(E(_hk)==13){var _hm=_h5,_hn=_h6,_ho=_h7,_hp=_h8,_hq=_h9,_hr=_ha,_hs=_hb,_ht=_hc,_hu=_hd,_hv=_hd;_gR=_hm;_gS=_hn;_gT=_ho;_gU=_hp;_gV=_hq;_gW=_hr;_gX=_hs;_gY=_ht;_gZ=_hu;_h0=0;_h1=new T(function(){return E(_hf)-E(_hl)*1.2;});_h2=_hv;_h3=_hj;return __continue;}else{var _hw=function(_){var _hx=new T(function(){return E(_hl)*1.1;}),_hy=new T(function(){var _hz=E(_hc)/E(_hx),_hA=_hz&4294967295;if(_hz>=_hA){return (_he+1|0)>(_hA-2|0);}else{return (_he+1|0)>((_hA-1|0)-2|0);}});return new F(function(){return _fm(new T2(0,_h5,_h6),_h7,_h8,_h9,_ha,new T2(0,_hb,_hc),_hd,new T(function(){if(!E(_hy)){return _he+1|0;}else{return E(_fj);}}),new T2(0,new T(function(){if(!E(_hy)){return E(_hf);}else{return E(_hf)-E(_hl)*1.2;}}),new T(function(){if(!E(_hy)){return E(_hg)+E(_hx);}else{return E(_hd);}})),_hj,_);});};if(!E(_h9)){var _hB=new T(function(){var _hC=new T(function(){return B(_dz(_dG,_dG,new T2(1,_hk,_v)));}),_hD=function(_hE,_){return new F(function(){return _dS(_dG,_hC,E(_hE),_);});};return B(_f6(new T(function(){return B(_3(B(_d(0,E(_ha),_v)),_fk));},1),function(_hF,_){return new F(function(){return _eb(_hf,_hg,_hD,E(_hF),_);});}));}),_hG=B(A(_eL,[_h8,_hB,_h5,_]));return new F(function(){return _hw(_);});}else{var _hH=new T(function(){return E(_ha)/20;}),_hI=function(_hJ,_){return new F(function(){return _e1(_hH,_hH,function(_hK,_){if(!B(_4d(_dO,_hk,_fl))){return new F(function(){return _el(B(_a1(_h7,14)),0,0,E(_hK),_);});}else{return new F(function(){return _el(B(_a1(_h7,B(_er(_dO,_hk,_fl)))),0,0,E(_hK),_);});}},E(_hJ),_);});},_hL=B(_eb(new T(function(){return E(_hf)-E(_hl)/6;},1),new T(function(){return E(_hg)-E(_hl)*3/4;},1),_hI,_h5,_));return new F(function(){return _hw(_);});}}}})(_gR,_gS,_gT,_gU,_gV,_gW,_gX,_gY,_gZ,_h0,_h1,_h2,_h3,_));if(_h4!=__continue){return _h4;}}},_hM=new T(function(){return eval("(function(ctx, x, y, radius, fromAngle, toAngle){ctx.arc(x, y, radius, fromAngle, toAngle);})");}),_hN=function(_hO,_hP,_hQ,_hR,_hS,_hT,_){var _hU=__apply(E(_hM),new T2(1,_hS,new T2(1,_hR,new T2(1,_hQ,new T2(1,_hP,new T2(1,_hO,new T2(1,_hT,_v)))))));return new F(function(){return _dx(_);});},_hV=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_hW=new T(function(){return eval("(function(ctx,x,y){ctx.lineTo(x,y);})");}),_hX=function(_hY,_hZ,_){var _i0=E(_hY);if(!_i0._){return _5L;}else{var _i1=E(_i0.a),_i2=E(_hZ),_i3=__app3(E(_hV),_i2,E(_i1.a),E(_i1.b)),_i4=E(_i0.b);if(!_i4._){return _5L;}else{var _i5=E(_i4.a),_i6=E(_hW),_i7=__app3(_i6,_i2,E(_i5.a),E(_i5.b)),_i8=function(_i9,_){while(1){var _ia=E(_i9);if(!_ia._){return _5L;}else{var _ib=E(_ia.a),_ic=__app3(_i6,_i2,E(_ib.a),E(_ib.b));_i9=_ia.b;continue;}}};return new F(function(){return _i8(_i4.b,_);});}}},_id=function(_ie,_if,_ig,_ih,_ii,_){var _ij=B(_hN(_ie+_ig-10,_if+_ih-10,10,0,1.5707963267948966,_ii,_)),_ik=B(_hN(_ie+10,_if+_ih-10,10,1.5707963267948966,3.141592653589793,_ii,_)),_il=B(_hN(_ie+10,_if+10,10,3.141592653589793,4.71238898038469,_ii,_)),_im=B(_hN(_ie+_ig-10,_if+10,10,4.71238898038469,6.283185307179586,_ii,_));return new F(function(){return _hX(new T2(1,new T2(0,_ie+_ig,_if+_ih-10),new T2(1,new T2(0,_ie+_ig,_if+10),_v)),_ii,_);});},_in=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_io=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_ip=function(_iq,_ir,_){var _is=__app1(E(_in),_ir),_it=B(A2(_iq,_ir,_)),_iu=__app1(E(_io),_ir);return new F(function(){return _dx(_);});},_iv=function(_iw,_ix,_iy,_iz,_iA,_){return new F(function(){return _hX(new T2(1,new T2(0,_iw,_ix),new T2(1,new T2(0,_iy,_ix),new T2(1,new T2(0,_iy,_iz),new T2(1,new T2(0,_iw,_iz),new T2(1,new T2(0,_iw,_ix),_v))))),_iA,_);});},_iB=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_iC=function(_iD,_iE,_){var _iF=__app1(E(_in),_iE),_iG=B(A2(_iD,_iE,_)),_iH=__app1(E(_iB),_iE);return new F(function(){return _dx(_);});},_iI=new T3(0,200,255,200),_iJ=new T3(0,255,204,153),_iK=new T3(0,255,153,204),_iL=new T3(0,153,255,255),_iM=new T3(0,0,128,128),_iN=new T3(0,0,0,0),_iO=new T2(1,_iN,_v),_iP=new T3(0,255,255,100),_iQ=new T2(1,_iP,_iO),_iR=new T2(1,_iM,_iQ),_iS=new T2(1,_iL,_iR),_iT=new T2(1,_iK,_iS),_iU=new T2(1,_iJ,_iT),_iV=new T2(1,_iI,_iU),_iW=new T3(0,200,200,180),_iX=new T2(1,_iW,_iV),_iY="lineWidth",_iZ=function(_j0,_j1){var _j2=new T(function(){return String(E(_j0));});return function(_j3,_){var _j4=E(_j3),_j5=E(_iY),_j6=__app2(E(_eJ),_j4,_j5),_j7=E(_eK),_j8=__app3(_j7,_j4,_j5,E(_j2)),_j9=B(A2(_j1,_j4,_)),_ja=String(_j6),_jb=__app3(_j7,_j4,_j5,_ja);return new F(function(){return _dx(_);});};},_jc=3,_jd=function(_je,_jf){var _jg=E(_je);if(!_jg._){return __Z;}else{var _jh=E(_jf);return (_jh._==0)?__Z:new T2(1,new T2(0,_jg.a,_jh.a),new T(function(){return B(_jd(_jg.b,_jh.b));}));}},_ji=function(_jj,_jk,_jl,_jm,_){var _jn=E(_jm);if(!_jn._){return _5L;}else{var _jo=E(E(_jk).a),_jp=new T(function(){return E(E(_jl).b);}),_jq=function(_jr,_){while(1){var _js=B((function(_jt,_){var _ju=E(_jt);if(!_ju._){return _5L;}else{var _jv=_ju.b,_jw=E(_ju.a),_jx=_jw.d,_jy=E(_jw.b),_jz=_jy.a,_jA=_jy.b,_jB=_jy.c,_jC=_jy.d,_jD=function(_){var _jE=function(_jF,_jG,_jH,_){while(1){var _jI=B((function(_jJ,_jK,_jL,_){var _jM=E(_jJ);if(!_jM._){return _5L;}else{var _jN=E(_jK);if(!_jN._){return _5L;}else{var _jO=E(_jL);if(!_jO._){return _5L;}else{var _jP=E(_jO.a),_jQ=E(_jP.a),_jR=E(_jP.b),_jS=new T(function(){return E(_jQ.b)+E(_jA);}),_jT=B(_fG(_jj,_jp,new T(function(){return B(_a1(_iX,E(_jR.b)));}),_jN.a,_jR.a,_jB,_jC,_jS,0,new T(function(){return E(_jQ.a)+E(_jz);}),_jS,_jM.a,_));_jF=_jM.b;_jG=_jN.b;_jH=_jO.b;return __continue;}}}})(_jF,_jG,_jH,_));if(_jI!=__continue){return _jI;}}},_jU=new T(function(){return B(_jd(_jw.f,new T(function(){return B(_jd(_jw.h,_jw.i));},1)));},1);return new F(function(){return _jE(_jw.j,_jw.k,_jU,_);});};switch(E(_jw.c)){case 0:var _jV=B(_jD(_));_jr=_jv;return __continue;case 1:var _jW=E(_jj),_jX=_jW.a,_jY=new T(function(){return E(_jz)+E(_jB);}),_jZ=new T(function(){return E(_jA)+E(_jC);}),_k0=function(_k1,_){return new F(function(){return _iv(_jz,_jA,_jY,_jZ,_k1,_);});},_k2=B(A(_eL,[new T(function(){return B(_a1(_iX,_jx));},1),function(_k3,_){return new F(function(){return _iC(_k0,E(_k3),_);});},_jX,_])),_k4=B(_jD(_)),_k5=function(_k6,_){while(1){var _k7=B((function(_k8,_){var _k9=E(_k8);if(!_k9._){return _5L;}else{var _ka=_k9.b,_kb=E(_k9.a),_kc=_kb.d,_kd=E(_kb.b),_ke=_kd.a,_kf=_kd.b,_kg=_kd.c,_kh=_kd.d,_ki=function(_){var _kj=function(_kk,_kl,_km,_){while(1){var _kn=B((function(_ko,_kp,_kq,_){var _kr=E(_ko);if(!_kr._){return _5L;}else{var _ks=E(_kp);if(!_ks._){return _5L;}else{var _kt=E(_kq);if(!_kt._){return _5L;}else{var _ku=E(_kt.a),_kv=E(_ku.a),_kw=E(_ku.b),_kx=new T(function(){return E(_kv.b)+E(_kf);}),_ky=B(_gQ(_jX,_jW.b,_jp,new T(function(){return B(_a1(_iX,E(_kw.b)));}),_ks.a,_kw.a,_kg,_kh,_kx,0,new T(function(){return E(_kv.a)+E(_ke);}),_kx,_kr.a,_));_kk=_kr.b;_kl=_ks.b;_km=_kt.b;return __continue;}}}})(_kk,_kl,_km,_));if(_kn!=__continue){return _kn;}}},_kz=new T(function(){return B(_jd(_kb.f,new T(function(){return B(_jd(_kb.h,_kb.i));},1)));},1);return new F(function(){return _kj(_kb.j,_kb.k,_kz,_);});};switch(E(_kb.c)){case 0:var _kA=B(_ki(_));_k6=_ka;return __continue;case 1:var _kB=new T(function(){return E(_ke)+E(_kg);}),_kC=new T(function(){return E(_kf)+E(_kh);}),_kD=function(_kE,_){return new F(function(){return _iv(_ke,_kf,_kB,_kC,_kE,_);});},_kF=B(A(_eL,[new T(function(){return B(_a1(_iX,_kc));},1),function(_kG,_){return new F(function(){return _iC(_kD,E(_kG),_);});},_jX,_])),_kH=B(_ki(_));_k6=_ka;return __continue;default:var _kI=function(_kJ,_){return new F(function(){return _id(E(_ke),E(_kf),E(_kg),E(_kh),E(_kJ),_);});},_kK=B(A(_eL,[new T(function(){return B(_a1(_iX,_kb.e));},1),function(_kL,_){return new F(function(){return _ip(_kI,E(_kL),_);});},_jX,_])),_kM=new T(function(){var _kN=function(_kO,_){return new F(function(){return _id(E(_ke),E(_kf),E(_kg),E(_kh),E(_kO),_);});};return B(_iZ(_jc,function(_kP,_){return new F(function(){return _iC(_kN,E(_kP),_);});}));}),_kQ=B(A(_eL,[new T(function(){return B(_a1(_iX,_kc));},1),_kM,_jX,_])),_kR=B(_ki(_));_k6=_ka;return __continue;}}})(_k6,_));if(_k7!=__continue){return _k7;}}};return new F(function(){return _k5(_jv,_);});break;default:var _kS=E(_jj),_kT=_kS.a,_kU=function(_kV,_){return new F(function(){return _id(E(_jz),E(_jA),E(_jB),E(_jC),E(_kV),_);});},_kW=B(A(_eL,[new T(function(){return B(_a1(_iX,_jw.e));},1),function(_kX,_){return new F(function(){return _ip(_kU,E(_kX),_);});},_kT,_])),_kY=new T(function(){var _kZ=function(_l0,_){return new F(function(){return _id(E(_jz),E(_jA),E(_jB),E(_jC),E(_l0),_);});};return B(_iZ(_jc,function(_l1,_){return new F(function(){return _iC(_kZ,E(_l1),_);});}));}),_l2=B(A(_eL,[new T(function(){return B(_a1(_iX,_jx));},1),_kY,_kT,_])),_l3=B(_jD(_)),_l4=function(_l5,_){while(1){var _l6=B((function(_l7,_){var _l8=E(_l7);if(!_l8._){return _5L;}else{var _l9=_l8.b,_la=E(_l8.a),_lb=_la.d,_lc=E(_la.b),_ld=_lc.a,_le=_lc.b,_lf=_lc.c,_lg=_lc.d,_lh=function(_){var _li=function(_lj,_lk,_ll,_){while(1){var _lm=B((function(_ln,_lo,_lp,_){var _lq=E(_ln);if(!_lq._){return _5L;}else{var _lr=E(_lo);if(!_lr._){return _5L;}else{var _ls=E(_lp);if(!_ls._){return _5L;}else{var _lt=E(_ls.a),_lu=E(_lt.a),_lv=E(_lt.b),_lw=new T(function(){return E(_lu.b)+E(_le);}),_lx=B(_gQ(_kT,_kS.b,_jp,new T(function(){return B(_a1(_iX,E(_lv.b)));}),_lr.a,_lv.a,_lf,_lg,_lw,0,new T(function(){return E(_lu.a)+E(_ld);}),_lw,_lq.a,_));_lj=_lq.b;_lk=_lr.b;_ll=_ls.b;return __continue;}}}})(_lj,_lk,_ll,_));if(_lm!=__continue){return _lm;}}},_ly=new T(function(){return B(_jd(_la.f,new T(function(){return B(_jd(_la.h,_la.i));},1)));},1);return new F(function(){return _li(_la.j,_la.k,_ly,_);});};switch(E(_la.c)){case 0:var _lz=B(_lh(_));_l5=_l9;return __continue;case 1:var _lA=new T(function(){return E(_ld)+E(_lf);}),_lB=new T(function(){return E(_le)+E(_lg);}),_lC=function(_lD,_){return new F(function(){return _iv(_ld,_le,_lA,_lB,_lD,_);});},_lE=B(A(_eL,[new T(function(){return B(_a1(_iX,_lb));},1),function(_lF,_){return new F(function(){return _iC(_lC,E(_lF),_);});},_kT,_])),_lG=B(_lh(_));_l5=_l9;return __continue;default:var _lH=function(_lI,_){return new F(function(){return _id(E(_ld),E(_le),E(_lf),E(_lg),E(_lI),_);});},_lJ=B(A(_eL,[new T(function(){return B(_a1(_iX,_la.e));},1),function(_lK,_){return new F(function(){return _ip(_lH,E(_lK),_);});},_kT,_])),_lL=new T(function(){var _lM=function(_lN,_){return new F(function(){return _id(E(_ld),E(_le),E(_lf),E(_lg),E(_lN),_);});};return B(_iZ(_jc,function(_lO,_){return new F(function(){return _iC(_lM,E(_lO),_);});}));}),_lP=B(A(_eL,[new T(function(){return B(_a1(_iX,_lb));},1),_lL,_kT,_])),_lQ=B(_lh(_));_l5=_l9;return __continue;}}})(_l5,_));if(_l6!=__continue){return _l6;}}};return new F(function(){return _l4(_jv,_);});}}})(_jr,_));if(_js!=__continue){return _js;}}},_lR=_jn.a,_lS=_jn.b,_lT=E(_lR),_lU=_lT.d,_lV=E(_lT.b),_lW=_lV.a,_lX=_lV.b,_lY=_lV.c,_lZ=_lV.d,_m0=function(_){var _m1=function(_m2,_m3,_m4,_){while(1){var _m5=B((function(_m6,_m7,_m8,_){var _m9=E(_m6);if(!_m9._){return _5L;}else{var _ma=E(_m7);if(!_ma._){return _5L;}else{var _mb=E(_m8);if(!_mb._){return _5L;}else{var _mc=E(_mb.a),_md=E(_mc.a),_me=E(_mc.b),_mf=new T(function(){return E(_md.b)+E(_lX);}),_mg=B(_fG(_jj,_jp,new T(function(){return B(_a1(_iX,E(_me.b)));}),_ma.a,_me.a,_lY,_lZ,_mf,0,new T(function(){return E(_md.a)+E(_lW);}),_mf,_m9.a,_));_m2=_m9.b;_m3=_ma.b;_m4=_mb.b;return __continue;}}}})(_m2,_m3,_m4,_));if(_m5!=__continue){return _m5;}}},_mh=new T(function(){return B(_jd(_lT.f,new T(function(){return B(_jd(_lT.h,_lT.i));},1)));},1);return new F(function(){return _m1(_lT.j,_lT.k,_mh,_);});};switch(E(_lT.c)){case 0:var _mi=B(_m0(_));return new F(function(){return _jq(_lS,_);});break;case 1:var _mj=E(_jj),_mk=_mj.a,_ml=new T(function(){return E(_lW)+E(_lY);}),_mm=new T(function(){return E(_lX)+E(_lZ);}),_mn=function(_mo,_){return new F(function(){return _iv(_lW,_lX,_ml,_mm,_mo,_);});},_mp=B(A(_eL,[new T(function(){return B(_a1(_iX,_lU));},1),function(_mq,_){return new F(function(){return _iC(_mn,E(_mq),_);});},_mk,_])),_mr=B(_m0(_)),_ms=function(_mt,_){while(1){var _mu=B((function(_mv,_){var _mw=E(_mv);if(!_mw._){return _5L;}else{var _mx=_mw.b,_my=E(_mw.a),_mz=_my.d,_mA=E(_my.b),_mB=_mA.a,_mC=_mA.b,_mD=_mA.c,_mE=_mA.d,_mF=function(_){var _mG=function(_mH,_mI,_mJ,_){while(1){var _mK=B((function(_mL,_mM,_mN,_){var _mO=E(_mL);if(!_mO._){return _5L;}else{var _mP=E(_mM);if(!_mP._){return _5L;}else{var _mQ=E(_mN);if(!_mQ._){return _5L;}else{var _mR=E(_mQ.a),_mS=E(_mR.a),_mT=E(_mR.b),_mU=new T(function(){return E(_mS.b)+E(_mC);}),_mV=B(_gQ(_mk,_mj.b,_jp,new T(function(){return B(_a1(_iX,E(_mT.b)));}),_mP.a,_mT.a,_mD,_mE,_mU,0,new T(function(){return E(_mS.a)+E(_mB);}),_mU,_mO.a,_));_mH=_mO.b;_mI=_mP.b;_mJ=_mQ.b;return __continue;}}}})(_mH,_mI,_mJ,_));if(_mK!=__continue){return _mK;}}},_mW=new T(function(){return B(_jd(_my.f,new T(function(){return B(_jd(_my.h,_my.i));},1)));},1);return new F(function(){return _mG(_my.j,_my.k,_mW,_);});};switch(E(_my.c)){case 0:var _mX=B(_mF(_));_mt=_mx;return __continue;case 1:var _mY=new T(function(){return E(_mB)+E(_mD);}),_mZ=new T(function(){return E(_mC)+E(_mE);}),_n0=function(_n1,_){return new F(function(){return _iv(_mB,_mC,_mY,_mZ,_n1,_);});},_n2=B(A(_eL,[new T(function(){return B(_a1(_iX,_mz));},1),function(_n3,_){return new F(function(){return _iC(_n0,E(_n3),_);});},_mk,_])),_n4=B(_mF(_));_mt=_mx;return __continue;default:var _n5=function(_n6,_){return new F(function(){return _id(E(_mB),E(_mC),E(_mD),E(_mE),E(_n6),_);});},_n7=B(A(_eL,[new T(function(){return B(_a1(_iX,_my.e));},1),function(_n8,_){return new F(function(){return _ip(_n5,E(_n8),_);});},_mk,_])),_n9=new T(function(){var _na=function(_nb,_){return new F(function(){return _id(E(_mB),E(_mC),E(_mD),E(_mE),E(_nb),_);});};return B(_iZ(_jc,function(_nc,_){return new F(function(){return _iC(_na,E(_nc),_);});}));}),_nd=B(A(_eL,[new T(function(){return B(_a1(_iX,_mz));},1),_n9,_mk,_])),_ne=B(_mF(_));_mt=_mx;return __continue;}}})(_mt,_));if(_mu!=__continue){return _mu;}}};return new F(function(){return _ms(_lS,_);});break;default:var _nf=E(_jj),_ng=_nf.a,_nh=function(_ni,_){return new F(function(){return _id(E(_lW),E(_lX),E(_lY),E(_lZ),E(_ni),_);});},_nj=B(A(_eL,[new T(function(){return B(_a1(_iX,_lT.e));},1),function(_nk,_){return new F(function(){return _ip(_nh,E(_nk),_);});},_ng,_])),_nl=new T(function(){var _nm=function(_nn,_){return new F(function(){return _id(E(_lW),E(_lX),E(_lY),E(_lZ),E(_nn),_);});};return B(_iZ(_jc,function(_no,_){return new F(function(){return _iC(_nm,E(_no),_);});}));}),_np=B(A(_eL,[new T(function(){return B(_a1(_iX,_lU));},1),_nl,_ng,_])),_nq=B(_m0(_)),_nr=function(_ns,_){while(1){var _nt=B((function(_nu,_){var _nv=E(_nu);if(!_nv._){return _5L;}else{var _nw=_nv.b,_nx=E(_nv.a),_ny=_nx.d,_nz=E(_nx.b),_nA=_nz.a,_nB=_nz.b,_nC=_nz.c,_nD=_nz.d,_nE=function(_){var _nF=function(_nG,_nH,_nI,_){while(1){var _nJ=B((function(_nK,_nL,_nM,_){var _nN=E(_nK);if(!_nN._){return _5L;}else{var _nO=E(_nL);if(!_nO._){return _5L;}else{var _nP=E(_nM);if(!_nP._){return _5L;}else{var _nQ=E(_nP.a),_nR=E(_nQ.a),_nS=E(_nQ.b),_nT=new T(function(){return E(_nR.b)+E(_nB);}),_nU=B(_gQ(_ng,_nf.b,_jp,new T(function(){return B(_a1(_iX,E(_nS.b)));}),_nO.a,_nS.a,_nC,_nD,_nT,0,new T(function(){return E(_nR.a)+E(_nA);}),_nT,_nN.a,_));_nG=_nN.b;_nH=_nO.b;_nI=_nP.b;return __continue;}}}})(_nG,_nH,_nI,_));if(_nJ!=__continue){return _nJ;}}},_nV=new T(function(){return B(_jd(_nx.f,new T(function(){return B(_jd(_nx.h,_nx.i));},1)));},1);return new F(function(){return _nF(_nx.j,_nx.k,_nV,_);});};switch(E(_nx.c)){case 0:var _nW=B(_nE(_));_ns=_nw;return __continue;case 1:var _nX=new T(function(){return E(_nA)+E(_nC);}),_nY=new T(function(){return E(_nB)+E(_nD);}),_nZ=function(_o0,_){return new F(function(){return _iv(_nA,_nB,_nX,_nY,_o0,_);});},_o1=B(A(_eL,[new T(function(){return B(_a1(_iX,_ny));},1),function(_o2,_){return new F(function(){return _iC(_nZ,E(_o2),_);});},_ng,_])),_o3=B(_nE(_));_ns=_nw;return __continue;default:var _o4=function(_o5,_){return new F(function(){return _id(E(_nA),E(_nB),E(_nC),E(_nD),E(_o5),_);});},_o6=B(A(_eL,[new T(function(){return B(_a1(_iX,_nx.e));},1),function(_o7,_){return new F(function(){return _ip(_o4,E(_o7),_);});},_ng,_])),_o8=new T(function(){var _o9=function(_oa,_){return new F(function(){return _id(E(_nA),E(_nB),E(_nC),E(_nD),E(_oa),_);});};return B(_iZ(_jc,function(_ob,_){return new F(function(){return _iC(_o9,E(_ob),_);});}));}),_oc=B(A(_eL,[new T(function(){return B(_a1(_iX,_ny));},1),_o8,_ng,_])),_od=B(_nE(_));_ns=_nw;return __continue;}}})(_ns,_));if(_nt!=__continue){return _nt;}}};return new F(function(){return _nr(_lS,_);});}}},_oe=function(_of){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_of));}))));});},_og=new T(function(){return B(_oe("ww_s3xm (Double, Double)"));}),_oh=new T(function(){return B(unCStr("Prelude.undefined"));}),_oi=new T(function(){return B(err(_oh));}),_oj=function(_ok){return E(_oi);},_ol=new T(function(){return B(_oj(_));}),_om=function(_on,_oo){if(_on<=0){if(_on>=0){return new F(function(){return quot(_on,_oo);});}else{if(_oo<=0){return new F(function(){return quot(_on,_oo);});}else{return quot(_on+1|0,_oo)-1|0;}}}else{if(_oo>=0){if(_on>=0){return new F(function(){return quot(_on,_oo);});}else{if(_oo<=0){return new F(function(){return quot(_on,_oo);});}else{return quot(_on+1|0,_oo)-1|0;}}}else{return quot(_on-1|0,_oo)-1|0;}}},_op=function(_oq,_or){if(_oq<=_or){var _os=function(_ot){return new T2(1,_ot,new T(function(){if(_ot!=_or){return B(_os(_ot+1|0));}else{return __Z;}}));};return new F(function(){return _os(_oq);});}else{return __Z;}},_ou=new T(function(){return B(_op(0,2147483647));}),_ov=40,_ow=60,_ox=new T2(0,_ov,_ow),_oy=new T2(1,_ox,_v),_oz=1,_oA=new T2(1,_oz,_v),_oB=1,_oC=new T2(1,_oB,_v),_oD=function(_oE,_oF){var _oG=_oE%_oF;if(_oE<=0){if(_oE>=0){return E(_oG);}else{if(_oF<=0){return E(_oG);}else{var _oH=E(_oG);return (_oH==0)?0:_oH+_oF|0;}}}else{if(_oF>=0){if(_oE>=0){return E(_oG);}else{if(_oF<=0){return E(_oG);}else{var _oI=E(_oG);return (_oI==0)?0:_oI+_oF|0;}}}else{var _oJ=E(_oG);return (_oJ==0)?0:_oJ+_oF|0;}}},_oK=function(_oL,_oM,_oN){var _oO=E(_oM);if(!_oO._){return __Z;}else{var _oP=E(_oN);return (_oP._==0)?__Z:new T2(1,new T(function(){return B(A2(_oL,_oO.a,_oP.a));}),new T(function(){return B(_oK(_oL,_oO.b,_oP.b));}));}},_oQ=function(_oR,_oS,_oT,_oU,_oV){var _oW=new T(function(){var _oX=new T(function(){return B(_9C(_oT,0));}),_oY=new T(function(){return B(_om(E(_oX)-3|0,2));}),_oZ=new T(function(){var _p0=E(_oX),_p1=B(_om(_p0,2)),_p2=_p1+B(_oD(_p0,2))|0,_p3=_p2-1|0,_p4=new T(function(){return E(_oS)/5-B(_om(_p0-3|0,2))*3;}),_p5=new T(function(){var _p6=E(_oS);return _p6/4+_p6/10;}),_p7=new T(function(){return E(_oR)/16-B(_om(_p0-3|0,2));}),_p8=new T(function(){var _p9=E(_p7);return _p9+_p9;}),_pa=new T(function(){var _pb=E(_p8);return (E(_oR)-(_pb+_pb)-E(_p7)*(_p2-1))/_p2;}),_pc=new T(function(){var _pd=_p1-1|0;if(0<=_pd){var _pe=new T(function(){return E(_p5)+E(_p4)+E(_oR)/20;}),_pf=new T(function(){return (E(_oR)-(E(_pa)*_p1+E(_p7)*(_p1-1)))/2;}),_pg=function(_ph){return new T2(1,new T4(0,new T(function(){return E(_pf)+(E(_pa)+E(_p7))*_ph;}),_pe,_pa,_p4),new T(function(){if(_ph!=_pd){return B(_pg(_ph+1|0));}else{return __Z;}}));};return B(_pg(0));}else{return __Z;}});if(0<=_p3){var _pi=function(_pj){return new T2(1,new T4(0,new T(function(){return E(_p8)+(E(_pa)+E(_p7))*_pj;}),_p5,_pa,_p4),new T(function(){if(_pj!=_p3){return B(_pi(_pj+1|0));}else{return E(_pc);}}));};return B(_pi(0));}else{return E(_pc);}},1),_pk=function(_pl,_pm){var _pn=E(_pl);return {_:0,a:_pn+1|0,b:E(_pm),c:E(_62),d:0,e:7,f:E(new T2(1,new T2(0,new T(function(){return 40-16.666666666666668*E(_oY);}),_ow),_v)),g:E(_v),h:E(new T2(1,new T(function(){var _po=50-E(_oY)*10,_pp=_po&4294967295;if(_po>=_pp){return _pp;}else{return _pp-1|0;}}),_v)),i:E(_oA),j:E(new T2(1,new T(function(){return B(_a1(_oT,_pn));}),_v)),k:E(_oC),l:E(_v),m:E(_v),n:E(new T1(1,new T(function(){return B(_a1(_oU,_pn));}))),o:E(new T1(2,_pn))};};return B(_oK(_pk,_ou,_oZ));});return new T2(0,{_:0,a:0,b:E(new T4(0,new T(function(){return E(_oR)/8;}),new T(function(){return E(_oS)/10;}),new T(function(){return E(_oR)/3;}),new T(function(){return E(_oS)/5;}))),c:E(_62),d:0,e:5,f:E(_oy),g:E(_v),h:E(_cI),i:E(_oA),j:E(new T2(1,new T(function(){return B(_a1(_oT,_oV));}),_v)),k:E(_cA),l:E(_v),m:E(_v),n:E(new T1(1,new T(function(){return B(_a1(_oU,_oV));}))),o:E(_am)},_oW);},_pq=function(_pr){return E(E(_pr).a);},_ps=function(_pt){return E(E(_pt).a);},_pu=new T1(1,_5N),_pv="false",_pw=new T1(1,_5Q),_px="true",_py=function(_pz){var _pA=strEq(_pz,E(_px));if(!E(_pA)){var _pB=strEq(_pz,E(_pv));return (E(_pB)==0)?__Z:E(_pu);}else{return E(_pw);}},_pC=2,_pD="paused",_pE="ended",_pF=function(_pG,_pH){var _pI=function(_){var _pJ=E(_pH),_pK=E(_eJ),_pL=__app2(_pK,_pJ,E(_pE)),_pM=String(_pL),_pN=function(_pO){var _pP=__app2(_pK,_pJ,E(_pD));return new T(function(){var _pQ=String(_pP),_pR=B(_py(_pQ));if(!_pR._){return 0;}else{if(!E(_pR.a)){return 0;}else{return 1;}}});},_pS=B(_py(_pM));if(!_pS._){return new F(function(){return _pN(_);});}else{if(!E(_pS.a)){return new F(function(){return _pN(_);});}else{return _pC;}}};return new F(function(){return A2(_5U,_pG,_pI);});},_pT="duration",_pU=new T(function(){return eval("(function(e,t) {e.currentTime = t;})");}),_pV=function(_pW,_pX,_pY){var _pZ=new T(function(){var _q0=E(_pY);switch(_q0._){case 0:return function(_){var _q1=__app2(E(_pU),E(_pX),0);return new F(function(){return _dx(_);});};break;case 1:return function(_){var _q2=E(_pX),_q3=__app2(E(_eJ),_q2,E(_pT)),_q4=String(_q3),_q5=Number(_q4),_q6=isDoubleNaN(_q5);if(!E(_q6)){var _q7=__app2(E(_pU),_q2,_q5);return new F(function(){return _dx(_);});}else{var _q8=__app2(E(_pU),_q2,0);return new F(function(){return _dx(_);});}};break;default:return function(_){var _q9=__app2(E(_pU),E(_pX),E(_q0.a));return new F(function(){return _dx(_);});};}});return new F(function(){return A2(_5U,_pW,_pZ);});},_qa=function(_qb){return E(E(_qb).c);},_qc=function(_qd){return E(E(_qd).b);},_qe=__Z,_qf=new T(function(){return eval("(function(x){x.play();})");}),_qg=function(_qh){return E(E(_qh).b);},_qi=function(_qj,_qk){var _ql=new T(function(){return B(_pV(_qj,_qk,_qe));}),_qm=B(_ps(_qj)),_qn=new T(function(){return B(A2(_qg,B(_pq(_qm)),_5L));}),_qo=new T(function(){var _qp=function(_){var _qq=__app1(E(_qf),E(_qk));return new F(function(){return _dx(_);});};return B(A2(_5U,_qj,_qp));}),_qr=function(_qs){return new F(function(){return A3(_qa,_qm,new T(function(){if(E(_qs)==2){return E(_ql);}else{return E(_qn);}}),_qo);});};return new F(function(){return A3(_qc,_qm,new T(function(){return B(_pF(_qj,_qk));}),_qr);});},_qt=new T(function(){return B(unCStr("base"));}),_qu=new T(function(){return B(unCStr("GHC.Exception"));}),_qv=new T(function(){return B(unCStr("ArithException"));}),_qw=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_qt,_qu,_qv),_qx=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_qw,_v,_v),_qy=function(_qz){return E(_qx);},_qA=function(_qB){var _qC=E(_qB);return new F(function(){return _X(B(_V(_qC.a)),_qy,_qC.b);});},_qD=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_qE=new T(function(){return B(unCStr("denormal"));}),_qF=new T(function(){return B(unCStr("divide by zero"));}),_qG=new T(function(){return B(unCStr("loss of precision"));}),_qH=new T(function(){return B(unCStr("arithmetic underflow"));}),_qI=new T(function(){return B(unCStr("arithmetic overflow"));}),_qJ=function(_qK,_qL){switch(E(_qK)){case 0:return new F(function(){return _3(_qI,_qL);});break;case 1:return new F(function(){return _3(_qH,_qL);});break;case 2:return new F(function(){return _3(_qG,_qL);});break;case 3:return new F(function(){return _3(_qF,_qL);});break;case 4:return new F(function(){return _3(_qE,_qL);});break;default:return new F(function(){return _3(_qD,_qL);});}},_qM=function(_qN){return new F(function(){return _qJ(_qN,_v);});},_qO=function(_qP,_qQ,_qR){return new F(function(){return _qJ(_qQ,_qR);});},_qS=function(_qT,_qU){return new F(function(){return _28(_qJ,_qT,_qU);});},_qV=new T3(0,_qO,_qM,_qS),_qW=new T(function(){return new T5(0,_qy,_qV,_qX,_qA,_qM);}),_qX=function(_b8){return new T2(0,_qW,_b8);},_qY=3,_qZ=new T(function(){return B(_qX(_qY));}),_r0=new T(function(){return die(_qZ);}),_r1=0,_r2=new T(function(){return B(_qX(_r1));}),_r3=new T(function(){return die(_r2);}),_r4=function(_r5,_r6){var _r7=E(_r6);switch(_r7){case  -1:var _r8=E(_r5);if(_r8==( -2147483648)){return E(_r3);}else{return new F(function(){return _om(_r8, -1);});}break;case 0:return E(_r0);default:return new F(function(){return _om(_r5,_r7);});}},_r9=new T1(0,0),_ra=function(_rb,_rc){while(1){var _rd=E(_rb);if(!_rd._){var _re=_rd.a,_rf=E(_rc);if(!_rf._){return new T1(0,(_re>>>0|_rf.a>>>0)>>>0&4294967295);}else{_rb=new T1(1,I_fromInt(_re));_rc=_rf;continue;}}else{var _rg=E(_rc);if(!_rg._){_rb=_rd;_rc=new T1(1,I_fromInt(_rg.a));continue;}else{return new T1(1,I_or(_rd.a,_rg.a));}}}},_rh=function(_ri,_rj){while(1){var _rk=E(_ri);if(!_rk._){_ri=new T1(1,I_fromInt(_rk.a));continue;}else{return new T1(1,I_shiftLeft(_rk.a,_rj));}}},_rl=function(_rm){var _rn=E(_rm);if(!_rn._){return E(_r9);}else{return new F(function(){return _ra(new T1(0,E(_rn.a)),B(_rh(B(_rl(_rn.b)),31)));});}},_ro=new T1(0,1),_rp=new T1(0,2147483647),_rq=function(_rr,_rs){while(1){var _rt=E(_rr);if(!_rt._){var _ru=_rt.a,_rv=E(_rs);if(!_rv._){var _rw=_rv.a,_rx=addC(_ru,_rw);if(!E(_rx.b)){return new T1(0,_rx.a);}else{_rr=new T1(1,I_fromInt(_ru));_rs=new T1(1,I_fromInt(_rw));continue;}}else{_rr=new T1(1,I_fromInt(_ru));_rs=_rv;continue;}}else{var _ry=E(_rs);if(!_ry._){_rr=_rt;_rs=new T1(1,I_fromInt(_ry.a));continue;}else{return new T1(1,I_add(_rt.a,_ry.a));}}}},_rz=new T(function(){return B(_rq(_rp,_ro));}),_rA=function(_rB){var _rC=E(_rB);if(!_rC._){var _rD=E(_rC.a);return (_rD==( -2147483648))?E(_rz):new T1(0, -_rD);}else{return new T1(1,I_negate(_rC.a));}},_rE=function(_rF,_rG){if(!E(_rF)){return new F(function(){return _rA(B(_rl(_rG)));});}else{return new F(function(){return _rl(_rG);});}},_rH=1420103680,_rI=465,_rJ=new T2(1,_rI,_v),_rK=new T2(1,_rH,_rJ),_rL=new T(function(){return B(_rE(_5Q,_rK));}),_rM=function(_rN){return E(_rL);},_rO=0,_rP=function(_rQ,_rR){var _rS=E(_rR);switch(_rS){case  -1:return E(_rO);case 0:return E(_r0);default:return new F(function(){return _oD(E(_rQ),_rS);});}},_rT=new T(function(){return B(unCStr("s"));}),_rU=function(_rV,_rW){while(1){var _rX=E(_rV);if(!_rX._){return E(_rW);}else{_rV=_rX.b;_rW=_rX.a;continue;}}},_rY=function(_rZ,_s0,_s1){return new F(function(){return _rU(_s0,_rZ);});},_s2=new T1(0,1),_s3=new T1(0,1),_s4=function(_s5,_s6){var _s7=E(_s5);return new T2(0,_s7,new T(function(){var _s8=B(_s4(B(_rq(_s7,_s6)),_s6));return new T2(1,_s8.a,_s8.b);}));},_s9=function(_sa){var _sb=B(_s4(_sa,_s3));return new T2(1,_sb.a,_sb.b);},_sc=function(_sd,_se){while(1){var _sf=E(_sd);if(!_sf._){var _sg=_sf.a,_sh=E(_se);if(!_sh._){var _si=_sh.a,_sj=subC(_sg,_si);if(!E(_sj.b)){return new T1(0,_sj.a);}else{_sd=new T1(1,I_fromInt(_sg));_se=new T1(1,I_fromInt(_si));continue;}}else{_sd=new T1(1,I_fromInt(_sg));_se=_sh;continue;}}else{var _sk=E(_se);if(!_sk._){_sd=_sf;_se=new T1(1,I_fromInt(_sk.a));continue;}else{return new T1(1,I_sub(_sf.a,_sk.a));}}}},_sl=function(_sm,_sn){var _so=B(_s4(_sm,new T(function(){return B(_sc(_sn,_sm));})));return new T2(1,_so.a,_so.b);},_sp=new T1(0,0),_sq=function(_sr,_ss){var _st=E(_sr);if(!_st._){var _su=_st.a,_sv=E(_ss);return (_sv._==0)?_su>=_sv.a:I_compareInt(_sv.a,_su)<=0;}else{var _sw=_st.a,_sx=E(_ss);return (_sx._==0)?I_compareInt(_sw,_sx.a)>=0:I_compare(_sw,_sx.a)>=0;}},_sy=function(_sz,_sA){var _sB=E(_sz);if(!_sB._){var _sC=_sB.a,_sD=E(_sA);return (_sD._==0)?_sC>_sD.a:I_compareInt(_sD.a,_sC)<0;}else{var _sE=_sB.a,_sF=E(_sA);return (_sF._==0)?I_compareInt(_sE,_sF.a)>0:I_compare(_sE,_sF.a)>0;}},_sG=function(_sH,_sI){var _sJ=E(_sH);if(!_sJ._){var _sK=_sJ.a,_sL=E(_sI);return (_sL._==0)?_sK<_sL.a:I_compareInt(_sL.a,_sK)>0;}else{var _sM=_sJ.a,_sN=E(_sI);return (_sN._==0)?I_compareInt(_sM,_sN.a)<0:I_compare(_sM,_sN.a)<0;}},_sO=function(_sP,_sQ,_sR){if(!B(_sq(_sQ,_sp))){var _sS=function(_sT){return (!B(_sG(_sT,_sR)))?new T2(1,_sT,new T(function(){return B(_sS(B(_rq(_sT,_sQ))));})):__Z;};return new F(function(){return _sS(_sP);});}else{var _sU=function(_sV){return (!B(_sy(_sV,_sR)))?new T2(1,_sV,new T(function(){return B(_sU(B(_rq(_sV,_sQ))));})):__Z;};return new F(function(){return _sU(_sP);});}},_sW=function(_sX,_sY,_sZ){return new F(function(){return _sO(_sX,B(_sc(_sY,_sX)),_sZ);});},_t0=function(_t1,_t2){return new F(function(){return _sO(_t1,_s3,_t2);});},_t3=function(_t4){var _t5=E(_t4);if(!_t5._){return E(_t5.a);}else{return new F(function(){return I_toInt(_t5.a);});}},_t6=function(_t7){return new F(function(){return _t3(_t7);});},_t8=function(_t9){return new F(function(){return _sc(_t9,_s3);});},_ta=function(_tb){return new F(function(){return _rq(_tb,_s3);});},_tc=function(_td){return new T1(0,_td);},_te=function(_tf){return new F(function(){return _tc(E(_tf));});},_tg={_:0,a:_ta,b:_t8,c:_te,d:_t6,e:_s9,f:_sl,g:_t0,h:_sW},_th=function(_ti,_tj){while(1){var _tk=E(_ti);if(!_tk._){var _tl=E(_tk.a);if(_tl==( -2147483648)){_ti=new T1(1,I_fromInt( -2147483648));continue;}else{var _tm=E(_tj);if(!_tm._){return new T1(0,B(_om(_tl,_tm.a)));}else{_ti=new T1(1,I_fromInt(_tl));_tj=_tm;continue;}}}else{var _tn=_tk.a,_to=E(_tj);return (_to._==0)?new T1(1,I_div(_tn,I_fromInt(_to.a))):new T1(1,I_div(_tn,_to.a));}}},_tp=function(_tq,_tr){var _ts=E(_tq);if(!_ts._){var _tt=_ts.a,_tu=E(_tr);return (_tu._==0)?_tt==_tu.a:(I_compareInt(_tu.a,_tt)==0)?true:false;}else{var _tv=_ts.a,_tw=E(_tr);return (_tw._==0)?(I_compareInt(_tv,_tw.a)==0)?true:false:(I_compare(_tv,_tw.a)==0)?true:false;}},_tx=new T1(0,0),_ty=function(_tz,_tA){if(!B(_tp(_tA,_tx))){return new F(function(){return _th(_tz,_tA);});}else{return E(_r0);}},_tB=function(_tC,_tD){while(1){var _tE=E(_tC);if(!_tE._){var _tF=E(_tE.a);if(_tF==( -2147483648)){_tC=new T1(1,I_fromInt( -2147483648));continue;}else{var _tG=E(_tD);if(!_tG._){var _tH=_tG.a;return new T2(0,new T1(0,B(_om(_tF,_tH))),new T1(0,B(_oD(_tF,_tH))));}else{_tC=new T1(1,I_fromInt(_tF));_tD=_tG;continue;}}}else{var _tI=E(_tD);if(!_tI._){_tC=_tE;_tD=new T1(1,I_fromInt(_tI.a));continue;}else{var _tJ=I_divMod(_tE.a,_tI.a);return new T2(0,new T1(1,_tJ.a),new T1(1,_tJ.b));}}}},_tK=function(_tL,_tM){if(!B(_tp(_tM,_tx))){var _tN=B(_tB(_tL,_tM));return new T2(0,_tN.a,_tN.b);}else{return E(_r0);}},_tO=function(_tP,_tQ){while(1){var _tR=E(_tP);if(!_tR._){var _tS=E(_tR.a);if(_tS==( -2147483648)){_tP=new T1(1,I_fromInt( -2147483648));continue;}else{var _tT=E(_tQ);if(!_tT._){return new T1(0,B(_oD(_tS,_tT.a)));}else{_tP=new T1(1,I_fromInt(_tS));_tQ=_tT;continue;}}}else{var _tU=_tR.a,_tV=E(_tQ);return (_tV._==0)?new T1(1,I_mod(_tU,I_fromInt(_tV.a))):new T1(1,I_mod(_tU,_tV.a));}}},_tW=function(_tX,_tY){if(!B(_tp(_tY,_tx))){return new F(function(){return _tO(_tX,_tY);});}else{return E(_r0);}},_tZ=function(_u0,_u1){while(1){var _u2=E(_u0);if(!_u2._){var _u3=E(_u2.a);if(_u3==( -2147483648)){_u0=new T1(1,I_fromInt( -2147483648));continue;}else{var _u4=E(_u1);if(!_u4._){return new T1(0,quot(_u3,_u4.a));}else{_u0=new T1(1,I_fromInt(_u3));_u1=_u4;continue;}}}else{var _u5=_u2.a,_u6=E(_u1);return (_u6._==0)?new T1(0,I_toInt(I_quot(_u5,I_fromInt(_u6.a)))):new T1(1,I_quot(_u5,_u6.a));}}},_u7=function(_u8,_u9){if(!B(_tp(_u9,_tx))){return new F(function(){return _tZ(_u8,_u9);});}else{return E(_r0);}},_ua=function(_ub,_uc){while(1){var _ud=E(_ub);if(!_ud._){var _ue=E(_ud.a);if(_ue==( -2147483648)){_ub=new T1(1,I_fromInt( -2147483648));continue;}else{var _uf=E(_uc);if(!_uf._){var _ug=_uf.a;return new T2(0,new T1(0,quot(_ue,_ug)),new T1(0,_ue%_ug));}else{_ub=new T1(1,I_fromInt(_ue));_uc=_uf;continue;}}}else{var _uh=E(_uc);if(!_uh._){_ub=_ud;_uc=new T1(1,I_fromInt(_uh.a));continue;}else{var _ui=I_quotRem(_ud.a,_uh.a);return new T2(0,new T1(1,_ui.a),new T1(1,_ui.b));}}}},_uj=function(_uk,_ul){if(!B(_tp(_ul,_tx))){var _um=B(_ua(_uk,_ul));return new T2(0,_um.a,_um.b);}else{return E(_r0);}},_un=function(_uo,_up){while(1){var _uq=E(_uo);if(!_uq._){var _ur=E(_uq.a);if(_ur==( -2147483648)){_uo=new T1(1,I_fromInt( -2147483648));continue;}else{var _us=E(_up);if(!_us._){return new T1(0,_ur%_us.a);}else{_uo=new T1(1,I_fromInt(_ur));_up=_us;continue;}}}else{var _ut=_uq.a,_uu=E(_up);return (_uu._==0)?new T1(1,I_rem(_ut,I_fromInt(_uu.a))):new T1(1,I_rem(_ut,_uu.a));}}},_uv=function(_uw,_ux){if(!B(_tp(_ux,_tx))){return new F(function(){return _un(_uw,_ux);});}else{return E(_r0);}},_uy=function(_uz){return E(_uz);},_uA=function(_uB){return E(_uB);},_uC=function(_uD){var _uE=E(_uD);if(!_uE._){var _uF=E(_uE.a);return (_uF==( -2147483648))?E(_rz):(_uF<0)?new T1(0, -_uF):E(_uE);}else{var _uG=_uE.a;return (I_compareInt(_uG,0)>=0)?E(_uE):new T1(1,I_negate(_uG));}},_uH=new T1(0, -1),_uI=function(_uJ){var _uK=E(_uJ);if(!_uK._){var _uL=_uK.a;return (_uL>=0)?(E(_uL)==0)?E(_r9):E(_ro):E(_uH);}else{var _uM=I_compareInt(_uK.a,0);return (_uM<=0)?(E(_uM)==0)?E(_r9):E(_uH):E(_ro);}},_uN=function(_uO,_uP){while(1){var _uQ=E(_uO);if(!_uQ._){var _uR=_uQ.a,_uS=E(_uP);if(!_uS._){var _uT=_uS.a;if(!(imul(_uR,_uT)|0)){return new T1(0,imul(_uR,_uT)|0);}else{_uO=new T1(1,I_fromInt(_uR));_uP=new T1(1,I_fromInt(_uT));continue;}}else{_uO=new T1(1,I_fromInt(_uR));_uP=_uS;continue;}}else{var _uU=E(_uP);if(!_uU._){_uO=_uQ;_uP=new T1(1,I_fromInt(_uU.a));continue;}else{return new T1(1,I_mul(_uQ.a,_uU.a));}}}},_uV={_:0,a:_rq,b:_sc,c:_uN,d:_rA,e:_uC,f:_uI,g:_uA},_uW=function(_uX,_uY){var _uZ=E(_uX);if(!_uZ._){var _v0=_uZ.a,_v1=E(_uY);return (_v1._==0)?_v0!=_v1.a:(I_compareInt(_v1.a,_v0)==0)?false:true;}else{var _v2=_uZ.a,_v3=E(_uY);return (_v3._==0)?(I_compareInt(_v2,_v3.a)==0)?false:true:(I_compare(_v2,_v3.a)==0)?false:true;}},_v4=new T2(0,_tp,_uW),_v5=function(_v6,_v7){var _v8=E(_v6);if(!_v8._){var _v9=_v8.a,_va=E(_v7);return (_va._==0)?_v9<=_va.a:I_compareInt(_va.a,_v9)>=0;}else{var _vb=_v8.a,_vc=E(_v7);return (_vc._==0)?I_compareInt(_vb,_vc.a)<=0:I_compare(_vb,_vc.a)<=0;}},_vd=function(_ve,_vf){return (!B(_v5(_ve,_vf)))?E(_ve):E(_vf);},_vg=function(_vh,_vi){return (!B(_v5(_vh,_vi)))?E(_vi):E(_vh);},_vj=function(_vk,_vl){var _vm=E(_vk);if(!_vm._){var _vn=_vm.a,_vo=E(_vl);if(!_vo._){var _vp=_vo.a;return (_vn!=_vp)?(_vn>_vp)?2:0:1;}else{var _vq=I_compareInt(_vo.a,_vn);return (_vq<=0)?(_vq>=0)?1:2:0;}}else{var _vr=_vm.a,_vs=E(_vl);if(!_vs._){var _vt=I_compareInt(_vr,_vs.a);return (_vt>=0)?(_vt<=0)?1:2:0;}else{var _vu=I_compare(_vr,_vs.a);return (_vu>=0)?(_vu<=0)?1:2:0;}}},_vv={_:0,a:_v4,b:_vj,c:_sG,d:_v5,e:_sy,f:_sq,g:_vd,h:_vg},_vw=function(_vx){return new T2(0,E(_vx),E(_s2));},_vy=new T3(0,_uV,_vv,_vw),_vz={_:0,a:_vy,b:_tg,c:_u7,d:_uv,e:_ty,f:_tW,g:_uj,h:_tK,i:_uy},_vA=new T1(0,0),_vB=function(_vC,_vD,_vE){var _vF=B(A1(_vC,_vD));if(!B(_tp(_vF,_vA))){return new F(function(){return _th(B(_uN(_vD,_vE)),_vF);});}else{return E(_r0);}},_vG=function(_vH,_vI){while(1){if(!B(_tp(_vI,_tx))){var _vJ=_vI,_vK=B(_uv(_vH,_vI));_vH=_vJ;_vI=_vK;continue;}else{return E(_vH);}}},_vL=5,_vM=new T(function(){return B(_qX(_vL));}),_vN=new T(function(){return die(_vM);}),_vO=function(_vP,_vQ){if(!B(_tp(_vQ,_tx))){var _vR=B(_vG(B(_uC(_vP)),B(_uC(_vQ))));return (!B(_tp(_vR,_tx)))?new T2(0,B(_tZ(_vP,_vR)),B(_tZ(_vQ,_vR))):E(_r0);}else{return E(_vN);}},_vS=function(_vT,_vU,_vV,_vW){var _vX=B(_uN(_vU,_vV));return new F(function(){return _vO(B(_uN(B(_uN(_vT,_vW)),B(_uI(_vX)))),B(_uC(_vX)));});},_vY=function(_vZ){return E(E(_vZ).a);},_w0=function(_w1){return E(E(_w1).a);},_w2=function(_w3){return E(E(_w3).g);},_w4=function(_w5,_w6,_w7){var _w8=new T(function(){if(!B(_tp(_w7,_tx))){var _w9=B(_ua(_w6,_w7));return new T2(0,_w9.a,_w9.b);}else{return E(_r0);}}),_wa=new T(function(){return B(A2(_w2,B(_w0(B(_vY(_w5)))),new T(function(){return E(E(_w8).a);})));});return new T2(0,_wa,new T(function(){return new T2(0,E(E(_w8).b),E(_w7));}));},_wb=function(_wc){return E(E(_wc).b);},_wd=function(_we,_wf,_wg){var _wh=B(_w4(_we,_wf,_wg)),_wi=_wh.a,_wj=E(_wh.b);if(!B(_sG(B(_uN(_wj.a,_s2)),B(_uN(_tx,_wj.b))))){return E(_wi);}else{var _wk=B(_w0(B(_vY(_we))));return new F(function(){return A3(_wb,_wk,_wi,new T(function(){return B(A2(_w2,_wk,_s2));}));});}},_wl=479723520,_wm=40233135,_wn=new T2(1,_wm,_v),_wo=new T2(1,_wl,_wn),_wp=new T(function(){return B(_rE(_5Q,_wo));}),_wq=new T1(0,40587),_wr=function(_ws){var _wt=new T(function(){var _wu=B(_vS(_ws,_s2,_rL,_s2)),_wv=B(_vS(_wp,_s2,_rL,_s2)),_ww=B(_vS(_wu.a,_wu.b,_wv.a,_wv.b));return B(_wd(_vz,_ww.a,_ww.b));});return new T2(0,new T(function(){return B(_rq(_wq,_wt));}),new T(function(){return B(_sc(_ws,B(_vB(_rM,B(_uN(_wt,_rL)),_wp))));}));},_wx=function(_wy,_wz){var _wA=E(_wz);if(!_wA._){return __Z;}else{var _wB=_wA.a,_wC=E(_wy);return (_wC==1)?new T2(1,_wB,_v):new T2(1,_wB,new T(function(){return B(_wx(_wC-1|0,_wA.b));}));}},_wD=function(_wE,_){var _wF=__get(_wE,0),_wG=__get(_wE,1),_wH=Number(_wF),_wI=jsTrunc(_wH),_wJ=Number(_wG),_wK=jsTrunc(_wJ);return new T2(0,_wI,_wK);},_wL=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_wM=660865024,_wN=465661287,_wO=new T2(1,_wN,_v),_wP=new T2(1,_wM,_wO),_wQ=new T(function(){return B(_rE(_5Q,_wP));}),_wR=function(_){var _wS=__app0(E(_wL)),_wT=B(_wD(_wS,_));return new T(function(){var _wU=E(_wT);if(!B(_tp(_wQ,_vA))){return B(_rq(B(_uN(B(_tc(E(_wU.a))),_rL)),B(_th(B(_uN(B(_uN(B(_tc(E(_wU.b))),_rL)),_rL)),_wQ))));}else{return E(_r0);}});},_wV=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_wW=new T(function(){return B(err(_wV));}),_wX=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_wY=new T(function(){return B(err(_wX));}),_wZ=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_x0=function(_x1){return new F(function(){return _b6(new T1(0,new T(function(){return B(_bk(_x1,_wZ));})),_aQ);});},_x2=new T(function(){return B(_x0("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_x3=function(_x4,_x5){while(1){var _x6=B((function(_x7,_x8){var _x9=E(_x7);switch(_x9._){case 0:var _xa=E(_x8);if(!_xa._){return __Z;}else{_x4=B(A1(_x9.a,_xa.a));_x5=_xa.b;return __continue;}break;case 1:var _xb=B(A1(_x9.a,_x8)),_xc=_x8;_x4=_xb;_x5=_xc;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_x9.a,_x8),new T(function(){return B(_x3(_x9.b,_x8));}));default:return E(_x9.a);}})(_x4,_x5));if(_x6!=__continue){return _x6;}}},_xd=function(_xe,_xf){var _xg=function(_xh){var _xi=E(_xf);if(_xi._==3){return new T2(3,_xi.a,new T(function(){return B(_xd(_xe,_xi.b));}));}else{var _xj=E(_xe);if(_xj._==2){return E(_xi);}else{var _xk=E(_xi);if(_xk._==2){return E(_xj);}else{var _xl=function(_xm){var _xn=E(_xk);if(_xn._==4){var _xo=function(_xp){return new T1(4,new T(function(){return B(_3(B(_x3(_xj,_xp)),_xn.a));}));};return new T1(1,_xo);}else{var _xq=E(_xj);if(_xq._==1){var _xr=_xq.a,_xs=E(_xn);if(!_xs._){return new T1(1,function(_xt){return new F(function(){return _xd(B(A1(_xr,_xt)),_xs);});});}else{var _xu=function(_xv){return new F(function(){return _xd(B(A1(_xr,_xv)),new T(function(){return B(A1(_xs.a,_xv));}));});};return new T1(1,_xu);}}else{var _xw=E(_xn);if(!_xw._){return E(_x2);}else{var _xx=function(_xy){return new F(function(){return _xd(_xq,new T(function(){return B(A1(_xw.a,_xy));}));});};return new T1(1,_xx);}}}},_xz=E(_xj);switch(_xz._){case 1:var _xA=E(_xk);if(_xA._==4){var _xB=function(_xC){return new T1(4,new T(function(){return B(_3(B(_x3(B(A1(_xz.a,_xC)),_xC)),_xA.a));}));};return new T1(1,_xB);}else{return new F(function(){return _xl(_);});}break;case 4:var _xD=_xz.a,_xE=E(_xk);switch(_xE._){case 0:var _xF=function(_xG){var _xH=new T(function(){return B(_3(_xD,new T(function(){return B(_x3(_xE,_xG));},1)));});return new T1(4,_xH);};return new T1(1,_xF);case 1:var _xI=function(_xJ){var _xK=new T(function(){return B(_3(_xD,new T(function(){return B(_x3(B(A1(_xE.a,_xJ)),_xJ));},1)));});return new T1(4,_xK);};return new T1(1,_xI);default:return new T1(4,new T(function(){return B(_3(_xD,_xE.a));}));}break;default:return new F(function(){return _xl(_);});}}}}},_xL=E(_xe);switch(_xL._){case 0:var _xM=E(_xf);if(!_xM._){var _xN=function(_xO){return new F(function(){return _xd(B(A1(_xL.a,_xO)),new T(function(){return B(A1(_xM.a,_xO));}));});};return new T1(0,_xN);}else{return new F(function(){return _xg(_);});}break;case 3:return new T2(3,_xL.a,new T(function(){return B(_xd(_xL.b,_xf));}));default:return new F(function(){return _xg(_);});}},_xP=new T(function(){return B(unCStr("("));}),_xQ=new T(function(){return B(unCStr(")"));}),_xR=function(_xS,_xT){return (!B(_7k(_xS,_xT)))?true:false;},_xU=new T2(0,_7k,_xR),_xV=function(_xW,_xX){var _xY=E(_xW);switch(_xY._){case 0:return new T1(0,function(_xZ){return new F(function(){return _xV(B(A1(_xY.a,_xZ)),_xX);});});case 1:return new T1(1,function(_y0){return new F(function(){return _xV(B(A1(_xY.a,_y0)),_xX);});});case 2:return new T0(2);case 3:return new F(function(){return _xd(B(A1(_xX,_xY.a)),new T(function(){return B(_xV(_xY.b,_xX));}));});break;default:var _y1=function(_y2){var _y3=E(_y2);if(!_y3._){return __Z;}else{var _y4=E(_y3.a);return new F(function(){return _3(B(_x3(B(A1(_xX,_y4.a)),_y4.b)),new T(function(){return B(_y1(_y3.b));},1));});}},_y5=B(_y1(_xY.a));return (_y5._==0)?new T0(2):new T1(4,_y5);}},_y6=new T0(2),_y7=function(_y8){return new T2(3,_y8,_y6);},_y9=function(_ya,_yb){var _yc=E(_ya);if(!_yc){return new F(function(){return A1(_yb,_5L);});}else{var _yd=new T(function(){return B(_y9(_yc-1|0,_yb));});return new T1(0,function(_ye){return E(_yd);});}},_yf=function(_yg,_yh,_yi){var _yj=new T(function(){return B(A1(_yg,_y7));}),_yk=function(_yl,_ym,_yn,_yo){while(1){var _yp=B((function(_yq,_yr,_ys,_yt){var _yu=E(_yq);switch(_yu._){case 0:var _yv=E(_yr);if(!_yv._){return new F(function(){return A1(_yh,_yt);});}else{var _yw=_ys+1|0,_yx=_yt;_yl=B(A1(_yu.a,_yv.a));_ym=_yv.b;_yn=_yw;_yo=_yx;return __continue;}break;case 1:var _yy=B(A1(_yu.a,_yr)),_yz=_yr,_yw=_ys,_yx=_yt;_yl=_yy;_ym=_yz;_yn=_yw;_yo=_yx;return __continue;case 2:return new F(function(){return A1(_yh,_yt);});break;case 3:var _yA=new T(function(){return B(_xV(_yu,_yt));});return new F(function(){return _y9(_ys,function(_yB){return E(_yA);});});break;default:return new F(function(){return _xV(_yu,_yt);});}})(_yl,_ym,_yn,_yo));if(_yp!=__continue){return _yp;}}};return function(_yC){return new F(function(){return _yk(_yj,_yC,0,_yi);});};},_yD=function(_yE){return new F(function(){return A1(_yE,_v);});},_yF=function(_yG,_yH){var _yI=function(_yJ){var _yK=E(_yJ);if(!_yK._){return E(_yD);}else{var _yL=_yK.a;if(!B(A1(_yG,_yL))){return E(_yD);}else{var _yM=new T(function(){return B(_yI(_yK.b));}),_yN=function(_yO){var _yP=new T(function(){return B(A1(_yM,function(_yQ){return new F(function(){return A1(_yO,new T2(1,_yL,_yQ));});}));});return new T1(0,function(_yR){return E(_yP);});};return E(_yN);}}};return function(_yS){return new F(function(){return A2(_yI,_yS,_yH);});};},_yT=new T0(6),_yU=new T(function(){return B(unCStr("valDig: Bad base"));}),_yV=new T(function(){return B(err(_yU));}),_yW=function(_yX,_yY){var _yZ=function(_z0,_z1){var _z2=E(_z0);if(!_z2._){var _z3=new T(function(){return B(A1(_z1,_v));});return function(_z4){return new F(function(){return A1(_z4,_z3);});};}else{var _z5=E(_z2.a),_z6=function(_z7){var _z8=new T(function(){return B(_yZ(_z2.b,function(_z9){return new F(function(){return A1(_z1,new T2(1,_z7,_z9));});}));}),_za=function(_zb){var _zc=new T(function(){return B(A1(_z8,_zb));});return new T1(0,function(_zd){return E(_zc);});};return E(_za);};switch(E(_yX)){case 8:if(48>_z5){var _ze=new T(function(){return B(A1(_z1,_v));});return function(_zf){return new F(function(){return A1(_zf,_ze);});};}else{if(_z5>55){var _zg=new T(function(){return B(A1(_z1,_v));});return function(_zh){return new F(function(){return A1(_zh,_zg);});};}else{return new F(function(){return _z6(_z5-48|0);});}}break;case 10:if(48>_z5){var _zi=new T(function(){return B(A1(_z1,_v));});return function(_zj){return new F(function(){return A1(_zj,_zi);});};}else{if(_z5>57){var _zk=new T(function(){return B(A1(_z1,_v));});return function(_zl){return new F(function(){return A1(_zl,_zk);});};}else{return new F(function(){return _z6(_z5-48|0);});}}break;case 16:if(48>_z5){if(97>_z5){if(65>_z5){var _zm=new T(function(){return B(A1(_z1,_v));});return function(_zn){return new F(function(){return A1(_zn,_zm);});};}else{if(_z5>70){var _zo=new T(function(){return B(A1(_z1,_v));});return function(_zp){return new F(function(){return A1(_zp,_zo);});};}else{return new F(function(){return _z6((_z5-65|0)+10|0);});}}}else{if(_z5>102){if(65>_z5){var _zq=new T(function(){return B(A1(_z1,_v));});return function(_zr){return new F(function(){return A1(_zr,_zq);});};}else{if(_z5>70){var _zs=new T(function(){return B(A1(_z1,_v));});return function(_zt){return new F(function(){return A1(_zt,_zs);});};}else{return new F(function(){return _z6((_z5-65|0)+10|0);});}}}else{return new F(function(){return _z6((_z5-97|0)+10|0);});}}}else{if(_z5>57){if(97>_z5){if(65>_z5){var _zu=new T(function(){return B(A1(_z1,_v));});return function(_zv){return new F(function(){return A1(_zv,_zu);});};}else{if(_z5>70){var _zw=new T(function(){return B(A1(_z1,_v));});return function(_zx){return new F(function(){return A1(_zx,_zw);});};}else{return new F(function(){return _z6((_z5-65|0)+10|0);});}}}else{if(_z5>102){if(65>_z5){var _zy=new T(function(){return B(A1(_z1,_v));});return function(_zz){return new F(function(){return A1(_zz,_zy);});};}else{if(_z5>70){var _zA=new T(function(){return B(A1(_z1,_v));});return function(_zB){return new F(function(){return A1(_zB,_zA);});};}else{return new F(function(){return _z6((_z5-65|0)+10|0);});}}}else{return new F(function(){return _z6((_z5-97|0)+10|0);});}}}else{return new F(function(){return _z6(_z5-48|0);});}}break;default:return E(_yV);}}},_zC=function(_zD){var _zE=E(_zD);if(!_zE._){return new T0(2);}else{return new F(function(){return A1(_yY,_zE);});}};return function(_zF){return new F(function(){return A3(_yZ,_zF,_5x,_zC);});};},_zG=16,_zH=8,_zI=function(_zJ){var _zK=function(_zL){return new F(function(){return A1(_zJ,new T1(5,new T2(0,_zH,_zL)));});},_zM=function(_zN){return new F(function(){return A1(_zJ,new T1(5,new T2(0,_zG,_zN)));});},_zO=function(_zP){switch(E(_zP)){case 79:return new T1(1,B(_yW(_zH,_zK)));case 88:return new T1(1,B(_yW(_zG,_zM)));case 111:return new T1(1,B(_yW(_zH,_zK)));case 120:return new T1(1,B(_yW(_zG,_zM)));default:return new T0(2);}};return function(_zQ){return (E(_zQ)==48)?E(new T1(0,_zO)):new T0(2);};},_zR=function(_zS){return new T1(0,B(_zI(_zS)));},_zT=function(_zU){return new F(function(){return A1(_zU,_2q);});},_zV=function(_zW){return new F(function(){return A1(_zW,_2q);});},_zX=10,_zY=new T1(0,10),_zZ=function(_A0){return new F(function(){return _tc(E(_A0));});},_A1=new T(function(){return B(unCStr("this should not happen"));}),_A2=new T(function(){return B(err(_A1));}),_A3=function(_A4,_A5){var _A6=E(_A5);if(!_A6._){return __Z;}else{var _A7=E(_A6.b);return (_A7._==0)?E(_A2):new T2(1,B(_rq(B(_uN(_A6.a,_A4)),_A7.a)),new T(function(){return B(_A3(_A4,_A7.b));}));}},_A8=new T1(0,0),_A9=function(_Aa,_Ab,_Ac){while(1){var _Ad=B((function(_Ae,_Af,_Ag){var _Ah=E(_Ag);if(!_Ah._){return E(_A8);}else{if(!E(_Ah.b)._){return E(_Ah.a);}else{var _Ai=E(_Af);if(_Ai<=40){var _Aj=function(_Ak,_Al){while(1){var _Am=E(_Al);if(!_Am._){return E(_Ak);}else{var _An=B(_rq(B(_uN(_Ak,_Ae)),_Am.a));_Ak=_An;_Al=_Am.b;continue;}}};return new F(function(){return _Aj(_A8,_Ah);});}else{var _Ao=B(_uN(_Ae,_Ae));if(!(_Ai%2)){var _Ap=B(_A3(_Ae,_Ah));_Aa=_Ao;_Ab=quot(_Ai+1|0,2);_Ac=_Ap;return __continue;}else{var _Ap=B(_A3(_Ae,new T2(1,_A8,_Ah)));_Aa=_Ao;_Ab=quot(_Ai+1|0,2);_Ac=_Ap;return __continue;}}}}})(_Aa,_Ab,_Ac));if(_Ad!=__continue){return _Ad;}}},_Aq=function(_Ar,_As){return new F(function(){return _A9(_Ar,new T(function(){return B(_9C(_As,0));},1),B(_d5(_zZ,_As)));});},_At=function(_Au){var _Av=new T(function(){var _Aw=new T(function(){var _Ax=function(_Ay){return new F(function(){return A1(_Au,new T1(1,new T(function(){return B(_Aq(_zY,_Ay));})));});};return new T1(1,B(_yW(_zX,_Ax)));}),_Az=function(_AA){if(E(_AA)==43){var _AB=function(_AC){return new F(function(){return A1(_Au,new T1(1,new T(function(){return B(_Aq(_zY,_AC));})));});};return new T1(1,B(_yW(_zX,_AB)));}else{return new T0(2);}},_AD=function(_AE){if(E(_AE)==45){var _AF=function(_AG){return new F(function(){return A1(_Au,new T1(1,new T(function(){return B(_rA(B(_Aq(_zY,_AG))));})));});};return new T1(1,B(_yW(_zX,_AF)));}else{return new T0(2);}};return B(_xd(B(_xd(new T1(0,_AD),new T1(0,_Az))),_Aw));});return new F(function(){return _xd(new T1(0,function(_AH){return (E(_AH)==101)?E(_Av):new T0(2);}),new T1(0,function(_AI){return (E(_AI)==69)?E(_Av):new T0(2);}));});},_AJ=function(_AK){var _AL=function(_AM){return new F(function(){return A1(_AK,new T1(1,_AM));});};return function(_AN){return (E(_AN)==46)?new T1(1,B(_yW(_zX,_AL))):new T0(2);};},_AO=function(_AP){return new T1(0,B(_AJ(_AP)));},_AQ=function(_AR){var _AS=function(_AT){var _AU=function(_AV){return new T1(1,B(_yf(_At,_zT,function(_AW){return new F(function(){return A1(_AR,new T1(5,new T3(1,_AT,_AV,_AW)));});})));};return new T1(1,B(_yf(_AO,_zV,_AU)));};return new F(function(){return _yW(_zX,_AS);});},_AX=function(_AY){return new T1(1,B(_AQ(_AY)));},_AZ=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_B0=function(_B1){return new F(function(){return _4d(_dO,_B1,_AZ);});},_B2=function(_B3){var _B4=new T(function(){return B(A1(_B3,_zH));}),_B5=new T(function(){return B(A1(_B3,_zG));});return function(_B6){switch(E(_B6)){case 79:return E(_B4);case 88:return E(_B5);case 111:return E(_B4);case 120:return E(_B5);default:return new T0(2);}};},_B7=function(_B8){return new T1(0,B(_B2(_B8)));},_B9=function(_Ba){return new F(function(){return A1(_Ba,_zX);});},_Bb=function(_Bc){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_d(9,_Bc,_v));}))));});},_Bd=function(_Be){return new T0(2);},_Bf=function(_Bg){var _Bh=E(_Bg);if(!_Bh._){return E(_Bd);}else{var _Bi=_Bh.a,_Bj=E(_Bh.b);if(!_Bj._){return E(_Bi);}else{var _Bk=new T(function(){return B(_Bf(_Bj));}),_Bl=function(_Bm){return new F(function(){return _xd(B(A1(_Bi,_Bm)),new T(function(){return B(A1(_Bk,_Bm));}));});};return E(_Bl);}}},_Bn=function(_Bo,_Bp){var _Bq=function(_Br,_Bs,_Bt){var _Bu=E(_Br);if(!_Bu._){return new F(function(){return A1(_Bt,_Bo);});}else{var _Bv=E(_Bs);if(!_Bv._){return new T0(2);}else{if(E(_Bu.a)!=E(_Bv.a)){return new T0(2);}else{var _Bw=new T(function(){return B(_Bq(_Bu.b,_Bv.b,_Bt));});return new T1(0,function(_Bx){return E(_Bw);});}}}};return function(_By){return new F(function(){return _Bq(_Bo,_By,_Bp);});};},_Bz=new T(function(){return B(unCStr("SO"));}),_BA=14,_BB=function(_BC){var _BD=new T(function(){return B(A1(_BC,_BA));});return new T1(1,B(_Bn(_Bz,function(_BE){return E(_BD);})));},_BF=new T(function(){return B(unCStr("SOH"));}),_BG=1,_BH=function(_BI){var _BJ=new T(function(){return B(A1(_BI,_BG));});return new T1(1,B(_Bn(_BF,function(_BK){return E(_BJ);})));},_BL=function(_BM){return new T1(1,B(_yf(_BH,_BB,_BM)));},_BN=new T(function(){return B(unCStr("NUL"));}),_BO=0,_BP=function(_BQ){var _BR=new T(function(){return B(A1(_BQ,_BO));});return new T1(1,B(_Bn(_BN,function(_BS){return E(_BR);})));},_BT=new T(function(){return B(unCStr("STX"));}),_BU=2,_BV=function(_BW){var _BX=new T(function(){return B(A1(_BW,_BU));});return new T1(1,B(_Bn(_BT,function(_BY){return E(_BX);})));},_BZ=new T(function(){return B(unCStr("ETX"));}),_C0=3,_C1=function(_C2){var _C3=new T(function(){return B(A1(_C2,_C0));});return new T1(1,B(_Bn(_BZ,function(_C4){return E(_C3);})));},_C5=new T(function(){return B(unCStr("EOT"));}),_C6=4,_C7=function(_C8){var _C9=new T(function(){return B(A1(_C8,_C6));});return new T1(1,B(_Bn(_C5,function(_Ca){return E(_C9);})));},_Cb=new T(function(){return B(unCStr("ENQ"));}),_Cc=5,_Cd=function(_Ce){var _Cf=new T(function(){return B(A1(_Ce,_Cc));});return new T1(1,B(_Bn(_Cb,function(_Cg){return E(_Cf);})));},_Ch=new T(function(){return B(unCStr("ACK"));}),_Ci=6,_Cj=function(_Ck){var _Cl=new T(function(){return B(A1(_Ck,_Ci));});return new T1(1,B(_Bn(_Ch,function(_Cm){return E(_Cl);})));},_Cn=new T(function(){return B(unCStr("BEL"));}),_Co=7,_Cp=function(_Cq){var _Cr=new T(function(){return B(A1(_Cq,_Co));});return new T1(1,B(_Bn(_Cn,function(_Cs){return E(_Cr);})));},_Ct=new T(function(){return B(unCStr("BS"));}),_Cu=8,_Cv=function(_Cw){var _Cx=new T(function(){return B(A1(_Cw,_Cu));});return new T1(1,B(_Bn(_Ct,function(_Cy){return E(_Cx);})));},_Cz=new T(function(){return B(unCStr("HT"));}),_CA=9,_CB=function(_CC){var _CD=new T(function(){return B(A1(_CC,_CA));});return new T1(1,B(_Bn(_Cz,function(_CE){return E(_CD);})));},_CF=new T(function(){return B(unCStr("LF"));}),_CG=10,_CH=function(_CI){var _CJ=new T(function(){return B(A1(_CI,_CG));});return new T1(1,B(_Bn(_CF,function(_CK){return E(_CJ);})));},_CL=new T(function(){return B(unCStr("VT"));}),_CM=11,_CN=function(_CO){var _CP=new T(function(){return B(A1(_CO,_CM));});return new T1(1,B(_Bn(_CL,function(_CQ){return E(_CP);})));},_CR=new T(function(){return B(unCStr("FF"));}),_CS=12,_CT=function(_CU){var _CV=new T(function(){return B(A1(_CU,_CS));});return new T1(1,B(_Bn(_CR,function(_CW){return E(_CV);})));},_CX=new T(function(){return B(unCStr("CR"));}),_CY=13,_CZ=function(_D0){var _D1=new T(function(){return B(A1(_D0,_CY));});return new T1(1,B(_Bn(_CX,function(_D2){return E(_D1);})));},_D3=new T(function(){return B(unCStr("SI"));}),_D4=15,_D5=function(_D6){var _D7=new T(function(){return B(A1(_D6,_D4));});return new T1(1,B(_Bn(_D3,function(_D8){return E(_D7);})));},_D9=new T(function(){return B(unCStr("DLE"));}),_Da=16,_Db=function(_Dc){var _Dd=new T(function(){return B(A1(_Dc,_Da));});return new T1(1,B(_Bn(_D9,function(_De){return E(_Dd);})));},_Df=new T(function(){return B(unCStr("DC1"));}),_Dg=17,_Dh=function(_Di){var _Dj=new T(function(){return B(A1(_Di,_Dg));});return new T1(1,B(_Bn(_Df,function(_Dk){return E(_Dj);})));},_Dl=new T(function(){return B(unCStr("DC2"));}),_Dm=18,_Dn=function(_Do){var _Dp=new T(function(){return B(A1(_Do,_Dm));});return new T1(1,B(_Bn(_Dl,function(_Dq){return E(_Dp);})));},_Dr=new T(function(){return B(unCStr("DC3"));}),_Ds=19,_Dt=function(_Du){var _Dv=new T(function(){return B(A1(_Du,_Ds));});return new T1(1,B(_Bn(_Dr,function(_Dw){return E(_Dv);})));},_Dx=new T(function(){return B(unCStr("DC4"));}),_Dy=20,_Dz=function(_DA){var _DB=new T(function(){return B(A1(_DA,_Dy));});return new T1(1,B(_Bn(_Dx,function(_DC){return E(_DB);})));},_DD=new T(function(){return B(unCStr("NAK"));}),_DE=21,_DF=function(_DG){var _DH=new T(function(){return B(A1(_DG,_DE));});return new T1(1,B(_Bn(_DD,function(_DI){return E(_DH);})));},_DJ=new T(function(){return B(unCStr("SYN"));}),_DK=22,_DL=function(_DM){var _DN=new T(function(){return B(A1(_DM,_DK));});return new T1(1,B(_Bn(_DJ,function(_DO){return E(_DN);})));},_DP=new T(function(){return B(unCStr("ETB"));}),_DQ=23,_DR=function(_DS){var _DT=new T(function(){return B(A1(_DS,_DQ));});return new T1(1,B(_Bn(_DP,function(_DU){return E(_DT);})));},_DV=new T(function(){return B(unCStr("CAN"));}),_DW=24,_DX=function(_DY){var _DZ=new T(function(){return B(A1(_DY,_DW));});return new T1(1,B(_Bn(_DV,function(_E0){return E(_DZ);})));},_E1=new T(function(){return B(unCStr("EM"));}),_E2=25,_E3=function(_E4){var _E5=new T(function(){return B(A1(_E4,_E2));});return new T1(1,B(_Bn(_E1,function(_E6){return E(_E5);})));},_E7=new T(function(){return B(unCStr("SUB"));}),_E8=26,_E9=function(_Ea){var _Eb=new T(function(){return B(A1(_Ea,_E8));});return new T1(1,B(_Bn(_E7,function(_Ec){return E(_Eb);})));},_Ed=new T(function(){return B(unCStr("ESC"));}),_Ee=27,_Ef=function(_Eg){var _Eh=new T(function(){return B(A1(_Eg,_Ee));});return new T1(1,B(_Bn(_Ed,function(_Ei){return E(_Eh);})));},_Ej=new T(function(){return B(unCStr("FS"));}),_Ek=28,_El=function(_Em){var _En=new T(function(){return B(A1(_Em,_Ek));});return new T1(1,B(_Bn(_Ej,function(_Eo){return E(_En);})));},_Ep=new T(function(){return B(unCStr("GS"));}),_Eq=29,_Er=function(_Es){var _Et=new T(function(){return B(A1(_Es,_Eq));});return new T1(1,B(_Bn(_Ep,function(_Eu){return E(_Et);})));},_Ev=new T(function(){return B(unCStr("RS"));}),_Ew=30,_Ex=function(_Ey){var _Ez=new T(function(){return B(A1(_Ey,_Ew));});return new T1(1,B(_Bn(_Ev,function(_EA){return E(_Ez);})));},_EB=new T(function(){return B(unCStr("US"));}),_EC=31,_ED=function(_EE){var _EF=new T(function(){return B(A1(_EE,_EC));});return new T1(1,B(_Bn(_EB,function(_EG){return E(_EF);})));},_EH=new T(function(){return B(unCStr("SP"));}),_EI=32,_EJ=function(_EK){var _EL=new T(function(){return B(A1(_EK,_EI));});return new T1(1,B(_Bn(_EH,function(_EM){return E(_EL);})));},_EN=new T(function(){return B(unCStr("DEL"));}),_EO=127,_EP=function(_EQ){var _ER=new T(function(){return B(A1(_EQ,_EO));});return new T1(1,B(_Bn(_EN,function(_ES){return E(_ER);})));},_ET=new T2(1,_EP,_v),_EU=new T2(1,_EJ,_ET),_EV=new T2(1,_ED,_EU),_EW=new T2(1,_Ex,_EV),_EX=new T2(1,_Er,_EW),_EY=new T2(1,_El,_EX),_EZ=new T2(1,_Ef,_EY),_F0=new T2(1,_E9,_EZ),_F1=new T2(1,_E3,_F0),_F2=new T2(1,_DX,_F1),_F3=new T2(1,_DR,_F2),_F4=new T2(1,_DL,_F3),_F5=new T2(1,_DF,_F4),_F6=new T2(1,_Dz,_F5),_F7=new T2(1,_Dt,_F6),_F8=new T2(1,_Dn,_F7),_F9=new T2(1,_Dh,_F8),_Fa=new T2(1,_Db,_F9),_Fb=new T2(1,_D5,_Fa),_Fc=new T2(1,_CZ,_Fb),_Fd=new T2(1,_CT,_Fc),_Fe=new T2(1,_CN,_Fd),_Ff=new T2(1,_CH,_Fe),_Fg=new T2(1,_CB,_Ff),_Fh=new T2(1,_Cv,_Fg),_Fi=new T2(1,_Cp,_Fh),_Fj=new T2(1,_Cj,_Fi),_Fk=new T2(1,_Cd,_Fj),_Fl=new T2(1,_C7,_Fk),_Fm=new T2(1,_C1,_Fl),_Fn=new T2(1,_BV,_Fm),_Fo=new T2(1,_BP,_Fn),_Fp=new T2(1,_BL,_Fo),_Fq=new T(function(){return B(_Bf(_Fp));}),_Fr=34,_Fs=new T1(0,1114111),_Ft=92,_Fu=39,_Fv=function(_Fw){var _Fx=new T(function(){return B(A1(_Fw,_Co));}),_Fy=new T(function(){return B(A1(_Fw,_Cu));}),_Fz=new T(function(){return B(A1(_Fw,_CA));}),_FA=new T(function(){return B(A1(_Fw,_CG));}),_FB=new T(function(){return B(A1(_Fw,_CM));}),_FC=new T(function(){return B(A1(_Fw,_CS));}),_FD=new T(function(){return B(A1(_Fw,_CY));}),_FE=new T(function(){return B(A1(_Fw,_Ft));}),_FF=new T(function(){return B(A1(_Fw,_Fu));}),_FG=new T(function(){return B(A1(_Fw,_Fr));}),_FH=new T(function(){var _FI=function(_FJ){var _FK=new T(function(){return B(_tc(E(_FJ)));}),_FL=function(_FM){var _FN=B(_Aq(_FK,_FM));if(!B(_v5(_FN,_Fs))){return new T0(2);}else{return new F(function(){return A1(_Fw,new T(function(){var _FO=B(_t3(_FN));if(_FO>>>0>1114111){return B(_Bb(_FO));}else{return _FO;}}));});}};return new T1(1,B(_yW(_FJ,_FL)));},_FP=new T(function(){var _FQ=new T(function(){return B(A1(_Fw,_EC));}),_FR=new T(function(){return B(A1(_Fw,_Ew));}),_FS=new T(function(){return B(A1(_Fw,_Eq));}),_FT=new T(function(){return B(A1(_Fw,_Ek));}),_FU=new T(function(){return B(A1(_Fw,_Ee));}),_FV=new T(function(){return B(A1(_Fw,_E8));}),_FW=new T(function(){return B(A1(_Fw,_E2));}),_FX=new T(function(){return B(A1(_Fw,_DW));}),_FY=new T(function(){return B(A1(_Fw,_DQ));}),_FZ=new T(function(){return B(A1(_Fw,_DK));}),_G0=new T(function(){return B(A1(_Fw,_DE));}),_G1=new T(function(){return B(A1(_Fw,_Dy));}),_G2=new T(function(){return B(A1(_Fw,_Ds));}),_G3=new T(function(){return B(A1(_Fw,_Dm));}),_G4=new T(function(){return B(A1(_Fw,_Dg));}),_G5=new T(function(){return B(A1(_Fw,_Da));}),_G6=new T(function(){return B(A1(_Fw,_D4));}),_G7=new T(function(){return B(A1(_Fw,_BA));}),_G8=new T(function(){return B(A1(_Fw,_Ci));}),_G9=new T(function(){return B(A1(_Fw,_Cc));}),_Ga=new T(function(){return B(A1(_Fw,_C6));}),_Gb=new T(function(){return B(A1(_Fw,_C0));}),_Gc=new T(function(){return B(A1(_Fw,_BU));}),_Gd=new T(function(){return B(A1(_Fw,_BG));}),_Ge=new T(function(){return B(A1(_Fw,_BO));}),_Gf=function(_Gg){switch(E(_Gg)){case 64:return E(_Ge);case 65:return E(_Gd);case 66:return E(_Gc);case 67:return E(_Gb);case 68:return E(_Ga);case 69:return E(_G9);case 70:return E(_G8);case 71:return E(_Fx);case 72:return E(_Fy);case 73:return E(_Fz);case 74:return E(_FA);case 75:return E(_FB);case 76:return E(_FC);case 77:return E(_FD);case 78:return E(_G7);case 79:return E(_G6);case 80:return E(_G5);case 81:return E(_G4);case 82:return E(_G3);case 83:return E(_G2);case 84:return E(_G1);case 85:return E(_G0);case 86:return E(_FZ);case 87:return E(_FY);case 88:return E(_FX);case 89:return E(_FW);case 90:return E(_FV);case 91:return E(_FU);case 92:return E(_FT);case 93:return E(_FS);case 94:return E(_FR);case 95:return E(_FQ);default:return new T0(2);}};return B(_xd(new T1(0,function(_Gh){return (E(_Gh)==94)?E(new T1(0,_Gf)):new T0(2);}),new T(function(){return B(A1(_Fq,_Fw));})));});return B(_xd(new T1(1,B(_yf(_B7,_B9,_FI))),_FP));});return new F(function(){return _xd(new T1(0,function(_Gi){switch(E(_Gi)){case 34:return E(_FG);case 39:return E(_FF);case 92:return E(_FE);case 97:return E(_Fx);case 98:return E(_Fy);case 102:return E(_FC);case 110:return E(_FA);case 114:return E(_FD);case 116:return E(_Fz);case 118:return E(_FB);default:return new T0(2);}}),_FH);});},_Gj=function(_Gk){return new F(function(){return A1(_Gk,_5L);});},_Gl=function(_Gm){var _Gn=E(_Gm);if(!_Gn._){return E(_Gj);}else{var _Go=E(_Gn.a),_Gp=_Go>>>0,_Gq=new T(function(){return B(_Gl(_Gn.b));});if(_Gp>887){var _Gr=u_iswspace(_Go);if(!E(_Gr)){return E(_Gj);}else{var _Gs=function(_Gt){var _Gu=new T(function(){return B(A1(_Gq,_Gt));});return new T1(0,function(_Gv){return E(_Gu);});};return E(_Gs);}}else{var _Gw=E(_Gp);if(_Gw==32){var _Gx=function(_Gy){var _Gz=new T(function(){return B(A1(_Gq,_Gy));});return new T1(0,function(_GA){return E(_Gz);});};return E(_Gx);}else{if(_Gw-9>>>0>4){if(E(_Gw)==160){var _GB=function(_GC){var _GD=new T(function(){return B(A1(_Gq,_GC));});return new T1(0,function(_GE){return E(_GD);});};return E(_GB);}else{return E(_Gj);}}else{var _GF=function(_GG){var _GH=new T(function(){return B(A1(_Gq,_GG));});return new T1(0,function(_GI){return E(_GH);});};return E(_GF);}}}}},_GJ=function(_GK){var _GL=new T(function(){return B(_GJ(_GK));}),_GM=function(_GN){return (E(_GN)==92)?E(_GL):new T0(2);},_GO=function(_GP){return E(new T1(0,_GM));},_GQ=new T1(1,function(_GR){return new F(function(){return A2(_Gl,_GR,_GO);});}),_GS=new T(function(){return B(_Fv(function(_GT){return new F(function(){return A1(_GK,new T2(0,_GT,_5Q));});}));}),_GU=function(_GV){var _GW=E(_GV);if(_GW==38){return E(_GL);}else{var _GX=_GW>>>0;if(_GX>887){var _GY=u_iswspace(_GW);return (E(_GY)==0)?new T0(2):E(_GQ);}else{var _GZ=E(_GX);return (_GZ==32)?E(_GQ):(_GZ-9>>>0>4)?(E(_GZ)==160)?E(_GQ):new T0(2):E(_GQ);}}};return new F(function(){return _xd(new T1(0,function(_H0){return (E(_H0)==92)?E(new T1(0,_GU)):new T0(2);}),new T1(0,function(_H1){var _H2=E(_H1);if(E(_H2)==92){return E(_GS);}else{return new F(function(){return A1(_GK,new T2(0,_H2,_5N));});}}));});},_H3=function(_H4,_H5){var _H6=new T(function(){return B(A1(_H5,new T1(1,new T(function(){return B(A1(_H4,_v));}))));}),_H7=function(_H8){var _H9=E(_H8),_Ha=E(_H9.a);if(E(_Ha)==34){if(!E(_H9.b)){return E(_H6);}else{return new F(function(){return _H3(function(_Hb){return new F(function(){return A1(_H4,new T2(1,_Ha,_Hb));});},_H5);});}}else{return new F(function(){return _H3(function(_Hc){return new F(function(){return A1(_H4,new T2(1,_Ha,_Hc));});},_H5);});}};return new F(function(){return _GJ(_H7);});},_Hd=new T(function(){return B(unCStr("_\'"));}),_He=function(_Hf){var _Hg=u_iswalnum(_Hf);if(!E(_Hg)){return new F(function(){return _4d(_dO,_Hf,_Hd);});}else{return true;}},_Hh=function(_Hi){return new F(function(){return _He(E(_Hi));});},_Hj=new T(function(){return B(unCStr(",;()[]{}`"));}),_Hk=new T(function(){return B(unCStr("=>"));}),_Hl=new T2(1,_Hk,_v),_Hm=new T(function(){return B(unCStr("~"));}),_Hn=new T2(1,_Hm,_Hl),_Ho=new T(function(){return B(unCStr("@"));}),_Hp=new T2(1,_Ho,_Hn),_Hq=new T(function(){return B(unCStr("->"));}),_Hr=new T2(1,_Hq,_Hp),_Hs=new T(function(){return B(unCStr("<-"));}),_Ht=new T2(1,_Hs,_Hr),_Hu=new T(function(){return B(unCStr("|"));}),_Hv=new T2(1,_Hu,_Ht),_Hw=new T(function(){return B(unCStr("\\"));}),_Hx=new T2(1,_Hw,_Hv),_Hy=new T(function(){return B(unCStr("="));}),_Hz=new T2(1,_Hy,_Hx),_HA=new T(function(){return B(unCStr("::"));}),_HB=new T2(1,_HA,_Hz),_HC=new T(function(){return B(unCStr(".."));}),_HD=new T2(1,_HC,_HB),_HE=function(_HF){var _HG=new T(function(){return B(A1(_HF,_yT));}),_HH=new T(function(){var _HI=new T(function(){var _HJ=function(_HK){var _HL=new T(function(){return B(A1(_HF,new T1(0,_HK)));});return new T1(0,function(_HM){return (E(_HM)==39)?E(_HL):new T0(2);});};return B(_Fv(_HJ));}),_HN=function(_HO){var _HP=E(_HO);switch(E(_HP)){case 39:return new T0(2);case 92:return E(_HI);default:var _HQ=new T(function(){return B(A1(_HF,new T1(0,_HP)));});return new T1(0,function(_HR){return (E(_HR)==39)?E(_HQ):new T0(2);});}},_HS=new T(function(){var _HT=new T(function(){return B(_H3(_5x,_HF));}),_HU=new T(function(){var _HV=new T(function(){var _HW=new T(function(){var _HX=function(_HY){var _HZ=E(_HY),_I0=u_iswalpha(_HZ);return (E(_I0)==0)?(E(_HZ)==95)?new T1(1,B(_yF(_Hh,function(_I1){return new F(function(){return A1(_HF,new T1(3,new T2(1,_HZ,_I1)));});}))):new T0(2):new T1(1,B(_yF(_Hh,function(_I2){return new F(function(){return A1(_HF,new T1(3,new T2(1,_HZ,_I2)));});})));};return B(_xd(new T1(0,_HX),new T(function(){return new T1(1,B(_yf(_zR,_AX,_HF)));})));}),_I3=function(_I4){return (!B(_4d(_dO,_I4,_AZ)))?new T0(2):new T1(1,B(_yF(_B0,function(_I5){var _I6=new T2(1,_I4,_I5);if(!B(_4d(_xU,_I6,_HD))){return new F(function(){return A1(_HF,new T1(4,_I6));});}else{return new F(function(){return A1(_HF,new T1(2,_I6));});}})));};return B(_xd(new T1(0,_I3),_HW));});return B(_xd(new T1(0,function(_I7){if(!B(_4d(_dO,_I7,_Hj))){return new T0(2);}else{return new F(function(){return A1(_HF,new T1(2,new T2(1,_I7,_v)));});}}),_HV));});return B(_xd(new T1(0,function(_I8){return (E(_I8)==34)?E(_HT):new T0(2);}),_HU));});return B(_xd(new T1(0,function(_I9){return (E(_I9)==39)?E(new T1(0,_HN)):new T0(2);}),_HS));});return new F(function(){return _xd(new T1(1,function(_Ia){return (E(_Ia)._==0)?E(_HG):new T0(2);}),_HH);});},_Ib=0,_Ic=function(_Id,_Ie){var _If=new T(function(){var _Ig=new T(function(){var _Ih=function(_Ii){var _Ij=new T(function(){var _Ik=new T(function(){return B(A1(_Ie,_Ii));});return B(_HE(function(_Il){var _Im=E(_Il);return (_Im._==2)?(!B(_8S(_Im.a,_xQ)))?new T0(2):E(_Ik):new T0(2);}));}),_In=function(_Io){return E(_Ij);};return new T1(1,function(_Ip){return new F(function(){return A2(_Gl,_Ip,_In);});});};return B(A2(_Id,_Ib,_Ih));});return B(_HE(function(_Iq){var _Ir=E(_Iq);return (_Ir._==2)?(!B(_8S(_Ir.a,_xP)))?new T0(2):E(_Ig):new T0(2);}));}),_Is=function(_It){return E(_If);};return function(_Iu){return new F(function(){return A2(_Gl,_Iu,_Is);});};},_Iv=function(_Iw,_Ix){var _Iy=function(_Iz){var _IA=new T(function(){return B(A1(_Iw,_Iz));}),_IB=function(_IC){return new F(function(){return _xd(B(A1(_IA,_IC)),new T(function(){return new T1(1,B(_Ic(_Iy,_IC)));}));});};return E(_IB);},_ID=new T(function(){return B(A1(_Iw,_Ix));}),_IE=function(_IF){return new F(function(){return _xd(B(A1(_ID,_IF)),new T(function(){return new T1(1,B(_Ic(_Iy,_IF)));}));});};return E(_IE);},_IG=function(_IH,_II){var _IJ=function(_IK,_IL){var _IM=function(_IN){return new F(function(){return A1(_IL,new T(function(){return  -E(_IN);}));});},_IO=new T(function(){return B(_HE(function(_IP){return new F(function(){return A3(_IH,_IP,_IK,_IM);});}));}),_IQ=function(_IR){return E(_IO);},_IS=function(_IT){return new F(function(){return A2(_Gl,_IT,_IQ);});},_IU=new T(function(){return B(_HE(function(_IV){var _IW=E(_IV);if(_IW._==4){var _IX=E(_IW.a);if(!_IX._){return new F(function(){return A3(_IH,_IW,_IK,_IL);});}else{if(E(_IX.a)==45){if(!E(_IX.b)._){return E(new T1(1,_IS));}else{return new F(function(){return A3(_IH,_IW,_IK,_IL);});}}else{return new F(function(){return A3(_IH,_IW,_IK,_IL);});}}}else{return new F(function(){return A3(_IH,_IW,_IK,_IL);});}}));}),_IY=function(_IZ){return E(_IU);};return new T1(1,function(_J0){return new F(function(){return A2(_Gl,_J0,_IY);});});};return new F(function(){return _Iv(_IJ,_II);});},_J1=function(_J2){var _J3=E(_J2);if(!_J3._){var _J4=_J3.b,_J5=new T(function(){return B(_A9(new T(function(){return B(_tc(E(_J3.a)));}),new T(function(){return B(_9C(_J4,0));},1),B(_d5(_zZ,_J4))));});return new T1(1,_J5);}else{return (E(_J3.b)._==0)?(E(_J3.c)._==0)?new T1(1,new T(function(){return B(_Aq(_zY,_J3.a));})):__Z:__Z;}},_J6=function(_J7,_J8){return new T0(2);},_J9=function(_Ja){var _Jb=E(_Ja);if(_Jb._==5){var _Jc=B(_J1(_Jb.a));if(!_Jc._){return E(_J6);}else{var _Jd=new T(function(){return B(_t3(_Jc.a));});return function(_Je,_Jf){return new F(function(){return A1(_Jf,_Jd);});};}}else{return E(_J6);}},_Jg=function(_Jh){var _Ji=function(_Jj){return E(new T2(3,_Jh,_y6));};return new T1(1,function(_Jk){return new F(function(){return A2(_Gl,_Jk,_Ji);});});},_Jl=new T(function(){return B(A3(_IG,_J9,_Ib,_Jg));}),_Jm=function(_Jn){while(1){var _Jo=B((function(_Jp){var _Jq=E(_Jp);if(!_Jq._){return __Z;}else{var _Jr=_Jq.b,_Js=E(_Jq.a);if(!E(_Js.b)._){return new T2(1,_Js.a,new T(function(){return B(_Jm(_Jr));}));}else{_Jn=_Jr;return __continue;}}})(_Jn));if(_Jo!=__continue){return _Jo;}}},_Jt=function(_Ju,_Jv,_Jw){var _Jx=E(_Jw);if(!_Jx._){return new T2(0,new T2(1,_Jv,_v),_v);}else{var _Jy=E(_Jv),_Jz=new T(function(){var _JA=B(_Jt(_Ju,_Jx.a,_Jx.b));return new T2(0,_JA.a,_JA.b);});return (_Ju!=_Jy)?new T2(0,new T2(1,_Jy,new T(function(){return E(E(_Jz).a);})),new T(function(){return E(E(_Jz).b);})):new T2(0,_v,new T2(1,new T(function(){return E(E(_Jz).a);}),new T(function(){return E(E(_Jz).b);})));}},_JB=new T1(0,1),_JC=new T1(0,10),_JD=function(_JE){while(1){var _JF=E(_JE);if(!_JF._){_JE=new T1(1,I_fromInt(_JF.a));continue;}else{return new F(function(){return I_toString(_JF.a);});}}},_JG=function(_JH,_JI){return new F(function(){return _3(fromJSStr(B(_JD(_JH))),_JI);});},_JJ=new T1(0,0),_JK=function(_JL,_JM,_JN){if(_JL<=6){return new F(function(){return _JG(_JM,_JN);});}else{if(!B(_sG(_JM,_JJ))){return new F(function(){return _JG(_JM,_JN);});}else{return new T2(1,_c,new T(function(){return B(_3(fromJSStr(B(_JD(_JM))),new T2(1,_b,_JN)));}));}}},_JO=function(_JP,_JQ,_JR){while(1){if(!(_JQ%2)){var _JS=B(_uN(_JP,_JP)),_JT=quot(_JQ,2);_JP=_JS;_JQ=_JT;continue;}else{var _JU=E(_JQ);if(_JU==1){return new F(function(){return _uN(_JP,_JR);});}else{var _JS=B(_uN(_JP,_JP)),_JV=B(_uN(_JP,_JR));_JP=_JS;_JQ=quot(_JU-1|0,2);_JR=_JV;continue;}}}},_JW=function(_JX,_JY){while(1){if(!(_JY%2)){var _JZ=B(_uN(_JX,_JX)),_K0=quot(_JY,2);_JX=_JZ;_JY=_K0;continue;}else{var _K1=E(_JY);if(_K1==1){return E(_JX);}else{return new F(function(){return _JO(B(_uN(_JX,_JX)),quot(_K1-1|0,2),_JX);});}}}},_K2=new T(function(){return B(unCStr("Negative exponent"));}),_K3=new T(function(){return B(err(_K2));}),_K4=function(_K5){return new F(function(){return _JK(0,_K5,_v);});},_K6=new T(function(){return B(_tp(_JC,_vA));}),_K7=function(_K8){while(1){if(!B(_tp(_K8,_vA))){if(!E(_K6)){if(!B(_tp(B(_tO(_K8,_JC)),_vA))){return new F(function(){return _K4(_K8);});}else{var _K9=B(_th(_K8,_JC));_K8=_K9;continue;}}else{return E(_r0);}}else{return __Z;}}},_Ka=function(_Kb){var _Kc=E(_Kb);if(!_Kc._){return _Kc.a;}else{return new F(function(){return I_toNumber(_Kc.a);});}},_Kd=46,_Ke=48,_Kf=function(_Kg,_Kh,_Ki){if(!B(_sG(_Ki,_vA))){var _Kj=B(A1(_Kg,_Ki));if(!B(_tp(_Kj,_vA))){var _Kk=B(_tB(_Ki,_Kj)),_Kl=_Kk.b,_Km=new T(function(){var _Kn=Math.log(B(_Ka(_Kj)))/Math.log(10),_Ko=_Kn&4294967295,_Kp=function(_Kq){if(_Kq>=0){var _Kr=E(_Kq);if(!_Kr){var _Ks=B(_th(B(_sc(B(_rq(B(_uN(_Kl,_s2)),_Kj)),_JB)),_Kj));}else{var _Ks=B(_th(B(_sc(B(_rq(B(_uN(_Kl,B(_JW(_JC,_Kr)))),_Kj)),_JB)),_Kj));}var _Kt=function(_Ku){var _Kv=B(_JK(0,_Ks,_v)),_Kw=_Kq-B(_9C(_Kv,0))|0;if(0>=_Kw){if(!E(_Kh)){return E(_Kv);}else{return new F(function(){return _K7(_Ks);});}}else{var _Kx=new T(function(){if(!E(_Kh)){return E(_Kv);}else{return B(_K7(_Ks));}}),_Ky=function(_Kz){var _KA=E(_Kz);return (_KA==1)?E(new T2(1,_Ke,_Kx)):new T2(1,_Ke,new T(function(){return B(_Ky(_KA-1|0));}));};return new F(function(){return _Ky(_Kw);});}};if(!E(_Kh)){var _KB=B(_Kt(_));return (_KB._==0)?__Z:new T2(1,_Kd,_KB);}else{if(!B(_tp(_Ks,_vA))){var _KC=B(_Kt(_));return (_KC._==0)?__Z:new T2(1,_Kd,_KC);}else{return __Z;}}}else{return E(_K3);}};if(_Ko>=_Kn){return B(_Kp(_Ko));}else{return B(_Kp(_Ko+1|0));}},1);return new F(function(){return _3(B(_JK(0,_Kk.a,_v)),_Km);});}else{return E(_r0);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_Kf(_Kg,_Kh,B(_rA(_Ki))));}));});}},_KD=function(_KE,_KF,_){var _KG=B(_wR(_)),_KH=new T(function(){var _KI=new T(function(){var _KJ=new T(function(){var _KK=B(_3(B(_Kf(_rM,_5Q,B(_wr(_KG)).b)),_rT));if(!_KK._){return E(_az);}else{var _KL=B(_ar(_KK.a,_KK.b));if(!_KL._){return B(_rY(_v,_v,_aB));}else{var _KM=_KL.a,_KN=E(_KL.b);if(!_KN._){return B(_rY(new T2(1,_KM,_v),_v,_aB));}else{var _KO=E(_KM),_KP=new T(function(){var _KQ=B(_Jt(46,_KN.a,_KN.b));return new T2(0,_KQ.a,_KQ.b);});if(E(_KO)==46){return B(_rY(_v,new T2(1,new T(function(){return E(E(_KP).a);}),new T(function(){return E(E(_KP).b);})),_aB));}else{return B(_rY(new T2(1,_KO,new T(function(){return E(E(_KP).a);})),new T(function(){return E(E(_KP).b);}),_aB));}}}}}),_KR=B(_Jm(B(_x3(_Jl,_KJ))));if(!_KR._){return E(_wY);}else{if(!E(_KR.b)._){return B(_wx(3,B(_d(0,E(_KR.a)+(imul(E(_KF),E(_KE)-1|0)|0)|0,_v))));}else{return E(_wW);}}}),_KS=B(_Jm(B(_x3(_Jl,_KI))));if(!_KS._){return E(_wY);}else{if(!E(_KS.b)._){return E(_KS.a);}else{return E(_wW);}}});return new T2(0,new T(function(){return B(_rP(_KH,_KE));}),_KH);},_KT=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_KU=new T(function(){return B(err(_KT));}),_KV=function(_KW,_KX){while(1){var _KY=E(_KX);if(!_KY._){return __Z;}else{var _KZ=_KY.b,_L0=E(_KW);if(_L0==1){return E(_KZ);}else{_KW=_L0-1|0;_KX=_KZ;continue;}}}},_L1=function(_L2,_L3){if(B(_9C(_L3,0))>=(_L2+1|0)){var _L4=new T(function(){var _L5=_L2+1|0;if(_L5>0){return B(_KV(_L5,_L3));}else{return E(_L3);}});if(0>=_L2){return E(_L4);}else{var _L6=function(_L7,_L8){var _L9=E(_L7);if(!_L9._){return E(_L4);}else{var _La=_L9.a,_Lb=E(_L8);return (_Lb==1)?new T2(1,_La,_L4):new T2(1,_La,new T(function(){return B(_L6(_L9.b,_Lb-1|0));}));}};return new F(function(){return _L6(_L3,_L2);});}}else{return E(_L3);}},_Lc=function(_Ld,_Le){return new F(function(){return _L1(E(_Ld),_Le);});},_Lf=function(_Lg){return E(E(_Lg).a);},_Lh=function(_Li){return new F(function(){return _d(0,E(_Li),_v);});},_Lj=function(_Lk,_Ll,_Lm){return new F(function(){return _d(E(_Lk),E(_Ll),_Lm);});},_Ln=function(_Lo,_Lp){return new F(function(){return _d(0,E(_Lo),_Lp);});},_Lq=function(_Lr,_Ls){return new F(function(){return _28(_Ln,_Lr,_Ls);});},_Lt=new T3(0,_Lj,_Lh,_Lq),_Lu=0,_Lv=function(_Lw,_Lx,_Ly){return new F(function(){return A1(_Lw,new T2(1,_25,new T(function(){return B(A1(_Lx,_Ly));})));});},_Lz=new T(function(){return B(unCStr("foldr1"));}),_LA=new T(function(){return B(_aw(_Lz));}),_LB=function(_LC,_LD){var _LE=E(_LD);if(!_LE._){return E(_LA);}else{var _LF=_LE.a,_LG=E(_LE.b);if(!_LG._){return E(_LF);}else{return new F(function(){return A2(_LC,_LF,new T(function(){return B(_LB(_LC,_LG));}));});}}},_LH=new T(function(){return B(unCStr(" out of range "));}),_LI=new T(function(){return B(unCStr("}.index: Index "));}),_LJ=new T(function(){return B(unCStr("Ix{"));}),_LK=new T2(1,_b,_v),_LL=new T2(1,_b,_LK),_LM=0,_LN=function(_LO){return E(E(_LO).a);},_LP=function(_LQ,_LR,_LS,_LT,_LU){var _LV=new T(function(){var _LW=new T(function(){var _LX=new T(function(){var _LY=new T(function(){var _LZ=new T(function(){return B(A3(_LB,_Lv,new T2(1,new T(function(){return B(A3(_LN,_LS,_LM,_LT));}),new T2(1,new T(function(){return B(A3(_LN,_LS,_LM,_LU));}),_v)),_LL));});return B(_3(_LH,new T2(1,_c,new T2(1,_c,_LZ))));});return B(A(_LN,[_LS,_Lu,_LR,new T2(1,_b,_LY)]));});return B(_3(_LI,new T2(1,_c,_LX)));},1);return B(_3(_LQ,_LW));},1);return new F(function(){return err(B(_3(_LJ,_LV)));});},_M0=function(_M1,_M2,_M3,_M4,_M5){return new F(function(){return _LP(_M1,_M2,_M5,_M3,_M4);});},_M6=function(_M7,_M8,_M9,_Ma){var _Mb=E(_M9);return new F(function(){return _M0(_M7,_M8,_Mb.a,_Mb.b,_Ma);});},_Mc=function(_Md,_Me,_Mf,_Mg){return new F(function(){return _M6(_Mg,_Mf,_Me,_Md);});},_Mh=new T(function(){return B(unCStr("Int"));}),_Mi=function(_Mj,_Mk,_Ml){return new F(function(){return _Mc(_Lt,new T2(0,_Mk,_Ml),_Mj,_Mh);});},_Mm=0,_Mn=new T(function(){return B(unCStr("Negative range size"));}),_Mo=new T(function(){return B(err(_Mn));}),_Mp=function(_Mq){var _Mr=B(A1(_Mq,_));return E(_Mr);},_Ms=function(_Mt,_Mu,_Mv,_){var _Mw=E(_Mt);if(!_Mw){return new T2(0,_v,_Mu);}else{var _Mx=new T(function(){return B(_9C(_Mv,0))-1|0;}),_My=B(_KD(new T(function(){return E(_Mx)+1|0;}),_Mu,_)),_Mz=E(_My),_MA=_Mz.a,_MB=_Mz.b,_MC=B(_Ms(_Mw-1|0,_MB,new T(function(){return B(_Lc(_MA,_Mv));}),_)),_MD=new T(function(){var _ME=function(_){var _MF=E(_Mx),_MG=function(_MH){if(_MH>=0){var _MI=newArr(_MH,_KU),_MJ=_MI,_MK=E(_MH);if(!_MK){return new T4(0,E(_Mm),E(_MF),0,_MJ);}else{var _ML=function(_MM,_MN,_){while(1){var _MO=E(_MM);if(!_MO._){return E(_);}else{var _=_MJ[_MN]=_MO.a;if(_MN!=(_MK-1|0)){var _MP=_MN+1|0;_MM=_MO.b;_MN=_MP;continue;}else{return E(_);}}}},_=B(_ML(_Mv,0,_));return new T4(0,E(_Mm),E(_MF),_MK,_MJ);}}else{return E(_Mo);}};if(0>_MF){return new F(function(){return _MG(0);});}else{return new F(function(){return _MG(_MF+1|0);});}},_MQ=B(_Mp(_ME)),_MR=E(_MQ.a),_MS=E(_MQ.b),_MT=E(_MA);if(_MR>_MT){return B(_Mi(_MT,_MR,_MS));}else{if(_MT>_MS){return B(_Mi(_MT,_MR,_MS));}else{return E(_MQ.d[_MT-_MR|0]);}}});return new T2(0,new T2(1,_MD,new T(function(){return B(_Lf(_MC));})),_MB);}},_MU=function(_MV){var _MW=E(_MV);if(!_MW._){return new T2(0,_v,_v);}else{var _MX=E(_MW.a),_MY=new T(function(){var _MZ=B(_MU(_MW.b));return new T2(0,_MZ.a,_MZ.b);});return new T2(0,new T2(1,_MX.a,new T(function(){return E(E(_MY).a);})),new T2(1,_MX.b,new T(function(){return E(E(_MY).b);})));}},_N0=function(_N1){return new T2(1,_N1,_v);},_N2=new T(function(){return B(unCStr("\u3042\u304b\u306f\u306a\u307e\u3044\u304d\u3072\u306b\u307f\u3046\u304f\u3075\u306c\u3080\u3048\u3051\u3078\u306d\u3081\u304a\u3053\u307b\u306e\u3082\u3068\u308d\u305d\u3088\u3092\u3066\u308c\u305b\u3091\u3064\u308b\u3059\u3086\u3093\u3061\u308a\u3057\u3090\u305f\u3089\u3055\u3084\u308f"));}),_N3=function(_N4,_N5,_){var _N6=new T(function(){var _N7=E(_N5);return 4+B(_r4(_N7,8-B(_om(_N7,8))|0))|0;}),_N8=B(_KD(_N6,_N4,_)),_N9=E(_N8),_Na=new T(function(){return B(_jd(_ou,new T(function(){var _Nb=E(_N5)+3|0;if(0>=_Nb){return __Z;}else{return B(_wx(_Nb,_N2));}},1)));}),_Nc=B(_Ms(E(_N6),_N9.b,_Na,_)),_Nd=E(_Nc);return new T2(0,new T(function(){var _Ne=B(_MU(_Nd.a));return new T3(0,E(B(_d5(_N0,_Ne.b))),E(_Ne.a),E(_N9.a));}),_Nd.b);},_Nf=function(_Ng){return E(_Ng).d;},_Nh=function(_Ni,_Nj,_Nk,_Nl,_){var _Nm=B(_N3(new T(function(){return B(_Nf(_Nl));},1),_Nk,_)),_Nn=E(_Nm),_No=E(_Nn.a),_Np=_No.b,_Nq=_No.c,_Nr=B(A3(_qi,_5z,B(_a1(_Nj,B(_a1(_Np,_Nq)))).a,_));return new T(function(){var _Ns=E(_Nl),_Nt=E(_Ni),_Nu=B(_oQ(_Nt.a,_Nt.b,_No.a,_Np,_Nq));return new T6(0,E(_Ns.a),E(new T1(1,_No)),E(new T2(1,_Nu.a,_Nu.b)),E(_Nn.b),E(_Ns.e),E(_Ns.f));});},_Nv=function(_Nw,_Nx,_Ny,_Nz,_NA,_NB,_NC,_ND,_NE,_NF,_NG,_NH,_NI,_NJ,_NK,_){var _NL=function(_,_NM,_NN,_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV){if(!B(_8X(_NB,_NC,_ND,_NE,_NF,_NG,_NH,_NI,_NJ,_NK,_NM,_NN,_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV))){var _NW=E(_Nw),_NX=__app1(E(_dw),_NW.b),_NY=B(A2(_dH,_NW.a,_)),_NZ=B(_ji(_NW,new T2(0,_Nx,_og),_Ny,_NO,_));return new T6(0,E(_NM),E(_NN),E(_NO),_NP,E(new T5(0,E(_NQ),E(_NR),E(_NS),E(_NT),E(_NU))),E(_NV));}else{return new T6(0,E(_NM),E(_NN),E(_NO),_NP,E(new T5(0,E(_NQ),E(_NR),E(_NS),E(_NT),E(_NU))),E(_NV));}},_O0=E(_NA);if(_O0==( -1)){return new F(function(){return _NL(_,_NB,_NC,_ND,_NE,_NF,_NG,_NH,_NI,_NJ,_NK);});}else{var _O1=B(_6R(_O0,_ND));if(!_O1._){return new F(function(){return _NL(_,_NB,_NC,_ND,_NE,_NF,_NG,_NH,_NI,_NJ,_NK);});}else{var _O2=E(E(_O1.a).o);switch(_O2._){case 0:return new F(function(){return _NL(_,_NB,_NC,_ND,_NE,_NF,_NG,_NH,_NI,_NJ,_NK);});break;case 1:var _O3=E(_O2.a);if(!_O3._){var _O4=B(_Nh(_Nx,_Nz,_O3.a,new T6(0,E(new T1(1,_O3)),E(_NC),E(_ND),_NE,E(new T5(0,E(_NF),E(_NG),E(_NH),E(_NI),E(_NJ))),E(_NK)),_)),_O5=E(_O4),_O6=E(_O5.e);return new F(function(){return _NL(_,_O5.a,_O5.b,_O5.c,_O5.d,_O6.a,_O6.b,_O6.c,_O6.d,_O6.e,_O5.f);});}else{return E(_ol);}break;case 2:var _O7=B(_d9(_Nx,new T(function(){return B(_9C(_ND,0));},1),_O2.a,_NB,_NC,_ND,_NE,new T5(0,E(_NF),E(_NG),E(_NH),E(_NI),E(_NJ)),_NK)),_O8=E(_O7.e);return new F(function(){return _NL(_,_O7.a,_O7.b,_O7.c,_O7.d,_O8.a,_O8.b,_O8.c,_O8.d,_O8.e,_O7.f);});break;default:var _O9=B(_bL(_Nx,E(_O2.a),_NB,_NC,_ND,_NE,new T5(0,E(_NF),E(_NG),E(_NH),E(_NI),E(_NJ)),_NK)),_Oa=E(_O9.e);return new F(function(){return _NL(_,_O9.a,_O9.b,_O9.c,_O9.d,_Oa.a,_Oa.b,_Oa.c,_Oa.d,_Oa.e,_O9.f);});}}}},_Ob=function(_Oc,_Od){while(1){var _Oe=E(_Oc);if(!_Oe._){return E(_Od);}else{var _Of=new T2(1,_Oe.a,_Od);_Oc=_Oe.b;_Od=_Of;continue;}}},_Og=function(_Oh,_Oi,_Oj,_Ok,_Ol,_Om,_On,_){var _Oo=E(_Oi),_Op=_Oo.a,_Oq=E(_On),_Or=_Oq.c,_Os=function(_Ot){var _Ou=E(_Oq.e);return new F(function(){return _Nv(_Oh,_Op,_Oj,_Ok,_Ot,_Oq.a,_Oq.b,_Or,_Oq.d,_Ou.a,_Ou.b,_Ou.c,_Ou.d,_Ou.e,_Oq.f,_);});},_Ov=B(_Ob(_Or,_v));if(!_Ov._){return new F(function(){return _Os( -1);});}else{var _Ow=_Ov.b,_Ox=E(_Op),_Oy=_Ox.b,_Oz=E(_Oo.b),_OA=_Oz.b,_OB=E(_Ol)*(E(_Ox.a)/E(_Oz.a)),_OC=E(_Ov.a),_OD=E(_OC.b),_OE=E(_OD.a);if(_OB<=_OE){return new F(function(){return _Os(B(_6G(_OB,new T(function(){return E(_Om)*(E(_Oy)/E(_OA));},1),_Ow)));});}else{if(_OB>=_OE+E(_OD.c)){return new F(function(){return _Os(B(_6G(_OB,new T(function(){return E(_Om)*(E(_Oy)/E(_OA));},1),_Ow)));});}else{var _OF=E(_Om)*(E(_Oy)/E(_OA)),_OG=E(_OD.b);if(_OF<=_OG){return new F(function(){return _Os(B(_6w(_OB,_OF,_Ow)));});}else{if(_OF>=_OG+E(_OD.d)){return new F(function(){return _Os(B(_6w(_OB,_OF,_Ow)));});}else{return new F(function(){return _Os(_OC.a);});}}}}}},_OH=function(_OI){return E(E(_OI).a);},_OJ=function(_OK){return E(E(_OK).b);},_OL=function(_OM){return E(E(_OM).a);},_ON=function(_){return new F(function(){return nMV(_2q);});},_OO=new T(function(){return B(_2J(_ON));}),_OP=function(_OQ){return E(E(_OQ).b);},_OR=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_OS=function(_OT){return E(E(_OT).d);},_OU=function(_OV,_OW,_OX,_OY,_OZ,_P0){var _P1=B(_OH(_OV)),_P2=B(_ps(_P1)),_P3=new T(function(){return B(_5U(_P1));}),_P4=new T(function(){return B(_OS(_P2));}),_P5=new T(function(){return B(A1(_OW,_OY));}),_P6=new T(function(){return B(A2(_OL,_OX,_OZ));}),_P7=function(_P8){return new F(function(){return A1(_P4,new T3(0,_P6,_P5,_P8));});},_P9=function(_Pa){var _Pb=new T(function(){var _Pc=new T(function(){var _Pd=__createJSFunc(2,function(_Pe,_){var _Pf=B(A2(E(_Pa),_Pe,_));return _2N;}),_Pg=_Pd;return function(_){return new F(function(){return __app3(E(_OR),E(_P5),E(_P6),_Pg);});};});return B(A1(_P3,_Pc));});return new F(function(){return A3(_qc,_P2,_Pb,_P7);});},_Ph=new T(function(){var _Pi=new T(function(){return B(_5U(_P1));}),_Pj=function(_Pk){var _Pl=new T(function(){return B(A1(_Pi,function(_){var _=wMV(E(_OO),new T1(1,_Pk));return new F(function(){return A(_OJ,[_OX,_OZ,_Pk,_]);});}));});return new F(function(){return A3(_qc,_P2,_Pl,_P0);});};return B(A2(_OP,_OV,_Pj));});return new F(function(){return A3(_qc,_P2,_Ph,_P9);});},_Pm=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_Pn=function(_){var _Po=rMV(E(_OO)),_Pp=E(_Po);if(!_Pp._){var _Pq=__app1(E(_Pm),E(_2N));return new F(function(){return _dx(_);});}else{var _Pr=__app1(E(_Pm),E(_Pp.a));return new F(function(){return _dx(_);});}},_Ps=new T(function(){return B(unCStr("\u4eca\u65e5\u3082\u6700\u9ad8\u306e\u4e00\u65e5\u306b\u306a\u308b\u3088\uff01\n\u30f2\u30b7\u30c6\u3092\u5b78\u3093\u3067\u3044\u304b\u3046\u3088\uff01\n\u304a\u3082\u3057\u308d\u3044\u3053\u3068\u306b\u306a\u3063\u3066\u304d\u305f\u306d\uff01\n\u3059\u3066\u304d\u306a \u51fa\u6703\u3072\u304c \u3042\u3063\u3066 \u3046\u308c\u3057\u3044\u306d\uff01\n\u5fc3\u306e\u6e96\u5099\u306f\u3067\u304d\u3066\u308b\uff1f\n\u3055\u3042 \u306f\u3058\u3081\u3084\u3046\u304b\uff01"));}),_Pt=function(_Pu,_Pv){var _Pw=E(_Pv);if(!_Pw._){return new T2(0,_v,_v);}else{var _Px=_Pw.a;if(!B(A1(_Pu,_Px))){var _Py=new T(function(){var _Pz=B(_Pt(_Pu,_Pw.b));return new T2(0,_Pz.a,_Pz.b);});return new T2(0,new T2(1,_Px,new T(function(){return E(E(_Py).a);})),new T(function(){return E(E(_Py).b);}));}else{return new T2(0,_v,_Pw);}}},_PA=function(_PB){return (E(_PB)==10)?true:false;},_PC=function(_PD){var _PE=E(_PD);if(!_PE._){return __Z;}else{var _PF=new T(function(){var _PG=B(_Pt(_PA,_PE));return new T2(0,_PG.a,new T(function(){var _PH=E(_PG.b);if(!_PH._){return __Z;}else{return B(_PC(_PH.b));}}));});return new T2(1,new T(function(){return E(E(_PF).a);}),new T(function(){return E(E(_PF).b);}));}},_PI=new T(function(){return B(_PC(_Ps));}),_PJ=function(_PK,_PL){while(1){var _PM=E(_PK);if(!_PM._){return E(_PL);}else{_PK=_PM.b;_PL=_PM.a;continue;}}},_PN=function(_PO,_PP,_PQ,_PR,_){var _PS=B(_Ms(1,new T(function(){return E(_PR).d;}),_PI,_));return new F(function(){return _ji(_PO,_PP,_PQ,new T2(1,{_:0,a:0,b:E(_6d),c:E(_62),d:0,e:5,f:E(_69),g:E(_v),h:E(_6k),i:E(_6i),j:E(new T2(1,new T(function(){return B(_PJ(E(_PS).a,_aB));}),_v)),k:E(_6f),l:E(_v),m:E(_v),n:E(_2q),o:E(_65)},_v),_);});},_PT=new T1(0,0),_PU=new T(function(){return B(unCStr("vaw"));}),_PV=new T(function(){return B(unCStr("ggo"));}),_PW=new T(function(){return B(unCStr("3pm"));}),_PX=0,_PY=1,_PZ=2,_Q0=function(_Q1){var _Q2=B(_wx(3,B(_Ob(fromJSStr(_Q1),_v))));return (!B(_8S(_Q2,_PW)))?(!B(_8S(_Q2,_PV)))?(!B(_8S(_Q2,_PU)))?__Z:new T1(1,new T2(0,E(_PZ),_Q1)):new T1(1,new T2(0,E(_PY),_Q1)):new T1(1,new T2(0,E(_PX),_Q1));},_Q3=new T(function(){return B(unCStr("Audio/"));}),_Q4=new T1(0,1),_Q5=new T1(0,15),_Q6=2,_Q7=new T6(0,E(_5N),E(_5N),E(_5N),E(_Q6),E(_5N),1),_Q8=new T(function(){return B(_bv("Browser.hs:83:7-34|Just adSrc"));}),_Q9=new T(function(){return B(unCStr(".mp3"));}),_Qa=function(_Qb){return new T1(1,E(_Qb));},_Qc=function(_Qd,_Qe){return new F(function(){return A2(_OS,B(_ps(_Qd)),new T1(1,_Qe));});},_Qf=new T2(0,_5x,_Qc),_Qg="auto",_Qh="metadata",_Qi="none",_Qj=new T(function(){return new T1(0,"preload");}),_Qk=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_Ql=function(_){return new F(function(){return __app1(E(_Qk),"source");});},_Qm=new T(function(){return new T1(0,"src");}),_Qn="audio/wav",_Qo="audio/ogg",_Qp="audio/mpeg",_Qq=new T(function(){return new T1(0,"type");}),_Qr=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_Qs=function(_Qt){return E(E(_Qt).a);},_Qu=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_Qv=new T(function(){return eval("(function(e,p,v){e.style[p] = v;})");}),_Qw=function(_Qx,_Qy,_Qz,_QA){var _QB=new T(function(){return B(A2(_Qs,_Qx,_Qz));}),_QC=function(_QD,_){var _QE=E(_QD);if(!_QE._){return _5L;}else{var _QF=E(_QB),_QG=E(_Qr),_QH=__app2(_QG,E(_QE.a),_QF),_QI=function(_QJ,_){while(1){var _QK=E(_QJ);if(!_QK._){return _5L;}else{var _QL=__app2(_QG,E(_QK.a),_QF);_QJ=_QK.b;continue;}}};return new F(function(){return _QI(_QE.b,_);});}},_QM=function(_QN,_){while(1){var _QO=B((function(_QP,_){var _QQ=E(_QP);if(!_QQ._){return _5L;}else{var _QR=_QQ.b,_QS=E(_QQ.a);if(!_QS._){var _QT=_QS.b,_QU=E(_QS.a);switch(_QU._){case 0:var _QV=E(_QB),_QW=E(_eK),_QX=__app3(_QW,_QV,_QU.a,_QT),_QY=function(_QZ,_){while(1){var _R0=E(_QZ);if(!_R0._){return _5L;}else{var _R1=_R0.b,_R2=E(_R0.a);if(!_R2._){var _R3=_R2.b,_R4=E(_R2.a);switch(_R4._){case 0:var _R5=__app3(_QW,_QV,_R4.a,_R3);_QZ=_R1;continue;case 1:var _R6=__app3(E(_Qv),_QV,_R4.a,_R3);_QZ=_R1;continue;default:var _R7=__app3(E(_Qu),_QV,_R4.a,_R3);_QZ=_R1;continue;}}else{var _R8=B(_QC(_R2.a,_));_QZ=_R1;continue;}}}};return new F(function(){return _QY(_QR,_);});break;case 1:var _R9=E(_QB),_Ra=E(_Qv),_Rb=__app3(_Ra,_R9,_QU.a,_QT),_Rc=function(_Rd,_){while(1){var _Re=E(_Rd);if(!_Re._){return _5L;}else{var _Rf=_Re.b,_Rg=E(_Re.a);if(!_Rg._){var _Rh=_Rg.b,_Ri=E(_Rg.a);switch(_Ri._){case 0:var _Rj=__app3(E(_eK),_R9,_Ri.a,_Rh);_Rd=_Rf;continue;case 1:var _Rk=__app3(_Ra,_R9,_Ri.a,_Rh);_Rd=_Rf;continue;default:var _Rl=__app3(E(_Qu),_R9,_Ri.a,_Rh);_Rd=_Rf;continue;}}else{var _Rm=B(_QC(_Rg.a,_));_Rd=_Rf;continue;}}}};return new F(function(){return _Rc(_QR,_);});break;default:var _Rn=E(_QB),_Ro=E(_Qu),_Rp=__app3(_Ro,_Rn,_QU.a,_QT),_Rq=function(_Rr,_){while(1){var _Rs=E(_Rr);if(!_Rs._){return _5L;}else{var _Rt=_Rs.b,_Ru=E(_Rs.a);if(!_Ru._){var _Rv=_Ru.b,_Rw=E(_Ru.a);switch(_Rw._){case 0:var _Rx=__app3(E(_eK),_Rn,_Rw.a,_Rv);_Rr=_Rt;continue;case 1:var _Ry=__app3(E(_Qv),_Rn,_Rw.a,_Rv);_Rr=_Rt;continue;default:var _Rz=__app3(_Ro,_Rn,_Rw.a,_Rv);_Rr=_Rt;continue;}}else{var _RA=B(_QC(_Ru.a,_));_Rr=_Rt;continue;}}}};return new F(function(){return _Rq(_QR,_);});}}else{var _RB=B(_QC(_QS.a,_));_QN=_QR;return __continue;}}})(_QN,_));if(_QO!=__continue){return _QO;}}};return new F(function(){return A2(_5U,_Qy,function(_){return new F(function(){return _QM(_QA,_);});});});},_RC=function(_RD,_RE,_RF,_RG){var _RH=B(_ps(_RE)),_RI=function(_RJ){return new F(function(){return A3(_qa,_RH,new T(function(){return B(_Qw(_RD,_RE,_RJ,_RG));}),new T(function(){return B(A2(_OS,_RH,_RJ));}));});};return new F(function(){return A3(_qc,_RH,_RF,_RI);});},_RK=function(_RL,_){var _RM=E(_RL);if(!_RM._){return _v;}else{var _RN=E(_RM.a),_RO=B(A(_RC,[_Qf,_5z,_Ql,new T2(1,new T(function(){var _RP=E(_Qq);switch(E(_RN.a)){case 0:return new T2(0,E(_RP),E(_Qp));break;case 1:return new T2(0,E(_RP),E(_Qo));break;default:return new T2(0,E(_RP),E(_Qn));}}),new T2(1,new T(function(){return new T2(0,E(_Qm),_RN.b);}),_v)),_])),_RQ=B(_RK(_RM.b,_));return new T2(1,_RO,_RQ);}},_RR=new T(function(){return new T1(0,"volume");}),_RS=new T(function(){return new T1(0,"muted");}),_RT=new T(function(){return new T1(0,"loop");}),_RU=new T(function(){return new T1(0,"autoplay");}),_RV="true",_RW=new T(function(){return toJSStr(_v);}),_RX=new T(function(){return new T1(0,"controls");}),_RY=function(_){return new F(function(){return __app1(E(_Qk),"audio");});},_RZ=function(_S0,_S1,_S2){var _S3=function(_){var _S4=B(_RK(_S2,_)),_S5=B(A(_RC,[_Qf,_5z,_RY,new T2(1,new T(function(){var _S6=E(_RX);if(!E(E(_S1).a)){return new T2(0,E(_S6),E(_RW));}else{return new T2(0,E(_S6),E(_RV));}}),new T2(1,new T(function(){var _S7=E(_RU);if(!E(E(_S1).b)){return new T2(0,E(_S7),E(_RW));}else{return new T2(0,E(_S7),E(_RV));}}),new T2(1,new T(function(){var _S8=E(_RT);if(!E(E(_S1).c)){return new T2(0,E(_S8),E(_RW));}else{return new T2(0,E(_S8),E(_RV));}}),new T2(1,new T(function(){var _S9=E(_RS);if(!E(E(_S1).e)){return new T2(0,E(_S9),E(_RW));}else{return new T2(0,E(_S9),E(_RV));}}),new T2(1,new T(function(){var _Sa=String(E(_S1).f);return new T2(0,E(_RR),_Sa);}),new T2(1,new T(function(){var _Sb=E(_Qj);switch(E(E(_S1).d)){case 0:return new T2(0,E(_Sb),E(_Qi));break;case 1:return new T2(0,E(_Sb),E(_Qh));break;default:return new T2(0,E(_Sb),E(_Qg));}}),new T2(1,new T(function(){return B(_Qa(_S4));}),_v))))))),_]));return new T1(0,_S5);};return new F(function(){return A2(_5U,_S0,_S3);});},_Sc=function(_Sd,_){if(!B(_sy(_Sd,_Q5))){var _Se=new T(function(){var _Sf=new T(function(){return B(unAppCStr("os",new T(function(){return B(_3(B(_JK(0,_Sd,_v)),_Q9));})));},1),_Sg=B(_Q0(toJSStr(B(_3(_Q3,_Sf)))));if(!_Sg._){return E(_Q8);}else{return E(_Sg.a);}}),_Sh=B(A(_RZ,[_5z,_Q7,new T2(1,_Se,_v),_])),_Si=B(_Sc(B(_rq(_Sd,_Q4)),_));return new T2(1,_Sh,_Si);}else{return _v;}},_Sj="src",_Sk=new T(function(){return B(unCStr("img"));}),_Sl=function(_Sm,_Sn){return new F(function(){return A2(_5U,_Sm,function(_){var _So=__app1(E(_Qk),toJSStr(E(_Sk))),_Sp=__app3(E(_eK),_So,E(_Sj),E(_Sn));return _So;});});},_Sq=new T(function(){return B(unCStr(".png"));}),_Sr=function(_Ss,_St){var _Su=E(_Ss);if(_Su==( -1)){return __Z;}else{var _Sv=new T(function(){var _Sw=new T(function(){return toJSStr(B(_3(_St,new T(function(){return B(_3(B(_d(0,_Su,_v)),_Sq));},1))));});return B(_Sl(_5z,_Sw));});return new F(function(){return _3(B(_Sr(_Su-1|0,_St)),new T2(1,_Sv,_v));});}},_Sx=new T(function(){return B(unCStr("Images/Wst/wst"));}),_Sy=new T(function(){return B(_Sr(120,_Sx));}),_Sz=function(_SA,_){var _SB=E(_SA);if(!_SB._){return _v;}else{var _SC=B(A1(_SB.a,_)),_SD=B(_Sz(_SB.b,_));return new T2(1,_SC,_SD);}},_SE=new T(function(){return B(unCStr("Images/img"));}),_SF=new T(function(){return B(_Sr(5,_SE));}),_SG=function(_SH,_){var _SI=E(_SH);if(!_SI._){return _v;}else{var _SJ=B(A1(_SI.a,_)),_SK=B(_SG(_SI.b,_));return new T2(1,_SJ,_SK);}},_SL=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_SM=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_SN=function(_SO,_SP,_SQ){var _SR=B(_OH(_SO)),_SS=new T(function(){return B(_5U(_SR));}),_ST=function(_SU){var _SV=function(_){var _SW=E(_SP);if(!_SW._){var _SX=B(A1(_SU,_5L)),_SY=__createJSFunc(0,function(_){var _SZ=B(A1(_SX,_));return _2N;}),_T0=__app2(E(_SM),_SW.a,_SY);return new T(function(){var _T1=Number(_T0),_T2=jsTrunc(_T1);return new T2(0,_T2,E(_SW));});}else{var _T3=B(A1(_SU,_5L)),_T4=__createJSFunc(0,function(_){var _T5=B(A1(_T3,_));return _2N;}),_T6=__app2(E(_SL),_SW.a,_T4);return new T(function(){var _T7=Number(_T6),_T8=jsTrunc(_T7);return new T2(0,_T8,E(_SW));});}};return new F(function(){return A1(_SS,_SV);});},_T9=new T(function(){return B(A2(_OP,_SO,function(_Ta){return E(_SQ);}));});return new F(function(){return A3(_qc,B(_ps(_SR)),_T9,_ST);});},_Tb=function(_){var _Tc=B(_SG(_SF,_)),_Td=B(_Sz(_Sy,_)),_Te=B(_Sc(_PT,_)),_Tf=_Te,_Tg=__app1(E(_5R),"canvas"),_Th=__eq(_Tg,E(_2N));if(!E(_Th)){var _Ti=__isUndef(_Tg);if(!E(_Ti)){var _Tj=B(A3(_5W,_5z,_Tg,_)),_Tk=E(_Tj);if(!_Tk._){return new F(function(){return die(_6v);});}else{var _Tl=E(_Tk.a),_Tm=B(_5F(_Tl.b,_)),_Tn=_Tm,_To=nMV(_6o),_Tp=_To,_Tq=new T2(0,_Tc,_Td),_Tr=B(_PN(_Tl,_Tn,_Tq,_6o,_)),_Ts=B(A(_OU,[_5A,_3g,_3f,_Tg,_5M,function(_Tt,_){var _Tu=E(E(_Tt).a),_Tv=rMV(_Tp),_Tw=B(_Og(_Tl,_Tn,_Tq,_Tf,_Tu.a,_Tu.b,_Tv,_)),_=wMV(_Tp,_Tw);return _5L;},_])),_Tx=B(A(_OU,[_5A,_3g,_4P,_Tg,_5P,function(_Ty,_){var _Tz=E(_Ty),_TA=rMV(_Tp),_TB=E(_TA);if(!E(E(_TB.e).c)){var _=wMV(_Tp,_TB);return _5L;}else{var _TC=B(_Pn(_)),_=wMV(_Tp,_TB);return _5L;}},_])),_TD=function(_){var _TE=rMV(_Tp),_=wMV(_Tp,new T(function(){var _TF=E(_TE),_TG=E(_TF.e);return new T6(0,E(_TF.a),E(_TF.b),E(_TF.c),_TF.d,E(new T5(0,E(_TG.a),E(_TG.b),E(_5N),E(_TG.d),E(_TG.e))),E(_TF.f));}));return _5L;},_TH=function(_TI,_){var _TJ=E(_TI),_TK=rMV(_Tp),_=wMV(_Tp,new T(function(){var _TL=E(_TK),_TM=E(_TL.e);return new T6(0,E(_TL.a),E(_TL.b),E(_TL.c),_TL.d,E(new T5(0,E(_TM.a),E(_TM.b),E(_5Q),E(_TM.d),E(_TM.e))),E(_TL.f));})),_TN=B(A(_SN,[_5A,_6p,_TD,_]));return _5L;},_TO=B(A(_OU,[_5A,_3g,_4P,_Tg,_5O,_TH,_]));return _5L;}}else{return new F(function(){return die(_6s);});}}else{return new F(function(){return die(_6s);});}},_TP=function(_){return new F(function(){return _Tb(_);});};
var hasteMain = function() {B(A(_TP, [0]));};window.onload = hasteMain;