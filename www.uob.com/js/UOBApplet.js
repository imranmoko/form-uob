/*!
 * This package includes code written by Tom Wu.
 * 
 * Copyright (c) 2003-2005  Tom Wu
 * All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 */

var dbits;

var j_lm = (((0xdeadbeefcafe)&0xffffff)==0xefcafe);

function BigInteger(a,b,c) {
  if(a != null)
    if(typeof a  == "number") this.fromNumber(a,b,c);
    else if( (b == null) &&  (typeof a != "string")) this.fromString(a,256);
    else this.fromString(a,b);
}

function nbi() { return new BigInteger(null); }

function am1(i,x,w,j,c,n) {
  while(--n >= 0) {
    var v = x*this[i++]+w[j]+c;
    c = Math.floor(v/0x4000000);
    w[j++] = v&0x3ffffff;
  }
  return c;
}
function am2(i,x,w,j,c,n) {
  var xl = x&0x7fff, xh = x>>15;
  while(--n >= 0) {
    var l = this[i]&0x7fff;
    var h = this[i++]>>15;
    var m = xh*l+h*xl;
    l = xl*l+((m&0x7fff)<<15)+w[j]+(c&0x3fffffff);
    c = (l>>>30)+(m>>>15)+xh*h+(c>>>30);
    w[j++] = l&0x3fffffff;
  }
  return c;
}
function am3(i,x,w,j,c,n) {
  var xl = x&0x3fff, xh = x>>14;
  while(--n >= 0) {
    var l = this[i]&0x3fff;
    var h = this[i++]>>14;
    var m = xh*l+h*xl;
    l = xl*l+((m&0x3fff)<<14)+w[j]+c;
    c = (l>>28)+(m>>14)+xh*h;
    w[j++] = l&0xfffffff;
  }
  return c;
}

if (navigator.appName == "Nokia"){
	BigInteger.prototype.am = am3;
  	dbits = 28;
}
else if(j_lm && (navigator.appName == "Microsoft Internet Explorer")) {
  BigInteger.prototype.am = am2;
  dbits = 30;
}
else if(j_lm && (navigator.appName != "Netscape")) {
  BigInteger.prototype.am = am1;
  dbits = 26;
}
else { 
  BigInteger.prototype.am = am1;
  dbits = 26;
}

BigInteger.prototype.DB = dbits;
BigInteger.prototype.DM = ((1<<dbits)-1);
BigInteger.prototype.DV = (1<<dbits);

var BI_FP = 52;
BigInteger.prototype.FV = Math.pow(2,BI_FP);
BigInteger.prototype.F1 = BI_FP-dbits;
BigInteger.prototype.F2 = 2*dbits-BI_FP;

// Digit conversions
var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
var BI_RC = new Array();
var rr,vv;
rr = "0".charCodeAt(0);
for(vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
rr = "a".charCodeAt(0);
for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
rr = "A".charCodeAt(0);
for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;

function int2char(n) { return BI_RM.charAt(n); }
function intAt(s,i) {
  var c = BI_RC[s.charCodeAt(i)];
  return (c==null)?-1:c;
}


function bnpCopyTo(r) {
  for(var i = this.t-1; i >= 0; --i) r[i] = this[i];
  r.t = this.t;
  r.s = this.s;
}

function bnpFromInt(x) {
  this.t = 1;
  this.s = (x<0)?-1:0;
  if(x > 0) this[0] = x;
  else if(x < -1) this[0] = x+DV;
  else this.t = 0;
}

function nbv(i) { var r = nbi(); r.fromInt(i); return r; }

function bnpFromString(s,b) {
  
  var k;
  if(b == 16) k = 4;
  else if(b == 8) k = 3;
  else if(b == 256) k = 8; 
  else if(b == 2) k = 1;
  else if(b == 32) k = 5;
  else if(b == 4) k = 2;
  else { this.fromRadix(s,b); return; }
  
  this.t = 0;
  this.s = 0;
  var i = s.length, mi = false, sh = 0;
  while(--i >= 0) {
    var x = (k==8)?s[i]&0xff:intAt(s,i);
    if(x < 0) {
      if(s.charAt(i) == "-") mi = true;
      continue;
    }
    mi = false;
    if(sh == 0)
      this[this.t++] = x;
    else if(sh+k > this.DB) {
      this[this.t-1] |= (x&((1<<(this.DB-sh))-1))<<sh;
      this[this.t++] = (x>>(this.DB-sh));
    }
    else
      this[this.t-1] |= x<<sh;
    sh += k;
    if(sh >= this.DB) sh -= this.DB;
  }
  if(k == 8 && (s[0]&0x80) != 0) {
    this.s = -1;
    if(sh > 0) this[this.t-1] |= ((1<<(this.DB-sh))-1)<<sh;
  }
  this.clamp();
  if(mi) BigInteger.ZERO.subTo(this,this);
}

function bnpClamp() {
  var c = this.s&this.DM;
  while(this.t > 0 && this[this.t-1] == c) --this.t;
}

function bnToString(b) {
  if(this.s < 0) return "-"+this.negate().toString(b);
  var k;
  if(b == 16) k = 4;
  else if(b == 8) k = 3;
  else if(b == 2) k = 1;
  else if(b == 32) k = 5;
  else if(b == 4) k = 2;
  else return this.toRadix(b);
  
  
  var km = (1<<k)-1, d, m = false, r = "", i = this.t;
  var p = this.DB-(i*this.DB)%k;
  if(i-- > 0) {
    if(p < this.DB && (d = this[i]>>p) > 0) { m = true; r = int2char(d); }
    while(i >= 0) {
      if(p < k) {
        d = (this[i]&((1<<p)-1))<<(k-p);
        d |= this[--i]>>(p+=this.DB-k);
      }
      else {
        d = (this[i]>>(p-=k))&km;
        if(p <= 0) { p += this.DB; --i; }
      }
      if(d > 0) m = true;
      if(m) r += int2char(d);
    }
  }
  
  if (b==16 && r.length%2>0)
      r = "0"+r;
  return m?r:"0";
}

function bnAbs() { return (this.s<0)?this.negate():this; }

function bnCompareTo(a) {
  var r = this.s-a.s;
  if(r != 0) return r;
  var i = this.t;
  r = i-a.t;
  if(r != 0) return r;
  while(--i >= 0) if((r=this[i]-a[i]) != 0) return r;
  return 0;
}

function nbits(x) {
  var r = 1, t;
  if((t=x>>>16) != 0) { x = t; r += 16; }
  if((t=x>>8) != 0) { x = t; r += 8; }
  if((t=x>>4) != 0) { x = t; r += 4; }
  if((t=x>>2) != 0) { x = t; r += 2; }
  if((t=x>>1) != 0) { x = t; r += 1; }
  return r;
}

function bnBitLength() {
  if(this.t <= 0) return 0;
  return this.DB*(this.t-1)+nbits(this[this.t-1]^(this.s&this.DM));
}

function bnpDLShiftTo(n,r) {
  var i;
  for(i = this.t-1; i >= 0; --i) r[i+n] = this[i];
  for(i = n-1; i >= 0; --i) r[i] = 0;
  r.t = this.t+n;
  r.s = this.s;
}


function bnpDRShiftTo(n,r) {
  for(var i = n; i < this.t; ++i) r[i-n] = this[i];
  r.t = Math.max(this.t-n,0);
  r.s = this.s;
}

function bnpLShiftTo(n,r) {
  var bs = n%this.DB;
  var cbs = this.DB-bs;
  var bm = (1<<cbs)-1;
  var ds = Math.floor(n/this.DB), c = (this.s<<bs)&this.DM, i;
  for(i = this.t-1; i >= 0; --i) {
    r[i+ds+1] = (this[i]>>cbs)|c;
    c = (this[i]&bm)<<bs;
  }
  for(i = ds-1; i >= 0; --i) r[i] = 0;
  r[ds] = c;
  r.t = this.t+ds+1;
  r.s = this.s;
  r.clamp();
}

function bnpRShiftTo(n,r) {
  r.s = this.s;
  var ds = Math.floor(n/this.DB);
  if(ds >= this.t) { r.t = 0; return; }
  var bs = n%this.DB;
  var cbs = this.DB-bs;
  var bm = (1<<bs)-1;
  r[0] = this[ds]>>bs;
  for(var i = ds+1; i < this.t; ++i) {
    r[i-ds-1] |= (this[i]&bm)<<cbs;
    r[i-ds] = this[i]>>bs;
  }
  if(bs > 0) r[this.t-ds-1] |= (this.s&bm)<<cbs;
  r.t = this.t-ds;
  r.clamp();
}

function bnpSubTo(a,r) {
  var i = 0, c = 0, m = Math.min(a.t,this.t);
  while(i < m) {
    c += this[i]-a[i];
    r[i++] = c&this.DM;
    c >>= this.DB;
  }
  if(a.t < this.t) {
    c -= a.s;
    while(i < this.t) {
      c += this[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c += this.s;
  }
  else {
    c += this.s;
    while(i < a.t) {
      c -= a[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c -= a.s;
  }
  r.s = (c<0)?-1:0;
  if(c < -1) r[i++] = this.DV+c;
  else if(c > 0) r[i++] = c;
  r.t = i;
  r.clamp();
}

function bnpMultiplyTo(a,r) {
  var x = this.abs(), y = a.abs();
  var i = x.t;
  r.t = i+y.t;
  while(--i >= 0) r[i] = 0;
  for(i = 0; i < y.t; ++i) r[i+x.t] = x.am(0,y[i],r,i,0,x.t);
  r.s = 0;
  r.clamp();
  if(this.s != a.s) BigInteger.ZERO.subTo(r,r);
}

function bnpSquareTo(r) {
  var x = this.abs();
  var i = r.t = 2*x.t;
  while(--i >= 0) r[i] = 0;
  for(i = 0; i < x.t-1; ++i) {
    var c = x.am(i,x[i],r,2*i,0,1);
    if((r[i+x.t]+=x.am(i+1,2*x[i],r,2*i+1,c,x.t-i-1)) >= x.DV) {
      r[i+x.t] -= x.DV;
      r[i+x.t+1] = 1;
    }
  }
  if(r.t > 0) r[r.t-1] += x.am(i,x[i],r,2*i,0,1);
  r.s = 0;
  r.clamp();
}

function bnpDivRemTo(m,q,r) {
  var pm = m.abs();
  if(pm.t <= 0) return;
  var pt = this.abs();
  if(pt.t < pm.t) {
    if(q != null) q.fromInt(0);
    if(r != null) this.copyTo(r);
    return;
  }
  if(r == null) r = nbi();
  var y = nbi(), ts = this.s, ms = m.s;
  var nsh = this.DB-nbits(pm[pm.t-1]);	// normalize modulus
  if(nsh > 0) { pm.lShiftTo(nsh,y); pt.lShiftTo(nsh,r); }
  else { pm.copyTo(y); pt.copyTo(r); }
  var ys = y.t;
  var y0 = y[ys-1];
  if(y0 == 0) return;
  var yt = y0*(1<<this.F1)+((ys>1)?y[ys-2]>>this.F2:0);
  var d1 = this.FV/yt, d2 = (1<<this.F1)/yt, e = 1<<this.F2;
  var i = r.t, j = i-ys, t = (q==null)?nbi():q;
  y.dlShiftTo(j,t);
  if(r.compareTo(t) >= 0) {
    r[r.t++] = 1;
    r.subTo(t,r);
  }
  BigInteger.ONE.dlShiftTo(ys,t);
  t.subTo(y,y);	
  while(y.t < ys) y[y.t++] = 0;
  while(--j >= 0) {
    var qd = (r[--i]==y0)?this.DM:Math.floor(r[i]*d1+(r[i-1]+e)*d2);
    if((r[i]+=y.am(0,qd,r,j,0,ys)) < qd) {	
      y.dlShiftTo(j,t);
      r.subTo(t,r);
      while(r[i] < --qd) r.subTo(t,r);
    }
  }
  if(q != null) {
    r.drShiftTo(ys,q);
    if(ts != ms) BigInteger.ZERO.subTo(q,q);
  }
  r.t = ys;
  r.clamp();
  if(nsh > 0) r.rShiftTo(nsh,r);	
  if(ts < 0) BigInteger.ZERO.subTo(r,r);
}

function Classic(m) { this.m = m; }
function cConvert(x) {
  if(x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
  else return x;
}
function cRevert(x) { return x; }
function cReduce(x) { x.divRemTo(this.m,null,x); }
function cMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }
function cSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

Classic.prototype.convert = cConvert;
Classic.prototype.revert = cRevert;
Classic.prototype.reduce = cReduce;
Classic.prototype.mulTo = cMulTo;
Classic.prototype.sqrTo = cSqrTo;


function bnpInvDigit() {
  if(this.t < 1) return 0;
  var x = this[0];
  if((x&1) == 0) return 0;
  var y = x&3;		
  y = (y*(2-(x&0xf)*y))&0xf;	
  y = (y*(2-(x&0xff)*y))&0xff;	
  y = (y*(2-(((x&0xffff)*y)&0xffff)))&0xffff;	

  y = (y*(2-x*y%this.DV))%this.DV;		
  return (y>0)?this.DV-y:-y;
}

function Montgomery(m) {
  this.m = m;
  this.mp = m.invDigit();
  this.mpl = this.mp&0x7fff;
  this.mph = this.mp>>15;
  this.um = (1<<(m.DB-15))-1;
  this.mt2 = 2*m.t;
}

function montConvert(x) {
  var r = nbi();
  x.abs().dlShiftTo(this.m.t,r);
  r.divRemTo(this.m,null,r);
  if(x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r,r);
  return r;
}

function montRevert(x) {
  var r = nbi();
  x.copyTo(r);
  this.reduce(r);
  return r;
}

function montReduce(x) {
  while(x.t <= this.mt2)	
    x[x.t++] = 0;
  for(var i = 0; i < this.m.t; ++i) {
    var j = x[i]&0x7fff;
    var u0 = (j*this.mpl+(((j*this.mph+(x[i]>>15)*this.mpl)&this.um)<<15))&x.DM;
    j = i+this.m.t;
    x[j] += this.m.am(0,u0,x,i,0,this.m.t);
    while(x[j] >= x.DV) { x[j] -= x.DV; x[++j]++; }
  }
  x.clamp();
  x.drShiftTo(this.m.t,x);
  if(x.compareTo(this.m) >= 0) x.subTo(this.m,x);
}

function montSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

function montMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }

Montgomery.prototype.convert = montConvert;
Montgomery.prototype.revert = montRevert;
Montgomery.prototype.reduce = montReduce;
Montgomery.prototype.mulTo = montMulTo;
Montgomery.prototype.sqrTo = montSqrTo;

function bnpIsEven() { return ((this.t>0)?(this[0]&1):this.s) == 0; }

function bnpExp(e,z) {
  var r = nbi(), r2 = nbi(), g = z.convert(this), i = nbits(e)-1;
  g.copyTo(r);
  while(--i >= 0) {
    z.sqrTo(r,r2);
    if((e&(1<<i)) > 0) z.mulTo(r2,g,r);
    else { var t = r; r = r2; r2 = t; }
  }
  return z.revert(r);
}

function bnModPowInt(e,m) {
  var z;
  if(e < 256 || m.isEven()) z = new Classic(m); else z = new Montgomery(m);
  return this.exp(e,z);
}

function bnpToRadix(b) {
  if(b == null) b = 10;
  if(this.signum() == 0 || b < 2 || b > 36) return "0";
  var cs = this.chunkSize(b);
  var a = Math.pow(b,cs);
  var d = nbv(a), y = nbi(), z = nbi(), r = "";
  this.divRemTo(d,y,z);
  while(y.signum() > 0) {
    r = (a+z.intValue()).toString(b).substr(1) + r;
    y.divRemTo(d,y,z);
  }
  return z.intValue().toString(b) + r;
}

function bnpBitwiseTo(a,op,r) {
  var i, f, m = Math.min(a.t,this.t);
  for(i = 0; i < m; ++i) r[i] = op(this[i],a[i]);
  if(a.t < this.t) {
    f = a.s&this.DM;
    for(i = m; i < this.t; ++i) r[i] = op(this[i],f);
    r.t = this.t;
  }
  else {
    f = this.s&this.DM;
    for(i = m; i < a.t; ++i) r[i] = op(f,a[i]);
    r.t = a.t;
  }
  r.s = op(this.s,a.s);
  r.clamp();
}

function op_xor(x,y) { return x^y; }
function bnXor(a) { var r = nbi(); this.bitwiseTo(a,op_xor,r); return r; }

function lbit(x) {
  if(x == 0) return -1;
  var r = 0;
  if((x&0xffff) == 0) { x >>= 16; r += 16; }
  if((x&0xff) == 0) { x >>= 8; r += 8; }
  if((x&0xf) == 0) { x >>= 4; r += 4; }
  if((x&3) == 0) { x >>= 2; r += 2; }
  if((x&1) == 0) ++r;
  return r;
}

BigInteger.prototype.copyTo = bnpCopyTo;
BigInteger.prototype.fromInt = bnpFromInt;
BigInteger.prototype.fromString = bnpFromString;
BigInteger.prototype.clamp = bnpClamp;
BigInteger.prototype.dlShiftTo = bnpDLShiftTo;
BigInteger.prototype.subTo = bnpSubTo;
BigInteger.prototype.rShiftTo = bnpRShiftTo;
BigInteger.prototype.drShiftTo = bnpDRShiftTo;


BigInteger.prototype.invDigit = bnpInvDigit;
BigInteger.prototype.isEven = bnpIsEven;

BigInteger.prototype.multiplyTo = bnpMultiplyTo;
BigInteger.prototype.lShiftTo = bnpLShiftTo;
BigInteger.prototype.divRemTo = bnpDivRemTo;
BigInteger.prototype.squareTo = bnpSquareTo;
BigInteger.prototype.exp = bnpExp;

BigInteger.prototype.toRadix = bnpToRadix;
BigInteger.prototype.bitwiseTo = bnpBitwiseTo;

BigInteger.prototype.toString = bnToString;

BigInteger.prototype.abs = bnAbs;
BigInteger.prototype.compareTo = bnCompareTo;
BigInteger.prototype.bitLength = bnBitLength;

BigInteger.prototype.modPowInt = bnModPowInt;

BigInteger.prototype.xor = bnXor;

BigInteger.ZERO = nbv(0);
BigInteger.ONE = nbv(1);
/**
 * @fileOverview DBS Vickers OBMApplet Javascript - OAEPEncodedMessage.js
 * @author Pedric Kng<br>DSSS, http://www.ds3global.com 
 * @version 1.0 August 2010
 */

function OAEPEncodedMessage(pinMessage){
    
    var ENCODING_PARAMETER_SIZE_IN_BYTES = 16;
    var SHA1_HASH_SIZE_IN_BYTES = 20;
    var MIN_PIN_MESSAGE_SIZE_IN_BYTES = 17;
    var MAX_PIN_MESSAGE_SIZE_IN_BYTES = OBMApplet.RSA_MODULUS_SIZE_IN_BYTES - 42; 
    var ENCODED_MESSAGE_SIZE_IN_BYTES = OBMApplet.RSA_MODULUS_SIZE_IN_BYTES - 1; 
    var DATA_BLOCK_SIZE_IN_BYTES = ENCODED_MESSAGE_SIZE_IN_BYTES - 20;  
    
    var ERR_INVALID_PIN_MESSAGE = OAEPEncodedMessage.ERR_INVALID_PIN_MESSAGE;
    var ERR_INVALID_PIN_MESSAGE_LENGTH = OAEPEncodedMessage.ERR_INVALID_PIN_MESSAGE_LENGTH;

    var _encodedMsgByteArray;
    var _encodingParameterString;

    function _OAEPEncodeMessage(pinMessage){
      
        var labelByteArray = randomGenerator(ENCODING_PARAMETER_SIZE_IN_BYTES);
        _encodedMsgByteArray = doOAEPEncoding(pinMessage, labelByteArray);
        _encodingParameterString = Util.toHexString(labelByteArray);
      
    }
    _OAEPEncodeMessage(pinMessage);
  

    function doOAEPEncoding(pinMessage, labelByteArray)
    {
        var pinMsgByteArray = new Array(MAX_PIN_MESSAGE_SIZE_IN_BYTES);
        
        if(pinMessage == null){
            throw {
                name: "OAEPEncodedMsgException",
                message: "Error no : "+ERR_INVALID_PIN_MESSAGE+" - Invalid PIN Message",
                code: ERR_INVALID_PIN_MESSAGE
            }
        }
        var pinMsgLength = pinMessage.length();
        if(pinMsgLength < MIN_PIN_MESSAGE_SIZE_IN_BYTES || pinMsgLength > MAX_PIN_MESSAGE_SIZE_IN_BYTES)
        {
            throw {
                name: "OAEPEncodedMsgException",
                message:  "Error no : "+ERR_INVALID_PIN_MESSAGE_LENGTH+" Invalid PIN message length",
                code: ERR_INVALID_PIN_MESSAGE_LENGTH
            }
        } 
        pinMessage.getBytes(pinMsgByteArray); 

        var pHash = doHash(labelByteArray);
        
        var DB = new Array(DATA_BLOCK_SIZE_IN_BYTES);
        OBMApplet.fillByteArray(DB, 0);
        OBMApplet.arraycopy(pHash, 0, DB, 0, 20);
        
        
        var offset = 20;
        var numberOfPaddingBytes = DATA_BLOCK_SIZE_IN_BYTES - 20 - pinMsgLength - 1;
        offset += numberOfPaddingBytes;
        DB[offset] = 1;
        offset++;
        
        OBMApplet.arraycopy(pinMsgByteArray, 0, DB, offset, pinMsgLength);
        
        
        var seed = randomGenerator(SHA1_HASH_SIZE_IN_BYTES);
        var dbMask = new Array(DATA_BLOCK_SIZE_IN_BYTES);
        MGF1(seed, dbMask, DATA_BLOCK_SIZE_IN_BYTES);
        
        var maskedDB = new Array(DATA_BLOCK_SIZE_IN_BYTES);
        OBMApplet.xorByteArray(DB, dbMask, maskedDB);
                
        var seedMask = new Array(SHA1_HASH_SIZE_IN_BYTES);
        MGF1(maskedDB, seedMask, SHA1_HASH_SIZE_IN_BYTES);
    
        var maskedSeed = new Array(SHA1_HASH_SIZE_IN_BYTES);
        
        OBMApplet.xorByteArray(seed, seedMask, maskedSeed);
        
        var encodedMsgByteArray = new Array(ENCODED_MESSAGE_SIZE_IN_BYTES);
        OBMApplet.arraycopy(maskedSeed, 0, encodedMsgByteArray, 0, 20);
        OBMApplet.arraycopy(maskedDB, 0, encodedMsgByteArray, 20, DATA_BLOCK_SIZE_IN_BYTES);
        
        return encodedMsgByteArray;
    }
  
    function MGF1(Z, T, l)
    {
        var C = new Array(4);
        var maxCount = Math.ceil(l/SHA1_HASH_SIZE_IN_BYTES) - 1;
       
        var _T = [];
        for(var counter = 0; counter <= maxCount; counter++)
        {
            I2OSP(counter, C, 0);
            _T = _T.concat(doHash(Z.concat(C)));
        }
        OBMApplet.arraycopy(_T, 0, T, 0, l);

    }
  
    function I2OSP(inputWord, byteArray, arrayOffset)
    {
        byteArray[arrayOffset] = (inputWord >>> 24);
        byteArray[arrayOffset + 1] = (inputWord >>> 16);
        byteArray[arrayOffset + 2] = (inputWord >>> 8);
        byteArray[arrayOffset + 3] = inputWord;
    }
  
    this.getBytes=function()
    {
        return _encodedMsgByteArray;
    }

    this.length=function()
    {
        return _encodedMsgByteArray.length;
    }

    this.getEncodingParameter=function()
    {
        return _encodingParameterString;
    }
  
    function doHash(inputMsgByteArray){
        return Util.fromHexString(SHA1Hash(Util.cByteArrayToNString(inputMsgByteArray)));
    }

    function randomGenerator(length)
    {
        var randomHexArray = new Array(length);
        var randomNo1, randomNo2;
        for (var i = 0; i < randomHexArray.length; i++) {
            randomNo1 = Math.floor(Math.random()*16);
            randomNo2 = Math.floor(Math.random()*16);
            randomHexArray[i] = ((randomNo1 << 4) + randomNo2);
        }
        return randomHexArray;
    }
}

OAEPEncodedMessage.ERR_INVALID_PIN_MESSAGE = 30;
OAEPEncodedMessage.ERR_INVALID_PIN_MESSAGE_LENGTH = 31;

function OBMApplet(){
    
    var ERR_INVALID_RSA_KEY = OBMApplet.ERR_INVALID_RSA_KEY;
    var ERR_INVALID_ENCODED_MSG_LENGTH = OBMApplet.ERR_INVALID_ENCODED_MSG_LENGTH;
    var ERR_INVALID_RSA_KEY_LENGTH = OBMApplet.ERR_INVALID_RSA_KEY_LENGTH;
    var ERR_OLD_NEW_PASSWORD_SAME = UOBApplet.ERR_OLD_NEW_PASSWORD_SAME;
    
    var PUBLIC_EXPONENT_STRING = OBMApplet.PUBLIC_EXPONENT_STRING;
    var MODULUS_STRING = OBMApplet.MODULUS_STRING;
    var RSA_MODULUS_SIZE_IN_BYTES = OBMApplet.RSA_MODULUS_SIZE_IN_BYTES;
    
    var _C_String="", _P_String="", isPublicKeyDataValid=false;
    
    function _OBMApplet(){
      if(RSA_MODULUS_SIZE_IN_BYTES == 0 || MODULUS_STRING == null || PUBLIC_EXPONENT_STRING == null)
            throw {
                name: "OBMAppletException",
                message:  "Error no : "+ERR_INVALID_RSA_KEY+" Invalid RSA key",
                code: ERR_INVALID_RSA_KEY
            }
        if((PUBLIC_EXPONENT_STRING.length/2) !=RSA_MODULUS_SIZE_IN_BYTES || (MODULUS_STRING.length/2)!=RSA_MODULUS_SIZE_IN_BYTES)
            throw{
                name: "OBMAppletException",
                message: "Error no : "+ERR_INVALID_RSA_KEY_LENGTH+" Invalid RSA key length",
                code: ERR_INVALID_RSA_KEY_LENGTH
            }
        isPublicKeyDataValid = true;
    }
    _OBMApplet();
    
    this.OBM_EncryptPassword = function(){
        
        if(arguments.length == 2){
            OBM_EncryptPassword2(arguments[0], arguments[1]);
        }else if(arguments.length == 3){
            OBM_EncryptPassword3(arguments[0], arguments[1], arguments[2]);
        }
    }
    
    function OBM_EncryptPassword2(pinString, RN_String){
        if(!isPublicKeyDataValid) throw {
            name: "OBMAppletException",
            message: "Error no : "+ERR_INVALID_RSA_KEY+" Invalid RSA key",
            code: ERR_INVALID_RSA_KEY
          }
        
        var pinBlock = new PINBlock(pinString);
        var pinMessage = new PINMessage(pinBlock, RN_String);
        var oaepEncMessage = new OAEPEncodedMessage(pinMessage);
        
        checkKeyMsgParameters(oaepEncMessage);
        
        _P_String = oaepEncMessage.getEncodingParameter();
        
        var dataBlock = [0x00].concat(oaepEncMessage.getBytes());
        
        var rsa = new RSAKey();
        rsa.setPublic(MODULUS_STRING, PUBLIC_EXPONENT_STRING);
        _C_String = rsa.encryptNativeBytes(dataBlock);
    }
    
    function OBM_EncryptPassword3(oldPINString, newPINString, RN_String){
        if(!isPublicKeyDataValid) throw {
            name: "OBMAppletException",
            message: "Error no : "+ERR_INVALID_RSA_KEY+" Invalid RSA key",
            code: ERR_INVALID_RSA_KEY
          }
        if(oldPINString == newPINString) throw{
            name: "OBMAppletException",
            message: "Error no : "+ERR_OLD_NEW_PASSWORD_SAME+" New password is same as old password.",
            code: ERR_OLD_NEW_PASSWORD_SAME
        }
        
        var oldpinBlock = new PINBlock(oldPINString);
        var newpinBlock = new PINBlock(newPINString);
        var pinMessage = new PINMessage(oldpinBlock, newpinBlock, RN_String);
        var oaepEncMessage = new OAEPEncodedMessage(pinMessage);
        
        checkKeyMsgParameters(oaepEncMessage);
        
        _P_String = oaepEncMessage.getEncodingParameter();
        var dataBlock = [0x00].concat(oaepEncMessage.getBytes());
        
        var rsa = new RSAKey();
        rsa.setPublic(MODULUS_STRING, PUBLIC_EXPONENT_STRING);
        _C_String = rsa.encryptNativeBytes(dataBlock);
        
    }
    
    this.OBM_GetEncryptedPassword = function()
    {
        return _C_String;
    }

    this.OBM_GetEncodingParameter = function()
    {
        return _P_String;
    }
    
    function checkKeyMsgParameters(oaepEncMessage){
        
        if(RSA_MODULUS_SIZE_IN_BYTES == 0 || MODULUS_STRING == null || PUBLIC_EXPONENT_STRING == null)
            throw {
                name: "EncryptedMessageException",
                message:  "Error no : "+ERR_INVALID_RSA_KEY+" Invalid RSA key",
                code: ERR_INVALID_RSA_KEY
            }
        if((PUBLIC_EXPONENT_STRING.length/2) !=RSA_MODULUS_SIZE_IN_BYTES || (MODULUS_STRING.length/2)!=RSA_MODULUS_SIZE_IN_BYTES)
            throw{
                name: "EncryptedMessageException",
                message: "Error no : "+ERR_INVALID_RSA_KEY_LENGTH+" Invalid RSA key length",
                code: ERR_INVALID_RSA_KEY_LENGTH
            }
        if(oaepEncMessage == null)
            throw {
                name: "EncryptedMessageException",
                message:  "Error no : "+ERR_INVALID_ENCODED_MSG_LENGTH+" Invalid OAEP-encoded message length",
                code: ERR_INVALID_ENCODED_MSG_LENGTH
            } 
        if(oaepEncMessage.length > RSA_MODULUS_SIZE_IN_BYTES)
            throw{
                name: "EncryptedMessageException",
                message: "Error no : "+ERR_INVALID_ENCODED_MSG_LENGTH+" input data too large for RSA encryption",
                code: ERR_INVALID_ENCODED_MSG_LENGTH
            }
        
    }
}

OBMApplet.ERR_INVALID_RSA_KEY = 42;

OBMApplet.ERR_INVALID_ENCODED_MSG_LENGTH = 40;

OBMApplet.ERR_INVALID_RSA_KEY_LENGTH = 41;

OBMApplet.PUBLIC_EXPONENT_STRING = "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000A1C3";

OBMApplet.MODULUS_STRING = "BB3DEFC03F8B0B2BEE2F62CE67691469EF96783D4B7788A1168D116B412833ECE1D44F0DA1EE66571C84C128E8BF6365151D5799193F11FA4FA6F7D0D2BD44AF2EB289DBAC477023389188FD9D88C91F69A5656FFD4853CF4D660134FE091E8D92E37DC6B2861F60BFF02D96042FD3A2A49F7C93C110BD534668A93905E40D23";

OBMApplet.RSA_MODULUS_SIZE_IN_BYTES = 256;

OBMApplet.fillByteArray = function( byteArray,  fillCharacter)
{
    var  index;
    for (index = 0; index < byteArray.length; index++)
    {  		
        byteArray[index] =  fillCharacter;
    }
}

OBMApplet.convertAsciiArrayToHexByteArray =  function( asciiArray, hexByteArray, 
HexByteArrayOffset, asciiArrayLength)
{
    var  NUM_OF_NIBBLES_PER_BYTE = 2;
		    
    var  tempInt, byteCount, digitCount, byteLength;
		  	
    byteLength = Math.ceil(asciiArrayLength / 2);
		  	
    for (byteCount = 0, digitCount = 0; byteCount < byteLength; byteCount++)
    {  		
        if (digitCount < (asciiArrayLength - 1))
        {
            tempInt = ( asciiArray[digitCount] & 0x0F) << 4;
            tempInt = tempInt |  asciiArray[digitCount + 1] & 0x0F;
        }
        else
        {
            tempInt =  hexByteArray[byteCount + HexByteArrayOffset] & 0x0F;
            tempInt = tempInt | ( asciiArray[digitCount] & 0x0F) << 4;
        }
        hexByteArray[byteCount + HexByteArrayOffset] = tempInt;
        digitCount += NUM_OF_NIBBLES_PER_BYTE;
    }

}

OBMApplet.arraycopy=function(srcArr, srcArrPos, destArr, destArrPos, length){
   var insertLen = Math.min(srcArrPos+length, srcArr.length);
   for(var i=srcArrPos, j=destArrPos; i<insertLen; i++,j++){
       destArr[j]=srcArr[i];
   }
}


OBMApplet.convertStringToPackedHexByteArray = function ( inputString,  hexArray,  hexArrayOffset)
{
    // constants
    var INVALID_HEX_CHAR_ERROR = 1;
    var NO_HEX_CONVERSION_ERRORS = 0;
                        
    var stringLength = inputString.length;
    for(var byteCount = 0, charCount = 0; charCount < stringLength; byteCount++, charCount++)
    {
        var inputChar = inputString.charAt(charCount);
        var hexValue = parseInt(inputChar, 16);
        if(isNaN(hexValue)) return INVALID_HEX_CHAR_ERROR;
        
        var temp = hexValue << 4;
        if(++charCount < stringLength)
        {
            inputChar = inputString.charAt(charCount);
            hexValue = parseInt(inputChar, 16);
            if(isNaN(hexValue))  return INVALID_HEX_CHAR_ERROR;
            
            hexArray[byteCount + hexArrayOffset] = (temp | hexValue);
        } else
        {
            hexArray[byteCount + hexArrayOffset] = (temp | 0x0f);
        }
    }

    return NO_HEX_CONVERSION_ERRORS;
}


OBMApplet.xorByteArray=function(byteArray1, byteArray2, resultByteArray){
    for(var index = 0; index < byteArray1.length; index++)
      resultByteArray[index] = (byteArray1[index] ^ byteArray2[index]);
}

function PINBlock(pinString){
    
    var ERR_INVALID_PIN_LENGTH = PINBlock.ERR_INVALID_PIN_LENGTH;
    var ERR_INVALID_PIN = PINBlock.ERR_INVALID_PIN;
    var ISO_FORMAT_2_TYPE = PINBlock.ISO_FORMAT_2_TYPE;
    var ISO_FORMAT_12_TYPE = PINBlock.ISO_FORMAT_12_TYPE;
    
    var PIN_BLOCK_FILL_CHARACTER = 0xFF;
    var FMT_2_CONTROL_BYTE = 0x02;
    var FMT_12_CONTROL_BYTE = 0xC1;
    
    var MAX_NUMERIC_PIN_STRING_SIZE = 12;
    var MAX_PIN_STRING_SIZE = UOBApplet.MAX_PIN_STRING_SIZE; //24
    var MIN_PIN_STRING_SIZE = UOBApplet.MIN_PIN_STRING_SIZE; //8
    var NUM_OF_BYTES_IN_FMT2_PIN_BLOCK = 8;
    
    var _PINBlockByteArray = [];
    var _PINBlockType = 0;
    var _PINBlockLength = 0;
    
    function _ValidateAndCreatePINBlockByteArray(pinString){
        
        var isPINNumeric = false;
        var isInvalidCharFound = false;
        var PinStringByteArray = []; 
        var numericPinStringByteArray = []; 
        
        if(pinString == null || pinString == undefined) 
            throw {
                name: "PINBlockException",
                message: "Error no : " + ERR_INVALID_PIN + " - Invalid PIN String",
                code: ERR_INVALID_PIN
            }
        
        var PINLength = pinString.length; 
        if (PINLength > MAX_PIN_STRING_SIZE || PINLength < MIN_PIN_STRING_SIZE)
            throw {
                name: "PINBlockException",
                message: "Error no : " + ERR_INVALID_PIN_LENGTH + " - Invalid PIN length",
                code: ERR_INVALID_PIN_LENGTH
            }
        
      
    for (var index = 0; index < PINLength; index++)
  	{
  	  var pinChar = pinString.charAt(index);
 	  
 	  if (!_isLetterOrDigit(pinChar))
 	  {
 	    isInvalidCharFound = true;
 	    break;
 	  }
 	  
 	  if (isPINNumeric)
 	  {
 	    if (!_isDigit(pinChar)) isPINNumeric = false;
 	    else numericPinStringByteArray[index] = parseInt(pinChar);
 	  }
 	  PinStringByteArray[index] = pinChar.charCodeAt(0);
  	}

  	if (isInvalidCharFound) {
  	  throw {
                name: "PINBlockException",
                message: "Error no : " + ERR_INVALID_PIN + " - Invalid PIN String",
                code: ERR_INVALID_PIN
          }
  	}else {
  	  if (isPINNumeric) _createFormat2PINBlock(numericPinStringByteArray,
            numericPinStringByteArray.length);
 	  else _createFormat12PINBlock(PinStringByteArray,
            PinStringByteArray.length);
 	}
  	
    }
    
    function _createFormat2PINBlock(numericPinByteArray, PINLength)
    {
          _PINBlockType = ISO_FORMAT_2_TYPE;
          
          _PINBlockLength = NUM_OF_BYTES_IN_FMT2_PIN_BLOCK;
          _PINBlockByteArray = new Array(NUM_OF_BYTES_IN_FMT2_PIN_BLOCK);
          OBMApplet.fillByteArray(_PINBlockByteArray, PIN_BLOCK_FILL_CHARACTER);
          
          var tempInt = FMT_2_CONTROL_BYTE << 4; //0x20
          _PINBlockByteArray[0] = (tempInt | (PINLength & 0x0F));
          
          OBMApplet.convertAsciiArrayToHexByteArray(numericPinByteArray, _PINBlockByteArray, 1, PINLength);
    }
    
    function _createFormat12PINBlock(PinStringByteArray, PINLength)
    {
          _PINBlockType = ISO_FORMAT_12_TYPE;

          var numberOfPINBlocks = 4; 
          if (PINLength <= 6) {
            numberOfPINBlocks = 1;
          }else {
            numberOfPINBlocks = Math.ceil( (2 + PINLength) / NUM_OF_BYTES_IN_FMT2_PIN_BLOCK);
          }

          _PINBlockLength = numberOfPINBlocks * NUM_OF_BYTES_IN_FMT2_PIN_BLOCK;
          _PINBlockByteArray = new Array(numberOfPINBlocks * NUM_OF_BYTES_IN_FMT2_PIN_BLOCK);
          
          OBMApplet.fillByteArray( _PINBlockByteArray, PIN_BLOCK_FILL_CHARACTER);
          _PINBlockByteArray[0] = FMT_12_CONTROL_BYTE;
          _PINBlockByteArray[1] = PINLength;
          
          for(var i=2, j=0; i<PINLength+2; i++, j++){
              _PINBlockByteArray[i] = PinStringByteArray[j];
          }
    }
    
    this.getPINBlockType=function(){
        return _PINBlockType;
    }
    
    this.getBytes=function(){
          return _PINBlockByteArray;
    }

    this.length=function(){
          return _PINBlockLength;
    }
    
    function _isDigit(c){
        var reDigit = /^\d/;
        return reDigit.test(c);
    }
    
    function _isLetterOrDigit(c){
        var reLetterOrDigit = /^([a-zA-Z_]|\d)$/;
        return reLetterOrDigit.test(c);
    }
    
    _ValidateAndCreatePINBlockByteArray(pinString);
}

PINBlock.ERR_INVALID_PIN_LENGTH = 10;

PINBlock.ERR_INVALID_PIN = 11;

PINBlock.ISO_FORMAT_2_TYPE = 1;

PINBlock.ISO_FORMAT_12_TYPE = 2;

function PINMessage(){
    
    var ONE_PIN_BLOCK_IN_MESSAGE = PINMessage.ONE_PIN_BLOCK_IN_MESSAGE;
    var TWO_PIN_BLOCKS_IN_MESSAGE = PINMessage.TWO_PIN_BLOCKS_IN_MESSAGE;
    
    var ERR_INVALID_PIN_BLOCK = PINMessage.ERR_INVALID_PIN_BLOCK;
    var ERR_INVALID_RANDOM_NUMBER_LENGTH = PINMessage.ERR_INVALID_RANDOM_NUMBER_LENGTH;
    var ERR_INVALID_RANDOM_NUMBER = PINMessage.ERR_INVALID_RANDOM_NUMBER;
    
    var OAEP_SHA1_OFFSET_IN_BYTES = 42;
    var MAX_MESSAGE_SIZE_IN_BYTES = OBMApplet.RSA_MODULUS_SIZE_IN_BYTES - OAEP_SHA1_OFFSET_IN_BYTES;
    
    var MIN_PIN_BLOCK_SIZE = 8;
    var PIN_MESSAGE_TYPE_SIZE = 1;
    var NUM_OF_NIBBLES_PER_BYTE = 2;
    var MIN_RANDOM_NUMBER_STRING_LENGTH = 16;
    var MAX_RANDOM_NUMBER_SIZE_IN_BYTES = MAX_MESSAGE_SIZE_IN_BYTES - 8 - 1;
    var MAX_RANDOM_NUMBER_STRING_LENGTH = MAX_RANDOM_NUMBER_SIZE_IN_BYTES * 2;
    
    var _pinMessageArray;
    var _pinMessageLength;
    var _pinMessageType;
    
    function _PINMessage2(pinBlock, RN_String){
        _pinMessageArray = new Array(MAX_MESSAGE_SIZE_IN_BYTES);
        _pinMessageType = ONE_PIN_BLOCK_IN_MESSAGE;
        _pinMessageArray[0] = _pinMessageType;
        _pinMessageLength = 1;
        _addPinBlockToMessageArray(pinBlock);
        _addRandomStringToMessageArray(RN_String);
    }
    
    function _PINMessage3(oldPINBlock, newPINBlock, RN_String){
        _pinMessageArray = new Array(MAX_MESSAGE_SIZE_IN_BYTES);
        _pinMessageType = TWO_PIN_BLOCKS_IN_MESSAGE;
        _pinMessageArray[0] = _pinMessageType;
        _pinMessageLength = 1;
        _addPinBlockToMessageArray(oldPINBlock);
        _addPinBlockToMessageArray(newPINBlock);
        _addRandomStringToMessageArray(RN_String);
    }
    
    if(arguments.length == 2){
        _PINMessage2(arguments[0],arguments[1]);
    }else if(arguments.length == 3){
        _PINMessage3(arguments[0],arguments[1], arguments[2]);
    }
    
    
    function _addPinBlockToMessageArray(pinBlock)
    {
        if(pinBlock == null)
        {   throw {
                name: "PINMessageException",
                message: "Error no : "+ERR_INVALID_PIN_BLOCK+" - Invalid PIN Block",
                code: ERR_INVALID_PIN_BLOCK
            }
        }else{
            
            OBMApplet.arraycopy(pinBlock.getBytes(), 0, _pinMessageArray, _pinMessageLength, pinBlock.length());
            _pinMessageLength = _pinMessageLength + pinBlock.length();
        }
    }
    
    function _addRandomStringToMessageArray(RN_String)        
    {
        if(RN_String == null){
            throw{
              name: "PINMessageException",
              message: "Error no : "+ERR_INVALID_RANDOM_NUMBER+" - Invalid Random Number String",
              code: ERR_INVALID_RANDOM_NUMBER
            } 
        }
            
        var RNStringLength = RN_String.length;
        var RNByteLength = Math.ceil(RNStringLength / 2);
        var maxRandomNumberStringSize = (MAX_MESSAGE_SIZE_IN_BYTES - _pinMessageLength) * 2;
        
        
        if(RNStringLength < MIN_RANDOM_NUMBER_STRING_LENGTH || RNStringLength > maxRandomNumberStringSize || RNStringLength != RNByteLength * 2)
            throw {
                name: "PINMessageException",
                message: "Error no : "+ERR_INVALID_RANDOM_NUMBER_LENGTH+" - Invalid Random Number String length",
                code: ERR_INVALID_RANDOM_NUMBER_LENGTH
            }
        
        var conversionError = OBMApplet.convertStringToPackedHexByteArray(RN_String, _pinMessageArray, _pinMessageLength);
        if(conversionError != 0)
        {
            throw {
                name: "PINMessageException",
                message: "Error no :"+ERR_INVALID_RANDOM_NUMBER+" - Invalid Random Number String",
                code: ERR_INVALID_RANDOM_NUMBER
            }
        } else {
            
            _pinMessageLength = _pinMessageLength + RNByteLength;
            return;
        }
    }


    this.getBytes=function(byteArray)
    {
        OBMApplet.arraycopy(_pinMessageArray, 0, byteArray, 0, _pinMessageLength);
    }

    this.length=function()
    {
        return _pinMessageLength;
    }
    
}

PINMessage.ONE_PIN_BLOCK_IN_MESSAGE = 0x01;

PINMessage.TWO_PIN_BLOCKS_IN_MESSAGE = 0x02;

PINMessage.ERR_INVALID_PIN_BLOCK = 20;

PINMessage.ERR_INVALID_RANDOM_NUMBER_LENGTH = 21;

PINMessage.ERR_INVALID_RANDOM_NUMBER = 22;

/*!
 * This package includes code written by Tom Wu.
 * 
 * Copyright (c) 2003-2005  Tom Wu
 * All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 */
/*!
 * Copyright (c) 2003-2005  Tom Wu
 * http://www-cs-students.stanford.edu/~tjw/jsbn/
 * All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS-IS" AND WITHOUT WARRANTY OF ANY KIND, 
 * EXPRESS, IMPLIED OR OTHERWISE, INCLUDING WITHOUT LIMITATION, ANY 
 * WARRANTY OF MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE.  
 *
 * IN NO EVENT SHALL TOM WU BE LIABLE FOR ANY SPECIAL, INCIDENTAL,
 * INDIRECT OR CONSEQUENTIAL DAMAGES OF ANY KIND, OR ANY DAMAGES WHATSOEVER
 * RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER OR NOT ADVISED OF
 * THE POSSIBILITY OF DAMAGE, AND ON ANY THEORY OF LIABILITY, ARISING OUT
 * OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 * In addition, the following condition applies:
 *
 * All redistributions must retain an intact copy of this copyright notice
 * and disclaimer.
 */


function parseBigInt(str,r) {
    return new BigInteger(str,r);
}

function pkcs1pad2B(dataBytes, n){
    var numOfBytes = dataBytes.length;

    if(numOfBytes > n - 11){
        throw "104";	
    }

    var result = [0x00, 0x02];
    var PS_Size = n - numOfBytes - 3;
	
    var PS = randomBytes(PS_Size);
	
    var final_padded = result.concat(PS, [0x00], dataBytes);
	
    var padded = new BigInteger(final_padded);
    return padded;
}

function randomBytes(numOfBytes){
    var x=[];
    var i = 0;
    for (i=0;i<numOfBytes;i++){
        x[i] = Math.ceil(Math.random()*255);
    }
    return x;
}

function RSAKey() {
    this.n = null;
    this.e = 0;
    this.d = null;
}

RSAKey.prototype.setPublic=function(N,E){
    if(N != null && E != null && N.length > 0 && E.length > 0) {
        this.n = parseBigInt(N,16);
        this.e = parseInt(E,16);
    }
    else alert("Invalid RSA public key");
}

RSAKey.prototype.doPublic=function(x){  
    return x.modPowInt(this.e, this.n);
}


RSAKey.prototype.encryptNativeBytes=function(dataBytes){
    
    var n = (this.n.bitLength()+7)>>3;  
    if(dataBytes.length > n){
        throw "104"; 
    }
    var m = new BigInteger(dataBytes);
    if(m == null) return null;
    var c = this.doPublic(m);
    if(c == null) return null;
    
    var h = c.toString(16);

    if(h.length>512) return null;
    if(h.length<512){
        for(var i=0; i<(512 - h.length); i++) h= "0"+h;
    }
    return h;
}


RSAKey.prototype.encryptB=function(dataBytes){  
  
    var m  = pkcs1pad2B(dataBytes,(this.n.bitLength()+7)>>3);
    if(m == null) return null;
    var c = this.doPublic(m);
    if(c == null) return null;
    var h = c.toString(16);

    if(h.length>512) return null;
    if(h.length<512){
        for(var i=0; i<(512 - h.length); i++) h= "0"+h;
    }
    return h;
}


function SHA1Hash(msg){
    var K = [0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xca62c1d6];

    msg += String.fromCharCode(0x80); 

    var l = msg.length/4 + 2;  
    var N = Math.ceil(l/16);   
    var M = new Array(N);
    for (var i=0; i<N; i++) {
        M[i] = new Array(16);
        for (var j=0; j<16; j++) { 
            M[i][j] = (msg.charCodeAt(i*64+j*4)<<24) | (msg.charCodeAt(i*64+j*4+1)<<16) | 
                      (msg.charCodeAt(i*64+j*4+2)<<8) | (msg.charCodeAt(i*64+j*4+3));
        }
    }

    M[N-1][14] = ((msg.length-1)*8) / Math.pow(2, 32); M[N-1][14] = Math.floor(M[N-1][14])
    M[N-1][15] = ((msg.length-1)*8) & 0xffffffff;

    var H0 = 0x67452301;
    var H1 = 0xefcdab89;
    var H2 = 0x98badcfe;
    var H3 = 0x10325476;
    var H4 = 0xc3d2e1f0;

    var W = new Array(80); var a, b, c, d, e;
    for (var i=0; i<N; i++) {

        for (var t=0;  t<16; t++) W[t] = M[i][t];
        for (var t=16; t<80; t++) W[t] = ROTL(W[t-3] ^ W[t-8] ^ W[t-14] ^ W[t-16], 1);

        a = H0; b = H1; c = H2; d = H3; e = H4;

        for (var t=0; t<80; t++) {
            var s = Math.floor(t/20); 
            var T = (ROTL(a,5) + f(s,b,c,d) + e + K[s] + W[t]) & 0xffffffff;
            e = d;
            d = c;
            c = ROTL(b, 30);
            b = a;
            a = T;
        }

        H0 = (H0+a) & 0xffffffff;  
        H1 = (H1+b) & 0xffffffff; 
        H2 = (H2+c) & 0xffffffff; 
        H3 = (H3+d) & 0xffffffff; 
        H4 = (H4+e) & 0xffffffff;
    }

    return H0.toHexStr() + H1.toHexStr() + H2.toHexStr() + H3.toHexStr() + H4.toHexStr();
    
    function f(s, x, y, z) 
    {
        switch (s) {
        case 0: return (x & y) ^ (~x & z);           
        case 1: return x ^ y ^ z;                    
        case 2: return (x & y) ^ (x & z) ^ (y & z);  
        case 3: return x ^ y ^ z;                    
        }
    }

    function ROTL(x, n)
    {
        return (x<<n) | (x>>>(32-n));
    }
    
}

Number.prototype.toHexStr = function()
{
    var s="", v;
    for (var i=7; i>=0; i--) { v = (this>>>(i*4)) & 0xf; s += v.toString(16); }
    return s;
}

function UOBApplet(){
    
    var obmApplet;

    this.OBM_SpecifyRSAPublicKey = function(mod_siz, pub_String, mod_String){
        "mod_siz:nomunge, pub_String:nomunge, mod_String:nomunge"
        OBMApplet.PUBLIC_EXPONENT_STRING = pub_String;
        OBMApplet.MODULUS_STRING = mod_String;
        OBMApplet.RSA_MODULUS_SIZE_IN_BYTES = mod_siz;
        try{
          obmApplet = new OBMApplet();
        }catch(err){
            return err.code;
        }
        return UOBApplet.ERR_NO_ERROR;
    }
    
    this.OBM_EncryptPassword = function(pinString, rn_String){
        "pinString:nomunge, rn_String:nomunge"
        
        try{
          obmApplet.OBM_EncryptPassword(pinString, rn_String);
        }catch(err){
            return err.code;
        }
        return UOBApplet.ERR_NO_ERROR;
    }
    
    this.OBM_EncryptChangedPassword = function(oldPinString, newPinString, rn_String){
        "oldPinString:nomunge, newPinString:nomunge, rn_String:nomunge"
        
        try{
          obmApplet.OBM_EncryptPassword(oldPinString, newPinString, rn_String);
        }catch(err){
            
            return err.code;
        }
        return UOBApplet.ERR_NO_ERROR;
    }
    
    this.OBM_GetEncryptedPassword = function(){
        return obmApplet.OBM_GetEncryptedPassword();
    }

    this.OBM_GetEncodingParameter = function(){
        return obmApplet.OBM_GetEncodingParameter();
    }
}

UOBApplet.ERR_NO_ERROR = 0;

UOBApplet.INVALID_PIN_LENGTH = 10;

UOBApplet.ERR_INVALID_PIN = 11;

UOBApplet.ERR_INVALID_PIN_BLOCK = 20;

UOBApplet.ERR_INVALID_RANDOM_NUMBER_LENGTH = 21;

UOBApplet.ERR_INVALID_RANDOM_NUMBER = 22;

UOBApplet.ERR_OLD_NEW_PASSWORD_SAME = 23;

UOBApplet.ERR_INVALID_PIN_MESSAGE = 30;

UOBApplet.ERR_INVALID_PIN_MESSAGE_LENGTH = 31;

UOBApplet.ERR_INVALID_RSA_KEY_LENGTH = 41;

UOBApplet.ERR_INVALID_RSA_KEY = 42;

function Util(){}

Util.toHexString=function(byteArr){
    var str = "";
    for(var i=0; i<byteArr.length;i++){
        
        var ch;
        if(typeof byteArr[i] == "number"){
            ch = (byteArr[i]).toString(16);
        }else if(typeof byteArr[i] == "string"){
            ch = byteArr.charCodeAt(i).toString(16);
        }
        if(ch.length==1) ch = "0"+ch;
        str += ch;
    }
    return str;
}


Util.fromHexString=function(hexStr){
    hexStr = (hexStr.length%2 == 0) ? hexStr : "0"+hexStr;
    var len = hexStr.length / 2;
    var str = [];
    for (var i=0, j=0; i<len; i++,j++){
        var start = i*2;
        str[j] = parseInt("0x"+hexStr.substring(start,start+2));
    }
    return str;
}

Util.getByteArray=function(s){
    a = new Array();
    for (var i = 0 ; i < s.length; i++){
        a[i] = s.charCodeAt(i);
    }
    return a;
}


Util.cByteArrayToNString=function(byteArr){
    var x = "";
    for(var i=0;i<byteArr.length;i++){
        x+=String.fromCharCode(byteArr[i]);
    }
    return x;
}

