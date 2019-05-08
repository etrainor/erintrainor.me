window.localizedMessages = {
  "tower.pips.published.contact.requiredField": "This field is required.",
  "tower.pips.published.contact.invalidEmail": "Invalid Email Address",
  "tower.pips.published.contact.error": "There was an error. Please try",
  "tower.pips.published.contact.resubmit": "resubmitting your message.",
  "tower.pips.published.contact.tryAgain": "If the problem persists, please try again in 5 minutes.",
  "tower.pips.published.paypal.addToCart": "Add to Cart",
  "tower.pips.published.paypal.quantityLabel": "Qty",
  "tower.published.paypalCart.title": "Shopping Cart",
  "tower.published.paypalCart.close": "Close",
  "tower.published.paypalCart.empty": "Your Cart is Empty",
  "tower.published.paypalCart.total": "Total",
  "tower.published.paypalCart.checkout": "Proceed To Checkout",
  "tower.published.paypalCart.continueShopping": "Continue Shopping"
};

/*********/
(function() {

  // Copyright (c) 2005  Tom Wu
  // All Rights Reserved.
  // See "LICENSE" for details.

  // Basic JavaScript BN library - subset useful for RSA encryption.

  // Bits per digit
  var dbits;

  // JavaScript engine analysis
  var canary = 0xdeadbeefcafe;
  var j_lm = ((canary & 0xffffff) == 0xefcafe);

  // (public) Constructor
  function BigInteger(a, b, c) {
      if (a != null)
          if ("number" == typeof a) this.fromNumber(a, b, c);
          else if (b == null && "string" != typeof a) this.fromString(a, 256);
      else this.fromString(a, b);
  }

  // return new, unset BigInteger
  function nbi() {
      return new BigInteger(null);
  }

  // am: Compute w_j += (x*this_i), propagate carries,
  // c is initial carry, returns final carry.
  // c < 3*dvalue, x < 2*dvalue, this_i < dvalue
  // We need to select the fastest one that works in this environment.

  // am1: use a single mult and divide to get the high bits,
  // max digit bits should be 26 because
  // max internal value = 2*dvalue^2-2*dvalue (< 2^53)
  function am1(i, x, w, j, c, n) {
      while (--n >= 0) {
          var v = x * this[i++] + w[j] + c;
          c = Math.floor(v / 0x4000000);
          w[j++] = v & 0x3ffffff;
      }
      return c;
  }
  // am2 avoids a big mult-and-extract completely.
  // Max digit bits should be <= 30 because we do bitwise ops
  // on values up to 2*hdvalue^2-hdvalue-1 (< 2^31)
  function am2(i, x, w, j, c, n) {
      var xl = x & 0x7fff,
          xh = x >> 15;
      while (--n >= 0) {
          var l = this[i] & 0x7fff;
          var h = this[i++] >> 15;
          var m = xh * l + h * xl;
          l = xl * l + ((m & 0x7fff) << 15) + w[j] + (c & 0x3fffffff);
          c = (l >>> 30) + (m >>> 15) + xh * h + (c >>> 30);
          w[j++] = l & 0x3fffffff;
      }
      return c;
  }
  // Alternately, set max digit bits to 28 since some
  // browsers slow down when dealing with 32-bit numbers.
  function am3(i, x, w, j, c, n) {
      var xl = x & 0x3fff,
          xh = x >> 14;
      while (--n >= 0) {
          var l = this[i] & 0x3fff;
          var h = this[i++] >> 14;
          var m = xh * l + h * xl;
          l = xl * l + ((m & 0x3fff) << 14) + w[j] + c;
          c = (l >> 28) + (m >> 14) + xh * h;
          w[j++] = l & 0xfffffff;
      }
      return c;
  }
  var inBrowser = typeof navigator !== "undefined";
  if (inBrowser && j_lm && (navigator.appName == "Microsoft Internet Explorer")) {
      BigInteger.prototype.am = am2;
      dbits = 30;
  } else if (inBrowser && j_lm && (navigator.appName != "Netscape")) {
      BigInteger.prototype.am = am1;
      dbits = 26;
  } else { // Mozilla/Netscape seems to prefer am3
      BigInteger.prototype.am = am3;
      dbits = 28;
  }

  BigInteger.prototype.DB = dbits;
  BigInteger.prototype.DM = ((1 << dbits) - 1);
  BigInteger.prototype.DV = (1 << dbits);

  var BI_FP = 52;
  BigInteger.prototype.FV = Math.pow(2, BI_FP);
  BigInteger.prototype.F1 = BI_FP - dbits;
  BigInteger.prototype.F2 = 2 * dbits - BI_FP;

  // Digit conversions
  var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
  var BI_RC = new Array();
  var rr, vv;
  rr = "0".charCodeAt(0);
  for (vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
  rr = "a".charCodeAt(0);
  for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
  rr = "A".charCodeAt(0);
  for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;

  function int2char(n) {
      return BI_RM.charAt(n);
  }

  function intAt(s, i) {
      var c = BI_RC[s.charCodeAt(i)];
      return (c == null) ? -1 : c;
  }

  // (protected) copy this to r
  function bnpCopyTo(r) {
      for (var i = this.t - 1; i >= 0; --i) r[i] = this[i];
      r.t = this.t;
      r.s = this.s;
  }

  // (protected) set from integer value x, -DV <= x < DV
  function bnpFromInt(x) {
      this.t = 1;
      this.s = (x < 0) ? -1 : 0;
      if (x > 0) this[0] = x;
      else if (x < -1) this[0] = x + this.DV;
      else this.t = 0;
  }

  // return bigint initialized to value
  function nbv(i) {
      var r = nbi();
      r.fromInt(i);
      return r;
  }

  // (protected) set from string and radix
  function bnpFromString(s, b) {
      var k;
      if (b == 16) k = 4;
      else if (b == 8) k = 3;
      else if (b == 256) k = 8; // byte array
      else if (b == 2) k = 1;
      else if (b == 32) k = 5;
      else if (b == 4) k = 2;
      else {
          this.fromRadix(s, b);
          return;
      }
      this.t = 0;
      this.s = 0;
      var i = s.length,
          mi = false,
          sh = 0;
      while (--i >= 0) {
          var x = (k == 8) ? s[i] & 0xff : intAt(s, i);
          if (x < 0) {
              if (s.charAt(i) == "-") mi = true;
              continue;
          }
          mi = false;
          if (sh == 0)
              this[this.t++] = x;
          else if (sh + k > this.DB) {
              this[this.t - 1] |= (x & ((1 << (this.DB - sh)) - 1)) << sh;
              this[this.t++] = (x >> (this.DB - sh));
          } else
              this[this.t - 1] |= x << sh;
          sh += k;
          if (sh >= this.DB) sh -= this.DB;
      }
      if (k == 8 && (s[0] & 0x80) != 0) {
          this.s = -1;
          if (sh > 0) this[this.t - 1] |= ((1 << (this.DB - sh)) - 1) << sh;
      }
      this.clamp();
      if (mi) BigInteger.ZERO.subTo(this, this);
  }

  // (protected) clamp off excess high words
  function bnpClamp() {
      var c = this.s & this.DM;
      while (this.t > 0 && this[this.t - 1] == c) --this.t;
  }

  // (public) return string representation in given radix
  function bnToString(b) {
      if (this.s < 0) return "-" + this.negate().toString(b);
      var k;
      if (b == 16) k = 4;
      else if (b == 8) k = 3;
      else if (b == 2) k = 1;
      else if (b == 32) k = 5;
      else if (b == 4) k = 2;
      else return this.toRadix(b);
      var km = (1 << k) - 1,
          d, m = false,
          r = "",
          i = this.t;
      var p = this.DB - (i * this.DB) % k;
      if (i-- > 0) {
          if (p < this.DB && (d = this[i] >> p) > 0) {
              m = true;
              r = int2char(d);
          }
          while (i >= 0) {
              if (p < k) {
                  d = (this[i] & ((1 << p) - 1)) << (k - p);
                  d |= this[--i] >> (p += this.DB - k);
              } else {
                  d = (this[i] >> (p -= k)) & km;
                  if (p <= 0) {
                      p += this.DB;
                      --i;
                  }
              }
              if (d > 0) m = true;
              if (m) r += int2char(d);
          }
      }
      return m ? r : "0";
  }

  // (public) -this
  function bnNegate() {
      var r = nbi();
      BigInteger.ZERO.subTo(this, r);
      return r;
  }

  // (public) |this|
  function bnAbs() {
      return (this.s < 0) ? this.negate() : this;
  }

  // (public) return + if this > a, - if this < a, 0 if equal
  function bnCompareTo(a) {
      var r = this.s - a.s;
      if (r != 0) return r;
      var i = this.t;
      r = i - a.t;
      if (r != 0) return (this.s < 0) ? -r : r;
      while (--i >= 0)
          if ((r = this[i] - a[i]) != 0) return r;
      return 0;
  }

  // returns bit length of the integer x
  function nbits(x) {
      var r = 1,
          t;
      if ((t = x >>> 16) != 0) {
          x = t;
          r += 16;
      }
      if ((t = x >> 8) != 0) {
          x = t;
          r += 8;
      }
      if ((t = x >> 4) != 0) {
          x = t;
          r += 4;
      }
      if ((t = x >> 2) != 0) {
          x = t;
          r += 2;
      }
      if ((t = x >> 1) != 0) {
          x = t;
          r += 1;
      }
      return r;
  }

  // (public) return the number of bits in "this"
  function bnBitLength() {
      if (this.t <= 0) return 0;
      return this.DB * (this.t - 1) + nbits(this[this.t - 1] ^ (this.s & this.DM));
  }

  // (protected) r = this << n*DB
  function bnpDLShiftTo(n, r) {
      var i;
      for (i = this.t - 1; i >= 0; --i) r[i + n] = this[i];
      for (i = n - 1; i >= 0; --i) r[i] = 0;
      r.t = this.t + n;
      r.s = this.s;
  }

  // (protected) r = this >> n*DB
  function bnpDRShiftTo(n, r) {
      for (var i = n; i < this.t; ++i) r[i - n] = this[i];
      r.t = Math.max(this.t - n, 0);
      r.s = this.s;
  }

  // (protected) r = this << n
  function bnpLShiftTo(n, r) {
      var bs = n % this.DB;
      var cbs = this.DB - bs;
      var bm = (1 << cbs) - 1;
      var ds = Math.floor(n / this.DB),
          c = (this.s << bs) & this.DM,
          i;
      for (i = this.t - 1; i >= 0; --i) {
          r[i + ds + 1] = (this[i] >> cbs) | c;
          c = (this[i] & bm) << bs;
      }
      for (i = ds - 1; i >= 0; --i) r[i] = 0;
      r[ds] = c;
      r.t = this.t + ds + 1;
      r.s = this.s;
      r.clamp();
  }

  // (protected) r = this >> n
  function bnpRShiftTo(n, r) {
      r.s = this.s;
      var ds = Math.floor(n / this.DB);
      if (ds >= this.t) {
          r.t = 0;
          return;
      }
      var bs = n % this.DB;
      var cbs = this.DB - bs;
      var bm = (1 << bs) - 1;
      r[0] = this[ds] >> bs;
      for (var i = ds + 1; i < this.t; ++i) {
          r[i - ds - 1] |= (this[i] & bm) << cbs;
          r[i - ds] = this[i] >> bs;
      }
      if (bs > 0) r[this.t - ds - 1] |= (this.s & bm) << cbs;
      r.t = this.t - ds;
      r.clamp();
  }

  // (protected) r = this - a
  function bnpSubTo(a, r) {
      var i = 0,
          c = 0,
          m = Math.min(a.t, this.t);
      while (i < m) {
          c += this[i] - a[i];
          r[i++] = c & this.DM;
          c >>= this.DB;
      }
      if (a.t < this.t) {
          c -= a.s;
          while (i < this.t) {
              c += this[i];
              r[i++] = c & this.DM;
              c >>= this.DB;
          }
          c += this.s;
      } else {
          c += this.s;
          while (i < a.t) {
              c -= a[i];
              r[i++] = c & this.DM;
              c >>= this.DB;
          }
          c -= a.s;
      }
      r.s = (c < 0) ? -1 : 0;
      if (c < -1) r[i++] = this.DV + c;
      else if (c > 0) r[i++] = c;
      r.t = i;
      r.clamp();
  }

  // (protected) r = this * a, r != this,a (HAC 14.12)
  // "this" should be the larger one if appropriate.
  function bnpMultiplyTo(a, r) {
      var x = this.abs(),
          y = a.abs();
      var i = x.t;
      r.t = i + y.t;
      while (--i >= 0) r[i] = 0;
      for (i = 0; i < y.t; ++i) r[i + x.t] = x.am(0, y[i], r, i, 0, x.t);
      r.s = 0;
      r.clamp();
      if (this.s != a.s) BigInteger.ZERO.subTo(r, r);
  }

  // (protected) r = this^2, r != this (HAC 14.16)
  function bnpSquareTo(r) {
      var x = this.abs();
      var i = r.t = 2 * x.t;
      while (--i >= 0) r[i] = 0;
      for (i = 0; i < x.t - 1; ++i) {
          var c = x.am(i, x[i], r, 2 * i, 0, 1);
          if ((r[i + x.t] += x.am(i + 1, 2 * x[i], r, 2 * i + 1, c, x.t - i - 1)) >= x.DV) {
              r[i + x.t] -= x.DV;
              r[i + x.t + 1] = 1;
          }
      }
      if (r.t > 0) r[r.t - 1] += x.am(i, x[i], r, 2 * i, 0, 1);
      r.s = 0;
      r.clamp();
  }

  // (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
  // r != q, this != m.  q or r may be null.
  function bnpDivRemTo(m, q, r) {
      var pm = m.abs();
      if (pm.t <= 0) return;
      var pt = this.abs();
      if (pt.t < pm.t) {
          if (q != null) q.fromInt(0);
          if (r != null) this.copyTo(r);
          return;
      }
      if (r == null) r = nbi();
      var y = nbi(),
          ts = this.s,
          ms = m.s;
      var nsh = this.DB - nbits(pm[pm.t - 1]); // normalize modulus
      if (nsh > 0) {
          pm.lShiftTo(nsh, y);
          pt.lShiftTo(nsh, r);
      } else {
          pm.copyTo(y);
          pt.copyTo(r);
      }
      var ys = y.t;
      var y0 = y[ys - 1];
      if (y0 == 0) return;
      var yt = y0 * (1 << this.F1) + ((ys > 1) ? y[ys - 2] >> this.F2 : 0);
      var d1 = this.FV / yt,
          d2 = (1 << this.F1) / yt,
          e = 1 << this.F2;
      var i = r.t,
          j = i - ys,
          t = (q == null) ? nbi() : q;
      y.dlShiftTo(j, t);
      if (r.compareTo(t) >= 0) {
          r[r.t++] = 1;
          r.subTo(t, r);
      }
      BigInteger.ONE.dlShiftTo(ys, t);
      t.subTo(y, y); // "negative" y so we can replace sub with am later
      while (y.t < ys) y[y.t++] = 0;
      while (--j >= 0) {
          // Estimate quotient digit
          var qd = (r[--i] == y0) ? this.DM : Math.floor(r[i] * d1 + (r[i - 1] + e) * d2);
          if ((r[i] += y.am(0, qd, r, j, 0, ys)) < qd) { // Try it out
              y.dlShiftTo(j, t);
              r.subTo(t, r);
              while (r[i] < --qd) r.subTo(t, r);
          }
      }
      if (q != null) {
          r.drShiftTo(ys, q);
          if (ts != ms) BigInteger.ZERO.subTo(q, q);
      }
      r.t = ys;
      r.clamp();
      if (nsh > 0) r.rShiftTo(nsh, r); // Denormalize remainder
      if (ts < 0) BigInteger.ZERO.subTo(r, r);
  }

  // (public) this mod a
  function bnMod(a) {
      var r = nbi();
      this.abs().divRemTo(a, null, r);
      if (this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r, r);
      return r;
  }

  // Modular reduction using "classic" algorithm
  function Classic(m) {
      this.m = m;
  }

  function cConvert(x) {
      if (x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
      else return x;
  }

  function cRevert(x) {
      return x;
  }

  function cReduce(x) {
      x.divRemTo(this.m, null, x);
  }

  function cMulTo(x, y, r) {
      x.multiplyTo(y, r);
      this.reduce(r);
  }

  function cSqrTo(x, r) {
      x.squareTo(r);
      this.reduce(r);
  }

  Classic.prototype.convert = cConvert;
  Classic.prototype.revert = cRevert;
  Classic.prototype.reduce = cReduce;
  Classic.prototype.mulTo = cMulTo;
  Classic.prototype.sqrTo = cSqrTo;

  // (protected) return "-1/this % 2^DB"; useful for Mont. reduction
  // justification:
  //         xy == 1 (mod m)
  //         xy =  1+km
  //   xy(2-xy) = (1+km)(1-km)
  // x[y(2-xy)] = 1-k^2m^2
  // x[y(2-xy)] == 1 (mod m^2)
  // if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
  // should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
  // JS multiply "overflows" differently from C/C++, so care is needed here.
  function bnpInvDigit() {
      if (this.t < 1) return 0;
      var x = this[0];
      if ((x & 1) == 0) return 0;
      var y = x & 3; // y == 1/x mod 2^2
      y = (y * (2 - (x & 0xf) * y)) & 0xf; // y == 1/x mod 2^4
      y = (y * (2 - (x & 0xff) * y)) & 0xff; // y == 1/x mod 2^8
      y = (y * (2 - (((x & 0xffff) * y) & 0xffff))) & 0xffff; // y == 1/x mod 2^16
      // last step - calculate inverse mod DV directly;
      // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
      y = (y * (2 - x * y % this.DV)) % this.DV; // y == 1/x mod 2^dbits
      // we really want the negative inverse, and -DV < y < DV
      return (y > 0) ? this.DV - y : -y;
  }

  // Montgomery reduction
  function Montgomery(m) {
      this.m = m;
      this.mp = m.invDigit();
      this.mpl = this.mp & 0x7fff;
      this.mph = this.mp >> 15;
      this.um = (1 << (m.DB - 15)) - 1;
      this.mt2 = 2 * m.t;
  }

  // xR mod m
  function montConvert(x) {
      var r = nbi();
      x.abs().dlShiftTo(this.m.t, r);
      r.divRemTo(this.m, null, r);
      if (x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r, r);
      return r;
  }

  // x/R mod m
  function montRevert(x) {
      var r = nbi();
      x.copyTo(r);
      this.reduce(r);
      return r;
  }

  // x = x/R mod m (HAC 14.32)
  function montReduce(x) {
      while (x.t <= this.mt2) // pad x so am has enough room later
          x[x.t++] = 0;
      for (var i = 0; i < this.m.t; ++i) {
          // faster way of calculating u0 = x[i]*mp mod DV
          var j = x[i] & 0x7fff;
          var u0 = (j * this.mpl + (((j * this.mph + (x[i] >> 15) * this.mpl) & this.um) << 15)) & x.DM;
          // use am to combine the multiply-shift-add into one call
          j = i + this.m.t;
          x[j] += this.m.am(0, u0, x, i, 0, this.m.t);
          // propagate carry
          while (x[j] >= x.DV) {
              x[j] -= x.DV;
              x[++j]++;
          }
      }
      x.clamp();
      x.drShiftTo(this.m.t, x);
      if (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
  }

  // r = "x^2/R mod m"; x != r
  function montSqrTo(x, r) {
      x.squareTo(r);
      this.reduce(r);
  }

  // r = "xy/R mod m"; x,y != r
  function montMulTo(x, y, r) {
      x.multiplyTo(y, r);
      this.reduce(r);
  }

  Montgomery.prototype.convert = montConvert;
  Montgomery.prototype.revert = montRevert;
  Montgomery.prototype.reduce = montReduce;
  Montgomery.prototype.mulTo = montMulTo;
  Montgomery.prototype.sqrTo = montSqrTo;

  // (protected) true iff this is even
  function bnpIsEven() {
      return ((this.t > 0) ? (this[0] & 1) : this.s) == 0;
  }

  // (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)
  function bnpExp(e, z) {
      if (e > 0xffffffff || e < 1) return BigInteger.ONE;
      var r = nbi(),
          r2 = nbi(),
          g = z.convert(this),
          i = nbits(e) - 1;
      g.copyTo(r);
      while (--i >= 0) {
          z.sqrTo(r, r2);
          if ((e & (1 << i)) > 0) z.mulTo(r2, g, r);
          else {
              var t = r;
              r = r2;
              r2 = t;
          }
      }
      return z.revert(r);
  }

  // (public) this^e % m, 0 <= e < 2^32
  function bnModPowInt(e, m) {
      var z;
      if (e < 256 || m.isEven()) z = new Classic(m);
      else z = new Montgomery(m);
      return this.exp(e, z);
  }

  // protected
  BigInteger.prototype.copyTo = bnpCopyTo;
  BigInteger.prototype.fromInt = bnpFromInt;
  BigInteger.prototype.fromString = bnpFromString;
  BigInteger.prototype.clamp = bnpClamp;
  BigInteger.prototype.dlShiftTo = bnpDLShiftTo;
  BigInteger.prototype.drShiftTo = bnpDRShiftTo;
  BigInteger.prototype.lShiftTo = bnpLShiftTo;
  BigInteger.prototype.rShiftTo = bnpRShiftTo;
  BigInteger.prototype.subTo = bnpSubTo;
  BigInteger.prototype.multiplyTo = bnpMultiplyTo;
  BigInteger.prototype.squareTo = bnpSquareTo;
  BigInteger.prototype.divRemTo = bnpDivRemTo;
  BigInteger.prototype.invDigit = bnpInvDigit;
  BigInteger.prototype.isEven = bnpIsEven;
  BigInteger.prototype.exp = bnpExp;

  // public
  BigInteger.prototype.toString = bnToString;
  BigInteger.prototype.negate = bnNegate;
  BigInteger.prototype.abs = bnAbs;
  BigInteger.prototype.compareTo = bnCompareTo;
  BigInteger.prototype.bitLength = bnBitLength;
  BigInteger.prototype.mod = bnMod;
  BigInteger.prototype.modPowInt = bnModPowInt;

  // "constants"
  BigInteger.ZERO = nbv(0);
  BigInteger.ONE = nbv(1);

  // Copyright (c) 2005-2009  Tom Wu
  // All Rights Reserved.
  // See "LICENSE" for details.

  // Extended JavaScript BN functions, required for RSA private ops.

  // Version 1.1: new BigInteger("0", 10) returns "proper" zero
  // Version 1.2: square() API, isProbablePrime fix

  // (public)
  function bnClone() {
      var r = nbi();
      this.copyTo(r);
      return r;
  }

  // (public) return value as integer
  function bnIntValue() {
      if (this.s < 0) {
          if (this.t == 1) return this[0] - this.DV;
          else if (this.t == 0) return -1;
      } else if (this.t == 1) return this[0];
      else if (this.t == 0) return 0;
      // assumes 16 < DB < 32
      return ((this[1] & ((1 << (32 - this.DB)) - 1)) << this.DB) | this[0];
  }

  // (public) return value as byte
  function bnByteValue() {
      return (this.t == 0) ? this.s : (this[0] << 24) >> 24;
  }

  // (public) return value as short (assumes DB>=16)
  function bnShortValue() {
      return (this.t == 0) ? this.s : (this[0] << 16) >> 16;
  }

  // (protected) return x s.t. r^x < DV
  function bnpChunkSize(r) {
      return Math.floor(Math.LN2 * this.DB / Math.log(r));
  }

  // (public) 0 if this == 0, 1 if this > 0
  function bnSigNum() {
      if (this.s < 0) return -1;
      else if (this.t <= 0 || (this.t == 1 && this[0] <= 0)) return 0;
      else return 1;
  }

  // (protected) convert to radix string
  function bnpToRadix(b) {
      if (b == null) b = 10;
      if (this.signum() == 0 || b < 2 || b > 36) return "0";
      var cs = this.chunkSize(b);
      var a = Math.pow(b, cs);
      var d = nbv(a),
          y = nbi(),
          z = nbi(),
          r = "";
      this.divRemTo(d, y, z);
      while (y.signum() > 0) {
          r = (a + z.intValue()).toString(b).substr(1) + r;
          y.divRemTo(d, y, z);
      }
      return z.intValue().toString(b) + r;
  }

  // (protected) convert from radix string
  function bnpFromRadix(s, b) {
      this.fromInt(0);
      if (b == null) b = 10;
      var cs = this.chunkSize(b);
      var d = Math.pow(b, cs),
          mi = false,
          j = 0,
          w = 0;
      for (var i = 0; i < s.length; ++i) {
          var x = intAt(s, i);
          if (x < 0) {
              if (s.charAt(i) == "-" && this.signum() == 0) mi = true;
              continue;
          }
          w = b * w + x;
          if (++j >= cs) {
              this.dMultiply(d);
              this.dAddOffset(w, 0);
              j = 0;
              w = 0;
          }
      }
      if (j > 0) {
          this.dMultiply(Math.pow(b, j));
          this.dAddOffset(w, 0);
      }
      if (mi) BigInteger.ZERO.subTo(this, this);
  }

  // (protected) alternate constructor
  function bnpFromNumber(a, b, c) {
      if ("number" == typeof b) {
          // new BigInteger(int,int,RNG)
          if (a < 2) this.fromInt(1);
          else {
              this.fromNumber(a, c);
              if (!this.testBit(a - 1)) // force MSB set
                  this.bitwiseTo(BigInteger.ONE.shiftLeft(a - 1), op_or, this);
              if (this.isEven()) this.dAddOffset(1, 0); // force odd
              while (!this.isProbablePrime(b)) {
                  this.dAddOffset(2, 0);
                  if (this.bitLength() > a) this.subTo(BigInteger.ONE.shiftLeft(a - 1), this);
              }
          }
      } else {
          // new BigInteger(int,RNG)
          var x = new Array(),
              t = a & 7;
          x.length = (a >> 3) + 1;
          b.nextBytes(x);
          if (t > 0) x[0] &= ((1 << t) - 1);
          else x[0] = 0;
          this.fromString(x, 256);
      }
  }

  // (public) convert to bigendian byte array
  function bnToByteArray() {
      var i = this.t,
          r = new Array();
      r[0] = this.s;
      var p = this.DB - (i * this.DB) % 8,
          d, k = 0;
      if (i-- > 0) {
          if (p < this.DB && (d = this[i] >> p) != (this.s & this.DM) >> p)
              r[k++] = d | (this.s << (this.DB - p));
          while (i >= 0) {
              if (p < 8) {
                  d = (this[i] & ((1 << p) - 1)) << (8 - p);
                  d |= this[--i] >> (p += this.DB - 8);
              } else {
                  d = (this[i] >> (p -= 8)) & 0xff;
                  if (p <= 0) {
                      p += this.DB;
                      --i;
                  }
              }
              if ((d & 0x80) != 0) d |= -256;
              if (k == 0 && (this.s & 0x80) != (d & 0x80)) ++k;
              if (k > 0 || d != this.s) r[k++] = d;
          }
      }
      return r;
  }

  function bnEquals(a) {
      return (this.compareTo(a) == 0);
  }

  function bnMin(a) {
      return (this.compareTo(a) < 0) ? this : a;
  }

  function bnMax(a) {
      return (this.compareTo(a) > 0) ? this : a;
  }

  // (protected) r = this op a (bitwise)
  function bnpBitwiseTo(a, op, r) {
      var i, f, m = Math.min(a.t, this.t);
      for (i = 0; i < m; ++i) r[i] = op(this[i], a[i]);
      if (a.t < this.t) {
          f = a.s & this.DM;
          for (i = m; i < this.t; ++i) r[i] = op(this[i], f);
          r.t = this.t;
      } else {
          f = this.s & this.DM;
          for (i = m; i < a.t; ++i) r[i] = op(f, a[i]);
          r.t = a.t;
      }
      r.s = op(this.s, a.s);
      r.clamp();
  }

  // (public) this & a
  function op_and(x, y) {
      return x & y;
  }

  function bnAnd(a) {
      var r = nbi();
      this.bitwiseTo(a, op_and, r);
      return r;
  }

  // (public) this | a
  function op_or(x, y) {
      return x | y;
  }

  function bnOr(a) {
      var r = nbi();
      this.bitwiseTo(a, op_or, r);
      return r;
  }

  // (public) this ^ a
  function op_xor(x, y) {
      return x ^ y;
  }

  function bnXor(a) {
      var r = nbi();
      this.bitwiseTo(a, op_xor, r);
      return r;
  }

  // (public) this & ~a
  function op_andnot(x, y) {
      return x & ~y;
  }

  function bnAndNot(a) {
      var r = nbi();
      this.bitwiseTo(a, op_andnot, r);
      return r;
  }

  // (public) ~this
  function bnNot() {
      var r = nbi();
      for (var i = 0; i < this.t; ++i) r[i] = this.DM & ~this[i];
      r.t = this.t;
      r.s = ~this.s;
      return r;
  }

  // (public) this << n
  function bnShiftLeft(n) {
      var r = nbi();
      if (n < 0) this.rShiftTo(-n, r);
      else this.lShiftTo(n, r);
      return r;
  }

  // (public) this >> n
  function bnShiftRight(n) {
      var r = nbi();
      if (n < 0) this.lShiftTo(-n, r);
      else this.rShiftTo(n, r);
      return r;
  }

  // return index of lowest 1-bit in x, x < 2^31
  function lbit(x) {
      if (x == 0) return -1;
      var r = 0;
      if ((x & 0xffff) == 0) {
          x >>= 16;
          r += 16;
      }
      if ((x & 0xff) == 0) {
          x >>= 8;
          r += 8;
      }
      if ((x & 0xf) == 0) {
          x >>= 4;
          r += 4;
      }
      if ((x & 3) == 0) {
          x >>= 2;
          r += 2;
      }
      if ((x & 1) == 0) ++r;
      return r;
  }

  // (public) returns index of lowest 1-bit (or -1 if none)
  function bnGetLowestSetBit() {
      for (var i = 0; i < this.t; ++i)
          if (this[i] != 0) return i * this.DB + lbit(this[i]);
      if (this.s < 0) return this.t * this.DB;
      return -1;
  }

  // return number of 1 bits in x
  function cbit(x) {
      var r = 0;
      while (x != 0) {
          x &= x - 1;
          ++r;
      }
      return r;
  }

  // (public) return number of set bits
  function bnBitCount() {
      var r = 0,
          x = this.s & this.DM;
      for (var i = 0; i < this.t; ++i) r += cbit(this[i] ^ x);
      return r;
  }

  // (public) true iff nth bit is set
  function bnTestBit(n) {
      var j = Math.floor(n / this.DB);
      if (j >= this.t) return (this.s != 0);
      return ((this[j] & (1 << (n % this.DB))) != 0);
  }

  // (protected) this op (1<<n)
  function bnpChangeBit(n, op) {
      var r = BigInteger.ONE.shiftLeft(n);
      this.bitwiseTo(r, op, r);
      return r;
  }

  // (public) this | (1<<n)
  function bnSetBit(n) {
      return this.changeBit(n, op_or);
  }

  // (public) this & ~(1<<n)
  function bnClearBit(n) {
      return this.changeBit(n, op_andnot);
  }

  // (public) this ^ (1<<n)
  function bnFlipBit(n) {
      return this.changeBit(n, op_xor);
  }

  // (protected) r = this + a
  function bnpAddTo(a, r) {
      var i = 0,
          c = 0,
          m = Math.min(a.t, this.t);
      while (i < m) {
          c += this[i] + a[i];
          r[i++] = c & this.DM;
          c >>= this.DB;
      }
      if (a.t < this.t) {
          c += a.s;
          while (i < this.t) {
              c += this[i];
              r[i++] = c & this.DM;
              c >>= this.DB;
          }
          c += this.s;
      } else {
          c += this.s;
          while (i < a.t) {
              c += a[i];
              r[i++] = c & this.DM;
              c >>= this.DB;
          }
          c += a.s;
      }
      r.s = (c < 0) ? -1 : 0;
      if (c > 0) r[i++] = c;
      else if (c < -1) r[i++] = this.DV + c;
      r.t = i;
      r.clamp();
  }

  // (public) this + a
  function bnAdd(a) {
      var r = nbi();
      this.addTo(a, r);
      return r;
  }

  // (public) this - a
  function bnSubtract(a) {
      var r = nbi();
      this.subTo(a, r);
      return r;
  }

  // (public) this * a
  function bnMultiply(a) {
      var r = nbi();
      this.multiplyTo(a, r);
      return r;
  }

  // (public) this^2
  function bnSquare() {
      var r = nbi();
      this.squareTo(r);
      return r;
  }

  // (public) this / a
  function bnDivide(a) {
      var r = nbi();
      this.divRemTo(a, r, null);
      return r;
  }

  // (public) this % a
  function bnRemainder(a) {
      var r = nbi();
      this.divRemTo(a, null, r);
      return r;
  }

  // (public) [this/a,this%a]
  function bnDivideAndRemainder(a) {
      var q = nbi(),
          r = nbi();
      this.divRemTo(a, q, r);
      return new Array(q, r);
  }

  // (protected) this *= n, this >= 0, 1 < n < DV
  function bnpDMultiply(n) {
      this[this.t] = this.am(0, n - 1, this, 0, 0, this.t);
      ++this.t;
      this.clamp();
  }

  // (protected) this += n << w words, this >= 0
  function bnpDAddOffset(n, w) {
      if (n == 0) return;
      while (this.t <= w) this[this.t++] = 0;
      this[w] += n;
      while (this[w] >= this.DV) {
          this[w] -= this.DV;
          if (++w >= this.t) this[this.t++] = 0;
          ++this[w];
      }
  }

  // A "null" reducer
  function NullExp() {}

  function nNop(x) {
      return x;
  }

  function nMulTo(x, y, r) {
      x.multiplyTo(y, r);
  }

  function nSqrTo(x, r) {
      x.squareTo(r);
  }

  NullExp.prototype.convert = nNop;
  NullExp.prototype.revert = nNop;
  NullExp.prototype.mulTo = nMulTo;
  NullExp.prototype.sqrTo = nSqrTo;

  // (public) this^e
  function bnPow(e) {
      return this.exp(e, new NullExp());
  }

  // (protected) r = lower n words of "this * a", a.t <= n
  // "this" should be the larger one if appropriate.
  function bnpMultiplyLowerTo(a, n, r) {
      var i = Math.min(this.t + a.t, n);
      r.s = 0; // assumes a,this >= 0
      r.t = i;
      while (i > 0) r[--i] = 0;
      var j;
      for (j = r.t - this.t; i < j; ++i) r[i + this.t] = this.am(0, a[i], r, i, 0, this.t);
      for (j = Math.min(a.t, n); i < j; ++i) this.am(0, a[i], r, i, 0, n - i);
      r.clamp();
  }

  // (protected) r = "this * a" without lower n words, n > 0
  // "this" should be the larger one if appropriate.
  function bnpMultiplyUpperTo(a, n, r) {
      --n;
      var i = r.t = this.t + a.t - n;
      r.s = 0; // assumes a,this >= 0
      while (--i >= 0) r[i] = 0;
      for (i = Math.max(n - this.t, 0); i < a.t; ++i)
          r[this.t + i - n] = this.am(n - i, a[i], r, 0, 0, this.t + i - n);
      r.clamp();
      r.drShiftTo(1, r);
  }

  // Barrett modular reduction
  function Barrett(m) {
      // setup Barrett
      this.r2 = nbi();
      this.q3 = nbi();
      BigInteger.ONE.dlShiftTo(2 * m.t, this.r2);
      this.mu = this.r2.divide(m);
      this.m = m;
  }

  function barrettConvert(x) {
      if (x.s < 0 || x.t > 2 * this.m.t) return x.mod(this.m);
      else if (x.compareTo(this.m) < 0) return x;
      else {
          var r = nbi();
          x.copyTo(r);
          this.reduce(r);
          return r;
      }
  }

  function barrettRevert(x) {
      return x;
  }

  // x = x mod m (HAC 14.42)
  function barrettReduce(x) {
      x.drShiftTo(this.m.t - 1, this.r2);
      if (x.t > this.m.t + 1) {
          x.t = this.m.t + 1;
          x.clamp();
      }
      this.mu.multiplyUpperTo(this.r2, this.m.t + 1, this.q3);
      this.m.multiplyLowerTo(this.q3, this.m.t + 1, this.r2);
      while (x.compareTo(this.r2) < 0) x.dAddOffset(1, this.m.t + 1);
      x.subTo(this.r2, x);
      while (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
  }

  // r = x^2 mod m; x != r
  function barrettSqrTo(x, r) {
      x.squareTo(r);
      this.reduce(r);
  }

  // r = x*y mod m; x,y != r
  function barrettMulTo(x, y, r) {
      x.multiplyTo(y, r);
      this.reduce(r);
  }

  Barrett.prototype.convert = barrettConvert;
  Barrett.prototype.revert = barrettRevert;
  Barrett.prototype.reduce = barrettReduce;
  Barrett.prototype.mulTo = barrettMulTo;
  Barrett.prototype.sqrTo = barrettSqrTo;

  // (public) this^e % m (HAC 14.85)
  function bnModPow(e, m) {
      var i = e.bitLength(),
          k, r = nbv(1),
          z;
      if (i <= 0) return r;
      else if (i < 18) k = 1;
      else if (i < 48) k = 3;
      else if (i < 144) k = 4;
      else if (i < 768) k = 5;
      else k = 6;
      if (i < 8)
          z = new Classic(m);
      else if (m.isEven())
          z = new Barrett(m);
      else
          z = new Montgomery(m);

      // precomputation
      var g = new Array(),
          n = 3,
          k1 = k - 1,
          km = (1 << k) - 1;
      g[1] = z.convert(this);
      if (k > 1) {
          var g2 = nbi();
          z.sqrTo(g[1], g2);
          while (n <= km) {
              g[n] = nbi();
              z.mulTo(g2, g[n - 2], g[n]);
              n += 2;
          }
      }

      var j = e.t - 1,
          w, is1 = true,
          r2 = nbi(),
          t;
      i = nbits(e[j]) - 1;
      while (j >= 0) {
          if (i >= k1) w = (e[j] >> (i - k1)) & km;
          else {
              w = (e[j] & ((1 << (i + 1)) - 1)) << (k1 - i);
              if (j > 0) w |= e[j - 1] >> (this.DB + i - k1);
          }

          n = k;
          while ((w & 1) == 0) {
              w >>= 1;
              --n;
          }
          if ((i -= n) < 0) {
              i += this.DB;
              --j;
          }
          if (is1) { // ret == 1, don't bother squaring or multiplying it
              g[w].copyTo(r);
              is1 = false;
          } else {
              while (n > 1) {
                  z.sqrTo(r, r2);
                  z.sqrTo(r2, r);
                  n -= 2;
              }
              if (n > 0) z.sqrTo(r, r2);
              else {
                  t = r;
                  r = r2;
                  r2 = t;
              }
              z.mulTo(r2, g[w], r);
          }

          while (j >= 0 && (e[j] & (1 << i)) == 0) {
              z.sqrTo(r, r2);
              t = r;
              r = r2;
              r2 = t;
              if (--i < 0) {
                  i = this.DB - 1;
                  --j;
              }
          }
      }
      return z.revert(r);
  }

  // (public) gcd(this,a) (HAC 14.54)
  function bnGCD(a) {
      var x = (this.s < 0) ? this.negate() : this.clone();
      var y = (a.s < 0) ? a.negate() : a.clone();
      if (x.compareTo(y) < 0) {
          var t = x;
          x = y;
          y = t;
      }
      var i = x.getLowestSetBit(),
          g = y.getLowestSetBit();
      if (g < 0) return x;
      if (i < g) g = i;
      if (g > 0) {
          x.rShiftTo(g, x);
          y.rShiftTo(g, y);
      }
      while (x.signum() > 0) {
          if ((i = x.getLowestSetBit()) > 0) x.rShiftTo(i, x);
          if ((i = y.getLowestSetBit()) > 0) y.rShiftTo(i, y);
          if (x.compareTo(y) >= 0) {
              x.subTo(y, x);
              x.rShiftTo(1, x);
          } else {
              y.subTo(x, y);
              y.rShiftTo(1, y);
          }
      }
      if (g > 0) y.lShiftTo(g, y);
      return y;
  }

  // (protected) this % n, n < 2^26
  function bnpModInt(n) {
      if (n <= 0) return 0;
      var d = this.DV % n,
          r = (this.s < 0) ? n - 1 : 0;
      if (this.t > 0)
          if (d == 0) r = this[0] % n;
          else
              for (var i = this.t - 1; i >= 0; --i) r = (d * r + this[i]) % n;
      return r;
  }

  // (public) 1/this % m (HAC 14.61)
  function bnModInverse(m) {
      var ac = m.isEven();
      if ((this.isEven() && ac) || m.signum() == 0) return BigInteger.ZERO;
      var u = m.clone(),
          v = this.clone();
      var a = nbv(1),
          b = nbv(0),
          c = nbv(0),
          d = nbv(1);
      while (u.signum() != 0) {
          while (u.isEven()) {
              u.rShiftTo(1, u);
              if (ac) {
                  if (!a.isEven() || !b.isEven()) {
                      a.addTo(this, a);
                      b.subTo(m, b);
                  }
                  a.rShiftTo(1, a);
              } else if (!b.isEven()) b.subTo(m, b);
              b.rShiftTo(1, b);
          }
          while (v.isEven()) {
              v.rShiftTo(1, v);
              if (ac) {
                  if (!c.isEven() || !d.isEven()) {
                      c.addTo(this, c);
                      d.subTo(m, d);
                  }
                  c.rShiftTo(1, c);
              } else if (!d.isEven()) d.subTo(m, d);
              d.rShiftTo(1, d);
          }
          if (u.compareTo(v) >= 0) {
              u.subTo(v, u);
              if (ac) a.subTo(c, a);
              b.subTo(d, b);
          } else {
              v.subTo(u, v);
              if (ac) c.subTo(a, c);
              d.subTo(b, d);
          }
      }
      if (v.compareTo(BigInteger.ONE) != 0) return BigInteger.ZERO;
      if (d.compareTo(m) >= 0) return d.subtract(m);
      if (d.signum() < 0) d.addTo(m, d);
      else return d;
      if (d.signum() < 0) return d.add(m);
      else return d;
  }

  var lowprimes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997];
  var lplim = (1 << 26) / lowprimes[lowprimes.length - 1];

  // (public) test primality with certainty >= 1-.5^t
  function bnIsProbablePrime(t) {
      var i, x = this.abs();
      if (x.t == 1 && x[0] <= lowprimes[lowprimes.length - 1]) {
          for (i = 0; i < lowprimes.length; ++i)
              if (x[0] == lowprimes[i]) return true;
          return false;
      }
      if (x.isEven()) return false;
      i = 1;
      while (i < lowprimes.length) {
          var m = lowprimes[i],
              j = i + 1;
          while (j < lowprimes.length && m < lplim) m *= lowprimes[j++];
          m = x.modInt(m);
          while (i < j)
              if (m % lowprimes[i++] == 0) return false;
      }
      return x.millerRabin(t);
  }

  // (protected) true if probably prime (HAC 4.24, Miller-Rabin)
  function bnpMillerRabin(t) {
      var n1 = this.subtract(BigInteger.ONE);
      var k = n1.getLowestSetBit();
      if (k <= 0) return false;
      var r = n1.shiftRight(k);
      t = (t + 1) >> 1;
      if (t > lowprimes.length) t = lowprimes.length;
      var a = nbi();
      for (var i = 0; i < t; ++i) {
          //Pick bases at random, instead of starting at 2
          a.fromInt(lowprimes[Math.floor(Math.random() * lowprimes.length)]);
          var y = a.modPow(r, this);
          if (y.compareTo(BigInteger.ONE) != 0 && y.compareTo(n1) != 0) {
              var j = 1;
              while (j++ < k && y.compareTo(n1) != 0) {
                  y = y.modPowInt(2, this);
                  if (y.compareTo(BigInteger.ONE) == 0) return false;
              }
              if (y.compareTo(n1) != 0) return false;
          }
      }
      return true;
  }

  // protected
  BigInteger.prototype.chunkSize = bnpChunkSize;
  BigInteger.prototype.toRadix = bnpToRadix;
  BigInteger.prototype.fromRadix = bnpFromRadix;
  BigInteger.prototype.fromNumber = bnpFromNumber;
  BigInteger.prototype.bitwiseTo = bnpBitwiseTo;
  BigInteger.prototype.changeBit = bnpChangeBit;
  BigInteger.prototype.addTo = bnpAddTo;
  BigInteger.prototype.dMultiply = bnpDMultiply;
  BigInteger.prototype.dAddOffset = bnpDAddOffset;
  BigInteger.prototype.multiplyLowerTo = bnpMultiplyLowerTo;
  BigInteger.prototype.multiplyUpperTo = bnpMultiplyUpperTo;
  BigInteger.prototype.modInt = bnpModInt;
  BigInteger.prototype.millerRabin = bnpMillerRabin;

  // public
  BigInteger.prototype.clone = bnClone;
  BigInteger.prototype.intValue = bnIntValue;
  BigInteger.prototype.byteValue = bnByteValue;
  BigInteger.prototype.shortValue = bnShortValue;
  BigInteger.prototype.signum = bnSigNum;
  BigInteger.prototype.toByteArray = bnToByteArray;
  BigInteger.prototype.equals = bnEquals;
  BigInteger.prototype.min = bnMin;
  BigInteger.prototype.max = bnMax;
  BigInteger.prototype.and = bnAnd;
  BigInteger.prototype.or = bnOr;
  BigInteger.prototype.xor = bnXor;
  BigInteger.prototype.andNot = bnAndNot;
  BigInteger.prototype.not = bnNot;
  BigInteger.prototype.shiftLeft = bnShiftLeft;
  BigInteger.prototype.shiftRight = bnShiftRight;
  BigInteger.prototype.getLowestSetBit = bnGetLowestSetBit;
  BigInteger.prototype.bitCount = bnBitCount;
  BigInteger.prototype.testBit = bnTestBit;
  BigInteger.prototype.setBit = bnSetBit;
  BigInteger.prototype.clearBit = bnClearBit;
  BigInteger.prototype.flipBit = bnFlipBit;
  BigInteger.prototype.add = bnAdd;
  BigInteger.prototype.subtract = bnSubtract;
  BigInteger.prototype.multiply = bnMultiply;
  BigInteger.prototype.divide = bnDivide;
  BigInteger.prototype.remainder = bnRemainder;
  BigInteger.prototype.divideAndRemainder = bnDivideAndRemainder;
  BigInteger.prototype.modPow = bnModPow;
  BigInteger.prototype.modInverse = bnModInverse;
  BigInteger.prototype.pow = bnPow;
  BigInteger.prototype.gcd = bnGCD;
  BigInteger.prototype.isProbablePrime = bnIsProbablePrime;

  // JSBN-specific extension
  BigInteger.prototype.square = bnSquare;

  // Expose the Barrett function
  BigInteger.prototype.Barrett = Barrett

  // BigInteger interfaces not implemented in jsbn:

  // BigInteger(int signum, byte[] magnitude)
  // double doubleValue()
  // float floatValue()
  // int hashCode()
  // long longValue()
  // static BigInteger valueOf(long val)

  // Random number generator - requires a PRNG backend, e.g. prng4.js

  // For best results, put code like
  // <body onClick='rng_seed_time();' onKeyPress='rng_seed_time();'>
  // in your main HTML document.

  var rng_state;
  var rng_pool;
  var rng_pptr;

  // Mix in a 32-bit integer into the pool
  function rng_seed_int(x) {
      rng_pool[rng_pptr++] ^= x & 255;
      rng_pool[rng_pptr++] ^= (x >> 8) & 255;
      rng_pool[rng_pptr++] ^= (x >> 16) & 255;
      rng_pool[rng_pptr++] ^= (x >> 24) & 255;
      if (rng_pptr >= rng_psize) rng_pptr -= rng_psize;
  }

  // Mix in the current time (w/milliseconds) into the pool
  function rng_seed_time() {
      rng_seed_int(new Date().getTime());
  }

  // Initialize the pool with junk if needed.
  if (rng_pool == null) {
      rng_pool = new Array();
      rng_pptr = 0;
      var t;
      if (typeof window !== "undefined" && window.crypto) {
          if (window.crypto.getRandomValues) {
              // Use webcrypto if available
              var ua = new Uint8Array(32);
              window.crypto.getRandomValues(ua);
              for (t = 0; t < 32; ++t)
                  rng_pool[rng_pptr++] = ua[t];
          } else if (navigator.appName == "Netscape" && navigator.appVersion < "5") {
              // Extract entropy (256 bits) from NS4 RNG if available
              var z = window.crypto.random(32);
              for (t = 0; t < z.length; ++t)
                  rng_pool[rng_pptr++] = z.charCodeAt(t) & 255;
          }
      }
      while (rng_pptr < rng_psize) { // extract some randomness from Math.random()
          t = Math.floor(65536 * Math.random());
          rng_pool[rng_pptr++] = t >>> 8;
          rng_pool[rng_pptr++] = t & 255;
      }
      rng_pptr = 0;
      rng_seed_time();
      //rng_seed_int(window.screenX);
      //rng_seed_int(window.screenY);
  }

  function rng_get_byte() {
      if (rng_state == null) {
          rng_seed_time();
          rng_state = prng_newstate();
          rng_state.init(rng_pool);
          for (rng_pptr = 0; rng_pptr < rng_pool.length; ++rng_pptr)
              rng_pool[rng_pptr] = 0;
          rng_pptr = 0;
          //rng_pool = null;
      }
      // TODO: allow reseeding after first request
      return rng_state.next();
  }

  function rng_get_bytes(ba) {
      var i;
      for (i = 0; i < ba.length; ++i) ba[i] = rng_get_byte();
  }

  function SecureRandom() {}

  SecureRandom.prototype.nextBytes = rng_get_bytes;

  // prng4.js - uses Arcfour as a PRNG

  function Arcfour() {
      this.i = 0;
      this.j = 0;
      this.S = new Array();
  }

  // Initialize arcfour context from key, an array of ints, each from [0..255]
  function ARC4init(key) {
      var i, j, t;
      for (i = 0; i < 256; ++i)
          this.S[i] = i;
      j = 0;
      for (i = 0; i < 256; ++i) {
          j = (j + this.S[i] + key[i % key.length]) & 255;
          t = this.S[i];
          this.S[i] = this.S[j];
          this.S[j] = t;
      }
      this.i = 0;
      this.j = 0;
  }

  function ARC4next() {
      var t;
      this.i = (this.i + 1) & 255;
      this.j = (this.j + this.S[this.i]) & 255;
      t = this.S[this.i];
      this.S[this.i] = this.S[this.j];
      this.S[this.j] = t;
      return this.S[(t + this.S[this.i]) & 255];
  }

  Arcfour.prototype.init = ARC4init;
  Arcfour.prototype.next = ARC4next;

  // Plug in your RNG constructor here
  function prng_newstate() {
      return new Arcfour();
  }

  // Pool size must be a multiple of 4 and greater than 32.
  // An array of bytes the size of the pool will be passed to init()
  var rng_psize = 256;

  if (typeof exports !== 'undefined') {
      exports = module.exports = {
          BigInteger: BigInteger,
          SecureRandom: SecureRandom,
      };
  } else {
      this.BigInteger = BigInteger;
      this.SecureRandom = SecureRandom;
  }

}).call(this);

/*********/
(function(factory) {
  "use strict";

  var root = (typeof self === "object" && self.self === self && self) ||
      (typeof global === "object" && global.global === global && global);

  if (typeof exports !== "undefined") {
      var BigInteger = require("jsbn").BigInteger;
      factory(root, exports, BigInteger);
  } else {
      var BigInt = root.BigInteger ? root.BigInteger : root.jsbn.BigInteger;
      root.Money = factory(root, {}, BigInt);
  }
}(function(root, Money, BigInteger) {
  "use strict";

  var Currency = function(code) {
          this.code = code;
      },

      separateThousands = function(inStr, withStr) {
          var sign = "",
              src = inStr,
              ret = "",
              appendix;

          if (inStr[0] === "-") {
              sign = "-";
              src = src.substr(1);
          }

          while (src.length > 0) {
              if (ret.length > 0) {
                  ret = withStr + ret;
              }

              if (src.length <= 3) {
                  ret = src + ret;
                  break;
              }

              appendix = src.substr(src.length - 3, 3);
              ret = appendix + ret;
              src = src.substr(0, src.length - 3);
          }

          return sign + ret;
      },

      integerValue = function(amount) {
          return (/^(\-?\d+)\.\d\d$/).exec(amount)[1];
      },

      isString = function(obj) {
          return Object.prototype.toString.call(obj) === "[object String]";
      },

      round = function(amount) {
          var fraction = parseInt(amount.substr(-2), 10),
              wholeAmount = integerValue(amount) + ".00";

          return (
              fraction < 50 ?
              wholeAmount :
              Money.add(wholeAmount, "1.00")
          );
      };

  Currency.prototype.format = function(amount) {
      switch (this.code) {
          case "JPY":
              return separateThousands(integerValue(amount), ",");

          case "EUR":
          case "GBP":
              return separateThousands(integerValue(amount), ".") + "," + amount.substr(-2);

          case "CHF":
          case "USD":
              return separateThousands(integerValue(amount), ",") + "." + amount.substr(-2);

          case "SEK":
          case "LTL":
          case "PLN":
          case "SKK":
          case "UAH":
              return separateThousands(integerValue(amount), " ") + "," + amount.substr(-2);

          default:
              return amount;
      }
  };

  Money.amountToCents = function(amount) {
      return amount.replace(".", "");
  };

  Money.centsToAmount = function(cents) {
      var sign,
          abs;

      if (!isString(cents)) {
          return undefined;
      }

      sign = (cents[0] === "-" ? "-" : "");
      abs = (sign === "-" ? cents.substr(1) : cents);

      while (abs.length < 3) {
          abs = ["0", abs].join("");
      }

      return sign + abs.substr(0, abs.length - 2) + "." + abs.substr(-2);
  };

  Money.floatToAmount = function(f) {
      return ("" + (Math.round(f * 100.0) / 100.0))
          .replace(/^-(\d+)$/, "-$1.00") //-xx
          .replace(/^(\d+)$/, "$1.00") //xx
          .replace(/^-(\d+)\.(\d)$/, "-$1.$20") //-xx.xx
          .replace(/^(\d+)\.(\d)$/, "$1.$20"); //xx.xx
  };

  Money.integralPart = function(amount) {
      return integerValue(amount);
  };

  Money.format = function(currency, amount) {
      return new Currency(currency).format(amount);
  };

  Money.add = function(a, b) {
      return Money.centsToAmount(
          new BigInteger(
              Money.amountToCents(a)
          ).add(
              new BigInteger(Money.amountToCents(b))
          ).toString()
      );
  };

  Money.subtract = function(a, b) {
      return Money.centsToAmount(
          new BigInteger(
              Money.amountToCents(a)
          ).subtract(
              new BigInteger(Money.amountToCents(b))
          ).toString()
      );
  };

  Money.mul = function(a, b) {
      return Money.centsToAmount(
          new BigInteger(
              Money.amountToCents(a)
          ).multiply(
              new BigInteger(Money.amountToCents(b))
          ).divide(
              new BigInteger("100")
          ).toString()
      );
  };

  Money.div = function(a, b) {
      var hundredthsOfCents = new BigInteger(
              Money.amountToCents(a)
          ).multiply(
              new BigInteger("10000")
          ).divide(
              new BigInteger(Money.amountToCents(b))
          ),

          remainder = parseInt(hundredthsOfCents.toString().substr(-2), 10);

      return Money.centsToAmount(
          hundredthsOfCents.divide(
              new BigInteger("100")
          ).add(
              new BigInteger(remainder > 50 ? "1" : "0")
          ).toString()
      );
  };

  Money.percent = function(value, percent) {
      var p = new BigInteger(
              Money.amountToCents(value)
          ).multiply(
              new BigInteger(Money.amountToCents(percent))
          ),

          q = p.divide(new BigInteger("10000")),
          r = p.mod(new BigInteger("10000"));

      return Money.centsToAmount(
          (r.compareTo(new BigInteger("4999")) > 0 ? q.add(new BigInteger("1")) : q).toString()
      );
  };

  Money.roundUpTo5Cents = function(amount) {
      var lastDigit = parseInt(amount.substr(-1), 10),
          additon = "0.00";

      if ((lastDigit % 5) !== 0) {
          additon = "0.0" + (5 - (lastDigit % 5));
      }

      return Money.add(amount, additon);
  };

  Money.roundTo5Cents = function(amount) {
      return Money.div(
          round(Money.mul(amount, "20.00")),
          "20.00"
      );
  };

  Money.cmp = function(a, b) {
      return new BigInteger(a.replace(".", "")).compareTo(new BigInteger(b.replace(".", "")));
  };

  return Money;
}));

/*********/
"use strict";

/* eslint no-var: 0, prefer-const: 0 */
/* exported throttle */
/**************
* UTILITY
*************/

// lodash.throttle, copy/pasted here to avoid including all of lodash

var _now = Date.now || function() {
  return new Date().getTime();
};

var throttle = function throttle(func, wait, options) {
  var context;
  var args;
  var result;
  var timeout = null;
  var previous = 0;
  if (!options) {
      options = {};
  }
  var later = function later() {
      previous = options.leading === false ? 0 : _now();
      timeout = null;
      result = func.apply(context, args);
      if (!timeout) {
          context = args = null;
      }
  };
  return function() {
      var now = _now();
      if (!previous && options.leading === false) {
          previous = now;
      }
      var remaining = wait - (now - previous);
      context = this;
      args = arguments;
      if (remaining <= 0 || remaining > wait) {
          clearTimeout(timeout);
          timeout = null;
          previous = now;
          result = func.apply(context, args);
          if (!timeout) {
              context = args = null;
          }
      } else if (!timeout && options.trailing !== false) {
          timeout = setTimeout(later, remaining);
      }
      return result;
  };
};
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIi4uLy4uLy4uLy4uL3NyYy9tYXNvbi9zY3JpcHQvcHVibGljLXNjcmlwdC91dGlscy5qcyJdLCJuYW1lcyI6WyJfbm93IiwiRGF0ZSIsIm5vdyIsImdldFRpbWUiLCJ0aHJvdHRsZSIsImZ1bmMiLCJ3YWl0Iiwib3B0aW9ucyIsImNvbnRleHQiLCJhcmdzIiwicmVzdWx0IiwidGltZW91dCIsInByZXZpb3VzIiwibGF0ZXIiLCJsZWFkaW5nIiwiYXBwbHkiLCJyZW1haW5pbmciLCJhcmd1bWVudHMiLCJjbGVhclRpbWVvdXQiLCJ0cmFpbGluZyIsInNldFRpbWVvdXQiXSwibWFwcGluZ3MiOiI7O0FBQUE7QUFDQTtBQUNBOzs7O0FBSUE7O0FBRUEsSUFBSUEsT0FBT0MsS0FBS0MsR0FBTCxJQUFZLFlBQVc7QUFDakMsUUFBTyxJQUFJRCxJQUFKLEdBQVdFLE9BQVgsRUFBUDtBQUNBLENBRkQ7O0FBSUEsSUFBSUMsV0FBVyxTQUFYQSxRQUFXLENBQVNDLElBQVQsRUFBZUMsSUFBZixFQUFxQkMsT0FBckIsRUFBOEI7QUFDNUMsS0FBSUMsT0FBSjtBQUNBLEtBQUlDLElBQUo7QUFDQSxLQUFJQyxNQUFKO0FBQ0EsS0FBSUMsVUFBVSxJQUFkO0FBQ0EsS0FBSUMsV0FBVyxDQUFmO0FBQ0EsS0FBSSxDQUFDTCxPQUFMLEVBQWM7QUFDYkEsWUFBVSxFQUFWO0FBQ0E7QUFDRCxLQUFJTSxRQUFRLFNBQVJBLEtBQVEsR0FBVztBQUN0QkQsYUFBV0wsUUFBUU8sT0FBUixLQUFvQixLQUFwQixHQUE0QixDQUE1QixHQUFnQ2QsTUFBM0M7QUFDQVcsWUFBVSxJQUFWO0FBQ0FELFdBQVNMLEtBQUtVLEtBQUwsQ0FBV1AsT0FBWCxFQUFvQkMsSUFBcEIsQ0FBVDtBQUNBLE1BQUksQ0FBQ0UsT0FBTCxFQUFjO0FBQ2JILGFBQVVDLE9BQU8sSUFBakI7QUFDQTtBQUNELEVBUEQ7QUFRQSxRQUFPLFlBQVc7QUFDakIsTUFBSVAsTUFBTUYsTUFBVjtBQUNBLE1BQUksQ0FBQ1ksUUFBRCxJQUFhTCxRQUFRTyxPQUFSLEtBQW9CLEtBQXJDLEVBQTRDO0FBQzNDRixjQUFXVixHQUFYO0FBQ0E7QUFDRCxNQUFJYyxZQUFZVixRQUFRSixNQUFNVSxRQUFkLENBQWhCO0FBQ0FKLFlBQVUsSUFBVjtBQUNBQyxTQUFPUSxTQUFQO0FBQ0EsTUFBSUQsYUFBYSxDQUFiLElBQWtCQSxZQUFZVixJQUFsQyxFQUF3QztBQUN2Q1ksZ0JBQWFQLE9BQWI7QUFDQUEsYUFBVSxJQUFWO0FBQ0FDLGNBQVdWLEdBQVg7QUFDQVEsWUFBU0wsS0FBS1UsS0FBTCxDQUFXUCxPQUFYLEVBQW9CQyxJQUFwQixDQUFUO0FBQ0EsT0FBSSxDQUFDRSxPQUFMLEVBQWM7QUFDYkgsY0FBVUMsT0FBTyxJQUFqQjtBQUNBO0FBQ0QsR0FSRCxNQVFPLElBQUksQ0FBQ0UsT0FBRCxJQUFZSixRQUFRWSxRQUFSLEtBQXFCLEtBQXJDLEVBQTRDO0FBQ2xEUixhQUFVUyxXQUFXUCxLQUFYLEVBQWtCRyxTQUFsQixDQUFWO0FBQ0E7QUFDRCxTQUFPTixNQUFQO0FBQ0EsRUFwQkQ7QUFxQkEsQ0F0Q0QiLCJmaWxlIjoidXRpbHMuanMiLCJzb3VyY2VzQ29udGVudCI6WyIvKiBlc2xpbnQgbm8tdmFyOiAwLCBwcmVmZXItY29uc3Q6IDAgKi9cbi8qIGV4cG9ydGVkIHRocm90dGxlICovXG4vKioqKioqKioqKioqKipcbiAqIFVUSUxJVFlcbiAqKioqKioqKioqKioqL1xuXG4vLyBsb2Rhc2gudGhyb3R0bGUsIGNvcHkvcGFzdGVkIGhlcmUgdG8gYXZvaWQgaW5jbHVkaW5nIGFsbCBvZiBsb2Rhc2hcblxudmFyIF9ub3cgPSBEYXRlLm5vdyB8fCBmdW5jdGlvbigpIHtcblx0cmV0dXJuIG5ldyBEYXRlKCkuZ2V0VGltZSgpO1xufTtcblxudmFyIHRocm90dGxlID0gZnVuY3Rpb24oZnVuYywgd2FpdCwgb3B0aW9ucykge1xuXHR2YXIgY29udGV4dDtcblx0dmFyIGFyZ3M7XG5cdHZhciByZXN1bHQ7XG5cdHZhciB0aW1lb3V0ID0gbnVsbDtcblx0dmFyIHByZXZpb3VzID0gMDtcblx0aWYgKCFvcHRpb25zKSB7XG5cdFx0b3B0aW9ucyA9IHt9O1xuXHR9XG5cdHZhciBsYXRlciA9IGZ1bmN0aW9uKCkge1xuXHRcdHByZXZpb3VzID0gb3B0aW9ucy5sZWFkaW5nID09PSBmYWxzZSA/IDAgOiBfbm93KCk7XG5cdFx0dGltZW91dCA9IG51bGw7XG5cdFx0cmVzdWx0ID0gZnVuYy5hcHBseShjb250ZXh0LCBhcmdzKTtcblx0XHRpZiAoIXRpbWVvdXQpIHtcblx0XHRcdGNvbnRleHQgPSBhcmdzID0gbnVsbDtcblx0XHR9XG5cdH07XG5cdHJldHVybiBmdW5jdGlvbigpIHtcblx0XHR2YXIgbm93ID0gX25vdygpO1xuXHRcdGlmICghcHJldmlvdXMgJiYgb3B0aW9ucy5sZWFkaW5nID09PSBmYWxzZSkge1xuXHRcdFx0cHJldmlvdXMgPSBub3c7XG5cdFx0fVxuXHRcdHZhciByZW1haW5pbmcgPSB3YWl0IC0gKG5vdyAtIHByZXZpb3VzKTtcblx0XHRjb250ZXh0ID0gdGhpcztcblx0XHRhcmdzID0gYXJndW1lbnRzO1xuXHRcdGlmIChyZW1haW5pbmcgPD0gMCB8fCByZW1haW5pbmcgPiB3YWl0KSB7XG5cdFx0XHRjbGVhclRpbWVvdXQodGltZW91dCk7XG5cdFx0XHR0aW1lb3V0ID0gbnVsbDtcblx0XHRcdHByZXZpb3VzID0gbm93O1xuXHRcdFx0cmVzdWx0ID0gZnVuYy5hcHBseShjb250ZXh0LCBhcmdzKTtcblx0XHRcdGlmICghdGltZW91dCkge1xuXHRcdFx0XHRjb250ZXh0ID0gYXJncyA9IG51bGw7XG5cdFx0XHR9XG5cdFx0fSBlbHNlIGlmICghdGltZW91dCAmJiBvcHRpb25zLnRyYWlsaW5nICE9PSBmYWxzZSkge1xuXHRcdFx0dGltZW91dCA9IHNldFRpbWVvdXQobGF0ZXIsIHJlbWFpbmluZyk7XG5cdFx0fVxuXHRcdHJldHVybiByZXN1bHQ7XG5cdH07XG59O1xuIl19

/*********/
/* eslint no-var: 0, prefer-const: 0 */
'use strict';

/*
* ANIMATED INTERNAL LINK SCROLLING
*/

var anchorScrolling = function anchorScrolling() {

  var navigationPipLinks = document.querySelectorAll('.navigation-pip .link a');
  var IE = navigator.userAgent.indexOf('Trident') >= 0;
  var FF = navigator.userAgent.indexOf('Gecko/') >= 0;

  function getViewportNode() {
      if (document.scrollingElement) {
          return document.scrollingElement;
      } else if (IE || FF) {
          return document.documentElement;
      } else {
          return document.body;
      }
  }

  function linkClickHandler(event) {
      event.preventDefault();
      var href = event.target.getAttribute('href');
      var targetName = event.target.getAttribute('data-destination-block');
      if (!targetName) {
          targetName = href.substring(1);
          event.target.setAttribute('data-destination-block', target);
      }
      var target = document.querySelector('[name="' + targetName + '"]');

      // The bounding rect's top is relative to the viewport, so it represents the delta
      // in scroll position (top > 0 : scroll down, top < 0 : scroll up)
      var delta = target.getBoundingClientRect().top;

      // Number of pixels we want to "ease" the block into view when scrolling
      var BLOCK_SCROLL_EASE_AMOUNT = 750;
      window.doScroll(getViewportNode(), delta, BLOCK_SCROLL_EASE_AMOUNT, function() {
          window.location.hash = href;
      });
  }

  for (var i = 0; i < navigationPipLinks.length; i++) {
      var link = navigationPipLinks.item(i);
      var href = link.getAttribute('href');
      if (href.indexOf('#') === 0) {
          if (link.addEventListener) {
              link.addEventListener('click', linkClickHandler);
          } else {
              // IE8
              link.attachEvent('onclick', linkClickHandler);
          }
      }
  }
};

anchorScrolling();
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIi4uLy4uLy4uLy4uL3NyYy9tYXNvbi9zY3JpcHQvcHVibGljLXNjcmlwdC9hbmltYXRlQmxvY2tMaW5rcy5qcyJdLCJuYW1lcyI6WyJhbmNob3JTY3JvbGxpbmciLCJuYXZpZ2F0aW9uUGlwTGlua3MiLCJkb2N1bWVudCIsInF1ZXJ5U2VsZWN0b3JBbGwiLCJJRSIsIm5hdmlnYXRvciIsInVzZXJBZ2VudCIsImluZGV4T2YiLCJGRiIsImdldFZpZXdwb3J0Tm9kZSIsInNjcm9sbGluZ0VsZW1lbnQiLCJkb2N1bWVudEVsZW1lbnQiLCJib2R5IiwibGlua0NsaWNrSGFuZGxlciIsImV2ZW50IiwicHJldmVudERlZmF1bHQiLCJocmVmIiwidGFyZ2V0IiwiZ2V0QXR0cmlidXRlIiwidGFyZ2V0TmFtZSIsInN1YnN0cmluZyIsInNldEF0dHJpYnV0ZSIsInF1ZXJ5U2VsZWN0b3IiLCJkZWx0YSIsImdldEJvdW5kaW5nQ2xpZW50UmVjdCIsInRvcCIsIkJMT0NLX1NDUk9MTF9FQVNFX0FNT1VOVCIsIndpbmRvdyIsImRvU2Nyb2xsIiwibG9jYXRpb24iLCJoYXNoIiwiaSIsImxlbmd0aCIsImxpbmsiLCJpdGVtIiwiYWRkRXZlbnRMaXN0ZW5lciIsImF0dGFjaEV2ZW50Il0sIm1hcHBpbmdzIjoiQUFBQTtBQUNBOztBQUVBOzs7O0FBR0EsSUFBSUEsa0JBQWtCLFNBQWxCQSxlQUFrQixHQUFZOztBQUVqQyxLQUFJQyxxQkFBcUJDLFNBQVNDLGdCQUFULENBQTBCLHlCQUExQixDQUF6QjtBQUNBLEtBQUlDLEtBQUtDLFVBQVVDLFNBQVYsQ0FBb0JDLE9BQXBCLENBQTRCLFNBQTVCLEtBQTBDLENBQW5EO0FBQ0EsS0FBSUMsS0FBS0gsVUFBVUMsU0FBVixDQUFvQkMsT0FBcEIsQ0FBNEIsUUFBNUIsS0FBeUMsQ0FBbEQ7O0FBRUEsVUFBU0UsZUFBVCxHQUEyQjtBQUMxQixNQUFJUCxTQUFTUSxnQkFBYixFQUErQjtBQUM5QixVQUFPUixTQUFTUSxnQkFBaEI7QUFDQSxHQUZELE1BRU8sSUFBSU4sTUFBTUksRUFBVixFQUFjO0FBQ3BCLFVBQU9OLFNBQVNTLGVBQWhCO0FBQ0EsR0FGTSxNQUVBO0FBQ04sVUFBT1QsU0FBU1UsSUFBaEI7QUFDQTtBQUNEOztBQUVELFVBQVNDLGdCQUFULENBQTBCQyxLQUExQixFQUFpQztBQUNoQ0EsUUFBTUMsY0FBTjtBQUNBLE1BQUlDLE9BQU9GLE1BQU1HLE1BQU4sQ0FBYUMsWUFBYixDQUEwQixNQUExQixDQUFYO0FBQ0EsTUFBSUMsYUFBYUwsTUFBTUcsTUFBTixDQUFhQyxZQUFiLENBQTBCLHdCQUExQixDQUFqQjtBQUNBLE1BQUksQ0FBQ0MsVUFBTCxFQUFpQjtBQUNoQkEsZ0JBQWFILEtBQUtJLFNBQUwsQ0FBZSxDQUFmLENBQWI7QUFDQU4sU0FBTUcsTUFBTixDQUFhSSxZQUFiLENBQTBCLHdCQUExQixFQUFvREosTUFBcEQ7QUFDQTtBQUNELE1BQUlBLFNBQVNmLFNBQVNvQixhQUFULENBQXVCLFlBQVlILFVBQVosR0FBeUIsSUFBaEQsQ0FBYjs7QUFFQTtBQUNBO0FBQ0EsTUFBSUksUUFBUU4sT0FBT08scUJBQVAsR0FBK0JDLEdBQTNDOztBQUVBO0FBQ0EsTUFBSUMsMkJBQTJCLEdBQS9CO0FBQ0FDLFNBQU9DLFFBQVAsQ0FBZ0JuQixpQkFBaEIsRUFBbUNjLEtBQW5DLEVBQTBDRyx3QkFBMUMsRUFBb0UsWUFBWTtBQUMvRUMsVUFBT0UsUUFBUCxDQUFnQkMsSUFBaEIsR0FBdUJkLElBQXZCO0FBQ0EsR0FGRDtBQUdBOztBQUVELE1BQUssSUFBSWUsSUFBSSxDQUFiLEVBQWdCQSxJQUFJOUIsbUJBQW1CK0IsTUFBdkMsRUFBK0NELEdBQS9DLEVBQW9EO0FBQ25ELE1BQUlFLE9BQU9oQyxtQkFBbUJpQyxJQUFuQixDQUF3QkgsQ0FBeEIsQ0FBWDtBQUNBLE1BQUlmLE9BQU9pQixLQUFLZixZQUFMLENBQWtCLE1BQWxCLENBQVg7QUFDQSxNQUFJRixLQUFLVCxPQUFMLENBQWEsR0FBYixNQUFzQixDQUExQixFQUE2QjtBQUM1QixPQUFJMEIsS0FBS0UsZ0JBQVQsRUFBMkI7QUFDMUJGLFNBQUtFLGdCQUFMLENBQXNCLE9BQXRCLEVBQStCdEIsZ0JBQS9CO0FBQ0EsSUFGRCxNQUVPO0FBQ047QUFDQW9CLFNBQUtHLFdBQUwsQ0FBaUIsU0FBakIsRUFBNEJ2QixnQkFBNUI7QUFDQTtBQUNEO0FBQ0Q7QUFDRCxDQWpERDs7QUFtREFiIiwiZmlsZSI6ImFuaW1hdGVCbG9ja0xpbmtzLmpzIiwic291cmNlc0NvbnRlbnQiOlsiLyogZXNsaW50IG5vLXZhcjogMCwgcHJlZmVyLWNvbnN0OiAwICovXG4ndXNlIHN0cmljdCc7XG5cbi8qXG4gKiBBTklNQVRFRCBJTlRFUk5BTCBMSU5LIFNDUk9MTElOR1xuICovXG52YXIgYW5jaG9yU2Nyb2xsaW5nID0gZnVuY3Rpb24gKCkge1xuXG5cdHZhciBuYXZpZ2F0aW9uUGlwTGlua3MgPSBkb2N1bWVudC5xdWVyeVNlbGVjdG9yQWxsKCcubmF2aWdhdGlvbi1waXAgLmxpbmsgYScpO1xuXHR2YXIgSUUgPSBuYXZpZ2F0b3IudXNlckFnZW50LmluZGV4T2YoJ1RyaWRlbnQnKSA+PSAwO1xuXHR2YXIgRkYgPSBuYXZpZ2F0b3IudXNlckFnZW50LmluZGV4T2YoJ0dlY2tvLycpID49IDA7XG5cblx0ZnVuY3Rpb24gZ2V0Vmlld3BvcnROb2RlKCkge1xuXHRcdGlmIChkb2N1bWVudC5zY3JvbGxpbmdFbGVtZW50KSB7XG5cdFx0XHRyZXR1cm4gZG9jdW1lbnQuc2Nyb2xsaW5nRWxlbWVudDtcblx0XHR9IGVsc2UgaWYgKElFIHx8IEZGKSB7XG5cdFx0XHRyZXR1cm4gZG9jdW1lbnQuZG9jdW1lbnRFbGVtZW50O1xuXHRcdH0gZWxzZSB7XG5cdFx0XHRyZXR1cm4gZG9jdW1lbnQuYm9keTtcblx0XHR9XG5cdH1cblxuXHRmdW5jdGlvbiBsaW5rQ2xpY2tIYW5kbGVyKGV2ZW50KSB7XG5cdFx0ZXZlbnQucHJldmVudERlZmF1bHQoKTtcblx0XHR2YXIgaHJlZiA9IGV2ZW50LnRhcmdldC5nZXRBdHRyaWJ1dGUoJ2hyZWYnKTtcblx0XHR2YXIgdGFyZ2V0TmFtZSA9IGV2ZW50LnRhcmdldC5nZXRBdHRyaWJ1dGUoJ2RhdGEtZGVzdGluYXRpb24tYmxvY2snKTtcblx0XHRpZiAoIXRhcmdldE5hbWUpIHtcblx0XHRcdHRhcmdldE5hbWUgPSBocmVmLnN1YnN0cmluZygxKTtcblx0XHRcdGV2ZW50LnRhcmdldC5zZXRBdHRyaWJ1dGUoJ2RhdGEtZGVzdGluYXRpb24tYmxvY2snLCB0YXJnZXQpO1xuXHRcdH1cblx0XHR2YXIgdGFyZ2V0ID0gZG9jdW1lbnQucXVlcnlTZWxlY3RvcignW25hbWU9XCInICsgdGFyZ2V0TmFtZSArICdcIl0nKTtcblxuXHRcdC8vIFRoZSBib3VuZGluZyByZWN0J3MgdG9wIGlzIHJlbGF0aXZlIHRvIHRoZSB2aWV3cG9ydCwgc28gaXQgcmVwcmVzZW50cyB0aGUgZGVsdGFcblx0XHQvLyBpbiBzY3JvbGwgcG9zaXRpb24gKHRvcCA+IDAgOiBzY3JvbGwgZG93biwgdG9wIDwgMCA6IHNjcm9sbCB1cClcblx0XHR2YXIgZGVsdGEgPSB0YXJnZXQuZ2V0Qm91bmRpbmdDbGllbnRSZWN0KCkudG9wO1xuXG5cdFx0Ly8gTnVtYmVyIG9mIHBpeGVscyB3ZSB3YW50IHRvIFwiZWFzZVwiIHRoZSBibG9jayBpbnRvIHZpZXcgd2hlbiBzY3JvbGxpbmdcblx0XHR2YXIgQkxPQ0tfU0NST0xMX0VBU0VfQU1PVU5UID0gNzUwO1xuXHRcdHdpbmRvdy5kb1Njcm9sbChnZXRWaWV3cG9ydE5vZGUoKSwgZGVsdGEsIEJMT0NLX1NDUk9MTF9FQVNFX0FNT1VOVCwgZnVuY3Rpb24gKCkge1xuXHRcdFx0d2luZG93LmxvY2F0aW9uLmhhc2ggPSBocmVmO1xuXHRcdH0pO1xuXHR9XG5cblx0Zm9yICh2YXIgaSA9IDA7IGkgPCBuYXZpZ2F0aW9uUGlwTGlua3MubGVuZ3RoOyBpKyspIHtcblx0XHR2YXIgbGluayA9IG5hdmlnYXRpb25QaXBMaW5rcy5pdGVtKGkpO1xuXHRcdHZhciBocmVmID0gbGluay5nZXRBdHRyaWJ1dGUoJ2hyZWYnKTtcblx0XHRpZiAoaHJlZi5pbmRleE9mKCcjJykgPT09IDApIHtcblx0XHRcdGlmIChsaW5rLmFkZEV2ZW50TGlzdGVuZXIpIHtcblx0XHRcdFx0bGluay5hZGRFdmVudExpc3RlbmVyKCdjbGljaycsIGxpbmtDbGlja0hhbmRsZXIpO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Ly8gSUU4XG5cdFx0XHRcdGxpbmsuYXR0YWNoRXZlbnQoJ29uY2xpY2snLCBsaW5rQ2xpY2tIYW5kbGVyKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cbn07XG5cbmFuY2hvclNjcm9sbGluZygpO1xuIl19

/*********/
/* eslint no-var: 0, prefer-const: 0 */
'use strict';

(function() {
  var currentLightboxImage = 0;
  var totalLightboxImages = 0;
  var lightboxVisible = false;
  var preloaded = false;
  var preloadUrls = [];
  var preloadedImages = [];
  var IMAGE_SELECTOR = 'section.lightbox-mode .graphic-pip-container:not(.force-disable-lightbox)' + ' img[data-lightbox-url], .force-lightbox img[data-lightbox-url]';

  // Preload all lightbox images when called. Only works on first call.
  function preloadImages() {
      if (!preloaded) {
          for (var i = 0; i < preloadUrls.length; i++) {
              preloadedImages[i] = new Image();
              preloadedImages[i].src = preloadUrls[i];
          }

          preloaded = true;
      }
  }

  // Handler for on hover on lightbox images
  function handlePreload() {
      forEachLightboxImage(function(thisImage) {
          thisImage.removeEventListener('mouseenter', handlePreload);
      });
      preloadImages();
  }

  // Returns the dom node list of all lightbox images
  function getLightboxImages() {
      return document.querySelectorAll(IMAGE_SELECTOR);
  }

  // Run a function for each lightbox image
  function forEachLightboxImage(callback) {
      var images = getLightboxImages();
      for (var i = 0; i < images.length; i++) {
          callback(images[i], i);
      }
  }

  // Do a first time setup for lightbox images
  function setupLightboxImage(thisImage, idx) {
      if (thisImage.dataset.lightboxUrl) {
          preloadUrls.push(thisImage.dataset.lightboxUrl);
          thisImage.dataset.lightboxImageIndex = idx;
          thisImage.style.cursor = 'pointer';
          thisImage.addEventListener('click', showLightboxImage.bind(thisImage, thisImage));
          thisImage.addEventListener('mouseenter', handlePreload);
      }
  }

  // Run the first time setup for all lightbox images
  function prepImagesForLightbox() {
      var images = getLightboxImages();
      totalLightboxImages = images.length;
      forEachLightboxImage(setupLightboxImage);
  }

  // Returns a dom node based on lightbox image index
  function getImageElementByLightboxId(id) {
      return document.querySelector('[data-lightbox-image-index="' + id + '"]');
  }

  // Show the next lightox image
  function nextLightboxImage() {
      currentLightboxImage += 1;
      if (currentLightboxImage >= totalLightboxImages) {
          currentLightboxImage = 0;
      }

      var nextImageEl = getImageElementByLightboxId(currentLightboxImage);
      showLightboxImage(nextImageEl);
  }

  // Show the previous lightbox image
  function previousLightboxImage() {
      currentLightboxImage -= 1;
      if (currentLightboxImage < 0) {
          currentLightboxImage = totalLightboxImages - 1;
      }

      var previousImageEl = getImageElementByLightboxId(currentLightboxImage);
      showLightboxImage(previousImageEl);
  }

  // Show a given image element in the lightbox
  function showLightboxImage(imageEl) {
      lightboxVisible = true;
      var imageToShow = imageEl.dataset.lightboxUrl;
      currentLightboxImage = parseInt(imageEl.dataset.lightboxImageIndex);

      document.querySelector('.lightbox-image').src = imageToShow;
      document.querySelector('.lightbox').classList.add('lightbox--visible');
  }

  // Close the lightbox
  function closeLightbox() {
      lightboxVisible = false;
      document.querySelector('.lightbox').classList.remove('lightbox--visible');
  }

  // Build the lightbox dom and add it to the page
  function addLightboxElementToPage() {
      var container = document.createElement('div');
      container.classList.add('lightbox');

      var cover = document.createElement('div');
      cover.classList.add('lightbox-cover');
      cover.addEventListener('click', closeLightbox);

      var xButton = document.createElement('div');
      xButton.innerHTML = '&times;';
      xButton.classList.add('lightbox-xButton');
      xButton.addEventListener('click', closeLightbox);

      var next = document.createElement('div');
      next.classList.add('lightbox-nav--next');
      next.classList.add('lightbox-nav');
      next.addEventListener('click', nextLightboxImage);

      var previous = document.createElement('div');
      previous.classList.add('lightbox-nav--previous');
      previous.classList.add('lightbox-nav');
      previous.addEventListener('click', previousLightboxImage);

      var image = document.createElement('img');
      image.classList.add('lightbox-image');
      image.addEventListener('click', nextLightboxImage);

      container.appendChild(cover);
      container.appendChild(image);
      container.appendChild(next);
      container.appendChild(previous);
      container.appendChild(xButton);
      document.body.appendChild(container);
  }

  // Add keyboard listeners for the lightbox
  function setupKeyboardLightboxControls() {
      window.addEventListener('keydown', function(keyboardEvent) {
          if (lightboxVisible) {
              switch (keyboardEvent.keyCode) {
                  case 37:
                      previousLightboxImage();
                      break;
                  case 39:
                      nextLightboxImage();
                      break;
                  case 27:
                      closeLightbox();
                      break;
              }
          }
      });
  }

  function removeLightboxClass() {
      var lightboxBlocks = document.querySelectorAll('section.lightbox-mode');
      for (var i = 0; i < lightboxBlocks.length; i++) {
          lightboxBlocks[i].classList.remove('lightbox-mode');
      }
  }

  // Only run the lightbox on browsers with dataset support (to prevent IE10- breakages)
  if (typeof document.body.dataset !== 'undefined') {
      addLightboxElementToPage();
      prepImagesForLightbox();
      setupKeyboardLightboxControls();
  } else {
      // If the browser doesn't support dataset, we also want to remove the lightbox-mode class from blocks
      removeLightboxClass();
  }
})();
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIi4uLy4uLy4uLy4uL3NyYy9tYXNvbi9zY3JpcHQvcHVibGljLXNjcmlwdC9saWdodGJveC5qcyJdLCJuYW1lcyI6WyJjdXJyZW50TGlnaHRib3hJbWFnZSIsInRvdGFsTGlnaHRib3hJbWFnZXMiLCJsaWdodGJveFZpc2libGUiLCJwcmVsb2FkZWQiLCJwcmVsb2FkVXJscyIsInByZWxvYWRlZEltYWdlcyIsIklNQUdFX1NFTEVDVE9SIiwicHJlbG9hZEltYWdlcyIsImkiLCJsZW5ndGgiLCJJbWFnZSIsInNyYyIsImhhbmRsZVByZWxvYWQiLCJmb3JFYWNoTGlnaHRib3hJbWFnZSIsInRoaXNJbWFnZSIsInJlbW92ZUV2ZW50TGlzdGVuZXIiLCJnZXRMaWdodGJveEltYWdlcyIsImRvY3VtZW50IiwicXVlcnlTZWxlY3RvckFsbCIsImNhbGxiYWNrIiwiaW1hZ2VzIiwic2V0dXBMaWdodGJveEltYWdlIiwiaWR4IiwiZGF0YXNldCIsImxpZ2h0Ym94VXJsIiwicHVzaCIsImxpZ2h0Ym94SW1hZ2VJbmRleCIsInN0eWxlIiwiY3Vyc29yIiwiYWRkRXZlbnRMaXN0ZW5lciIsInNob3dMaWdodGJveEltYWdlIiwiYmluZCIsInByZXBJbWFnZXNGb3JMaWdodGJveCIsImdldEltYWdlRWxlbWVudEJ5TGlnaHRib3hJZCIsImlkIiwicXVlcnlTZWxlY3RvciIsIm5leHRMaWdodGJveEltYWdlIiwibmV4dEltYWdlRWwiLCJwcmV2aW91c0xpZ2h0Ym94SW1hZ2UiLCJwcmV2aW91c0ltYWdlRWwiLCJpbWFnZUVsIiwiaW1hZ2VUb1Nob3ciLCJwYXJzZUludCIsImNsYXNzTGlzdCIsImFkZCIsImNsb3NlTGlnaHRib3giLCJyZW1vdmUiLCJhZGRMaWdodGJveEVsZW1lbnRUb1BhZ2UiLCJjb250YWluZXIiLCJjcmVhdGVFbGVtZW50IiwiY292ZXIiLCJ4QnV0dG9uIiwiaW5uZXJIVE1MIiwibmV4dCIsInByZXZpb3VzIiwiaW1hZ2UiLCJhcHBlbmRDaGlsZCIsImJvZHkiLCJzZXR1cEtleWJvYXJkTGlnaHRib3hDb250cm9scyIsIndpbmRvdyIsImtleWJvYXJkRXZlbnQiLCJrZXlDb2RlIiwicmVtb3ZlTGlnaHRib3hDbGFzcyIsImxpZ2h0Ym94QmxvY2tzIl0sIm1hcHBpbmdzIjoiQUFBQTtBQUNBOztBQUVBLENBQUMsWUFBWTtBQUNaLEtBQUlBLHVCQUF1QixDQUEzQjtBQUNBLEtBQUlDLHNCQUFzQixDQUExQjtBQUNBLEtBQUlDLGtCQUFrQixLQUF0QjtBQUNBLEtBQUlDLFlBQVksS0FBaEI7QUFDQSxLQUFJQyxjQUFjLEVBQWxCO0FBQ0EsS0FBSUMsa0JBQWtCLEVBQXRCO0FBQ0EsS0FBSUMsaUJBQWlCLDhFQUNwQixpRUFERDs7QUFHQTtBQUNBLFVBQVNDLGFBQVQsR0FBeUI7QUFDeEIsTUFBSSxDQUFDSixTQUFMLEVBQWdCO0FBQ2YsUUFBSyxJQUFJSyxJQUFJLENBQWIsRUFBZ0JBLElBQUlKLFlBQVlLLE1BQWhDLEVBQXdDRCxHQUF4QyxFQUE2QztBQUM1Q0gsb0JBQWdCRyxDQUFoQixJQUFxQixJQUFJRSxLQUFKLEVBQXJCO0FBQ0FMLG9CQUFnQkcsQ0FBaEIsRUFBbUJHLEdBQW5CLEdBQXlCUCxZQUFZSSxDQUFaLENBQXpCO0FBQ0E7O0FBRURMLGVBQVksSUFBWjtBQUNBO0FBQ0Q7O0FBRUQ7QUFDQSxVQUFTUyxhQUFULEdBQXlCO0FBQ3hCQyx1QkFBcUIsVUFBVUMsU0FBVixFQUFxQjtBQUN6Q0EsYUFBVUMsbUJBQVYsQ0FBOEIsWUFBOUIsRUFBNENILGFBQTVDO0FBQ0EsR0FGRDtBQUdBTDtBQUNBOztBQUVEO0FBQ0EsVUFBU1MsaUJBQVQsR0FBNkI7QUFDNUIsU0FBT0MsU0FBU0MsZ0JBQVQsQ0FBMEJaLGNBQTFCLENBQVA7QUFDQTs7QUFFRDtBQUNBLFVBQVNPLG9CQUFULENBQThCTSxRQUE5QixFQUF3QztBQUN2QyxNQUFJQyxTQUFTSixtQkFBYjtBQUNBLE9BQUssSUFBSVIsSUFBSSxDQUFiLEVBQWdCQSxJQUFJWSxPQUFPWCxNQUEzQixFQUFt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QUFDRCxVQUFLLEVBQUw7QUFDQ0Y7QUFDQTtBQUNELFVBQUssRUFBTDtBQUNDUztBQUNBO0FBVEY7QUFXQTtBQUNELEdBZEQ7QUFlQTs7QUFFRCxVQUFTaUIsbUJBQVQsR0FBK0I7QUFDOUIsTUFBSUMsaUJBQWlCOUMsU0FBU0MsZ0JBQVQsQ0FBMEIsdUJBQTFCLENBQXJCO0FBQ0EsT0FBSyxJQUFJVixJQUFJLENBQWIsRUFBZ0JBLElBQUl1RCxlQUFldEQsTUFBbkMsRUFBMkNELEdBQTNDLEVBQWdEO0FBQy9DdUQsa0JBQWV2RCxDQUFmLEVBQWtCbUMsU0FBbEIsQ0FBNEJHLE1BQTVCLENBQW1DLGVBQW5DO0FBQ0E7QUFDRDs7QUFFRDtBQUNBLEtBQUksT0FBTzdCLFNBQVN3QyxJQUFULENBQWNsQyxPQUFyQixLQUFpQyxXQUFyQyxFQUFrRDtBQUNqRHdCO0FBQ0FmO0FBQ0EwQjtBQUNBLEVBSkQsTUFJTztBQUNOO0FBQ0FJO0FBQ0E7QUFFRCxDQWhMRCIsImZpbGUiOiJsaWdodGJveC5qcyIsInNvdXJjZXNDb250ZW50IjpbIi8qIGVzbGludCBuby12YXI6IDAsIHByZWZlci1jb25zdDogMCAqL1xuJ3VzZSBzdHJpY3QnO1xuXG4oZnVuY3Rpb24gKCkge1xuXHR2YXIgY3VycmVudExpZ2h0Ym94SW1hZ2UgPSAwO1xuXHR2YXIgdG90YWxMaWdodGJveEltYWdlcyA9IDA7XG5cdHZhciBsaWdodGJveFZpc2libGUgPSBmYWxzZTtcblx0dmFyIHByZWxvYWRlZCA9IGZhbHNlO1xuXHR2YXIgcHJlbG9hZFVybHMgPSBbXTtcblx0dmFyIHByZWxvYWRlZEltYWdlcyA9IFtdO1xuXHR2YXIgSU1BR0VfU0VMRUNUT1IgPSAnc2VjdGlvbi5saWdodGJveC1tb2RlIC5ncmFwaGljLXBpcC1jb250YWluZXI6bm90KC5mb3JjZS1kaXNhYmxlLWxpZ2h0Ym94KScgK1xuXHRcdCcgaW1nW2RhdGEtbGlnaHRib3gtdXJsXSwgLmZvcmNlLWxpZ2h0Ym94IGltZ1tkYXRhLWxpZ2h0Ym94LXVybF0nO1xuXG5cdC8vIFByZWxvYWQgYWxsIGxpZ2h0Ym94IGltYWdlcyB3aGVuIGNhbGxlZC4gT25seSB3b3JrcyBvbiBmaXJzdCBjYWxsLlxuXHRmdW5jdGlvbiBwcmVsb2FkSW1hZ2VzKCkge1xuXHRcdGlmICghcHJlbG9hZGVkKSB7XG5cdFx0XHRmb3IgKHZhciBpID0gMDsgaSA8IHByZWxvYWRVcmxzLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRcdHByZWxvYWRlZEltYWdlc1tpXSA9IG5ldyBJbWFnZSgpO1xuXHRcdFx0XHRwcmVsb2FkZWRJbWFnZXNbaV0uc3JjID0gcHJlbG9hZFVybHNbaV07XG5cdFx0XHR9XG5cblx0XHRcdHByZWxvYWRlZCA9IHRydWU7XG5cdFx0fVxuXHR9XG5cblx0Ly8gSGFuZGxlciBmb3Igb24gaG92ZXIgb24gbGlnaHRib3ggaW1hZ2VzXG5cdGZ1bmN0aW9uIGhhbmRsZVByZWxvYWQoKSB7XG5cdFx0Zm9yRWFjaExpZ2h0Ym94SW1hZ2UoZnVuY3Rpb24gKHRoaXNJbWFnZSkge1xuXHRcdFx0dGhpc0ltYWdlLnJlbW92ZUV2ZW50TGlzdGVuZXIoJ21vdXNlZW50ZXInLCBoYW5kbGVQcmVsb2FkKTtcblx0XHR9KTtcblx0XHRwcmVsb2FkSW1hZ2VzKCk7XG5cdH1cblxuXHQvLyBSZXR1cm5zIHRoZSBkb20gbm9kZSBsaXN0IG9mIGFsbCBsaWdodGJveCBpbWFnZXNcblx0ZnVuY3Rpb24gZ2V0TGlnaHRib3hJbWFnZXMoKSB7XG5cdFx0cmV0dXJuIGRvY3VtZW50LnF1ZXJ5U2VsZWN0b3JBbGwoSU1BR0VfU0VMRUNUT1IpO1xuXHR9XG5cblx0Ly8gUnVuIGEgZnVuY3Rpb24gZm9yIGVhY2ggbGlnaHRib3ggaW1hZ2Vcblx0ZnVuY3Rpb24gZm9yRWFjaExpZ2h0Ym94SW1hZ2UoY2FsbGJhY2spIHtcblx0XHR2YXIgaW1hZ2VzID0gZ2V0TGlnaHRib3hJbWFnZXMoKTtcblx0XHRmb3IgKHZhciBpID0gMDsgaSA8IGltYWdlcy5sZW5ndGg7IGkrKykge1xuXHRcdFx0Y2FsbGJhY2soaW1hZ2VzW2ldLCBpKTtcblx0XHR9XG5cdH1cblxuXHQvLyBEbyBhIGZpcnN0IHRpbWUgc2V0dXAgZm9yIGxpZ2h0Ym94IGltYWdlc1xuXHRmdW5jdGlvbiBzZXR1cExpZ2h0Ym94SW1hZ2UodGhpc0ltYWdlLCBpZHgpIHtcblx0XHRpZiAodGhpc0ltYWdlLmRhdGFzZXQubGlnaHRib3hVcmwpIHtcblx0XHRcdHByZWxvYWRVcmxzLnB1c2godGhpc0ltYWdlLmRhdGFzZXQubGlnaHRib3hVcmwpO1xuXHRcdFx0dGhpc0ltYWdlLmRhdGFzZXQubGlnaHRib3hJbWFnZUluZGV4ID0gaWR4O1xuXHRcdFx0dGhpc0ltYWdlLnN0eWxlLmN1cnNvciA9ICdwb2ludGVyJztcblx0XHRcdHRoaXNJbWFnZS5hZGRFdmVudExpc3RlbmVyKCdjbGljaycsIHNob3dMaWdodGJveEltYWdlLmJpbmQodGhpc0ltYWdlLCB0aGlzSW1hZ2UpKTtcblx0XHRcdHRoaXNJbWFnZS5hZGRFdmVudExpc3RlbmVyKCdtb3VzZWVudGVyJywgaGFuZGxlUHJlbG9hZCk7XG5cdFx0fVxuXHR9XG5cblx0Ly8gUnVuIHRoZSBmaXJzdCB0aW1lIHNldHVwIGZvciBhbGwgbGlnaHRib3ggaW1hZ2VzXG5cdGZ1bmN0aW9uIHByZXBJbWFnZXNGb3JMaWdodGJveCgpIHtcblx0XHR2YXIgaW1hZ2VzID0gZ2V0TGlnaHRib3hJbWFnZXMoKTtcblx0XHR0b3RhbExpZ2h0Ym94SW1hZ2VzID0gaW1hZ2VzLmxlbmd0aDtcblx0XHRmb3JFYWNoTGlnaHRib3hJbWFnZShzZXR1cExpZ2h0Ym94SW1hZ2UpO1xuXHR9XG5cblx0Ly8gUmV0dXJucyBhIGRvbSBub2RlIGJhc2VkIG9uIGxpZ2h0Ym94IGltYWdlIGluZGV4XG5cdGZ1bmN0aW9uIGdldEltYWdlRWxlbWVudEJ5TGlnaHRib3hJZChpZCkge1xuXHRcdHJldHVybiBkb2N1bWVudC5xdWVyeVNlbGVjdG9yKCdbZGF0YS1saWdodGJveC1pbWFnZS1pbmRleD1cIicgKyBpZCArICdcIl0nKTtcblx0fVxuXG5cdC8vIFNob3cgdGhlIG5leHQgbGlnaHRveCBpbWFnZVxuXHRmdW5jdGlvbiBuZXh0TGlnaHRib3hJbWFnZSgpIHtcblx0XHRjdXJyZW50TGlnaHRib3hJbWFnZSArPSAxO1xuXHRcdGlmIChjdXJyZW50TGlnaHRib3hJbWFnZSA+PSB0b3RhbExpZ2h0Ym94SW1hZ2VzKSB7XG5cdFx0XHRjdXJyZW50TGlnaHRib3hJbWFnZSA9IDA7XG5cdFx0fVxuXG5cdFx0dmFyIG5leHRJbWFnZUVsID0gZ2V0SW1hZ2VFbGVtZW50QnlMaWdodGJveElkKGN1cnJlbnRMaWdodGJveEltYWdlKTtcblx0XHRzaG93TGlnaHRib3hJbWFnZShuZXh0SW1hZ2VFbCk7XG5cdH1cblxuXHQvLyBTaG93IHRoZSBwcmV2aW91cyBsaWdodGJveCBpbWFnZVxuXHRmdW5jdGlvbiBwcmV2aW91c0xpZ2h0Ym94SW1hZ2UoKSB7XG5cdFx0Y3VycmVudExpZ2h0Ym94SW1hZ2UgLT0gMTtcblx0XHRpZiAoY3VycmVudExpZ2h0Ym94SW1hZ2UgPCAwKSB7XG5cdFx0XHRjdXJyZW50TGlnaHRib3hJbWFnZSA9IHRvdGFsTGlnaHRib3hJbWFnZXMgLSAxO1xuXHRcdH1cblxuXHRcdHZhciBwcmV2aW91c0ltYWdlRWwgPSBnZXRJbWFnZUVsZW1lbnRCeUxpZ2h0Ym94SWQoY3VycmVudExpZ2h0Ym94SW1hZ2UpO1xuXHRcdHNob3dMaWdodGJveEltYWdlKHByZXZpb3VzSW1hZ2VFbCk7XG5cdH1cblxuXHQvLyBTaG93IGEgZ2l2ZW4gaW1hZ2UgZWxlbWVudCBpbiB0aGUgbGlnaHRib3hcblx0ZnVuY3Rpb24gc2hvd0xpZ2h0Ym94SW1hZ2UoaW1hZ2VFbCkge1xuXHRcdGxpZ2h0Ym94VmlzaWJsZSA9IHRydWU7XG5cdFx0dmFyIGltYWdlVG9TaG93ID0gaW1hZ2VFbC5kYXRhc2V0LmxpZ2h0Ym94VXJsO1xuXHRcdGN1cnJlbnRMaWdodGJveEltYWdlID0gcGFyc2VJbnQoaW1hZ2VFbC5kYXRhc2V0LmxpZ2h0Ym94SW1hZ2VJbmRleCk7XG5cblx0XHRkb2N1bWVudC5xdWVyeVNlbGVjdG9yKCcubGlnaHRib3gtaW1hZ2UnKS5zcmMgPSBpbWFnZVRvU2hvdztcblx0XHRkb2N1bWVudC5xdWVyeVNlbGVjdG9yKCcubGlnaHRib3gnKS5jbGFzc0xpc3QuYWRkKCdsaWdodGJveC0tdmlzaWJsZScpO1xuXHR9XG5cblx0Ly8gQ2xvc2UgdGhlIGxpZ2h0Ym94XG5cdGZ1bmN0aW9uIGNsb3NlTGlnaHRib3goKSB7XG5cdFx0bGlnaHRib3hWaXNpYmxlID0gZmFsc2U7XG5cdFx0ZG9jdW1lbnQucXVlcnlTZWxlY3RvcignLmxpZ2h0Ym94JykuY2xhc3NMaXN0LnJlbW92ZSgnbGlnaHRib3gtLXZpc2libGUnKTtcblx0fVxuXG5cdC8vIEJ1aWxkIHRoZSBsaWdodGJveCBkb20gYW5kIGFkZCBpdCB0byB0aGUgcGFnZVxuXHRmdW5jdGlvbiBhZGRMaWdodGJveEVsZW1lbnRUb1BhZ2UoKSB7XG5cdFx0dmFyIGNvbnRhaW5lciA9IGRvY3VtZW50LmNyZWF0ZUVsZW1lbnQoJ2RpdicpO1xuXHRcdGNvbnRhaW5lci5jbGFzc0xpc3QuYWRkKCdsaWdodGJveCcpO1xuXG5cdFx0dmFyIGNvdmVyID0gZG9jdW1lbnQuY3JlYXRlRWxlbWVudCgnZGl2Jyk7XG5cdFx0Y292ZXIuY2xhc3NMaXN0LmFkZCgnbGlnaHRib3gtY292ZXInKTtcblx0XHRjb3Zlci5hZGRFdmVudExpc3RlbmVyKCdjbGljaycsIGNsb3NlTGlnaHRib3gpO1xuXG5cdFx0dmFyIHhCdXR0b24gPSBkb2N1bWVudC5jcmVhdGVFbGVtZW50KCdkaXYnKTtcblx0XHR4QnV0dG9uLmlubmVySFRNTCA9ICcmdGltZXM7Jztcblx0XHR4QnV0dG9uLmNsYXNzTGlzdC5hZGQoJ2xpZ2h0Ym94LXhCdXR0b24nKTtcblx0XHR4QnV0dG9uLmFkZEV2ZW50TGlzdGVuZXIoJ2NsaWNrJywgY2xvc2VMaWdodGJveCk7XG5cblx0XHR2YXIgbmV4dCA9IGRvY3VtZW50LmNyZWF0ZUVsZW1lbnQoJ2RpdicpO1xuXHRcdG5leHQuY2xhc3NMaXN0LmFkZCgnbGlnaHRib3gtbmF2LS1uZXh0Jyk7XG5cdFx0bmV4dC5jbGFzc0xpc3QuYWRkKCdsaWdodGJveC1uYXYnKTtcblx0XHRuZXh0LmFkZEV2ZW50TGlzdGVuZXIoJ2NsaWNrJywgbmV4dExpZ2h0Ym94SW1hZ2UpO1xuXG5cdFx0dmFyIHByZXZpb3VzID0gZG9jdW1lbnQuY3JlYXRlRWxlbWVudCgnZGl2Jyk7XG5cdFx0cHJldmlvdXMuY2xhc3NMaXN0LmFkZCgnbGlnaHRib3gtbmF2LS1wcmV2aW91cycpO1xuXHRcdHByZXZpb3VzLmNsYXNzTGlzdC5hZGQoJ2xpZ2h0Ym94LW5hdicpO1xuXHRcdHByZXZpb3VzLmFkZEV2ZW50TGlzdGVuZXIoJ2NsaWNrJywgcHJldmlvdXNMaWdodGJveEltYWdlKTtcblxuXHRcdHZhciBpbWFnZSA9IGRvY3VtZW50LmNyZWF0ZUVsZW1lbnQoJ2ltZycpO1xuXHRcdGltYWdlLmNsYXNzTGlzdC5hZGQoJ2xpZ2h0Ym94LWltYWdlJyk7XG5cdFx0aW1hZ2UuYWRkRXZlbnRMaXN0ZW5lcignY2xpY2snLCBuZXh0TGlnaHRib3hJbWFnZSk7XG5cblx0XHRjb250YWluZXIuYXBwZW5kQ2hpbGQoY292ZXIpO1xuXHRcdGNvbnRhaW5lci5hcHBlbmRDaGlsZChpbWFnZSk7XG5cdFx0Y29udGFpbmVyLmFwcGVuZENoaWxkKG5leHQpO1xuXHRcdGNvbnRhaW5lci5hcHBlbmRDaGlsZChwcmV2aW91cyk7XG5cdFx0Y29udGFpbmVyLmFwcGVuZENoaWxkKHhCdXR0b24pO1xuXHRcdGRvY3VtZW50LmJvZHkuYXBwZW5kQ2hpbGQoY29udGFpbmVyKTtcblx0fVxuXG5cdC8vIEFkZCBrZXlib2FyZCBsaXN0ZW5lcnMgZm9yIHRoZSBsaWdodGJveFxuXHRmdW5jdGlvbiBzZXR1cEtleWJvYXJkTGlnaHRib3hDb250cm9scygpIHtcblx0XHR3aW5kb3cuYWRkRXZlbnRMaXN0ZW5lcigna2V5ZG93bicsIGZ1bmN0aW9uIChrZXlib2FyZEV2ZW50KSB7XG5cdFx0XHRpZiAobGlnaHRib3hWaXNpYmxlKSB7XG5cdFx0XHRcdHN3aXRjaCAoa2V5Ym9hcmRFdmVudC5rZXlDb2RlKSB7XG5cdFx0XHRcdFx0Y2FzZSAzNzpcblx0XHRcdFx0XHRcdHByZXZpb3VzTGlnaHRib3hJbWFnZSgpO1xuXHRcdFx0XHRcdFx0YnJlYWs7XG5cdFx0XHRcdFx0Y2FzZSAzOTpcblx0XHRcdFx0XHRcdG5leHRMaWdodGJveEltYWdlKCk7XG5cdFx0XHRcdFx0XHRicmVhaztcblx0XHRcdFx0XHRjYXNlIDI3OlxuXHRcdFx0XHRcdFx0Y2xvc2VMaWdodGJveCgpO1xuXHRcdFx0XHRcdFx0YnJlYWs7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9KTtcblx0fVxuXG5cdGZ1bmN0aW9uIHJlbW92ZUxpZ2h0Ym94Q2xhc3MoKSB7XG5cdFx0dmFyIGxpZ2h0Ym94QmxvY2tzID0gZG9jdW1lbnQucXVlcnlTZWxlY3RvckFsbCgnc2VjdGlvbi5saWdodGJveC1tb2RlJyk7XG5cdFx0Zm9yICh2YXIgaSA9IDA7IGkgPCBsaWdodGJveEJsb2Nrcy5sZW5ndGg7IGkrKykge1xuXHRcdFx0bGlnaHRib3hCbG9ja3NbaV0uY2xhc3NMaXN0LnJlbW92ZSgnbGlnaHRib3gtbW9kZScpO1xuXHRcdH1cblx0fVxuXG5cdC8vIE9ubHkgcnVuIHRoZSBsaWdodGJveCBvbiBicm93c2VycyB3aXRoIGRhdGFzZXQgc3VwcG9ydCAodG8gcHJldmVudCBJRTEwLSBicmVha2FnZXMpXG5cdGlmICh0eXBlb2YgZG9jdW1lbnQuYm9keS5kYXRhc2V0ICE9PSAndW5kZWZpbmVkJykge1xuXHRcdGFkZExpZ2h0Ym94RWxlbWVudFRvUGFnZSgpO1xuXHRcdHByZXBJbWFnZXNGb3JMaWdodGJveCgpO1xuXHRcdHNldHVwS2V5Ym9hcmRMaWdodGJveENvbnRyb2xzKCk7XG5cdH0gZWxzZSB7XG5cdFx0Ly8gSWYgdGhlIGJyb3dzZXIgZG9lc24ndCBzdXBwb3J0IGRhdGFzZXQsIHdlIGFsc28gd2FudCB0byByZW1vdmUgdGhlIGxpZ2h0Ym94LW1vZGUgY2xhc3MgZnJvbSBibG9ja3Ncblx0XHRyZW1vdmVMaWdodGJveENsYXNzKCk7XG5cdH1cblxufSkoKTtcbiJdfQ==

/*********/
/* eslint no-var: 0, prefer-const: 0 */
'use strict';

(function() {

  var CAROUSEL_SELECTOR = '.block-content.carousel';
  var FACE_WRAPPER_SELECTOR = '.carousel-faces';
  var FACE_CONTROL_SELECTOR = '.carousel-face-controls .face-control';
  var FACE_SELECTOR = FACE_WRAPPER_SELECTOR + ' .carousel-face';
  var CURRENT_FACE_SELECTOR = FACE_WRAPPER_SELECTOR + ' .current';
  var SWIPE_THRESHOLD = 50;

  function getCarouselBlocks() {
      return document.querySelectorAll(CAROUSEL_SELECTOR);
  }

  function getCarouselFaceControls(block) {
      return block.querySelectorAll(FACE_CONTROL_SELECTOR);
  }

  function getCarouselFaces(block) {
      return block.querySelectorAll(FACE_SELECTOR);
  }

  // Run a function for each element in the array
  function forEachElement(elements, callback) {
      for (var i = 0; i < elements.length; i++) {
          callback(elements[i], i);
      }
  }

  // Update the dot controls to display newly selected index
  function updateSelectedControls(block, selectedIndex) {
      forEachElement(getCarouselFaceControls(block), function(control, index) {
          if (index === selectedIndex) {
              control.classList.add('selected');
          } else {
              control.classList.remove('selected');
          }
      });
  }

  // Set the transitioning class on the face wrapper and attach listener for its transitionend
  function setTransitionState(block, currentFace) {
      var faceWrapper = block.querySelector(FACE_WRAPPER_SELECTOR);
      faceWrapper.classList.add('transitioning');
      currentFace.addEventListener(currentFace.style.WebkitTransition !== undefined ? 'webkitTransitionEnd' : 'transitionend', removeTransitionState.bind(null, block));
  }

  // Remove the transition class and event when the animation has ended
  function removeTransitionState(block, transitionEvent) {
      if (!transitionEvent.target.classList.contains('carousel-face')) {
          return;
      }
      transitionEvent.target.parentNode.classList.remove('transitioning');
      transitionEvent.target.removeEventListener(transitionEvent.type, this.removeTransitionState);
  }

  // Returns the currently selected block face index
  function getCurrentFaceIndex(block) {
      var faces = getCarouselFaces(block);
      var currentFace = block.querySelector(CURRENT_FACE_SELECTOR);
      return Array.prototype.indexOf.call(faces, currentFace);
  }

  function selectNextCarouselFace(block) {
      return selectCarouselFace(getCurrentFaceIndex(block) + 1, block);
  }

  function selectPreviousCarouselFace(block) {
      return selectCarouselFace(getCurrentFaceIndex(block) - 1, block);
  }

  // Handles the selection of a carousel face
  function selectCarouselFace(selectedIndex, block) {
      var faces = getCarouselFaces(block);
      var previousFace = block.querySelector(CURRENT_FACE_SELECTOR);
      var previousIndex = Array.prototype.indexOf.call(faces, previousFace);

      // Cycle through faces if we're at the end
      if (selectedIndex < 0) {
          selectedIndex = faces.length - 1;
      } else if (selectedIndex >= faces.length) {
          selectedIndex = 0;
      }

      updateSelectedControls(block, selectedIndex);

      setTransitionState(block, faces[selectedIndex]);

      forEachElement(getCarouselFaces(block), function(face, index) {
          if (index === selectedIndex) {
              face.classList.add('current');
              face.classList.remove('left');
              face.classList.remove('right');
              face.classList.remove('previous');
          } else {
              face.classList.remove('current');

              if (index === previousIndex) {
                  face.classList.add('previous');
              } else {
                  face.classList.remove('previous');
              }
              if (index > selectedIndex) {
                  face.classList.remove('left');
                  face.classList.add('right');
              } else {
                  face.classList.add('left');
                  face.classList.remove('right');
              }
          }
      });
  }

  function setContainerHeight(block) {
      // Set the height of the faces container to equal the height of the tallest face
      var maxFaceHeight = 0;
      forEachElement(block.querySelectorAll('.carousel-face'), function(face) {
          var faceHeight = face.getBoundingClientRect().height;
          if (faceHeight > maxFaceHeight) {
              maxFaceHeight = faceHeight;
          }
      });
      block.querySelector('.carousel-faces').style.height = maxFaceHeight + 'px';
  }

  // Initialize all the listeners we need for clickable elements
  forEachElement(getCarouselBlocks(), function(block) {
      var swipeStartX = 0;

      block.addEventListener('touchstart', function(event) {
          var touchInfo = event.changedTouches[0];
          swipeStartX = touchInfo.pageX;
      });

      block.addEventListener('touchend', function(event) {
          var touchInfo = event.changedTouches[0];
          var swipeEndX = touchInfo.pageX;
          var swipeDiff = swipeStartX - swipeEndX;

          // Swipe right
          if (swipeDiff > SWIPE_THRESHOLD) {
              selectNextCarouselFace(block);
          } else if (swipeDiff < -1 * SWIPE_THRESHOLD) {
              selectPreviousCarouselFace(block);
          }
      });

      // Attach click listeners for the dot controls.
      forEachElement(getCarouselFaceControls(block), function(control, index) {
          control.addEventListener('click', selectCarouselFace.bind(null, index, block));
      });

      // Attach click listners for the side controls.
      forEachElement(block.querySelectorAll('.face-control-side'), function(control) {
          if (control.classList.contains('left')) {
              control.addEventListener('click', selectPreviousCarouselFace.bind(null, block));
          } else if (control.classList.contains('right')) {
              control.addEventListener('click', selectNextCarouselFace.bind(null, block));
          }
      });

      window.setTimeout(setContainerHeight.bind(null, block), 1);
      window.addEventListener('resize', setContainerHeight.bind(null, block));
      var imagesInCarousel = block.querySelectorAll('.carousel-face img');
      var imagesLoaded = 0;
      forEachElement(imagesInCarousel, function(image) {
          var imageToLoad = new Image();
          imageToLoad.onload = function() {
              imagesLoaded++;
              if (imagesLoaded === imagesInCarousel.length) {
                  setContainerHeight(block);
              }
          };
          imageToLoad.src = image.getAttribute('src');
      });
  });
})();
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIi4uLy4uLy4uLy4uL3NyYy9tYXNvbi9zY3JpcHQvcHVibGljLXNjcmlwdC9jYXJvdXNlbC5qcyJdLCJuYW1lcyI6WyJDQVJPVVNFTF9TRUxFQ1RPUiIsIkZBQ0VfV1JBUFBFUl9TRUxFQ1RPUiIsIkZBQ0VfQ09OVFJPTF9TRUxFQ1RPUiIsIkZBQ0VfU0VMRUNUT1IiLCJDVVJSRU5UX0ZBQ0VfU0VMRUNUT1IiLCJTV0lQRV9USFJFU0hPTEQiLCJnZXRDYXJvdXNlbEJsb2NrcyIsImRvY3VtZW50IiwicXVlcnlTZWxlY3RvckFsbCIsImdldENhcm91c2VsRmFjZUNvbnRyb2xzIiwiYmxvY2siLCJnZXRDYXJvdXNlbEZhY2VzIiwiZm9yRWFjaEVsZW1lbnQiLCJlbGVtZW50cyIsImNhbGxiYWNrIiwiaSIsImxlbmd0aCIsInVwZGF0ZVNlbGVjdGVkQ29udHJvbHMiLCJzZWxlY3RlZEluZGV4IiwiY29udHJvbCIsImluZGV4IiwiY2xhc3NMaXN0IiwiYWRkIiwicmVtb3ZlIiwic2V0VHJhbnNpdGlvblN0YXRlIiwiY3VycmVudEZhY2UiLCJmYWNlV3JhcHBlciIsInF1ZXJ5U2VsZWN0b3IiLCJhZGRFdmVudExpc3RlbmVyIiwic3R5bGUiLCJXZWJraXRUcmFuc2l0aW9uIiwidW5kZWZpbmVkIiwicmVtb3ZlVHJhbnNpdGlvblN0YXRlIiwiYmluZCIsInRyYW5zaXRpb25FdmVudCIsInRhcmdldCIsImNvbnRhaW5zIiwicGFyZW50Tm9kZSIsInJlbW92ZUV2ZW50TGlzdGVuZXIiLCJ0eXBlIiwiZ2V0Q3VycmVudEZhY2VJbmRleCIsImZhY2VzIiwiQXJyYXkiLCJwcm90b3R5cGUiLCJpbmRleE9mIiwiY2FsbCIsInNlbGVjdE5leHRDYXJvdXNlbEZhY2UiLCJzZWxlY3RDYXJvdXNlbEZhY2UiLCJzZWxlY3RQcmV2aW91c0Nhcm91c2VsRmFjZSIsInByZXZpb3VzRmFjZSIsInByZXZpb3VzSW5kZXgiLCJmYWNlIiwic2V0Q29udGFpbmVySGVpZ2h0IiwibWF4RmFjZUhlaWdodCIsImZhY2VIZWlnaHQiLCJnZXRCb3VuZGluZ0NsaWVudFJlY3QiLCJoZWlnaHQiLCJzd2lwZVN0YXJ0WCIsImV2ZW50IiwidG91Y2hJbmZvIiwiY2hhbmdlZFRvdWNoZXMiLCJwYWdlWCIsInN3aXBlRW5kWCIsInN3aXBlRGlmZiIsIndpbmRvdyIsInNldFRpbWVvdXQiLCJpbWFnZXNJbkNhcm91c2VsIiwiaW1hZ2VzTG9hZGVkIiwiaW1hZ2UiLCJpbWFnZVRvTG9hZCIsIkltYWdlIiwib25sb2FkIiwic3JjIiwiZ2V0QXR0cmlidXRlIl0sIm1hcHBpbmdzIjoiQUFBQTtBQUNBOztBQUVBLENBQUMsWUFBWTs7QUFFWixLQUFJQSxvQkFBb0IseUJBQXhCO0FBQ0EsS0FBSUMsd0JBQXdCLGlCQUE1QjtBQUNBLEtBQUlDLHdCQUF3Qix1Q0FBNUI7QUFDQSxLQUFJQyxnQkFBZ0JGLHdCQUF3QixpQkFBNUM7QUFDQSxLQUFJRyx3QkFBd0JILHdCQUF3QixXQUFwRDtBQUNBLEtBQUlJLGtCQUFrQixFQUF0Qjs7QUFFQSxVQUFTQyxpQkFBVCxHQUE2QjtBQUM1QixTQUFPQyxTQUFTQyxnQkFBVCxDQUEwQlIsaUJBQTFCLENBQVA7QUFDQTs7QUFFRCxVQUFTUyx1QkFBVCxDQUFpQ0MsS0FBakMsRUFBd0M7QUFDdkMsU0FBT0EsTUFBTUYsZ0JBQU4sQ0FBdUJOLHFCQUF2QixDQUFQO0FBQ0E7O0FBRUQsVUFBU1MsZ0JBQVQsQ0FBMEJELEtBQTFCLEVBQWlDO0FBQ2hDLFNBQU9BLE1BQU1GLGdCQUFOLENBQXVCTCxhQUF2QixDQUFQO0FBQ0E7O0FBRUQ7QUFDQSxVQUFTUyxjQUFULENBQXdCQyxRQUF4QixFQUFrQ0MsUUFBbEMsRUFBNEM7QUFDM0MsT0FBSyxJQUFJQyxJQUFJLENBQWIsRUFBZ0JBLElBQUlGLFNBQVNHLE1BQTdCLEVBQXFDRCxHQUFyQyxFQUEwQztBQUN6Q0QsWUFBU0QsU0FBU0UsQ0FBVCxDQUFULEVBQXNCQSxDQUF0QjtBQUNBO0FBQ0Q7O0FBRUQ7QUFDQSxVQUFTRSxzQkFBVCxD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QUEzQixDQUFKLEVBQXdDO0FBQ3ZDakIsWUFBUVMsZ0JBQVIsQ0FBeUIsT0FBekIsRUFBa0NvQiwyQkFBMkJmLElBQTNCLENBQWdDLElBQWhDLEVBQXNDdkIsS0FBdEMsQ0FBbEM7QUFDQSxJQUZELE1BRU8sSUFBSVMsUUFBUUUsU0FBUixDQUFrQmUsUUFBbEIsQ0FBMkIsT0FBM0IsQ0FBSixFQUF5QztBQUMvQ2pCLFlBQVFTLGdCQUFSLENBQXlCLE9BQXpCLEVBQWtDa0IsdUJBQXVCYixJQUF2QixDQUE0QixJQUE1QixFQUFrQ3ZCLEtBQWxDLENBQWxDO0FBQ0E7QUFDRCxHQU5EOztBQVFBc0QsU0FBT0MsVUFBUCxDQUFrQmIsbUJBQW1CbkIsSUFBbkIsQ0FBd0IsSUFBeEIsRUFBOEJ2QixLQUE5QixDQUFsQixFQUF3RCxDQUF4RDtBQUNBc0QsU0FBT3BDLGdCQUFQLENBQXdCLFFBQXhCLEVBQWtDd0IsbUJBQW1CbkIsSUFBbkIsQ0FBd0IsSUFBeEIsRUFBOEJ2QixLQUE5QixDQUFsQztBQUNBLE1BQUl3RCxtQkFBbUJ4RCxNQUFNRixnQkFBTixDQUF1QixvQkFBdkIsQ0FBdkI7QUFDQSxNQUFJMkQsZUFBZSxDQUFuQjtBQUNBdkQsaUJBQWVzRCxnQkFBZixFQUFpQyxVQUFVRSxLQUFWLEVBQWlCO0FBQ2pELE9BQUlDLGNBQWMsSUFBSUMsS0FBSixFQUFsQjtBQUNBRCxlQUFZRSxNQUFaLEdBQXFCLFlBQVk7QUFDaENKO0FBQ0EsUUFBSUEsaUJBQWlCRCxpQkFBaUJsRCxNQUF0QyxFQUE4QztBQUM3Q29DLHdCQUFtQjFDLEtBQW5CO0FBQ0E7QUFDRCxJQUxEO0FBTUEyRCxlQUFZRyxHQUFaLEdBQWtCSixNQUFNSyxZQUFOLENBQW1CLEtBQW5CLENBQWxCO0FBQ0EsR0FURDtBQVVBLEVBakREO0FBa0RBLENBakxEIiwiZmlsZSI6ImNhcm91c2VsLmpzIiwic291cmNlc0NvbnRlbnQiOlsiLyogZXNsaW50IG5vLXZhcjogMCwgcHJlZmVyLWNvbnN0OiAwICovXG4ndXNlIHN0cmljdCc7XG5cbihmdW5jdGlvbiAoKSB7XG5cblx0dmFyIENBUk9VU0VMX1NFTEVDVE9SID0gJy5ibG9jay1jb250ZW50LmNhcm91c2VsJztcblx0dmFyIEZBQ0VfV1JBUFBFUl9TRUxFQ1RPUiA9ICcuY2Fyb3VzZWwtZmFjZXMnO1xuXHR2YXIgRkFDRV9DT05UUk9MX1NFTEVDVE9SID0gJy5jYXJvdXNlbC1mYWNlLWNvbnRyb2xzIC5mYWNlLWNvbnRyb2wnO1xuXHR2YXIgRkFDRV9TRUxFQ1RPUiA9IEZBQ0VfV1JBUFBFUl9TRUxFQ1RPUiArICcgLmNhcm91c2VsLWZhY2UnO1xuXHR2YXIgQ1VSUkVOVF9GQUNFX1NFTEVDVE9SID0gRkFDRV9XUkFQUEVSX1NFTEVDVE9SICsgJyAuY3VycmVudCc7XG5cdHZhciBTV0lQRV9USFJFU0hPTEQgPSA1MDtcblxuXHRmdW5jdGlvbiBnZXRDYXJvdXNlbEJsb2NrcygpIHtcblx0XHRyZXR1cm4gZG9jdW1lbnQucXVlcnlTZWxlY3RvckFsbChDQVJPVVNFTF9TRUxFQ1RPUik7XG5cdH1cblxuXHRmdW5jdGlvbiBnZXRDYXJvdXNlbEZhY2VDb250cm9scyhibG9jaykge1xuXHRcdHJldHVybiBibG9jay5xdWVyeVNlbGVjdG9yQWxsKEZBQ0VfQ09OVFJPTF9TRUxFQ1RPUik7XG5cdH1cblxuXHRmdW5jdGlvbiBnZXRDYXJvdXNlbEZhY2VzKGJsb2NrKSB7XG5cdFx0cmV0dXJuIGJsb2NrLnF1ZXJ5U2VsZWN0b3JBbGwoRkFDRV9TRUxFQ1RPUik7XG5cdH1cblxuXHQvLyBSdW4gYSBmdW5jdGlvbiBmb3IgZWFjaCBlbGVtZW50IGluIHRoZSBhcnJheVxuXHRmdW5jdGlvbiBmb3JFYWNoRWxlbWVudChlbGVtZW50cywgY2FsbGJhY2spIHtcblx0XHRmb3IgKHZhciBpID0gMDsgaSA8IGVsZW1lbnRzLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRjYWxsYmFjayhlbGVtZW50c1tpXSwgaSk7XG5cdFx0fVxuXHR9XG5cblx0Ly8gVXBkYXRlIHRoZSBkb3QgY29udHJvbHMgdG8gZGlzcGxheSBuZXdseSBzZWxlY3RlZCBpbmRleFxuXHRmdW5jdGlvbiB1cGRhdGVTZWxlY3RlZENvbnRyb2xzKGJsb2NrLCBzZWxlY3RlZEluZGV4KSB7XG5cdFx0Zm9yRWFjaEVsZW1lbnQoZ2V0Q2Fyb3VzZWxGYWNlQ29udHJvbHMoYmxvY2spLCBmdW5jdGlvbiAoY29udHJvbCwgaW5kZXgpIHtcblx0XHRcdGlmIChpbmRleCA9PT0gc2VsZWN0ZWRJbmRleCkge1xuXHRcdFx0XHRjb250cm9sLmNsYXNzTGlzdC5hZGQoJ3NlbGVjdGVkJyk7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRjb250cm9sLmNsYXNzTGlzdC5yZW1vdmUoJ3NlbGVjdGVkJyk7XG5cdFx0XHR9XG5cdFx0fSk7XG5cdH1cblxuXHQvLyBTZXQgdGhlIHRyYW5zaXRpb25pbmcgY2xhc3Mgb24gdGhlIGZhY2Ugd3JhcHBlciBhbmQgYXR0YWNoIGxpc3RlbmVyIGZvciBpdHMgdHJhbnNpdGlvbmVuZFxuXHRmdW5jdGlvbiBzZXRUcmFuc2l0aW9uU3RhdGUoYmxvY2ssIGN1cnJlbnRGYWNlKSB7XG5cdFx0dmFyIGZhY2VXcmFwcGVyID0gYmxvY2sucXVlcnlTZWxlY3RvcihGQUNFX1dSQVBQRVJfU0VMRUNUT1IpO1xuXHRcdGZhY2VXcmFwcGVyLmNsYXNzTGlzdC5hZGQoJ3RyYW5zaXRpb25pbmcnKTtcblx0XHRjdXJyZW50RmFjZS5hZGRFdmVudExpc3RlbmVyKFxuXHRcdFx0KGN1cnJlbnRGYWNlLnN0eWxlLldlYmtpdFRyYW5zaXRpb24gIT09IHVuZGVmaW5lZCkgPyAnd2Via2l0VHJhbnNpdGlvbkVuZCcgOiAndHJhbnNpdGlvbmVuZCcsXG5cdFx0XHRyZW1vdmVUcmFuc2l0aW9uU3RhdGUuYmluZChudWxsLCBibG9jaykpO1xuXHR9XG5cblx0Ly8gUmVtb3ZlIHRoZSB0cmFuc2l0aW9uIGNsYXNzIGFuZCBldmVudCB3aGVuIHRoZSBhbmltYXRpb24gaGFzIGVuZGVkXG5cdGZ1bmN0aW9uIHJlbW92ZVRyYW5zaXRpb25TdGF0ZShibG9jaywgdHJhbnNpdGlvbkV2ZW50KSB7XG5cdFx0aWYgKCF0cmFuc2l0aW9uRXZlbnQudGFyZ2V0LmNsYXNzTGlzdC5jb250YWlucygnY2Fyb3VzZWwtZmFjZScpKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdHRyYW5zaXRpb25FdmVudC50YXJnZXQucGFyZW50Tm9kZS5jbGFzc0xpc3QucmVtb3ZlKCd0cmFuc2l0aW9uaW5nJyk7XG5cdFx0dHJhbnNpdGlvbkV2ZW50LnRhcmdldC5yZW1vdmVFdmVudExpc3RlbmVyKHRyYW5zaXRpb25FdmVudC50eXBlLCB0aGlzLnJlbW92ZVRyYW5zaXRpb25TdGF0ZSk7XG5cdH1cblxuXHQvLyBSZXR1cm5zIHRoZSBjdXJyZW50bHkgc2VsZWN0ZWQgYmxvY2sgZmFjZSBpbmRleFxuXHRmdW5jdGlvbiBnZXRDdXJyZW50RmFjZUluZGV4KGJsb2NrKSB7XG5cdFx0dmFyIGZhY2VzID0gZ2V0Q2Fyb3VzZWxGYWNlcyhibG9jayk7XG5cdFx0dmFyIGN1cnJlbnRGYWNlID0gYmxvY2sucXVlcnlTZWxlY3RvcihDVVJSRU5UX0ZBQ0VfU0VMRUNUT1IpO1xuXHRcdHJldHVybiBBcnJheS5wcm90b3R5cGUuaW5kZXhPZi5jYWxsKGZhY2VzLCBjdXJyZW50RmFjZSk7XG5cdH1cblxuXHRmdW5jdGlvbiBzZWxlY3ROZXh0Q2Fyb3VzZWxGYWNlKGJsb2NrKSB7XG5cdFx0cmV0dXJuIHNlbGVjdENhcm91c2VsRmFjZShnZXRDdXJyZW50RmFjZUluZGV4KGJsb2NrKSArIDEsIGJsb2NrKTtcblx0fVxuXG5cdGZ1bmN0aW9uIHNlbGVjdFByZXZpb3VzQ2Fyb3VzZWxGYWNlKGJsb2NrKSB7XG5cdFx0cmV0dXJuIHNlbGVjdENhcm91c2VsRmFjZShnZXRDdXJyZW50RmFjZUluZGV4KGJsb2NrKSAtIDEsIGJsb2NrKTtcblx0fVxuXG5cdC8vIEhhbmRsZXMgdGhlIHNlbGVjdGlvbiBvZiBhIGNhcm91c2VsIGZhY2Vcblx0ZnVuY3Rpb24gc2VsZWN0Q2Fyb3VzZWxGYWNlKHNlbGVjdGVkSW5kZXgsIGJsb2NrKSB7XG5cdFx0dmFyIGZhY2VzID0gZ2V0Q2Fyb3VzZWxGYWNlcyhibG9jayk7XG5cdFx0dmFyIHByZXZpb3VzRmFjZSA9IGJsb2NrLnF1ZXJ5U2VsZWN0b3IoQ1VSUkVOVF9GQUNFX1NFTEVDVE9SKTtcblx0XHR2YXIgcHJldmlvdXNJbmRleCA9IEFycmF5LnByb3RvdHlwZS5pbmRleE9mLmNhbGwoZmFjZXMsIHByZXZpb3VzRmFjZSk7XG5cblx0XHQvLyBDeWNsZSB0aHJvdWdoIGZhY2VzIGlmIHdlJ3JlIGF0IHRoZSBlbmRcblx0XHRpZiAoc2VsZWN0ZWRJbmRleCA8IDApIHtcblx0XHRcdHNlbGVjdGVkSW5kZXggPSBmYWNlcy5sZW5ndGggLSAxO1xuXHRcdH0gZWxzZSBpZiAoc2VsZWN0ZWRJbmRleCA+PSBmYWNlcy5sZW5ndGgpIHtcblx0XHRcdHNlbGVjdGVkSW5kZXggPSAwO1xuXHRcdH1cblxuXHRcdHVwZGF0ZVNlbGVjdGVkQ29udHJvbHMoYmxvY2ssIHNlbGVjdGVkSW5kZXgpO1xuXG5cdFx0c2V0VHJhbnNpdGlvblN0YXRlKGJsb2NrLCBmYWNlc1tzZWxlY3RlZEluZGV4XSk7XG5cblx0XHRmb3JFYWNoRWxlbWVudChnZXRDYXJvdXNlbEZhY2VzKGJsb2NrKSwgZnVuY3Rpb24gKGZhY2UsIGluZGV4KSB7XG5cdFx0XHRpZiAoaW5kZXggPT09IHNlbGVjdGVkSW5kZXgpIHtcblx0XHRcdFx0ZmFjZS5jbGFzc0xpc3QuYWRkKCdjdXJyZW50Jyk7XG5cdFx0XHRcdGZhY2UuY2xhc3NMaXN0LnJlbW92ZSgnbGVmdCcpO1xuXHRcdFx0XHRmYWNlLmNsYXNzTGlzdC5yZW1vdmUoJ3JpZ2h0Jyk7XG5cdFx0XHRcdGZhY2UuY2xhc3NMaXN0LnJlbW92ZSgncHJldmlvdXMnKTtcblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGZhY2UuY2xhc3NMaXN0LnJlbW92ZSgnY3VycmVudCcpO1xuXG5cdFx0XHRcdGlmIChpbmRleCA9PT0gcHJldmlvdXNJbmRleCkge1xuXHRcdFx0XHRcdGZhY2UuY2xhc3NMaXN0LmFkZCgncHJldmlvdXMnKTtcblx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHRmYWNlLmNsYXNzTGlzdC5yZW1vdmUoJ3ByZXZpb3VzJyk7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGluZGV4ID4gc2VsZWN0ZWRJbmRleCkge1xuXHRcdFx0XHRcdGZhY2UuY2xhc3NMaXN0LnJlbW92ZSgnbGVmdCcpO1xuXHRcdFx0XHRcdGZhY2UuY2xhc3NMaXN0LmFkZCgncmlnaHQnKTtcblx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHRmYWNlLmNsYXNzTGlzdC5hZGQoJ2xlZnQnKTtcblx0XHRcdFx0XHRmYWNlLmNsYXNzTGlzdC5yZW1vdmUoJ3JpZ2h0Jyk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9KTtcblx0fVxuXG5cdGZ1bmN0aW9uIHNldENvbnRhaW5lckhlaWdodChibG9jaykge1xuXHRcdC8vIFNldCB0aGUgaGVpZ2h0IG9mIHRoZSBmYWNlcyBjb250YWluZXIgdG8gZXF1YWwgdGhlIGhlaWdodCBvZiB0aGUgdGFsbGVzdCBmYWNlXG5cdFx0dmFyIG1heEZhY2VIZWlnaHQgPSAwO1xuXHRcdGZvckVhY2hFbGVtZW50KGJsb2NrLnF1ZXJ5U2VsZWN0b3JBbGwoJy5jYXJvdXNlbC1mYWNlJyksIGZ1bmN0aW9uIChmYWNlKSB7XG5cdFx0XHR2YXIgZmFjZUhlaWdodCA9IGZhY2UuZ2V0Qm91bmRpbmdDbGllbnRSZWN0KCkuaGVpZ2h0O1xuXHRcdFx0aWYgKGZhY2VIZWlnaHQgPiBtYXhGYWNlSGVpZ2h0KSB7XG5cdFx0XHRcdG1heEZhY2VIZWlnaHQgPSBmYWNlSGVpZ2h0O1xuXHRcdFx0fVxuXHRcdH0pO1xuXHRcdGJsb2NrLnF1ZXJ5U2VsZWN0b3IoJy5jYXJvdXNlbC1mYWNlcycpLnN0eWxlLmhlaWdodCA9IG1heEZhY2VIZWlnaHQgKyAncHgnO1xuXHR9XG5cblx0Ly8gSW5pdGlhbGl6ZSBhbGwgdGhlIGxpc3RlbmVycyB3ZSBuZWVkIGZvciBjbGlja2FibGUgZWxlbWVudHNcblx0Zm9yRWFjaEVsZW1lbnQoZ2V0Q2Fyb3VzZWxCbG9ja3MoKSwgZnVuY3Rpb24gKGJsb2NrKSB7XG5cdFx0dmFyIHN3aXBlU3RhcnRYID0gMDtcblxuXHRcdGJsb2NrLmFkZEV2ZW50TGlzdGVuZXIoJ3RvdWNoc3RhcnQnLCBmdW5jdGlvbiAoZXZlbnQpIHtcblx0XHRcdHZhciB0b3VjaEluZm8gPSBldmVudC5jaGFuZ2VkVG91Y2hlc1swXTtcblx0XHRcdHN3aXBlU3RhcnRYID0gdG91Y2hJbmZvLnBhZ2VYO1xuXHRcdH0pO1xuXG5cdFx0YmxvY2suYWRkRXZlbnRMaXN0ZW5lcigndG91Y2hlbmQnLCBmdW5jdGlvbiAoZXZlbnQpIHtcblx0XHRcdHZhciB0b3VjaEluZm8gPSBldmVudC5jaGFuZ2VkVG91Y2hlc1swXTtcblx0XHRcdHZhciBzd2lwZUVuZFggPSB0b3VjaEluZm8ucGFnZVg7XG5cdFx0XHR2YXIgc3dpcGVEaWZmID0gc3dpcGVTdGFydFggLSBzd2lwZUVuZFg7XG5cblx0XHRcdC8vIFN3aXBlIHJpZ2h0XG5cdFx0XHRpZiAoc3dpcGVEaWZmID4gU1dJUEVfVEhSRVNIT0xEKSB7XG5cdFx0XHRcdHNlbGVjdE5leHRDYXJvdXNlbEZhY2UoYmxvY2spO1xuXHRcdFx0fSBlbHNlIGlmIChzd2lwZURpZmYgPCAtMSAqIFNXSVBFX1RIUkVTSE9MRCkge1xuXHRcdFx0XHRzZWxlY3RQcmV2aW91c0Nhcm91c2VsRmFjZShibG9jayk7XG5cdFx0XHR9XG5cdFx0fSk7XG5cblx0XHQvLyBBdHRhY2ggY2xpY2sgbGlzdGVuZXJzIGZvciB0aGUgZG90IGNvbnRyb2xzLlxuXHRcdGZvckVhY2hFbGVtZW50KGdldENhcm91c2VsRmFjZUNvbnRyb2xzKGJsb2NrKSwgZnVuY3Rpb24gKGNvbnRyb2wsIGluZGV4KSB7XG5cdFx0XHRjb250cm9sLmFkZEV2ZW50TGlzdGVuZXIoJ2NsaWNrJywgc2VsZWN0Q2Fyb3VzZWxGYWNlLmJpbmQobnVsbCwgaW5kZXgsIGJsb2NrKSk7XG5cdFx0fSk7XG5cblx0XHQvLyBBdHRhY2ggY2xpY2sgbGlzdG5lcnMgZm9yIHRoZSBzaWRlIGNvbnRyb2xzLlxuXHRcdGZvckVhY2hFbGVtZW50KGJsb2NrLnF1ZXJ5U2VsZWN0b3JBbGwoJy5mYWNlLWNvbnRyb2wtc2lkZScpLCBmdW5jdGlvbiAoY29udHJvbCkge1xuXHRcdFx0aWYgKGNvbnRyb2wuY2xhc3NMaXN0LmNvbnRhaW5zKCdsZWZ0JykpIHtcblx0XHRcdFx0Y29udHJvbC5hZGRFdmVudExpc3RlbmVyKCdjbGljaycsIHNlbGVjdFByZXZpb3VzQ2Fyb3VzZWxGYWNlLmJpbmQobnVsbCwgYmxvY2spKTtcblx0XHRcdH0gZWxzZSBpZiAoY29udHJvbC5jbGFzc0xpc3QuY29udGFpbnMoJ3JpZ2h0JykpIHtcblx0XHRcdFx0Y29udHJvbC5hZGRFdmVudExpc3RlbmVyKCdjbGljaycsIHNlbGVjdE5leHRDYXJvdXNlbEZhY2UuYmluZChudWxsLCBibG9jaykpO1xuXHRcdFx0fVxuXHRcdH0pO1xuXG5cdFx0d2luZG93LnNldFRpbWVvdXQoc2V0Q29udGFpbmVySGVpZ2h0LmJpbmQobnVsbCwgYmxvY2spLCAxKTtcblx0XHR3aW5kb3cuYWRkRXZlbnRMaXN0ZW5lcigncmVzaXplJywgc2V0Q29udGFpbmVySGVpZ2h0LmJpbmQobnVsbCwgYmxvY2spKTtcblx0XHR2YXIgaW1hZ2VzSW5DYXJvdXNlbCA9IGJsb2NrLnF1ZXJ5U2VsZWN0b3JBbGwoJy5jYXJvdXNlbC1mYWNlIGltZycpO1xuXHRcdHZhciBpbWFnZXNMb2FkZWQgPSAwO1xuXHRcdGZvckVhY2hFbGVtZW50KGltYWdlc0luQ2Fyb3VzZWwsIGZ1bmN0aW9uIChpbWFnZSkge1xuXHRcdFx0dmFyIGltYWdlVG9Mb2FkID0gbmV3IEltYWdlKCk7XG5cdFx0XHRpbWFnZVRvTG9hZC5vbmxvYWQgPSBmdW5jdGlvbiAoKSB7XG5cdFx0XHRcdGltYWdlc0xvYWRlZCsrO1xuXHRcdFx0XHRpZiAoaW1hZ2VzTG9hZGVkID09PSBpbWFnZXNJbkNhcm91c2VsLmxlbmd0aCkge1xuXHRcdFx0XHRcdHNldENvbnRhaW5lckhlaWdodChibG9jayk7XG5cdFx0XHRcdH1cblx0XHRcdH07XG5cdFx0XHRpbWFnZVRvTG9hZC5zcmMgPSBpbWFnZS5nZXRBdHRyaWJ1dGUoJ3NyYycpO1xuXHRcdH0pO1xuXHR9KTtcbn0pKCk7XG5cbiJdfQ==

/*********/
'use strict';

/* eslint no-var: 0, prefer-const: 0 */
/* eslint camelcase: 0 */
(function() {

  var PAYPAL_ENDPOINT = 'https://www.paypal.com/cgi-bin/webscr';
  var Money = window.Money;
  var validMoneyRegex = /^\-?\d+\.\d\d$/;

  function Cart() {
      this.items = [];
      this.cartNode = document.getElementsByClassName('shoppingCart')[0];
      this.pipNodes = document.getElementsByClassName('paypal-pip');
      this.business = this.cartNode && this.cartNode.getAttribute('data-publishedjs-merchant-id');
      this.currency = this.cartNode && this.cartNode.getAttribute('data-publishedjs-currency');
      this.currencySymbol = this.cartNode && this.cartNode.getAttribute('data-publishedjs-currency-symbol');

      // abort cart creation in the case of no cart or business
      if (!this.cartNode || !this.business) {
          return false;
      }

      if (typeof window.localStorage !== 'undefined') {
          this.fromJSON(window.localStorage.getItem('shoppingCart'));
      }

      // attach event listeners to payment buttons
      for (var i = 0; i < this.pipNodes.length; i++) {
          var paypalPip = this.pipNodes[i];
          var paypalPipButton = paypalPip.getElementsByClassName('paypal-addToCart')[0];

          paypalPipButton.addEventListener('click', function(event) {
              var item = getItemData(event.target);

              this.addItem(item);

              event.preventDefault();
              return false;
          }.bind(this));
      }

      // attach event listener to cart widget
      var cartHandler = this.cartNode.querySelector('.shoppingCart__openHandler');
      cartHandler.addEventListener('click', this.toggleCartOpen.bind(this));

      var continueShoppingButton = this.cartNode.querySelector('.shoppingCart__button__continue');
      continueShoppingButton.addEventListener('click', this.toggleCartOpen.bind(this));

      var closeButton = this.cartNode.querySelector('.shoppingCart__close');
      closeButton.addEventListener('click', this.toggleCartOpen.bind(this));

      var checkoutButton = this.cartNode.querySelector('.shoppingCart__button__checkout');
      checkoutButton.addEventListener('click', this.checkout.bind(this));

      document.addEventListener('click', function(e) {
          if (this.cartNode.classList.contains('shoppingCart--open') && !this.cartNode.contains(e.target)) {
              this.toggleCartOpen(e);
          }
      }.bind(this));

      this.updateCartContents();
  }

  Cart.prototype.toggleCartOpen = function(event) {
      this.cartNode.classList.toggle('shoppingCart--open');
      document.body.classList.toggle('no-scroll');
      event.preventDefault();
      event.stopPropagation();
      return false;
  };

  Cart.prototype.fromJSON = function(json) {
      if (!json) {
          return;
      }
      if (typeof json === 'string') {
          try {
              json = JSON.parse(json);
          } catch (e) {
              console.error(e);
              return;
          }
      }
      if (json.items) {
          this.items = json.items;
      }
  };

  Cart.prototype.toJSON = function() {
      return {
          items: this.items
      };
  };

  Cart.prototype.addItem = function(item) {

      // If an entry already exists for this item, combine quantity
      var itemExists = false;
      for (var i = 0; i < this.items.length; i++) {
          if (this.items[i].id === item.id) {
              this.items[i].quantity += item.quantity;
              itemExists = true;
              break;
          }
      }

      // Otherwise add entry for item
      if (!itemExists) {
          this.items.push(item);
      }

      this.updateCartContents();
  };

  Cart.prototype.removeItemAtIndex = function(index) {
      this.items.splice(index, 1);
      this.updateCartContents();
  };

  Cart.prototype.isEmpty = function() {
      return this.items.length === 0;
  };

  Cart.prototype.removeAllItems = function() {
      this.items = [];
      this.updateCartContents();
  };

  /*
   * Returns an object that represents the cart and the items in it.
   * The attributes in the object conform directly to the paypal cart upload command:
   * https://developer.paypal.com/docs/classic/paypal-payments-standard/integration-guide/cart_upload/
   */
  Cart.prototype.getCart = function() {
      var cart = this.items.reduce(function(result, item, index) {
          for (var key in item) {
              result[[key, index + 1].join('_')] = item[key];
          }
          return result;
      }, {});

      cart.cmd = '_cart';
      cart.upload = '1';
      cart.business = this.business;
      cart.currency_code = this.currency;

      return cart;
  };

  Cart.prototype.getQuantity = function() {
      return this.items.reduce(function(sum, item) {
          return sum + item.quantity;
      }, 0);
  };

  Cart.prototype.updateCartContents = function() {
      var contentsNode = this.cartNode.querySelector('.shoppingCart__contents');
      if (this.items.length) {
          contentsNode.classList.remove('shoppingCart__contents--empty');
      } else {
          contentsNode.classList.add('shoppingCart__contents--empty');
      }
      var itemsNode = this.cartNode.querySelector('.shoppingCart__items');
      itemsNode.innerHTML = '';
      for (var i = 0; i < this.items.length; i++) {
          var item = this.createItemNode(this.items[i], i);
          itemsNode.appendChild(item);
      }

      var removeButtons = this.cartNode.querySelectorAll('.shoppingCart__item .item-remove');
      for (i = 0; i < removeButtons.length; i++) {
          var button = removeButtons[i];
          button.addEventListener('click', function(e) {
              var itemIndex = e.target.getAttribute('data-item-index');
              this.removeItemAtIndex(itemIndex);
              e.preventDefault();
              e.stopPropagation();
              return false;
          }.bind(this));
      }
      this.updateLabel();
      this.updateTotal();

      if (this.items.length > 0) {
          if (typeof window.localStorage !== 'undefined') {
              window.localStorage.setItem('shoppingCart', JSON.stringify(this.toJSON()));
          }
      } else {
          if (typeof window.localStorage !== 'undefined') {
              window.localStorage.removeItem('shoppingCart');
          }
      }
  };

  Cart.prototype.createItemNode = function(item, index) {
      var totalItemAmount = Money.mul(item.amount, Money.floatToAmount(item.quantity));
      var itemNode = this.cartNode.querySelector('.shoppingCart__item__template').firstChild.cloneNode(true);
      if (item.quantity > 1) {
          itemNode.classList.add('hasQuantity');
          itemNode.querySelector('.item-quantity').innerHTML = item.quantity + ' x ' + this.currencySymbol + Money.format(this.currency_code, item.amount);
      } else {
          var quantityNode = itemNode.querySelector('.item-quantity');
          quantityNode.parentNode.removeChild(quantityNode);
      }
      itemNode.querySelector('.item-name').innerHTML = item.item_name;
      itemNode.querySelector('.item-price').innerHTML = this.currencySymbol + Money.format(this.currency_code, totalItemAmount);
      itemNode.querySelector('.item-remove').setAttribute('data-item-index', index);
      return itemNode;
  };

  Cart.prototype.updateLabel = function() {
      var quantity = this.getQuantity();
      this.cartNode.setAttribute('data-quantity', quantity);

      if (quantity >= 100) {
          this.cartNode.classList.add('shoppingCart--large');
      } else {
          this.cartNode.classList.remove('shoppingCart--large');
      }
  };

  Cart.prototype.updateTotal = function() {
      if (!this.items.length) {
          return;
      }
      var total = this.items.reduce(function(sum, item) {
          return Money.add(Money.floatToAmount(sum), Money.mul(item.amount, Money.floatToAmount(item.quantity)));
      }, 0);
      var totalNode = this.cartNode.querySelector('.shoppingCart__total .total-amount');
      totalNode.innerHTML = this.currencySymbol + Money.format(this.currency_code, total);
  };

  Cart.prototype.checkout = function(event) {
      if (this.isEmpty()) {
          return false;
      }

      post(PAYPAL_ENDPOINT, this.getCart());
      this.removeAllItems();
      event.preventDefault();
      return false;
  };

  /*
   *  Ensure that the amount is in the format xx.xx
   * This is a requirement for the money-math library.
   */
  function getMoneyAmount(value) {
      if (!value || value.match(validMoneyRegex)) {
          return value;
      }
      value = parseFloat(value);
      return Money.floatToAmount(value);
  }

  function getItemData(element) {
      return {
          id: element.getAttribute('data-publishedjs-id'),
          item_name: element.getAttribute('data-publishedjs-item-name'),
          amount: getMoneyAmount(element.getAttribute('data-publishedjs-amount')),
          shipping: getMoneyAmount(element.getAttribute('data-publishedjs-shipping')),
          tax: getMoneyAmount(element.getAttribute('data-publishedjs-tax')),
          quantity: parseInt(element.getAttribute('data-publishedjs-quantity'), 10)
      };
  }

  function post(path, params) {
      var form = document.createElement('form');
      form.setAttribute('method', 'post');
      form.setAttribute('target', '_blank');
      if (path) {
          form.setAttribute('action', path);
      }

      for (var key in params) {
          var name = key;
          var value = params[key];
          var hiddenField = document.createElement('input');
          hiddenField.setAttribute('type', 'hidden');
          hiddenField.setAttribute('name', name);
          hiddenField.setAttribute('value', value);
          form.appendChild(hiddenField);
      }

      document.body.appendChild(form);
      form.submit();
  }

  new Cart();
})();
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIi4uLy4uLy4uLy4uL3NyYy9tYXNvbi9zY3JpcHQvcHVibGljLXNjcmlwdC9wYXlwYWxDYXJ0LmpzIl0sIm5hbWVzIjpbIlBBWVBBTF9FTkRQT0lOVCIsIk1vbmV5Iiwid2luZG93IiwidmFsaWRNb25leVJlZ2V4IiwiQ2FydCIsIml0ZW1zIiwiY2FydE5vZGUiLCJkb2N1bWVudCIsImdldEVsZW1lbnRzQnlDbGFzc05hbWUiLCJwaXBOb2RlcyIsImJ1c2luZXNzIiwiZ2V0QXR0cmlidXRlIiwiY3VycmVuY3kiLCJjdXJyZW5jeVN5bWJvbCIsImxvY2FsU3RvcmFnZSIsImZyb21KU09OIiwiZ2V0SXRlbSIsImkiLCJsZW5ndGgiLCJwYXlwYWxQaXAiLCJwYXlwYWxQaXBCdXR0b24iLCJhZGRFdmVudExpc3RlbmVyIiwiZXZlbnQiLCJpdGVtIiwiZ2V0SXRlbURhdGEiLCJ0YXJnZXQiLCJhZGRJdGVtIiwicHJldmVudERlZmF1bHQiLCJiaW5kIiwiY2FydEhhbmRsZXIiLCJxdWVyeVNlbGVjdG9yIiwidG9nZ2xlQ2FydE9wZW4iLCJjb250aW51ZVNob3BwaW5nQnV0dG9uIiwiY2xvc2VCdXR0b24iLCJjaGVja291dEJ1dHRvbiIsImNoZWNrb3V0IiwiZSIsImNsYXNzTGlzdCIsImNvbnRhaW5zIiwidXBkYXRlQ2FydENvbnRlbnRzIiwicHJvdG90eXBlIiwidG9nZ2xlIiwiYm9keSIsInN0b3BQcm9wYWdhdGlvbiIsImpzb24iLCJKU09OIiwicGFyc2UiLCJjb25zb2xlIiwiZXJyb3IiLCJ0b0pTT04iLCJpdGVtRXhpc3RzIiwiaWQiLCJxdWFudGl0eSIsInB1c2giLCJyZW1vdmVJdGVtQXRJbmRleCIsImluZGV4Iiwic3BsaWNlIiwiaXNFbXB0eSIsInJlbW92ZUFsbEl0ZW1zIiwiZ2V0Q2FydCIsImNhcnQiLCJyZWR1Y2UiLCJyZXN1bHQiLCJrZXkiLCJqb2luIiwiY21kIiwidXBsb2FkIiwiY3VycmVuY3lfY29kZSIsImdldFF1YW50aXR5Iiwic3VtIiwiY29udGVudHNOb2RlIiwicmVtb3ZlIiwiYWRkIiwiaXRlbXNOb2RlIiwiaW5uZXJIVE1MIiwiY3JlYXRlSXRlbU5vZGUiLCJhcHBlbmRDaGlsZCIsInJlbW92ZUJ1dHRvbnMiLCJxdWVyeVNlbGVjdG9yQWxsIiwiYnV0dG9uIiwiaXRlbUluZGV4IiwidXBkYXRlTGFiZWwiLCJ1cGRhdGVUb3RhbCIsInNldEl0ZW0iLCJzdHJpbmdpZnkiLCJyZW1vdmVJdGVtIiwidG90YWxJdGVtQW1vdW50IiwibXVsIiwiYW1vdW50IiwiZmxvYXRUb0Ftb3VudCIsIml0ZW1Ob2RlIiwiZmlyc3RDaGlsZCIsImNsb25lTm9kZSIsImZvcm1hdCIsInF1YW50aXR5Tm9kZSIsInBhcmVudE5vZGUiLCJyZW1vdmVDaGlsZCIsIml0ZW1fbmFtZSIsInNldEF0dHJpYnV0ZSIsInRvdGFsIiwidG90YWxOb2RlIiwicG9zdCIsImdldE1vbmV5QW1vdW50IiwidmFsdWUiLCJtYXRjaCIsInBhcnNlRmxvYXQiLCJlbGVtZW50Iiwic2hpcHBpbmciLCJ0YXgiLCJwYXJzZUludCIsInBhdGgiLCJwYXJhbXMiLCJmb3JtIiwiY3JlYXRlRWxlbWVudCIsIm5hbWUiLCJoaWRkZW5GaWVsZCIsInN1Ym1pdCJdLCJtYXBwaW5ncyI6Ijs7QUFBQTtBQUNBO0FBQ0EsQ0FBQyxZQUFZOztBQUVaLEtBQUlBLGtCQUFrQix1Q0FBdEI7QUFDQSxLQUFJQyxRQUFRQyxPQUFPRCxLQUFuQjtBQUNBLEtBQUlFLGtCQUFrQixnQkFBdEI7O0FBRUEsVUFBU0MsSUFBVCxHQUFnQjtBQUNmLE9BQUtDLEtBQUwsR0FBYSxFQUFiO0FBQ0EsT0FBS0MsUUFBTCxHQUFnQkMsU0FBU0Msc0JBQVQsQ0FBZ0MsY0FBaEMsRUFBZ0QsQ0FBaEQsQ0FBaEI7QUFDQSxPQUFLQyxRQUFMLEdBQWdCRixTQUFTQyxzQkFBVCxDQUFnQyxZQUFoQyxDQUFoQjtBQUNBLE9BQUtFLFFBQUwsR0FBZ0IsS0FBS0osUUFBTCxJQUFpQixLQUFLQSxRQUFMLENBQWNLLFlBQWQsQ0FBMkIs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LFdBQUwsQ0FBaUJ1QyxXQUFqQjtBQUNBOztBQUVENUcsV0FBU21DLElBQVQsQ0FBY2tDLFdBQWQsQ0FBMEJvQyxJQUExQjtBQUNBQSxPQUFLSSxNQUFMO0FBQ0E7O0FBRUQsS0FBSWhILElBQUo7QUFDQSxDQWxTRCIsImZpbGUiOiJwYXlwYWxDYXJ0LmpzIiwic291cmNlc0NvbnRlbnQiOlsiLyogZXNsaW50IG5vLXZhcjogMCwgcHJlZmVyLWNvbnN0OiAwICovXG4vKiBlc2xpbnQgY2FtZWxjYXNlOiAwICovXG4oZnVuY3Rpb24gKCkge1xuXG5cdHZhciBQQVlQQUxfRU5EUE9JTlQgPSAnaHR0cHM6Ly93d3cucGF5cGFsLmNvbS9jZ2ktYmluL3dlYnNjcic7XG5cdHZhciBNb25leSA9IHdpbmRvdy5Nb25leTtcblx0dmFyIHZhbGlkTW9uZXlSZWdleCA9IC9eXFwtP1xcZCtcXC5cXGRcXGQkLztcblxuXHRmdW5jdGlvbiBDYXJ0KCkge1xuXHRcdHRoaXMuaXRlbXMgPSBbXTtcblx0XHR0aGlzLmNhcnROb2RlID0gZG9jdW1lbnQuZ2V0RWxlbWVudHNCeUNsYXNzTmFtZSgnc2hvcHBpbmdDYXJ0JylbMF07XG5cdFx0dGhpcy5waXBOb2RlcyA9IGRvY3VtZW50LmdldEVsZW1lbnRzQnlDbGFzc05hbWUoJ3BheXBhbC1waXAnKTtcblx0XHR0aGlzLmJ1c2luZXNzID0gdGhpcy5jYXJ0Tm9kZSAmJiB0aGlzLmNhcnROb2RlLmdldEF0dHJpYnV0ZSgnZGF0YS1wdWJsaXNoZWRqcy1tZXJjaGFudC1pZCcpO1xuXHRcdHRoaXMuY3VycmVuY3kgPSB0aGlzLmNhcnROb2RlICYmIHRoaXMuY2FydE5vZGUuZ2V0QXR0cmlidXRlKCdkYXRhLXB1Ymxpc2hlZGpzLWN1cnJlbmN5Jyk7XG5cdFx0dGhpcy5jdXJyZW5jeVN5bWJvbCA9IHRoaXMuY2FydE5vZGUgJiYgdGhpcy5jYXJ0Tm9kZS5nZXRBdHRyaWJ1dGUoJ2RhdGEtcHVibGlzaGVkanMtY3VycmVuY3ktc3ltYm9sJyk7XG5cblx0XHQvLyBhYm9ydCBjYXJ0IGNyZWF0aW9uIGluIHRoZSBjYXNlIG9mIG5vIGNhcnQgb3IgYnVzaW5lc3Ncblx0XHRpZiAoIXRoaXMuY2FydE5vZGUgfHwgIXRoaXMuYnVzaW5lc3MpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cblx0XHRpZiAodHlwZW9mIHdpbmRvdy5sb2NhbFN0b3JhZ2UgIT09ICd1bmRlZmluZWQnKSB7XG5cdFx0XHR0aGlzLmZyb21KU09OKHdpbmRvdy5sb2NhbFN0b3JhZ2UuZ2V0SXRlbSgnc2hvcHBpbmdDYXJ0JykpO1xuXHRcdH1cblxuXHRcdC8vIGF0dGFjaCBldmVudCBsaXN0ZW5lcnMgdG8gcGF5bWVudCBidXR0b25zXG5cdFx0Zm9yICh2YXIgaSA9IDA7IGkgPCB0aGlzLnBpcE5vZGVzLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHR2YXIgcGF5cGFsUGlwID0gdGhpcy5waXBOb2Rlc1tpXTtcblx0XHRcdHZhciBwYXlwYWxQaXBCdXR0b24gPSBwYXlwYWxQaXAuZ2V0RWxlbWVudHNCeUNsYXNzTmFtZSgncGF5cGFsLWFkZFRvQ2FydCcpWzBdO1xuXG5cdFx0XHRwYXlwYWxQaXBCdXR0b24uYWRkRXZlbnRMaXN0ZW5lcignY2xpY2snLCBmdW5jdGlvbiAoZXZlbnQpIHtcblx0XHRcdFx0dmFyIGl0ZW0gPSBnZXRJdGVtRGF0YShldmVudC50YXJnZXQpO1xuXG5cdFx0XHRcdHRoaXMuYWRkSXRlbShpdGVtKTtcblxuXHRcdFx0XHRldmVudC5wcmV2ZW50RGVmYXVsdCgpO1xuXHRcdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0XHR9LmJpbmQodGhpcykpO1xuXHRcdH1cblxuXHRcdC8vIGF0dGFjaCBldmVudCBsaXN0ZW5lciB0byBjYXJ0IHdpZGdldFxuXHRcdHZhciBjYXJ0SGFuZGxlciA9IHRoaXMuY2FydE5vZGUucXVlcnlTZWxlY3RvcignLnNob3BwaW5nQ2FydF9fb3BlbkhhbmRsZXInKTtcblx0XHRjYXJ0SGFuZGxlci5hZGRFdmVudExpc3RlbmVyKCdjbGljaycsIHRoaXMudG9nZ2xlQ2FydE9wZW4uYmluZCh0aGlzKSk7XG5cblx0XHR2YXIgY29udGludWVTaG9wcGluZ0J1dHRvbiA9IHRoaXMuY2FydE5vZGUucXVlcnlTZWxlY3RvcignLnNob3BwaW5nQ2FydF9fYnV0dG9uX19jb250aW51ZScpO1xuXHRcdGNvbnRpbnVlU2hvcHBpbmdCdXR0b24uYWRkRXZlbnRMaXN0ZW5lcignY2xpY2snLCB0aGlzLnRvZ2dsZUNhcnRPcGVuLmJpbmQodGhpcykpO1xuXG5cdFx0dmFyIGNsb3NlQnV0dG9uID0gdGhpcy5jYXJ0Tm9kZS5xdWVyeVNlbGVjdG9yKCcuc2hvcHBpbmdDYXJ0X19jbG9zZScpO1xuXHRcdGNsb3NlQnV0dG9uLmFkZEV2ZW50TGlzdGVuZXIoJ2NsaWNrJywgdGhpcy50b2dnbGVDYXJ0T3Blbi5iaW5kKHRoaXMpKTtcblxuXHRcdHZhciBjaGVja291dEJ1dHRvbiA9IHRoaXMuY2FydE5vZGUucXVlcnlTZWxlY3RvcignLnNob3BwaW5nQ2FydF9fYnV0dG9uX19jaGVja291dCcpO1xuXHRcdGNoZWNrb3V0QnV0dG9uLmFkZEV2ZW50TGlzdGVuZXIoJ2NsaWNrJywgdGhpcy5jaGVja291dC5iaW5kKHRoaXMpKTtcblxuXHRcdGRvY3VtZW50LmFkZEV2ZW50TGlzdGVuZXIoJ2NsaWNrJywgZnVuY3Rpb24gKGUpIHtcblx0XHRcdGlmICh0aGlzLmNhcnROb2RlLmNsYXNzTGlzdC5jb250YWlucygnc2hvcHBpbmdDYXJ0LS1vcGVuJykgJiYgIXRoaXMuY2FydE5vZGUuY29udGFpbnMoZS50YXJnZXQpKSB7XG5cdFx0XHRcdHRoaXMudG9nZ2xlQ2FydE9wZW4oZSk7XG5cdFx0XHR9XG5cdFx0fS5iaW5kKHRoaXMpKTtcblxuXHRcdHRoaXMudXBkYXRlQ2FydENvbnRlbnRzKCk7XG5cdH1cblxuXHRDYXJ0LnByb3RvdHlwZS50b2dnbGVDYXJ0T3BlbiA9IGZ1bmN0aW9uIChldmVudCkge1xuXHRcdHRoaXMuY2FydE5vZGUuY2xhc3NMaXN0LnRvZ2dsZSgnc2hvcHBpbmdDYXJ0LS1vcGVuJyk7XG5cdFx0ZG9jdW1lbnQuYm9keS5jbGFzc0xpc3QudG9nZ2xlKCduby1zY3JvbGwnKTtcblx0XHRldmVudC5wcmV2ZW50RGVmYXVsdCgpO1xuXHRcdGV2ZW50LnN0b3BQcm9wYWdhdGlvbigpO1xuXHRcdHJldHVybiBmYWxzZTtcblx0fTtcblxuXHRDYXJ0LnByb3RvdHlwZS5mcm9tSlNPTiA9IGZ1bmN0aW9uIChqc29uKSB7XG5cdFx0aWYgKCFqc29uKSB7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGlmICh0eXBlb2YganNvbiA9PT0gJ3N0cmluZycpIHtcblx0XHRcdHRyeSB7XG5cdFx0XHRcdGpzb24gPSBKU09OLnBhcnNlKGpzb24pO1xuXHRcdFx0fSBjYXRjaCAoZSkge1xuXHRcdFx0XHRjb25zb2xlLmVycm9yKGUpO1xuXHRcdFx0XHRyZXR1cm47XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGlmIChqc29uLml0ZW1zKSB7XG5cdFx0XHR0aGlzLml0ZW1zID0ganNvbi5pdGVtcztcblx0XHR9XG5cdH07XG5cblx0Q2FydC5wcm90b3R5cGUudG9KU09OID0gZnVuY3Rpb24gKCkge1xuXHRcdHJldHVybiB7XG5cdFx0XHRpdGVtczogdGhpcy5pdGVtcyxcblx0XHR9O1xuXHR9O1xuXG5cdENhcnQucHJvdG90eXBlLmFkZEl0ZW0gPSBmdW5jdGlvbiAoaXRlbSkge1xuXG5cdFx0Ly8gSWYgYW4gZW50cnkgYWxyZWFkeSBleGlzdHMgZm9yIHRoaXMgaXRlbSwgY29tYmluZSBxdWFudGl0eVxuXHRcdHZhciBpdGVtRXhpc3RzID0gZmFsc2U7XG5cdFx0Zm9yICh2YXIgaSA9IDA7IGkgPCB0aGlzLml0ZW1zLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRpZiAodGhpcy5pdGVtc1tpXS5pZCA9PT0gaXRlbS5pZCkge1xuXHRcdFx0XHR0aGlzLml0ZW1zW2ldLnF1YW50aXR5ICs9IGl0ZW0ucXVhbnRpdHk7XG5cdFx0XHRcdGl0ZW1FeGlzdHMgPSB0cnVlO1xuXHRcdFx0XHRicmVhaztcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBPdGhlcndpc2UgYWRkIGVudHJ5IGZvciBpdGVtXG5cdFx0aWYgKCFpdGVtRXhpc3RzKSB7XG5cdFx0XHR0aGlzLml0ZW1zLnB1c2goaXRlbSk7XG5cdFx0fVxuXG5cdFx0dGhpcy51cGRhdGVDYXJ0Q29udGVudHMoKTtcblx0fTtcblxuXHRDYXJ0LnByb3RvdHlwZS5yZW1vdmVJdGVtQXRJbmRleCA9IGZ1bmN0aW9uIChpbmRleCkge1xuXHRcdHRoaXMuaXRlbXMuc3BsaWNlKGluZGV4LCAxKTtcblx0XHR0aGlzLnVwZGF0ZUNhcnRDb250ZW50cygpO1xuXHR9O1xuXG5cdENhcnQucHJvdG90eXBlLmlzRW1wdHkgPSBmdW5jdGlvbiAoKSB7XG5cdFx0cmV0dXJuIHRoaXMuaXRlbXMubGVuZ3RoID09PSAwO1xuXHR9O1xuXG5cdENhcnQucHJvdG90eXBlLnJlbW92ZUFsbEl0ZW1zID0gZnVuY3Rpb24gKCkge1xuXHRcdHRoaXMuaXRlbXMgPSBbXTtcblx0XHR0aGlzLnVwZGF0ZUNhcnRDb250ZW50cygpO1xuXHR9O1xuXG5cdC8qXG5cdCAqIFJldHVybnMgYW4gb2JqZWN0IHRoYXQgcmVwcmVzZW50cyB0aGUgY2FydCBhbmQgdGhlIGl0ZW1zIGluIGl0LlxuXHQgKiBUaGUgYXR0cmlidXRlcyBpbiB0aGUgb2JqZWN0IGNvbmZvcm0gZGlyZWN0bHkgdG8gdGhlIHBheXBhbCBjYXJ0IHVwbG9hZCBjb21tYW5kOlxuXHQgKiBodHRwczovL2RldmVsb3Blci5wYXlwYWwuY29tL2RvY3MvY2xhc3NpYy9wYXlwYWwtcGF5bWVudHMtc3RhbmRhcmQvaW50ZWdyYXRpb24tZ3VpZGUvY2FydF91cGxvYWQvXG5cdCAqL1xuXHRDYXJ0LnByb3RvdHlwZS5nZXRDYXJ0ID0gZnVuY3Rpb24gKCkge1xuXHRcdHZhciBjYXJ0ID0gdGhpcy5pdGVtcy5yZWR1Y2UoZnVuY3Rpb24gKHJlc3VsdCwgaXRlbSwgaW5kZXgpIHtcblx0XHRcdGZvciAodmFyIGtleSBpbiBpdGVtKSB7XG5cdFx0XHRcdHJlc3VsdFtba2V5LCBpbmRleCArIDFdLmpvaW4oJ18nKV0gPSBpdGVtW2tleV07XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH0sIHt9KTtcblxuXHRcdGNhcnQuY21kID0gJ19jYXJ0Jztcblx0XHRjYXJ0LnVwbG9hZCA9ICcxJztcblx0XHRjYXJ0LmJ1c2luZXNzID0gdGhpcy5idXNpbmVzcztcblx0XHRjYXJ0LmN1cnJlbmN5X2NvZGUgPSB0aGlzLmN1cnJlbmN5O1xuXG5cdFx0cmV0dXJuIGNhcnQ7XG5cdH07XG5cblx0Q2FydC5wcm90b3R5cGUuZ2V0UXVhbnRpdHkgPSBmdW5jdGlvbiAoKSB7XG5cdFx0cmV0dXJuIHRoaXMuaXRlbXMucmVkdWNlKGZ1bmN0aW9uIChzdW0sIGl0ZW0pIHtcblx0XHRcdHJldHVybiBzdW0gKyBpdGVtLnF1YW50aXR5O1xuXHRcdH0sIDApO1xuXHR9O1xuXG5cdENhcnQucHJvdG90eXBlLnVwZGF0ZUNhcnRDb250ZW50cyA9IGZ1bmN0aW9uICgpIHtcblx0XHR2YXIgY29udGVudHNOb2RlID0gdGhpcy5jYXJ0Tm9kZS5xdWVyeVNlbGVjdG9yKCcuc2hvcHBpbmdDYXJ0X19jb250ZW50cycpO1xuXHRcdGlmICh0aGlzLml0ZW1zLmxlbmd0aCkge1xuXHRcdFx0Y29udGVudHNOb2RlLmNsYXNzTGlzdC5yZW1vdmUoJ3Nob3BwaW5nQ2FydF9fY29udGVudHMtLWVtcHR5Jyk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdGNvbnRlbnRzTm9kZS5jbGFzc0xpc3QuYWRkKCdzaG9wcGluZ0NhcnRfX2NvbnRlbnRzLS1lbXB0eScpO1xuXHRcdH1cblx0XHR2YXIgaXRlbXNOb2RlID0gdGhpcy5jYXJ0Tm9kZS5xdWVyeVNlbGVjdG9yKCcuc2hvcHBpbmdDYXJ0X19pdGVtcycpO1xuXHRcdGl0ZW1zTm9kZS5pbm5lckhUTUwgPSAnJztcblx0XHRmb3IgKHZhciBpID0gMDsgaSA8IHRoaXMuaXRlbXMubGVuZ3RoOyBpKyspIHtcblx0XHRcdHZhciBpdGVtID0gdGhpcy5jcmVhdGVJdGVtTm9kZSh0aGlzLml0ZW1zW2ldLCBpKTtcblx0XHRcdGl0ZW1zTm9kZS5hcHBlbmRDaGlsZChpdGVtKTtcblx0XHR9XG5cblx0XHR2YXIgcmVtb3ZlQnV0dG9ucyA9IHRoaXMuY2FydE5vZGUucXVlcnlTZWxlY3RvckFsbCgnLnNob3BwaW5nQ2FydF9faXRlbSAuaXRlbS1yZW1vdmUnKTtcblx0XHRmb3IgKGkgPSAwOyBpIDwgcmVtb3ZlQnV0dG9ucy5sZW5ndGg7IGkrKykge1xuXHRcdFx0dmFyIGJ1dHRvbiA9IHJlbW92ZUJ1dHRvbnNbaV07XG5cdFx0XHRidXR0b24uYWRkRXZlbnRMaXN0ZW5lcignY2xpY2snLCBmdW5jdGlvbiAoZSkge1xuXHRcdFx0XHR2YXIgaXRlbUluZGV4ID0gZS50YXJnZXQuZ2V0QXR0cmlidXRlKCdkYXRhLWl0ZW0taW5kZXgnKTtcblx0XHRcdFx0dGhpcy5yZW1vdmVJdGVtQXRJbmRleChpdGVtSW5kZXgpO1xuXHRcdFx0XHRlLnByZXZlbnREZWZhdWx0KCk7XG5cdFx0XHRcdGUuc3RvcFByb3BhZ2F0aW9uKCk7XG5cdFx0XHRcdHJldHVybiBmYWxzZTtcblx0XHRcdH0uYmluZCh0aGlzKSk7XG5cdFx0fVxuXHRcdHRoaXMudXBkYXRlTGFiZWwoKTtcblx0XHR0aGlzLnVwZGF0ZVRvdGFsKCk7XG5cblx0XHRpZiAodGhpcy5pdGVtcy5sZW5ndGggPiAwKSB7XG5cdFx0XHRpZiAodHlwZW9mIHdpbmRvdy5sb2NhbFN0b3JhZ2UgIT09ICd1bmRlZmluZWQnKSB7XG5cdFx0XHRcdHdpbmRvdy5sb2NhbFN0b3JhZ2Uuc2V0SXRlbSgnc2hvcHBpbmdDYXJ0JywgSlNPTi5zdHJpbmdpZnkodGhpcy50b0pTT04oKSkpO1xuXHRcdFx0fVxuXHRcdH0gZWxzZSB7XG5cdFx0XHRpZiAodHlwZW9mIHdpbmRvdy5sb2NhbFN0b3JhZ2UgIT09ICd1bmRlZmluZWQnKSB7XG5cdFx0XHRcdHdpbmRvdy5sb2NhbFN0b3JhZ2UucmVtb3ZlSXRlbSgnc2hvcHBpbmdDYXJ0Jyk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9O1xuXG5cdENhcnQucHJvdG90eXBlLmNyZWF0ZUl0ZW1Ob2RlID0gZnVuY3Rpb24gKGl0ZW0sIGluZGV4KSB7XG5cdFx0dmFyIHRvdGFsSXRlbUFtb3VudCA9IE1vbmV5Lm11bChpdGVtLmFtb3VudCwgTW9uZXkuZmxvYXRUb0Ftb3VudChpdGVtLnF1YW50aXR5KSk7XG5cdFx0dmFyIGl0ZW1Ob2RlID0gdGhpcy5jYXJ0Tm9kZS5xdWVyeVNlbGVjdG9yKCcuc2hvcHBpbmdDYXJ0X19pdGVtX190ZW1wbGF0ZScpLmZpcnN0Q2hpbGQuY2xvbmVOb2RlKHRydWUpO1xuXHRcdGlmIChpdGVtLnF1YW50aXR5ID4gMSkge1xuXHRcdFx0aXRlbU5vZGUuY2xhc3NMaXN0LmFkZCgnaGFzUXVhbnRpdHknKTtcblx0XHRcdGl0ZW1Ob2RlLnF1ZXJ5U2VsZWN0b3IoJy5pdGVtLXF1YW50aXR5JykuaW5uZXJIVE1MID0gaXRlbS5xdWFudGl0eSArICcgeCAnICtcblx0XHRcdFx0dGhpcy5jdXJyZW5jeVN5bWJvbCArXG5cdFx0XHRcdE1vbmV5LmZvcm1hdCh0aGlzLmN1cnJlbmN5X2NvZGUsIGl0ZW0uYW1vdW50KTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0dmFyIHF1YW50aXR5Tm9kZSA9IGl0ZW1Ob2RlLnF1ZXJ5U2VsZWN0b3IoJy5pdGVtLXF1YW50aXR5Jyk7XG5cdFx0XHRxdWFudGl0eU5vZGUucGFyZW50Tm9kZS5yZW1vdmVDaGlsZChxdWFudGl0eU5vZGUpO1xuXHRcdH1cblx0XHRpdGVtTm9kZS5xdWVyeVNlbGVjdG9yKCcuaXRlbS1uYW1lJykuaW5uZXJIVE1MID0gaXRlbS5pdGVtX25hbWU7XG5cdFx0aXRlbU5vZGUucXVlcnlTZWxlY3RvcignLml0ZW0tcHJpY2UnKS5pbm5lckhUTUwgPSB0aGlzLmN1cnJlbmN5U3ltYm9sICtcblx0XHRcdE1vbmV5LmZvcm1hdCh0aGlzLmN1cnJlbmN5X2NvZGUsIHRvdGFsSXRlbUFtb3VudCk7XG5cdFx0aXRlbU5vZGUucXVlcnlTZWxlY3RvcignLml0ZW0tcmVtb3ZlJykuc2V0QXR0cmlidXRlKCdkYXRhLWl0ZW0taW5kZXgnLCBpbmRleCk7XG5cdFx0cmV0dXJuIGl0ZW1Ob2RlO1xuXHR9O1xuXG5cdENhcnQucHJvdG90eXBlLnVwZGF0ZUxhYmVsID0gZnVuY3Rpb24gKCkge1xuXHRcdHZhciBxdWFudGl0eSA9IHRoaXMuZ2V0UXVhbnRpdHkoKTtcblx0XHR0aGlzLmNhcnROb2RlLnNldEF0dHJpYnV0ZSgnZGF0YS1xdWFudGl0eScsIHF1YW50aXR5KTtcblxuXHRcdGlmIChxdWFudGl0eSA+PSAxMDApIHtcblx0XHRcdHRoaXMuY2FydE5vZGUuY2xhc3NMaXN0LmFkZCgnc2hvcHBpbmdDYXJ0LS1sYXJnZScpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHR0aGlzLmNhcnROb2RlLmNsYXNzTGlzdC5yZW1vdmUoJ3Nob3BwaW5nQ2FydC0tbGFyZ2UnKTtcblx0XHR9XG5cdH07XG5cblx0Q2FydC5wcm90b3R5cGUudXBkYXRlVG90YWwgPSBmdW5jdGlvbiAoKSB7XG5cdFx0aWYgKCF0aGlzLml0ZW1zLmxlbmd0aCkge1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHR2YXIgdG90YWwgPSB0aGlzLml0ZW1zLnJlZHVjZShmdW5jdGlvbiAoc3VtLCBpdGVtKSB7XG5cdFx0XHRyZXR1cm4gTW9uZXkuYWRkKE1vbmV5LmZsb2F0VG9BbW91bnQoc3VtKSxcblx0XHRcdFx0TW9uZXkubXVsKGl0ZW0uYW1vdW50LCBNb25leS5mbG9hdFRvQW1vdW50KGl0ZW0ucXVhbnRpdHkpKSk7XG5cdFx0fSwgMCk7XG5cdFx0dmFyIHRvdGFsTm9kZSA9IHRoaXMuY2FydE5vZGUucXVlcnlTZWxlY3RvcignLnNob3BwaW5nQ2FydF9fdG90YWwgLnRvdGFsLWFtb3VudCcpO1xuXHRcdHRvdGFsTm9kZS5pbm5lckhUTUwgPSB0aGlzLmN1cnJlbmN5U3ltYm9sICsgTW9uZXkuZm9ybWF0KHRoaXMuY3VycmVuY3lfY29kZSwgdG90YWwpO1xuXHR9O1xuXG5cdENhcnQucHJvdG90eXBlLmNoZWNrb3V0ID0gZnVuY3Rpb24gKGV2ZW50KSB7XG5cdFx0aWYgKHRoaXMuaXNFbXB0eSgpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0cG9zdChQQVlQQUxfRU5EUE9JTlQsIHRoaXMuZ2V0Q2FydCgpKTtcblx0XHR0aGlzLnJlbW92ZUFsbEl0ZW1zKCk7XG5cdFx0ZXZlbnQucHJldmVudERlZmF1bHQoKTtcblx0XHRyZXR1cm4gZmFsc2U7XG5cdH07XG5cblx0Lypcblx0ICogIEVuc3VyZSB0aGF0IHRoZSBhbW91bnQgaXMgaW4gdGhlIGZvcm1hdCB4eC54eFxuXHQgKiBUaGlzIGlzIGEgcmVxdWlyZW1lbnQgZm9yIHRoZSBtb25leS1tYXRoIGxpYnJhcnkuXG5cdCAqL1xuXHRmdW5jdGlvbiBnZXRNb25leUFtb3VudCh2YWx1ZSkge1xuXHRcdGlmICghdmFsdWUgfHwgdmFsdWUubWF0Y2godmFsaWRNb25leVJlZ2V4KSkge1xuXHRcdFx0cmV0dXJuIHZhbHVlO1xuXHRcdH1cblx0XHR2YWx1ZSA9IHBhcnNlRmxvYXQodmFsdWUpO1xuXHRcdHJldHVybiBNb25leS5mbG9hdFRvQW1vdW50KHZhbHVlKTtcblx0fVxuXG5cdGZ1bmN0aW9uIGdldEl0ZW1EYXRhKGVsZW1lbnQpIHtcblx0XHRyZXR1cm4ge1xuXHRcdFx0aWQ6IGVsZW1lbnQuZ2V0QXR0cmlidXRlKCdkYXRhLXB1Ymxpc2hlZGpzLWlkJyksXG5cdFx0XHRpdGVtX25hbWU6IGVsZW1lbnQuZ2V0QXR0cmlidXRlKCdkYXRhLXB1Ymxpc2hlZGpzLWl0ZW0tbmFtZScpLFxuXHRcdFx0YW1vdW50OiBnZXRNb25leUFtb3VudChlbGVtZW50LmdldEF0dHJpYnV0ZSgnZGF0YS1wdWJsaXNoZWRqcy1hbW91bnQnKSksXG5cdFx0XHRzaGlwcGluZzogZ2V0TW9uZXlBbW91bnQoZWxlbWVudC5nZXRBdHRyaWJ1dGUoJ2RhdGEtcHVibGlzaGVkanMtc2hpcHBpbmcnKSksXG5cdFx0XHR0YXg6IGdldE1vbmV5QW1vdW50KGVsZW1lbnQuZ2V0QXR0cmlidXRlKCdkYXRhLXB1Ymxpc2hlZGpzLXRheCcpKSxcblx0XHRcdHF1YW50aXR5OiBwYXJzZUludChlbGVtZW50LmdldEF0dHJpYnV0ZSgnZGF0YS1wdWJsaXNoZWRqcy1xdWFudGl0eScpLCAxMCksXG5cdFx0fTtcblx0fVxuXG5cdGZ1bmN0aW9uIHBvc3QocGF0aCwgcGFyYW1zKSB7XG5cdFx0dmFyIGZvcm0gPSBkb2N1bWVudC5jcmVhdGVFbGVtZW50KCdmb3JtJyk7XG5cdFx0Zm9ybS5zZXRBdHRyaWJ1dGUoJ21ldGhvZCcsICdwb3N0Jyk7XG5cdFx0Zm9ybS5zZXRBdHRyaWJ1dGUoJ3RhcmdldCcsICdfYmxhbmsnKTtcblx0XHRpZiAocGF0aCkge1xuXHRcdFx0Zm9ybS5zZXRBdHRyaWJ1dGUoJ2FjdGlvbicsIHBhdGgpO1xuXHRcdH1cblxuXHRcdGZvciAodmFyIGtleSBpbiBwYXJhbXMpIHtcblx0XHRcdHZhciBuYW1lID0ga2V5O1xuXHRcdFx0dmFyIHZhbHVlID0gcGFyYW1zW2tleV07XG5cdFx0XHR2YXIgaGlkZGVuRmllbGQgPSBkb2N1bWVudC5jcmVhdGVFbGVtZW50KCdpbnB1dCcpO1xuXHRcdFx0aGlkZGVuRmllbGQuc2V0QXR0cmlidXRlKCd0eXBlJywgJ2hpZGRlbicpO1xuXHRcdFx0aGlkZGVuRmllbGQuc2V0QXR0cmlidXRlKCduYW1lJywgbmFtZSk7XG5cdFx0XHRoaWRkZW5GaWVsZC5zZXRBdHRyaWJ1dGUoJ3ZhbHVlJywgdmFsdWUpO1xuXHRcdFx0Zm9ybS5hcHBlbmRDaGlsZChoaWRkZW5GaWVsZCk7XG5cdFx0fVxuXG5cdFx0ZG9jdW1lbnQuYm9keS5hcHBlbmRDaGlsZChmb3JtKTtcblx0XHRmb3JtLnN1Ym1pdCgpO1xuXHR9XG5cblx0bmV3IENhcnQoKTtcbn0pKCk7XG4iXX0=

/*********/
/* eslint no-var: 0, prefer-const: 0 */
'use strict';

(function() {
  function toggleMenuClasses() {
      var mobileContent = document.querySelector('.mobile-content');

      document.body.classList.toggle('no-scroll');
      document.body.classList.toggle('mobile-menu-active');
      mobileContent.classList.toggle('active');
  }

  function handleMenuClick(event) {
      if (event) {
          event.preventDefault();
          event.stopPropagation();
      }

      toggleMenuClasses();
  }

  function setUpButtonHandler() {

      // Set header z-index to be higher permanently at the block level
      // This guarantees that the overlay will be above all other site content
      // By changing its stacking context
      var headerBlock = document.querySelector('.is-position-top');

      if (headerBlock) {
          headerBlock.style.zIndex = '10';
      }

      var menuButton = document.querySelectorAll('.pip.navigation-pip .mobile-menu-button');

      for (var m = 0; m < menuButton.length; m++) {
          menuButton[m].onclick = handleMenuClick;
      }

      var navLinks = document.querySelectorAll('.mobile-wrapper a');

      for (var i = 0; i < navLinks.length; i++) {
          // Only apply a click handler to internal block links
          if (navLinks[i].getAttribute('href').indexOf('#') === 0) {
              navLinks[i].addEventListener('click', toggleMenuClasses);
          }
      }
  }

  setUpButtonHandler();
})();
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIi4uLy4uLy4uLy4uL3NyYy9tYXNvbi9zY3JpcHQvcHVibGljLXNjcmlwdC9uYXZpZ2F0aW9uLmpzIl0sIm5hbWVzIjpbInRvZ2dsZU1lbnVDbGFzc2VzIiwibW9iaWxlQ29udGVudCIsImRvY3VtZW50IiwicXVlcnlTZWxlY3RvciIsImJvZHkiLCJjbGFzc0xpc3QiLCJ0b2dnbGUiLCJoYW5kbGVNZW51Q2xpY2siLCJldmVudCIsInByZXZlbnREZWZhdWx0Iiwic3RvcFByb3BhZ2F0aW9uIiwic2V0VXBCdXR0b25IYW5kbGVyIiwiaGVhZGVyQmxvY2siLCJzdHlsZSIsInpJbmRleCIsIm1lbnVCdXR0b24iLCJxdWVyeVNlbGVjdG9yQWxsIiwibSIsImxlbmd0aCIsIm9uY2xpY2siLCJuYXZMaW5rcyIsImkiLCJnZXRBdHRyaWJ1dGUiLCJpbmRleE9mIiwiYWRkRXZlbnRMaXN0ZW5lciJdLCJtYXBwaW5ncyI6IkFBQUE7QUFDQTs7QUFFQSxDQUFDLFlBQVk7QUFDWixVQUFTQSxpQkFBVCxHQUE2QjtBQUM1QixNQUFJQyxnQkFBZ0JDLFNBQVNDLGFBQVQsQ0FBdUIsaUJBQXZCLENBQXBCOztBQUVBRCxXQUFTRSxJQUFULENBQWNDLFNBQWQsQ0FBd0JDLE1BQXhCLENBQStCLFdBQS9CO0FBQ0FKLFdBQVNFLElBQVQsQ0FBY0MsU0FBZCxDQUF3QkMsTUFBeEIsQ0FBK0Isb0JBQS9CO0FBQ0FMLGdCQUFjSSxTQUFkLENBQXdCQyxNQUF4QixDQUErQixRQUEvQjtBQUNBOztBQUVELFVBQVNDLGVBQVQsQ0FBeUJDLEtBQXpCLEVBQWdDO0FBQy9CLE1BQUlBLEtBQUosRUFBVztBQUNWQSxTQUFNQyxjQUFOO0FBQ0FELFNBQU1FLGVBQU47QUFDQTs7QUFFRFY7QUFDQTs7QUFFRCxVQUFTVyxrQkFBVCxHQUE4Qjs7QUFFN0I7QUFDQTtBQUNBO0FBQ0EsTUFBSUMsY0FBY1YsU0FBU0MsYUFBVCxDQUF1QixrQkFBdkIsQ0FBbEI7O0FBRUEsTUFBSVMsV0FBSixFQUFpQjtBQUNoQkEsZUFBWUMsS0FBWixDQUFrQkMsTUFBbEIsR0FBMkIsSUFBM0I7QUFDQTs7QUFFRCxNQUFJQyxhQUFhYixTQUFTYyxnQkFBVCxDQUNoQix5Q0FEZ0IsQ0FBakI7O0FBSUEsT0FBSyxJQUFJQyxJQUFJLENBQWIsRUFBZ0JBLElBQUlGLFdBQVdHLE1BQS9CLEVBQXVDRCxHQUF2QyxFQUE0QztBQUMzQ0YsY0FBV0UsQ0FBWCxFQUFjRSxPQUFkLEdBQXdCWixlQUF4QjtBQUNBOztBQUVELE1BQUlhLFdBQVdsQixTQUFTYyxnQkFBVCxDQUEwQixtQkFBMUIsQ0FBZjs7QUFFQSxPQUFLLElBQUlLLElBQUksQ0FBYixFQUFnQkEsSUFBSUQsU0FBU0YsTUFBN0IsRUFBcUNHLEdBQXJDLEVBQTBDO0FBQ3pDO0FBQ0EsT0FBSUQsU0FBU0MsQ0FBVCxFQUFZQyxZQUFaLENBQXlCLE1BQXpCLEVBQWlDQyxPQUFqQyxDQUF5QyxHQUF6QyxNQUFrRCxDQUF0RCxFQUF5RDtBQUN4REgsYUFBU0MsQ0FBVCxFQUFZRyxnQkFBWixDQUE2QixPQUE3QixFQUFzQ3hCLGlCQUF0QztBQUNBO0FBQ0Q7QUFDRDs7QUFFRFc7QUFDQSxDQWhERCIsImZpbGUiOiJuYXZpZ2F0aW9uLmpzIiwic291cmNlc0NvbnRlbnQiOlsiLyogZXNsaW50IG5vLXZhcjogMCwgcHJlZmVyLWNvbnN0OiAwICovXG4ndXNlIHN0cmljdCc7XG5cbihmdW5jdGlvbiAoKSB7XG5cdGZ1bmN0aW9uIHRvZ2dsZU1lbnVDbGFzc2VzKCkge1xuXHRcdHZhciBtb2JpbGVDb250ZW50ID0gZG9jdW1lbnQucXVlcnlTZWxlY3RvcignLm1vYmlsZS1jb250ZW50Jyk7XG5cblx0XHRkb2N1bWVudC5ib2R5LmNsYXNzTGlzdC50b2dnbGUoJ25vLXNjcm9sbCcpO1xuXHRcdGRvY3VtZW50LmJvZHkuY2xhc3NMaXN0LnRvZ2dsZSgnbW9iaWxlLW1lbnUtYWN0aXZlJyk7XG5cdFx0bW9iaWxlQ29udGVudC5jbGFzc0xpc3QudG9nZ2xlKCdhY3RpdmUnKTtcblx0fVxuXG5cdGZ1bmN0aW9uIGhhbmRsZU1lbnVDbGljayhldmVudCkge1xuXHRcdGlmIChldmVudCkge1xuXHRcdFx0ZXZlbnQucHJldmVudERlZmF1bHQoKTtcblx0XHRcdGV2ZW50LnN0b3BQcm9wYWdhdGlvbigpO1xuXHRcdH1cblxuXHRcdHRvZ2dsZU1lbnVDbGFzc2VzKCk7XG5cdH1cblxuXHRmdW5jdGlvbiBzZXRVcEJ1dHRvbkhhbmRsZXIoKSB7XG5cblx0XHQvLyBTZXQgaGVhZGVyIHotaW5kZXggdG8gYmUgaGlnaGVyIHBlcm1hbmVudGx5IGF0IHRoZSBibG9jayBsZXZlbFxuXHRcdC8vIFRoaXMgZ3VhcmFudGVlcyB0aGF0IHRoZSBvdmVybGF5IHdpbGwgYmUgYWJvdmUgYWxsIG90aGVyIHNpdGUgY29udGVudFxuXHRcdC8vIEJ5IGNoYW5naW5nIGl0cyBzdGFja2luZyBjb250ZXh0XG5cdFx0dmFyIGhlYWRlckJsb2NrID0gZG9jdW1lbnQucXVlcnlTZWxlY3RvcignLmlzLXBvc2l0aW9uLXRvcCcpO1xuXG5cdFx0aWYgKGhlYWRlckJsb2NrKSB7XG5cdFx0XHRoZWFkZXJCbG9jay5zdHlsZS56SW5kZXggPSAnMTAnO1xuXHRcdH1cblxuXHRcdHZhciBtZW51QnV0dG9uID0gZG9jdW1lbnQucXVlcnlTZWxlY3RvckFsbChcblx0XHRcdCcucGlwLm5hdmlnYXRpb24tcGlwIC5tb2JpbGUtbWVudS1idXR0b24nXG5cdFx0KTtcblxuXHRcdGZvciAodmFyIG0gPSAwOyBtIDwgbWVudUJ1dHRvbi5sZW5ndGg7IG0rKykge1xuXHRcdFx0bWVudUJ1dHRvblttXS5vbmNsaWNrID0gaGFuZGxlTWVudUNsaWNrO1xuXHRcdH1cblxuXHRcdHZhciBuYXZMaW5rcyA9IGRvY3VtZW50LnF1ZXJ5U2VsZWN0b3JBbGwoJy5tb2JpbGUtd3JhcHBlciBhJyk7XG5cblx0XHRmb3IgKHZhciBpID0gMDsgaSA8IG5hdkxpbmtzLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHQvLyBPbmx5IGFwcGx5IGEgY2xpY2sgaGFuZGxlciB0byBpbnRlcm5hbCBibG9jayBsaW5rc1xuXHRcdFx0aWYgKG5hdkxpbmtzW2ldLmdldEF0dHJpYnV0ZSgnaHJlZicpLmluZGV4T2YoJyMnKSA9PT0gMCkge1xuXHRcdFx0XHRuYXZMaW5rc1tpXS5hZGRFdmVudExpc3RlbmVyKCdjbGljaycsIHRvZ2dsZU1lbnVDbGFzc2VzKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHRzZXRVcEJ1dHRvbkhhbmRsZXIoKTtcbn0pKCk7XG4iXX0=

/*********/
/* eslint no-var: 0, prefer-const: 0 */

'use strict';

function shouldDockRight(elm) {
  if (!elm) {
      return false;
  }
  var rect = elm.getBoundingClientRect();
  var elmWidth = rect.width;
  var elmLeft = rect.left;

  return elmWidth + elmLeft > window.pageXOffset + window.innerWidth;
}

function positionChildNav(elm) {
  if (shouldDockRight(elm)) {
      elm.classList.add('nav-children--right');
  }
}

function applyPositionToSubnav(elm) {
  if (elm.tagName === 'LI' && elm.classList.contains('link')) {
      return positionChildNav(elm.querySelector('.nav-children'));
  } else if (elm.parentNode) {
      // recursively call to check if the parent node is `li.link`
      return applyPositionToSubnav(elm.parentNode);
  }
}

function handleSubnavEvent(event) {
  applyPositionToSubnav(event.target);
}

function setupSubNavPositioningEventHandlers() {
  var desktopLinkList = document.querySelector('.desktopLinks');

  if (!desktopLinkList) {
      return;
  }

  desktopLinkList.addEventListener('mouseover', handleSubnavEvent);
  desktopLinkList.addEventListener('click', handleSubnavEvent);

  var topLevelLinks = document.querySelectorAll('.desktopLinks > li > a');

  if (!topLevelLinks) {
      return;
  }

  for (var i = 0; i < topLevelLinks.length; i++) {
      topLevelLinks[i].addEventListener('focus', handleSubnavEvent);
  }
}

// only execute when in preview or publish mode
if (typeof window !== 'undefined' && window.towerData === undefined) {
  setupSubNavPositioningEventHandlers();
}

if (typeof module !== 'undefined') {
  module.exports = {
      shouldDockRight: shouldDockRight
  };
}
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIi4uLy4uLy4uLy4uL3NyYy9tYXNvbi9zY3JpcHQvcHVibGljLXNjcmlwdC9zdWJuYXYuanMiXSwibmFtZXMiOlsic2hvdWxkRG9ja1JpZ2h0IiwiZWxtIiwicmVjdCIsImdldEJvdW5kaW5nQ2xpZW50UmVjdCIsImVsbVdpZHRoIiwid2lkdGgiLCJlbG1MZWZ0IiwibGVmdCIsIndpbmRvdyIsInBhZ2VYT2Zmc2V0IiwiaW5uZXJXaWR0aCIsInBvc2l0aW9uQ2hpbGROYXYiLCJjbGFzc0xpc3QiLCJhZGQiLCJhcHBseVBvc2l0aW9uVG9TdWJuYXYiLCJ0YWdOYW1lIiwiY29udGFpbnMiLCJxdWVyeVNlbGVjdG9yIiwicGFyZW50Tm9kZSIsImhhbmRsZVN1Ym5hdkV2ZW50IiwiZXZlbnQiLCJ0YXJnZXQiLCJzZXR1cFN1Yk5hdlBvc2l0aW9uaW5nRXZlbnRIYW5kbGVycyIsImRlc2t0b3BMaW5rTGlzdCIsImRvY3VtZW50IiwiYWRkRXZlbnRMaXN0ZW5lciIsInRvcExldmVsTGlua3MiLCJxdWVyeVNlbGVjdG9yQWxsIiwiaSIsImxlbmd0aCIsInRvd2VyRGF0YSIsInVuZGVmaW5lZCIsIm1vZHVsZSIsImV4cG9ydHMiXSwibWFwcGluZ3MiOiJBQUFBOztBQUVBOztBQUVBLFNBQVNBLGVBQVQsQ0FBeUJDLEdBQXpCLEVBQThCO0FBQzdCLEtBQUksQ0FBQ0EsR0FBTCxFQUFVO0FBQ1QsU0FBTyxLQUFQO0FBQ0E7QUFDRCxLQUFJQyxPQUFPRCxJQUFJRSxxQkFBSixFQUFYO0FBQ0EsS0FBSUMsV0FBV0YsS0FBS0csS0FBcEI7QUFDQSxLQUFJQyxVQUFVSixLQUFLSyxJQUFuQjs7QUFFQSxRQUFTSCxXQUFXRSxPQUFaLEdBQXdCRSxPQUFPQyxXQUFQLEdBQXFCRCxPQUFPRSxVQUE1RDtBQUNBOztBQUVELFNBQVNDLGdCQUFULENBQTBCVixHQUExQixFQUErQjtBQUM5QixLQUFJRCxnQkFBZ0JDLEdBQWhCLENBQUosRUFBMEI7QUFDekJBLE1BQUlXLFNBQUosQ0FBY0MsR0FBZCxDQUFrQixxQkFBbEI7QUFDQTtBQUNEOztBQUVELFNBQVNDLHFCQUFULENBQStCYixHQUEvQixFQUFvQztBQUNuQyxLQUFJQSxJQUFJYyxPQUFKLEtBQWdCLElBQWhCLElBQXdCZCxJQUFJVyxTQUFKLENBQWNJLFFBQWQsQ0FBdUIsTUFBdkIsQ0FBNUIsRUFBNEQ7QUFDM0QsU0FBT0wsaUJBQWlCVixJQUFJZ0IsYUFBSixDQUFrQixlQUFsQixDQUFqQixDQUFQO0FBQ0EsRUFGRCxNQUVPLElBQUloQixJQUFJaUIsVUFBUixFQUFvQjtBQUMxQjtBQUNBLFNBQU9KLHNCQUFzQmIsSUFBSWlCLFVBQTFCLENBQVA7QUFDQTtBQUNEOztBQUVELFNBQVNDLGlCQUFULENBQTJCQyxLQUEzQixFQUFrQztBQUNqQ04sdUJBQXNCTSxNQUFNQyxNQUE1QjtBQUNBOztBQUVELFNBQVNDLG1DQUFULEdBQStDO0FBQzlDLEtBQUlDLGtCQUFrQkMsU0FBU1AsYUFBVCxDQUF1QixlQUF2QixDQUF0Qjs7QUFFQSxLQUFJLENBQUNNLGVBQUwsRUFBc0I7QUFDckI7QUFDQTs7QUFFREEsaUJBQWdCRSxnQkFBaEIsQ0FBaUMsV0FBakMsRUFBOENOLGlCQUE5QztBQUNBSSxpQkFBZ0JFLGdCQUFoQixDQUFpQyxPQUFqQyxFQUEwQ04saUJBQTFDOztBQUVBLEtBQUlPLGdCQUFnQkYsU0FBU0csZ0JBQVQsQ0FBMEIsd0JBQTFCLENBQXBCOztBQUVBLEtBQUksQ0FBQ0QsYUFBTCxFQUFvQjtBQUNuQjtBQUNBOztBQUVELE1BQUssSUFBSUUsSUFBSSxDQUFiLEVBQWdCQSxJQUFJRixjQUFjRyxNQUFsQyxFQUEwQ0QsR0FBMUMsRUFBK0M7QUFDOUNGLGdCQUFjRSxDQUFkLEVBQWlCSCxnQkFBakIsQ0FBa0MsT0FBbEMsRUFBMkNOLGlCQUEzQztBQUNBO0FBQ0Q7O0FBRUQ7QUFDQSxJQUFJLE9BQU9YLE1BQVAsS0FBa0IsV0FBbEIsSUFBaUNBLE9BQU9zQixTQUFQLEtBQXFCQyxTQUExRCxFQUFxRTtBQUNwRVQ7QUFDQTs7QUFFRCxJQUFJLE9BQU9VLE1BQVAsS0FBa0IsV0FBdEIsRUFBbUM7QUFDbENBLFFBQU9DLE9BQVAsR0FBaUI7QUFDaEJqQztBQURnQixFQUFqQjtBQUdBIiwiZmlsZSI6InN1Ym5hdi5qcyIsInNvdXJjZXNDb250ZW50IjpbIi8qIGVzbGludCBuby12YXI6IDAsIHByZWZlci1jb25zdDogMCAqL1xuXG4ndXNlIHN0cmljdCc7XG5cbmZ1bmN0aW9uIHNob3VsZERvY2tSaWdodChlbG0pIHtcblx0aWYgKCFlbG0pIHtcblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblx0dmFyIHJlY3QgPSBlbG0uZ2V0Qm91bmRpbmdDbGllbnRSZWN0KCk7XG5cdHZhciBlbG1XaWR0aCA9IHJlY3Qud2lkdGg7XG5cdHZhciBlbG1MZWZ0ID0gcmVjdC5sZWZ0O1xuXG5cdHJldHVybiAoKGVsbVdpZHRoICsgZWxtTGVmdCkgPiAod2luZG93LnBhZ2VYT2Zmc2V0ICsgd2luZG93LmlubmVyV2lkdGgpKTtcbn1cblxuZnVuY3Rpb24gcG9zaXRpb25DaGlsZE5hdihlbG0pIHtcblx0aWYgKHNob3VsZERvY2tSaWdodChlbG0pKSB7XG5cdFx0ZWxtLmNsYXNzTGlzdC5hZGQoJ25hdi1jaGlsZHJlbi0tcmlnaHQnKTtcblx0fVxufVxuXG5mdW5jdGlvbiBhcHBseVBvc2l0aW9uVG9TdWJuYXYoZWxtKSB7XG5cdGlmIChlbG0udGFnTmFtZSA9PT0gJ0xJJyAmJiBlbG0uY2xhc3NMaXN0LmNvbnRhaW5zKCdsaW5rJykpIHtcblx0XHRyZXR1cm4gcG9zaXRpb25DaGlsZE5hdihlbG0ucXVlcnlTZWxlY3RvcignLm5hdi1jaGlsZHJlbicpKTtcblx0fSBlbHNlIGlmIChlbG0ucGFyZW50Tm9kZSkge1xuXHRcdC8vIHJlY3Vyc2l2ZWx5IGNhbGwgdG8gY2hlY2sgaWYgdGhlIHBhcmVudCBub2RlIGlzIGBsaS5saW5rYFxuXHRcdHJldHVybiBhcHBseVBvc2l0aW9uVG9TdWJuYXYoZWxtLnBhcmVudE5vZGUpO1xuXHR9XG59XG5cbmZ1bmN0aW9uIGhhbmRsZVN1Ym5hdkV2ZW50KGV2ZW50KSB7XG5cdGFwcGx5UG9zaXRpb25Ub1N1Ym5hdihldmVudC50YXJnZXQpO1xufVxuXG5mdW5jdGlvbiBzZXR1cFN1Yk5hdlBvc2l0aW9uaW5nRXZlbnRIYW5kbGVycygpIHtcblx0dmFyIGRlc2t0b3BMaW5rTGlzdCA9IGRvY3VtZW50LnF1ZXJ5U2VsZWN0b3IoJy5kZXNrdG9wTGlua3MnKTtcblxuXHRpZiAoIWRlc2t0b3BMaW5rTGlzdCkge1xuXHRcdHJldHVybjtcblx0fVxuXG5cdGRlc2t0b3BMaW5rTGlzdC5hZGRFdmVudExpc3RlbmVyKCdtb3VzZW92ZXInLCBoYW5kbGVTdWJuYXZFdmVudCk7XG5cdGRlc2t0b3BMaW5rTGlzdC5hZGRFdmVudExpc3RlbmVyKCdjbGljaycsIGhhbmRsZVN1Ym5hdkV2ZW50KTtcblxuXHR2YXIgdG9wTGV2ZWxMaW5rcyA9IGRvY3VtZW50LnF1ZXJ5U2VsZWN0b3JBbGwoJy5kZXNrdG9wTGlua3MgPiBsaSA+IGEnKTtcblxuXHRpZiAoIXRvcExldmVsTGlua3MpIHtcblx0XHRyZXR1cm47XG5cdH1cblxuXHRmb3IgKHZhciBpID0gMDsgaSA8IHRvcExldmVsTGlua3MubGVuZ3RoOyBpKyspIHtcblx0XHR0b3BMZXZlbExpbmtzW2ldLmFkZEV2ZW50TGlzdGVuZXIoJ2ZvY3VzJywgaGFuZGxlU3VibmF2RXZlbnQpO1xuXHR9XG59XG5cbi8vIG9ubHkgZXhlY3V0ZSB3aGVuIGluIHByZXZpZXcgb3IgcHVibGlzaCBtb2RlXG5pZiAodHlwZW9mIHdpbmRvdyAhPT0gJ3VuZGVmaW5lZCcgJiYgd2luZG93LnRvd2VyRGF0YSA9PT0gdW5kZWZpbmVkKSB7XG5cdHNldHVwU3ViTmF2UG9zaXRpb25pbmdFdmVudEhhbmRsZXJzKCk7XG59XG5cbmlmICh0eXBlb2YgbW9kdWxlICE9PSAndW5kZWZpbmVkJykge1xuXHRtb2R1bGUuZXhwb3J0cyA9IHtcblx0XHRzaG91bGREb2NrUmlnaHQsXG5cdH07XG59XG4iXX0=

/*********/
var tower = {
  "document": {
      "documentStyle": {
          "backgroundColor": "#f05867",
          "colorPalette": {
              "colors": {
                  "color1": {
                      "name": "Custom1",
                      "value": "#f05867"
                  },
                  "color2": {
                      "name": "Custom2",
                      "value": "#7cccbf"
                  },
                  "color3": {
                      "name": "Custom3",
                      "value": "#ffffff"
                  },
                  "color4": {
                      "name": "Default - White",
                      "value": "#ffffff"
                  },
                  "color5": {
                      "name": "Default - Black",
                      "value": "#333333"
                  }
              },
              "name": "Custom",
              "slug": "custom",
              "recommended": true,
              "matchingDefault": false
          },
          "customColorPalette": ["#f05867", "#7cccbf", "#ffffff"],
          "fontPack": {
              "fontSizes": {
                  "fontSize1": {
                      "name": "Smallest",
                      "value": "60%"
                  },
                  "fontSize2": {
                      "name": "Smaller",
                      "value": "80%"
                  },
                  "fontSize3": {
                      "name": "Normal",
                      "value": "100%"
                  },
                  "fontSize4": {
                      "name": "Larger",
                      "value": "120%"
                  },
                  "fontSize5": {
                      "name": "Largest",
                      "value": "140%"
                  }
              },
              "fonts": {
                  "font1": {
                      "name": "Josefin Sans",
                      "value": "Josefin Sans"
                  },
                  "font2": {
                      "name": "Josefin Sans",
                      "value": "Josefin Sans"
                  }
              },
              "imports": {
                  "google": ["Josefin Sans", "Josefin Sans"]
              },
              "name": "Josefin Sans & Josefin Sans",
              "slug": "josefin_sans_josefin_sans",
              "recommended": true
          },
          "width": "1100px",
          "align": "center",
          "buttonStyle": {
              "radius": "square",
              "style": "flat"
          }
      },
      "headerBlock": {
          "slug": "header-matched",
          "assets": [{
              "propertyPath": ["displayName"],
              "assetPath": ["displayName"]
          }, {
              "propertyPath": ["props", "background"],
              "assetPath": ["blockBackground"]
          }, {
              "propertyPath": ["props", "userHeight"],
              "assetPath": ["userHeight"]
          }],
          "props": {
              "hidden": true,
              "className": "cover shadow-2",
              "type": "header",
              "nameable": true,
              "name": "",
              "moveable": false,
              "disableTopResizing": true,
              "position": "top",
              "background": {
                  "color": {
                      "value": "color3",
                      "opacity": 0
                  },
                  "image": {
                      "url": "https://assets.digital.vistaprint.com/production/5fde27bf-5ce7-4332-9ae3-df00da82cd7c"
                  },
                  "tags": ["printBackground"],
                  "contentBinding": {
                      "name": "headerBackgroundImage",
                      "source": "page"
                  },
                  "imageTransparency": true,
                  "backgroundType": "image"
              },
              "instanceLess": "",
              "layouts": null
          },
          "children": [{
              "pip": "row",
              "props": {
                  "className": "mb0 mb5-l",
                  "uid": "ee6d73a7c5a7413ab628eb029b927961",
                  "backgroundOpacity": 1
              },
              "children": [{
                  "pip": "col",
                  "children": [{
                      "pip": "row",
                      "props": {
                          "className": "justify-center",
                          "uid": "ec91f45498b7438586ac2467283eb531",
                          "backgroundOpacity": 1
                      },
                      "children": [{
                          "pip": "navigation",
                          "assets": [{
                              "propertyPath": ["props", "linkColor"],
                              "assetPath": ["navigation", "bodyTextColor"]
                          }],
                          "props": {
                              "defaultFontSize": "fontSize4",
                              "defaultFont": "font2",
                              "mobileMenu": "tablet",
                              "linkColor": "color2",
                              "uid": "7ab4c3405ceb42149a677162bb33a766",
                              "defaultColor": "color4",
                              "isRelative": false,
                              "adjustableMobileMenuColor": false
                          }
                      }]
                  }],
                  "props": {
                      "uid": "323e90405c5f49acaa3a77cc47923d21"
                  }
              }]
          }, {
              "pip": "group",
              "props": {
                  "className": "content-group",
                  "uid": "927276f0f21049268104226add015ea8",
                  "backgroundOpacity": 1
              },
              "children": [{
                  "pip": "row",
                  "props": {
                      "className": "brand-icon-row",
                      "hideable": true,
                      "uid": "5a94de1bf71a43c5868d9e1414e0ece1",
                      "backgroundOpacity": 1
                  },
                  "assets": [{
                      "propertyPath": ["props", "hidden"],
                      "assetPath": ["row", "0", "hidden"]
                  }],
                  "children": [{
                      "pip": "logo",
                      "assets": [{
                          "propertyPath": ["props", "logoMode"],
                          "assetPath": ["logos", "0", "mode"]
                      }],
                      "props": {
                          "className": "f1",
                          "level": 5,
                          "defaultFont": "font1",
                          "defaultFontSize": "fontSize3",
                          "homeLink": true,
                          "layout": "centerStacked",
                          "contentBinding": {
                              "name": "headerLogoMode",
                              "source": "site"
                          },
                          "logoMode": "textOnly",
                          "uid": "9cc140400ef343058aea26918c049a53"
                      },
                      "children": [{
                          "pip": "graphic",
                          "assets": [{
                              "propertyPath": ["props"],
                              "assetPath": ["logos", "0", "graphics", "0"]
                          }],
                          "props": {
                              "svgdata": "<svg xmlns:x=\"http://ns.adobe.com/Extensibility/1.0/\" xmlns:i=\"http://ns.adobe.com/AdobeIllustrator/10.0/\" xmlns:graph=\"http://ns.adobe.com/Graphs/1.0/\" xmlns=\"http://www.w3.org/2000/svg\" xmlns:xlink=\"http://www.w3.org/1999/xlink\" version=\"1.1\" x=\"0px\" y=\"0px\" viewBox=\"0 0 100 100\" enable-background=\"new 0 0 100 100\" xml:space=\"preserve\"><switch><foreignObject requiredExtensions=\"http://ns.adobe.com/AdobeIllustrator/10.0/\" x=\"0\" y=\"0\" width=\"1\" height=\"1\"></foreignObject><g i:extraneous=\"self\"><g><path d=\"M94.503,7.95c-0.045-0.027-0.092-0.051-0.14-0.072c-0.141-0.062-0.295-0.097-0.459-0.097H88.32     c-0.166,0-0.323,0.037-0.465,0.099c-0.049,0.022-0.097,0.046-0.142,0.074c-0.163,0.099-0.299,0.234-0.397,0.397L50.563,45.104     L38.394,32.934c1.992-2.935,3.065-6.395,3.065-10.02c0-0.066-0.004-0.132-0.005-0.198c0.001-0.083,0.005-0.167,0.005-0.25     c0-4.779-1.861-9.273-5.241-12.652s-7.873-5.241-12.652-5.241s-9.272,1.861-12.652,5.241c-3.379,3.379-5.241,7.873-5.241,12.652     c0,0.075,0.004,0.149,0.005,0.224c-0.001,0.075-0.005,0.149-0.005,0.224c0,4.779,1.861,9.272,5.241,12.652     c3.38,3.38,7.873,5.241,12.652,5.241c3.791,0,7.398-1.175,10.416-3.345l12.111,12.111L33.982,61.685     c-3.018-2.17-6.625-3.345-10.416-3.345c-4.779,0-9.272,1.861-12.652,5.241c-3.379,3.379-5.241,7.873-5.241,12.652     c0,0.075,0.004,0.149,0.005,0.224c-0.001,0.075-0.005,0.149-0.005,0.224c0,4.78,1.861,9.273,5.241,12.652     c3.38,3.379,7.873,5.241,12.652,5.241s9.273-1.861,12.652-5.241s5.241-7.873,5.241-12.652c0-0.083-0.003-0.167-0.005-0.25     c0.001-0.066,0.005-0.131,0.005-0.198c0-3.625-1.073-7.084-3.065-10.02l12.169-12.169l36.752,36.752     c0.099,0.163,0.234,0.298,0.397,0.397c0.045,0.028,0.093,0.052,0.142,0.074c0.142,0.063,0.299,0.099,0.465,0.099h5.584     c0.164,0,0.318-0.036,0.459-0.097c0.048-0.021,0.095-0.045,0.14-0.072c0.345-0.206,0.579-0.578,0.579-1.009v-0.034v0     c0-0.011-0.003-0.022-0.003-0.033c0.009-0.298-0.097-0.599-0.325-0.827l-39.72-39.72l39.72-39.72     c0.228-0.228,0.334-0.528,0.325-0.827c0-0.011,0.003-0.022,0.003-0.033v0V8.959C95.082,8.528,94.848,8.156,94.503,7.95z      M23.566,36.468c-7.474,0-13.554-6.081-13.554-13.553c0-7.473,6.08-13.554,13.554-13.554c7.473,0,13.554,6.081,13.554,13.554     C37.12,30.387,31.04,36.468,23.566,36.468z M23.566,90.234c-7.474,0-13.554-6.081-13.554-13.554s6.08-13.554,13.554-13.554     c7.473,0,13.554,6.081,13.554,13.554S31.04,90.234,23.566,90.234z\"></path></g></g></switch></svg>",
                              "tags": ["printIcon"],
                              "supportedTypes": ["icon", "image"],
                              "iconColor": "buttonBackground",
                              "style": {
                                  "width": "100%"
                              },
                              "contentBinding": {
                                  "name": "headerLogoImage",
                                  "source": "site"
                              },
                              "uid": "c683249fed6146f495bd513d2e862143",
                              "resizeMin": 25,
                              "resizeMax": 105,
                              "resizeDefault": 100,
                              "userSize": 100,
                              "hideStockImages": false,
                              "setCropBoxToPicture": false,
                              "linkUrl": "",
                              "linkNewTab": true,
                              "linkEmailUrl": "",
                              "lightboxStatus": "default"
                          }
                      }, {
                          "pip": "logo-text",
                          "assets": [{
                              "propertyPath": ["props", "content"],
                              "assetPath": ["logos", "0", "text", "titles", "0", "content"]
                          }, {
                              "propertyPath": ["props", "defaultColor"],
                              "assetPath": ["contentBox", "titleTextColor"]
                          }],
                          "props": {
                              "className": "scene-title",
                              "defaultFontSize": "fontSize5",
                              "contentBinding": {
                                  "name": "headerLogoText",
                                  "source": "site"
                              },
                              "content": "<p>Your Business Name</p>",
                              "defaultColor": "color1",
                              "uid": "33e7c302172141839251d0cdc14163dd",
                              "fontRequired": [],
                              "defaultFont": "font1",
                              "paragraphWrappedContent": true
                          }
                      }]
                  }]
              }, {
                  "pip": "row",
                  "props": {
                      "className": "row--divider m3 ",
                      "hideable": true,
                      "uid": "5e2fdeaa5ea04f10bb99ec3134e42dc0",
                      "backgroundOpacity": 1
                  },
                  "assets": [{
                      "propertyPath": ["props", "hidden"],
                      "assetPath": ["row", "1", "hidden"]
                  }],
                  "children": [{
                      "pip": "icon",
                      "assets": [{
                          "propertyPath": ["props", "svgdata"],
                          "assetPath": ["dividers", "0", "svgdata"]
                      }, {
                          "propertyPath": ["props", "hidden"],
                          "assetPath": ["dividers", "0", "hidden"]
                      }, {
                          "propertyPath": ["props", "iconColor"],
                          "assetPath": ["dividers", "0", "iconColor"]
                      }],
                      "props": {
                          "hideable": true,
                          "svgdata": "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 500 22.2\"><switch><g><path fill=\"none\" stroke=\"#ab9e9a\" stroke-width=\"2.3\" d=\"M0 11.1h500\"/></g></switch></svg>",
                          "iconColor": "unset",
                          "uid": "98ebe8d6d4ed4a19b43de6527c08a820",
                          "resizeMin": 25,
                          "resizeMax": 105,
                          "resizeDefault": 100,
                          "userSize": 100,
                          "hideStockImages": false,
                          "setCropBoxToPicture": false,
                          "linkUrl": "",
                          "linkNewTab": true,
                          "linkEmailUrl": "",
                          "lightboxStatus": "default"
                      }
                  }]
              }, {
                  "pip": "row",
                  "props": {
                      "className": "scene-tagline",
                      "hideable": true,
                      "uid": "08bda139541840f392d2d6377f3250df",
                      "backgroundOpacity": 1
                  },
                  "assets": [{
                      "propertyPath": ["props", "hidden"],
                      "assetPath": ["row", "2", "hidden"]
                  }],
                  "children": [{
                      "pip": "paragraph",
                      "assets": [{
                          "propertyPath": ["props", "content"],
                          "assetPath": ["text", "titles", "0", "content"]
                      }, {
                          "propertyPath": ["props", "defaultColor"],
                          "assetPath": ["contentBox", "bodyTextColor"]
                      }],
                      "props": {
                          "className": "f3",
                          "level": 3,
                          "defaultFont": "font2",
                          "defaultFontSize": "fontSize4",
                          "contentBinding": {
                              "name": "headerTitleText",
                              "source": "page"
                          },
                          "content": "<p>Your Business Tagline</p>",
                          "defaultColor": "color2",
                          "uid": "22716836a2024065a81908937b45f69c",
                          "requiresCustomization": true,
                          "fontRequired": [],
                          "websafeFonts": [],
                          "paragraphWrappedContent": true
                      }
                  }]
              }, {
                  "pip": "row",
                  "props": {
                      "className": "button-pip",
                      "hideable": true,
                      "uid": "92dd60b4c41c47f4924d5a0ba82a32e9",
                      "backgroundOpacity": 1
                  },
                  "assets": [{
                      "propertyPath": ["props", "hidden"],
                      "assetPath": ["row", "3", "hidden"]
                  }],
                  "children": [{
                      "pip": "button",
                      "assets": [{
                          "propertyPath": ["props", "content"],
                          "assetPath": ["text", "buttons", "0"]
                      }, {
                          "propertyPath": ["props", "color"],
                          "assetPath": ["contentBox", "buttonColor"]
                      }, {
                          "propertyPath": ["props", "isDonateButton"],
                          "assetPath": ["buttons", "0", "isDonateButton"]
                      }, {
                          "propertyPath": ["props", "donationCause"],
                          "assetPath": ["buttons", "0", "donationCause"]
                      }, {
                          "propertyPath": ["props", "donationAmount"],
                          "assetPath": ["buttons", "0", "donationAmount"]
                      }],
                      "props": {
                          "className": "block-button tracked-mega w-100 w-50-ns",
                          "href": "",
                          "defaultFontSize": "fontSize3",
                          "homePageOnly": true,
                          "contentBinding": {
                              "name": "headerCallToAction",
                              "source": "page"
                          },
                          "content": "<p>LEARN MORE</p>",
                          "color": "color2",
                          "uid": "ce184902dbc44142b96a5cbceb7210c5",
                          "defaultFont": "font2",
                          "requiresCustomization": true,
                          "quarkClassName": "",
                          "isDonateButton": false,
                          "donateButtonCause": "",
                          "donateButtonAmount": -1,
                          "paragraphWrappedContent": true
                      }
                  }]
              }]
          }],
          "displayName": "Matching Header",
          "lessSheet": ".block.header-matched {\n\t// this rule exists to increase the width of horizontally oriented vectors\n\t.row--divider, .brand-icon-row {\n\t\t.icon-pip-container {\n\t\t\twidth: 100%;\n\t\t}\n\t}\n\t.brand-icon-row svg {\n\t\tmax-height: 100px;\n\t}\n\n\t// these important rule are a consequence of how the hacky background-image svg\n\t// we have to inline 100% to make it work generally for content binding\n\t// but we want specifically constrain it in the case of dividers\n\t.row--divider svg {\n\t\twidth: 50% !important;\n\t\tmax-height: 50px;\n\t\t@media (min-width: @larger-than-mobile) {\n\t\t\twidth: 80% !important;\n\t\t}\n\t\t@media (min-width: @larger-than-tablet) {\n\t\t\twidth: 60% !important;\n\t\t}\n\t}\n}\n",
          "_uid": "48fe1c1154704c23b2d8cd5746568d9f",
          "version": 2
      },
      "footerBlock": {
          "children": [{
              "pip": "grid",
              "children": [{
                  "pip": "gridCol",
                  "props": {
                      "size": 6,
                      "alignment": "center",
                      "contentPadding": {
                          "left": 20,
                          "right": 20,
                          "top": 10,
                          "bottom": 10
                      },
                      "uid": "3aa5f224fc66476ab9ffe01874556e91",
                      "backgrounds": [],
                      "spacing": {},
                      "mobileOverrides": {
                          "contentPadding": {
                              "top": 10,
                              "right": 10,
                              "bottom": 10,
                              "left": 10
                          },
                          "spacing": {
                              "top": 0,
                              "right": 0,
                              "bottom": 0,
                              "left": 0
                          }
                      },
                      "pipToHighlight": [],
                      "pipToMoveIndex": []
                  },
                  "children": [{
                      "pip": "title",
                      "props": {
                          "level": 5,
                          "defaultFont": "font2",
                          "content": "<p>© 2019 My Small Business, LLC</p>",
                          "uid": "62caa59d8dd94325899a715a84d35156",
                          "contentMargin": {
                              "top": 0,
                              "right": "auto",
                              "bottom": 20,
                              "left": "auto"
                          },
                          "defaultAlignment": "left",
                          "tabletOverrides": {},
                          "mobileOverrides": {},
                          "requiresCustomization": true,
                          "contentBinding": null,
                          "fontRequired": [],
                          "websafeFonts": [],
                          "className": "",
                          "paragraphWrappedContent": true
                      }
                  }]
              }, {
                  "pip": "gridCol",
                  "props": {
                      "size": 6,
                      "contentPadding": {
                          "left": 20,
                          "right": 20,
                          "top": 10,
                          "bottom": 10
                      },
                      "uid": "c526ae89f9964d1aa3c104c537289ef1",
                      "alignment": "top",
                      "backgrounds": [],
                      "spacing": {},
                      "mobileOverrides": {
                          "contentPadding": {
                              "top": 10,
                              "right": 10,
                              "bottom": 10,
                              "left": 10
                          },
                          "spacing": {
                              "top": 0,
                              "right": 0,
                              "bottom": 0,
                              "left": 0
                          }
                      },
                      "pipToHighlight": [],
                      "pipToMoveIndex": []
                  },
                  "children": [{
                      "pip": "social",
                      "props": {
                          "links": [{
                              "service": "instagram",
                              "url": ""
                          }, {
                              "service": "facebook",
                              "url": ""
                          }, {
                              "service": "twitter",
                              "url": ""
                          }],
                          "iconType": "circle",
                          "uid": "e1d3b3c563c443e69effedb67347ad6c",
                          "contentMargin": {
                              "top": 0,
                              "right": 0,
                              "bottom": 20,
                              "left": "auto"
                          },
                          "tabletOverrides": {
                              "contentMargin": {
                                  "top": 0,
                                  "right": "auto",
                                  "left": "auto"
                              }
                          },
                          "mobileOverrides": {
                              "contentMargin": {
                                  "top": 0,
                                  "right": "auto",
                                  "left": "auto"
                              }
                          },
                          "outerSize": "42px",
                          "innerSizeNoBG": "26px",
                          "innerSizeWithBG": "16px",
                          "requiresCustomization": true
                      }
                  }]
              }],
              "props": {
                  "uid": "4f771d3c2af240deb56380d6dce6f446"
              }
          }],
          "props": {
              "nameable": false,
              "moveable": false,
              "position": "bottom",
              "positionOverlay": true,
              "background": {
                  "imageTransparency": true,
                  "color": {
                      "value": "color4",
                      "opacity": 1
                  },
                  "backgroundType": "color"
              },
              "userHeight": {
                  "bottom": 10,
                  "top": 10
              }
          },
          "slug": "grid-footer-social-links",
          "displayName": "Social Links Footer",
          "version": 3,
          "_uid": "0d381c1e892b488b86e28a793d9ff245"
      },
      "homePageId": 2684818741,
      "multipage": true,
      "pages": {
          "2684818741": {
              "id": 2684818741,
              "name": "Home",
              "path": "",
              "order": 0,
              "blockLinks": [],
              "hidden": false,
              "seoTitle": "Home"
          },
          "1632494318174952": {
              "id": 1632494318174952,
              "name": "About",
              "path": "about",
              "order": 1,
              "blockLinks": [],
              "hidden": false,
              "seoTitle": "About"
          },
          "1632494317601370": {
              "id": 1632494317601370,
              "name": "Contact",
              "path": "contact",
              "order": 2,
              "blockLinks": [{
                  "blockName": "Contact",
                  "blockAnchor": "contact",
                  "inNavigation": false
              }],
              "hidden": false,
              "seoTitle": "Contact"
          }
      },
      "metadata": {
          "email": "trainor.erin@gmail.com",
          "industry": null,
          "businessName": null,
          "contentBinding": {},
          "headerStyle": "full",
          "towerVersion": "17.0.0"
      },
      "id": 2684818741,
      "blocks": [{
          "slug": "header-matched",
          "assets": [{
              "propertyPath": ["displayName"],
              "assetPath": ["displayName"]
          }, {
              "propertyPath": ["props", "background"],
              "assetPath": ["blockBackground"]
          }, {
              "propertyPath": ["props", "userHeight"],
              "assetPath": ["userHeight"]
          }],
          "props": {
              "hidden": true,
              "className": "cover shadow-2",
              "type": "header",
              "nameable": true,
              "name": "",
              "moveable": false,
              "disableTopResizing": true,
              "position": "top",
              "background": {
                  "color": {
                      "value": "color3",
                      "opacity": 0
                  },
                  "image": {
                      "url": "https://assets.digital.vistaprint.com/production/5fde27bf-5ce7-4332-9ae3-df00da82cd7c"
                  },
                  "tags": ["printBackground"],
                  "contentBinding": {
                      "name": "headerBackgroundImage",
                      "source": "page"
                  },
                  "imageTransparency": true,
                  "backgroundType": "image"
              },
              "instanceLess": "",
              "layouts": null
          },
          "children": [{
              "pip": "row",
              "props": {
                  "className": "mb0 mb5-l",
                  "uid": "ee6d73a7c5a7413ab628eb029b927961",
                  "backgroundOpacity": 1
              },
              "children": [{
                  "pip": "col",
                  "children": [{
                      "pip": "row",
                      "props": {
                          "className": "justify-center",
                          "uid": "ec91f45498b7438586ac2467283eb531",
                          "backgroundOpacity": 1
                      },
                      "children": [{
                          "pip": "navigation",
                          "assets": [{
                              "propertyPath": ["props", "linkColor"],
                              "assetPath": ["navigation", "bodyTextColor"]
                          }],
                          "props": {
                              "defaultFontSize": "fontSize4",
                              "defaultFont": "font2",
                              "mobileMenu": "tablet",
                              "linkColor": "color2",
                              "uid": "7ab4c3405ceb42149a677162bb33a766",
                              "defaultColor": "color4",
                              "isRelative": false,
                              "adjustableMobileMenuColor": false
                          }
                      }]
                  }],
                  "props": {
                      "uid": "323e90405c5f49acaa3a77cc47923d21"
                  }
              }]
          }, {
              "pip": "group",
              "props": {
                  "className": "content-group",
                  "uid": "927276f0f21049268104226add015ea8",
                  "backgroundOpacity": 1
              },
              "children": [{
                  "pip": "row",
                  "props": {
                      "className": "brand-icon-row",
                      "hideable": true,
                      "uid": "5a94de1bf71a43c5868d9e1414e0ece1",
                      "backgroundOpacity": 1
                  },
                  "assets": [{
                      "propertyPath": ["props", "hidden"],
                      "assetPath": ["row", "0", "hidden"]
                  }],
                  "children": [{
                      "pip": "logo",
                      "assets": [{
                          "propertyPath": ["props", "logoMode"],
                          "assetPath": ["logos", "0", "mode"]
                      }],
                      "props": {
                          "className": "f1",
                          "level": 5,
                          "defaultFont": "font1",
                          "defaultFontSize": "fontSize3",
                          "homeLink": true,
                          "layout": "centerStacked",
                          "contentBinding": {
                              "name": "headerLogoMode",
                              "source": "site"
                          },
                          "logoMode": "textOnly",
                          "uid": "9cc140400ef343058aea26918c049a53"
                      },
                      "children": [{
                          "pip": "graphic",
                          "assets": [{
                              "propertyPath": ["props"],
                              "assetPath": ["logos", "0", "graphics", "0"]
                          }],
                          "props": {
                              "svgdata": "<svg xmlns:x=\"http://ns.adobe.com/Extensibility/1.0/\" xmlns:i=\"http://ns.adobe.com/AdobeIllustrator/10.0/\" xmlns:graph=\"http://ns.adobe.com/Graphs/1.0/\" xmlns=\"http://www.w3.org/2000/svg\" xmlns:xlink=\"http://www.w3.org/1999/xlink\" version=\"1.1\" x=\"0px\" y=\"0px\" viewBox=\"0 0 100 100\" enable-background=\"new 0 0 100 100\" xml:space=\"preserve\"><switch><foreignObject requiredExtensions=\"http://ns.adobe.com/AdobeIllustrator/10.0/\" x=\"0\" y=\"0\" width=\"1\" height=\"1\"></foreignObject><g i:extraneous=\"self\"><g><path d=\"M94.503,7.95c-0.045-0.027-0.092-0.051-0.14-0.072c-0.141-0.062-0.295-0.097-0.459-0.097H88.32     c-0.166,0-0.323,0.037-0.465,0.099c-0.049,0.022-0.097,0.046-0.142,0.074c-0.163,0.099-0.299,0.234-0.397,0.397L50.563,45.104     L38.394,32.934c1.992-2.935,3.065-6.395,3.065-10.02c0-0.066-0.004-0.132-0.005-0.198c0.001-0.083,0.005-0.167,0.005-0.25     c0-4.779-1.861-9.273-5.241-12.652s-7.873-5.241-12.652-5.241s-9.272,1.861-12.652,5.241c-3.379,3.379-5.241,7.873-5.241,12.652     c0,0.075,0.004,0.149,0.005,0.224c-0.001,0.075-0.005,0.149-0.005,0.224c0,4.779,1.861,9.272,5.241,12.652     c3.38,3.38,7.873,5.241,12.652,5.241c3.791,0,7.398-1.175,10.416-3.345l12.111,12.111L33.982,61.685     c-3.018-2.17-6.625-3.345-10.416-3.345c-4.779,0-9.272,1.861-12.652,5.241c-3.379,3.379-5.241,7.873-5.241,12.652     c0,0.075,0.004,0.149,0.005,0.224c-0.001,0.075-0.005,0.149-0.005,0.224c0,4.78,1.861,9.273,5.241,12.652     c3.38,3.379,7.873,5.241,12.652,5.241s9.273-1.861,12.652-5.241s5.241-7.873,5.241-12.652c0-0.083-0.003-0.167-0.005-0.25     c0.001-0.066,0.005-0.131,0.005-0.198c0-3.625-1.073-7.084-3.065-10.02l12.169-12.169l36.752,36.752     c0.099,0.163,0.234,0.298,0.397,0.397c0.045,0.028,0.093,0.052,0.142,0.074c0.142,0.063,0.299,0.099,0.465,0.099h5.584     c0.164,0,0.318-0.036,0.459-0.097c0.048-0.021,0.095-0.045,0.14-0.072c0.345-0.206,0.579-0.578,0.579-1.009v-0.034v0     c0-0.011-0.003-0.022-0.003-0.033c0.009-0.298-0.097-0.599-0.325-0.827l-39.72-39.72l39.72-39.72     c0.228-0.228,0.334-0.528,0.325-0.827c0-0.011,0.003-0.022,0.003-0.033v0V8.959C95.082,8.528,94.848,8.156,94.503,7.95z      M23.566,36.468c-7.474,0-13.554-6.081-13.554-13.553c0-7.473,6.08-13.554,13.554-13.554c7.473,0,13.554,6.081,13.554,13.554     C37.12,30.387,31.04,36.468,23.566,36.468z M23.566,90.234c-7.474,0-13.554-6.081-13.554-13.554s6.08-13.554,13.554-13.554     c7.473,0,13.554,6.081,13.554,13.554S31.04,90.234,23.566,90.234z\"></path></g></g></switch></svg>",
                              "tags": ["printIcon"],
                              "supportedTypes": ["icon", "image"],
                              "iconColor": "buttonBackground",
                              "style": {
                                  "width": "100%"
                              },
                              "contentBinding": {
                                  "name": "headerLogoImage",
                                  "source": "site"
                              },
                              "uid": "c683249fed6146f495bd513d2e862143",
                              "resizeMin": 25,
                              "resizeMax": 105,
                              "resizeDefault": 100,
                              "userSize": 100,
                              "hideStockImages": false,
                              "setCropBoxToPicture": false,
                              "linkUrl": "",
                              "linkNewTab": true,
                              "linkEmailUrl": "",
                              "lightboxStatus": "default"
                          }
                      }, {
                          "pip": "logo-text",
                          "assets": [{
                              "propertyPath": ["props", "content"],
                              "assetPath": ["logos", "0", "text", "titles", "0", "content"]
                          }, {
                              "propertyPath": ["props", "defaultColor"],
                              "assetPath": ["contentBox", "titleTextColor"]
                          }],
                          "props": {
                              "className": "scene-title",
                              "defaultFontSize": "fontSize5",
                              "contentBinding": {
                                  "name": "headerLogoText",
                                  "source": "site"
                              },
                              "content": "<p>Your Business Name</p>",
                              "defaultColor": "color1",
                              "uid": "33e7c302172141839251d0cdc14163dd",
                              "fontRequired": [],
                              "defaultFont": "font1",
                              "paragraphWrappedContent": true
                          }
                      }]
                  }]
              }, {
                  "pip": "row",
                  "props": {
                      "className": "row--divider m3 ",
                      "hideable": true,
                      "uid": "5e2fdeaa5ea04f10bb99ec3134e42dc0",
                      "backgroundOpacity": 1
                  },
                  "assets": [{
                      "propertyPath": ["props", "hidden"],
                      "assetPath": ["row", "1", "hidden"]
                  }],
                  "children": [{
                      "pip": "icon",
                      "assets": [{
                          "propertyPath": ["props", "svgdata"],
                          "assetPath": ["dividers", "0", "svgdata"]
                      }, {
                          "propertyPath": ["props", "hidden"],
                          "assetPath": ["dividers", "0", "hidden"]
                      }, {
                          "propertyPath": ["props", "iconColor"],
                          "assetPath": ["dividers", "0", "iconColor"]
                      }],
                      "props": {
                          "hideable": true,
                          "svgdata": "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 500 22.2\"><switch><g><path fill=\"none\" stroke=\"#ab9e9a\" stroke-width=\"2.3\" d=\"M0 11.1h500\"/></g></switch></svg>",
                          "iconColor": "unset",
                          "uid": "98ebe8d6d4ed4a19b43de6527c08a820",
                          "resizeMin": 25,
                          "resizeMax": 105,
                          "resizeDefault": 100,
                          "userSize": 100,
                          "hideStockImages": false,
                          "setCropBoxToPicture": false,
                          "linkUrl": "",
                          "linkNewTab": true,
                          "linkEmailUrl": "",
                          "lightboxStatus": "default"
                      }
                  }]
              }, {
                  "pip": "row",
                  "props": {
                      "className": "scene-tagline",
                      "hideable": true,
                      "uid": "08bda139541840f392d2d6377f3250df",
                      "backgroundOpacity": 1
                  },
                  "assets": [{
                      "propertyPath": ["props", "hidden"],
                      "assetPath": ["row", "2", "hidden"]
                  }],
                  "children": [{
                      "pip": "paragraph",
                      "assets": [{
                          "propertyPath": ["props", "content"],
                          "assetPath": ["text", "titles", "0", "content"]
                      }, {
                          "propertyPath": ["props", "defaultColor"],
                          "assetPath": ["contentBox", "bodyTextColor"]
                      }],
                      "props": {
                          "className": "f3",
                          "level": 3,
                          "defaultFont": "font2",
                          "defaultFontSize": "fontSize4",
                          "contentBinding": {
                              "name": "headerTitleText",
                              "source": "page"
                          },
                          "content": "<p>Your Business Tagline</p>",
                          "defaultColor": "color2",
                          "uid": "22716836a2024065a81908937b45f69c",
                          "requiresCustomization": true,
                          "fontRequired": [],
                          "websafeFonts": [],
                          "paragraphWrappedContent": true
                      }
                  }]
              }, {
                  "pip": "row",
                  "props": {
                      "className": "button-pip",
                      "hideable": true,
                      "uid": "92dd60b4c41c47f4924d5a0ba82a32e9",
                      "backgroundOpacity": 1
                  },
                  "assets": [{
                      "propertyPath": ["props", "hidden"],
                      "assetPath": ["row", "3", "hidden"]
                  }],
                  "children": [{
                      "pip": "button",
                      "assets": [{
                          "propertyPath": ["props", "content"],
                          "assetPath": ["text", "buttons", "0"]
                      }, {
                          "propertyPath": ["props", "color"],
                          "assetPath": ["contentBox", "buttonColor"]
                      }, {
                          "propertyPath": ["props", "isDonateButton"],
                          "assetPath": ["buttons", "0", "isDonateButton"]
                      }, {
                          "propertyPath": ["props", "donationCause"],
                          "assetPath": ["buttons", "0", "donationCause"]
                      }, {
                          "propertyPath": ["props", "donationAmount"],
                          "assetPath": ["buttons", "0", "donationAmount"]
                      }],
                      "props": {
                          "className": "block-button tracked-mega w-100 w-50-ns",
                          "href": "",
                          "defaultFontSize": "fontSize3",
                          "homePageOnly": true,
                          "contentBinding": {
                              "name": "headerCallToAction",
                              "source": "page"
                          },
                          "content": "<p>LEARN MORE</p>",
                          "color": "color2",
                          "uid": "ce184902dbc44142b96a5cbceb7210c5",
                          "defaultFont": "font2",
                          "requiresCustomization": true,
                          "quarkClassName": "",
                          "isDonateButton": false,
                          "donateButtonCause": "",
                          "donateButtonAmount": -1,
                          "paragraphWrappedContent": true
                      }
                  }]
              }]
          }],
          "displayName": "Matching Header",
          "lessSheet": ".block.header-matched {\n\t// this rule exists to increase the width of horizontally oriented vectors\n\t.row--divider, .brand-icon-row {\n\t\t.icon-pip-container {\n\t\t\twidth: 100%;\n\t\t}\n\t}\n\t.brand-icon-row svg {\n\t\tmax-height: 100px;\n\t}\n\n\t// these important rule are a consequence of how the hacky background-image svg\n\t// we have to inline 100% to make it work generally for content binding\n\t// but we want specifically constrain it in the case of dividers\n\t.row--divider svg {\n\t\twidth: 50% !important;\n\t\tmax-height: 50px;\n\t\t@media (min-width: @larger-than-mobile) {\n\t\t\twidth: 80% !important;\n\t\t}\n\t\t@media (min-width: @larger-than-tablet) {\n\t\t\twidth: 60% !important;\n\t\t}\n\t}\n}\n",
          "_uid": "48fe1c1154704c23b2d8cd5746568d9f",
          "version": 2
      }, {
          "slug": "text-button-v2",
          "props": {
              "contentClassName": "pv5-ns",
              "background": {
                  "color": {
                      "value": "color1",
                      "opacity": 1
                  },
                  "imageTransparency": true,
                  "backgroundType": "color"
              },
              "instanceLess": "",
              "layouts": null
          },
          "children": [{
              "pip": "row",
              "children": [{
                  "pip": "col",
                  "props": {
                      "hideable": true,
                      "className": "flex ml0 mb0-l mr3-l mr0 items-center flex-grow-5 w-100",
                      "uid": "fb4e371863454f0b8db80659c8cd1745"
                  },
                  "children": [{
                      "pip": "row",
                      "props": {
                          "className": "w-100 mb3 mb0-l",
                          "uid": "7cce8d522b314adaa58be6be9357cdb0",
                          "backgroundOpacity": 1
                      },
                      "children": [{
                          "pip": "paragraph",
                          "assets": [{
                              "propertyPath": ["props", "content"],
                              "assetPath": ["text", "paragraphs", "0", "content"]
                          }, {
                              "propertyPath": ["props", "lineHeightClassName"],
                              "assetPath": ["text", "paragraphs", "0", "lineHeightClassName"]
                          }],
                          "props": {
                              "content": "<p>Click this text to edit. Tell users why they should click the button.</p>",
                              "uid": "9bb7dce84f1c4d31badcfefddf85f612",
                              "defaultFontSize": "fontSize3",
                              "defaultFont": "font2",
                              "requiresCustomization": true,
                              "fontRequired": [],
                              "websafeFonts": [],
                              "className": "",
                              "paragraphWrappedContent": true
                          }
                      }]
                  }],
                  "assets": [{
                      "propertyPath": ["props", "hidden"],
                      "assetPath": ["cols", "0", "hidden"]
                  }]
              }, {
                  "pip": "col",
                  "props": {
                      "hideable": true,
                      "className": "flex-grow-2 center",
                      "uid": "ea1988ff9ca04427b11253d39be77826"
                  },
                  "children": [{
                      "pip": "button",
                      "props": {
                          "className": "mh0 mh5-ns center-l w-auto",
                          "content": "<p>Learn More</p>",
                          "color": "color2",
                          "uid": "bc784ab6f7824d64bcc9c93e5ddbbf13",
                          "href": "",
                          "defaultFont": "font2",
                          "defaultFontSize": "fontSize3",
                          "requiresCustomization": true,
                          "quarkClassName": "",
                          "isDonateButton": false,
                          "donateButtonCause": "",
                          "donateButtonAmount": -1,
                          "paragraphWrappedContent": true
                      },
                      "assets": [{
                          "propertyPath": ["props", "content"],
                          "assetPath": ["buttons", "0", "content"]
                      }, {
                          "propertyPath": ["props", "color"],
                          "assetPath": ["buttons", "0", "color"]
                      }, {
                          "propertyPath": ["props", "href"],
                          "assetPath": ["buttons", "0", "href"]
                      }, {
                          "propertyPath": ["props", "isDonateButton"],
                          "assetPath": ["buttons", "0", "isDonateButton"]
                      }, {
                          "propertyPath": ["props", "donationCause"],
                          "assetPath": ["buttons", "0", "donationCause"]
                      }, {
                          "propertyPath": ["props", "donationAmount"],
                          "assetPath": ["buttons", "0", "donationAmount"]
                      }]
                  }],
                  "assets": [{
                      "propertyPath": ["props", "hidden"],
                      "assetPath": ["cols", "1", "hidden"]
                  }]
              }],
              "props": {
                  "uid": "6ce8ebb5b62d4839845c5f99e43fa922",
                  "backgroundOpacity": 1
              }
          }],
          "assets": [{
              "propertyPath": ["displayName"],
              "assetPath": ["displayName"]
          }, {
              "propertyPath": ["props", "background"],
              "assetPath": ["background"]
          }, {
              "propertyPath": ["props", "userHeight"],
              "assetPath": ["userHeight"]
          }],
          "displayName": "Text & Button",
          "lessSheet": "",
          "_uid": "56be1bb07e534f5c9131f342febadfcd",
          "version": 2
      }, {
          "children": [{
              "pip": "grid",
              "children": [{
                  "pip": "gridCol",
                  "props": {
                      "size": 12,
                      "contentPadding": {
                          "top": 10,
                          "right": 10,
                          "bottom": 10,
                          "left": 10
                      },
                      "uid": "64a8a763f6724730bf34e4d8c5da7727",
                      "alignment": "top",
                      "backgrounds": [],
                      "spacing": {},
                      "mobileOverrides": {
                          "contentPadding": {
                              "top": 10,
                              "right": 10,
                              "bottom": 10,
                              "left": 10
                          },
                          "spacing": {
                              "top": 0,
                              "right": 0,
                              "bottom": 0,
                              "left": 0
                          }
                      },
                      "pipToHighlight": [],
                      "pipToMoveIndex": []
                  },
                  "children": [{
                      "pip": "title",
                      "props": {
                          "level": 2,
                          "content": "<p>Click Here to Add a Title</p>",
                          "uid": "ffda92e84d9948708eab7c9741f7f64b",
                          "contentMargin": {
                              "top": 0,
                              "right": "auto",
                              "bottom": 21,
                              "left": "auto"
                          },
                          "tabletOverrides": {},
                          "mobileOverrides": {},
                          "defaultFont": "font1",
                          "requiresCustomization": true,
                          "contentBinding": null,
                          "fontRequired": [],
                          "websafeFonts": [],
                          "className": "",
                          "paragraphWrappedContent": true
                      }
                  }, {
                      "pip": "paragraph",
                      "props": {
                          "content": "<p>Click this text to start editing. This block is a basic combination of a title and a paragraph. Use it to welcome visitors to your website, or explain a product or service without using an image. Try keeping the paragraph short and breaking off the text-only areas of your page to keep your website interesting to visitors.</p>",
                          "uid": "e9b1c85bd894422b828382c8daa43d53",
                          "contentMargin": {
                              "top": 0,
                              "right": "auto",
                              "bottom": 20,
                              "left": "auto"
                          },
                          "tabletOverrides": {},
                          "mobileOverrides": {},
                          "defaultFontSize": "fontSize3",
                          "defaultFont": "font2",
                          "requiresCustomization": true,
                          "fontRequired": [],
                          "websafeFonts": [],
                          "className": "",
                          "paragraphWrappedContent": true
                      }
                  }]
              }],
              "props": {
                  "uid": "ebeb0312ac714fe6865c21d1e270eea9"
              }
          }],
          "props": {
              "background": {
                  "imageTransparency": true,
                  "color": {
                      "value": "color4",
                      "opacity": 1
                  },
                  "backgroundType": "color"
              },
              "userHeight": {
                  "top": 57,
                  "bottom": 70
              }
          },
          "slug": "grid-title-text-v2",
          "displayName": "Title & Text",
          "version": 3,
          "_uid": "1844eceb41844bb09497270396ad6273"
      }, {
          "children": [{
              "pip": "grid",
              "children": [{
                  "pip": "gridCol",
                  "props": {
                      "size": 6,
                      "alignment": "center",
                      "contentPadding": {
                          "left": 20,
                          "right": 20,
                          "top": 10,
                          "bottom": 10
                      },
                      "uid": "8ee135d356c64126825df96d31d4639d",
                      "backgrounds": [],
                      "spacing": {},
                      "mobileOverrides": {
                          "contentPadding": {
                              "top": 10,
                              "right": 10,
                              "bottom": 10,
                              "left": 10
                          },
                          "spacing": {
                              "top": 0,
                              "right": 0,
                              "bottom": 0,
                              "left": 0
                          }
                      },
                      "pipToHighlight": [],
                      "pipToMoveIndex": []
                  },
                  "children": [{
                      "pip": "title",
                      "props": {
                          "level": 3,
                          "content": "<p>Click Here to Add a Title</p>",
                          "uid": "e16f4149401e4e8794db2d64d6cce876",
                          "contentMargin": {
                              "top": 0,
                              "right": "auto",
                              "bottom": 20,
                              "left": "auto"
                          },
                          "tabletOverrides": {},
                          "mobileOverrides": {},
                          "defaultFont": "font1",
                          "requiresCustomization": true,
                          "contentBinding": null,
                          "fontRequired": [],
                          "websafeFonts": [],
                          "className": "",
                          "paragraphWrappedContent": true
                      }
                  }, {
                      "pip": "paragraph",
                      "props": {
                          "content": "<p>Click this text to start editing. This image and text block is great for descriptions about your business, products, or services. Double-click the image on the right to change it. You can also stack more of these blocks to describe items with imagery.</p>",
                          "uid": "ccd7ad5db37440d58fd13686ca0f377b",
                          "contentMargin": {
                              "top": 0,
                              "right": "auto",
                              "bottom": 20,
                              "left": "auto"
                          },
                          "tabletOverrides": {},
                          "mobileOverrides": {},
                          "defaultFontSize": "fontSize3",
                          "defaultFont": "font2",
                          "requiresCustomization": true,
                          "fontRequired": [],
                          "websafeFonts": [],
                          "className": "",
                          "paragraphWrappedContent": true
                      }
                  }]
              }, {
                  "pip": "gridCol",
                  "props": {
                      "size": 6,
                      "contentPadding": {
                          "left": 20,
                          "right": 20,
                          "top": 10,
                          "bottom": 10
                      },
                      "uid": "26caf07e13c7444fafca1893724d796b",
                      "alignment": "top",
                      "backgrounds": [],
                      "spacing": {},
                      "mobileOverrides": {
                          "contentPadding": {
                              "top": 10,
                              "right": 10,
                              "bottom": 10,
                              "left": 10
                          },
                          "spacing": {
                              "top": 0,
                              "right": 0,
                              "bottom": 0,
                              "left": 0
                          }
                      },
                      "pipToHighlight": [],
                      "pipToMoveIndex": []
                  },
                  "children": [{
                      "props": {
                          "uid": "ebdf8b8e5fa348a791cdb123dd0cfd66",
                          "percentWidth": 89.0909090909091,
                          "originalUrl": "//studio.digital.vistaprint.com/images/lake_80qual.jpg",
                          "cropData": {
                              "x": 128,
                              "y": 92,
                              "width": 1024,
                              "height": 617
                          },
                          "openLinkInNewTab": false,
                          "lightboxStatus": null,
                          "url": "https://imageprocessor.digital.vistaprint.com/crop/128,92,1024x617/maxWidth/2000/http://studio.digital.vistaprint.com/images/lake_80qual.jpg",
                          "contentMargin": {
                              "top": 0,
                              "right": "auto",
                              "bottom": 20,
                              "left": "auto"
                          },
                          "tabletOverrides": {
                              "contentMargin": {
                                  "top": 0,
                                  "right": "auto",
                                  "left": "auto"
                              }
                          },
                          "mobileOverrides": {
                              "percentWidth": 100,
                              "contentMargin": {
                                  "top": 0,
                                  "right": "auto",
                                  "left": "auto"
                              }
                          },
                          "tag": "div",
                          "mode": {}
                      },
                      "pip": "imageMedia"
                  }]
              }],
              "props": {
                  "uid": "4e3ea4fd96cc47d882f8dd1560034fd5"
              }
          }],
          "props": {
              "background": {
                  "color": {
                      "value": "color4",
                      "opacity": 1
                  },
                  "imageTransparency": true,
                  "backgroundType": "color"
              },
              "userHeight": {
                  "top": 70,
                  "bottom": 70
              }
          },
          "slug": "grid-paragraph-graphic",
          "displayName": "Paragraph & Graphic",
          "version": 3,
          "_uid": "931c1860ba0c4a76a425f09d125c30c7"
      }, {
          "slug": "quote-v2",
          "children": [{
              "pip": "row",
              "props": {
                  "hideable": true,
                  "className": "mb0 mb4-ns",
                  "uid": "b20c9da8022a46bb8ca201f96c030bab",
                  "backgroundOpacity": 1
              },
              "children": [{
                  "pip": "title",
                  "props": {
                      "className": "lh-title",
                      "level": 2,
                      "content": "<p>What our customers are saying</p>",
                      "uid": "962c4fdbf5d44ad6b416d12cd72f9331",
                      "defaultFont": "font1",
                      "requiresCustomization": true,
                      "contentBinding": null,
                      "fontRequired": [],
                      "websafeFonts": [],
                      "paragraphWrappedContent": true
                  },
                  "assets": [{
                      "propertyPath": ["props", "content"],
                      "assetPath": ["text", "titles", "0", "content"]
                  }, {
                      "propertyPath": ["props", "lineHeightClassName"],
                      "assetPath": ["text", "titles", "0", "lineHeightClassName"]
                  }]
              }],
              "assets": [{
                  "propertyPath": ["props", "hidden"],
                  "assetPath": ["rows", "0", "hidden"]
              }]
          }, {
              "pip": "row",
              "props": {
                  "className": "flex-column flex-row-ns",
                  "uid": "0a21ff7901a54ad29f2bc359a09904ef",
                  "backgroundOpacity": 1
              },
              "children": [{
                  "pip": "col",
                  "props": {
                      "className": "flex-1 h2 h-auto-ns",
                      "uid": "851d0e6ceea44625b0e8fb98892905e8"
                  },
                  "children": [{
                      "pip": "paragraph",
                      "props": {
                          "className": "serif tr-ns",
                          "readOnly": true,
                          "defaultColor": "accent1",
                          "defaultFontSize": "size10",
                          "content": "<p><b>“</b></p>",
                          "uid": "ec901b83a649449ca951b6f0b896e4e8",
                          "defaultFont": "font2",
                          "requiresCustomization": true,
                          "fontRequired": [],
                          "websafeFonts": [],
                          "paragraphWrappedContent": true
                      },
                      "assets": [{
                          "propertyPath": ["props", "content"],
                          "assetPath": ["text", "paragraphs", "0", "content"]
                      }, {
                          "propertyPath": ["props", "lineHeightClassName"],
                          "assetPath": ["text", "paragraphs", "0", "lineHeightClassName"]
                      }]
                  }]
              }, {
                  "pip": "col",
                  "props": {
                      "className": "flex-3",
                      "uid": "054f0b23e52044149c57c0930b81a76e"
                  },
                  "children": [{
                      "pip": "row",
                      "props": {
                          "hideable": true,
                          "uid": "9e85c1609dc644bc92f9648d0d846cd1",
                          "backgroundOpacity": 1
                      },
                      "children": [{
                          "pip": "paragraph",
                          "assets": [{
                              "propertyPath": ["props", "content"],
                              "assetPath": ["text", "paragraphs", "1", "content"]
                          }, {
                              "propertyPath": ["props", "lineHeightClassName"],
                              "assetPath": ["text", "paragraphs", "1", "lineHeightClassName"]
                          }],
                          "props": {
                              "content": "<p>Click this text to edit. Choose a customer testimonial, review, or a quote from the media gives prospective buyers confidence in your brand, your products, and/or your customer service.</p>",
                              "uid": "8618d2b1abb44a2cb4a7e47bfb389746",
                              "defaultFontSize": "fontSize3",
                              "defaultFont": "font2",
                              "requiresCustomization": true,
                              "fontRequired": [],
                              "websafeFonts": [],
                              "className": "",
                              "paragraphWrappedContent": true
                          }
                      }],
                      "assets": [{
                          "propertyPath": ["props", "hidden"],
                          "assetPath": ["rows", "1", "hidden"]
                      }]
                  }, {
                      "pip": "row",
                      "props": {
                          "hideable": true,
                          "uid": "2502ff804a9042228b034d44c43b70f9",
                          "backgroundOpacity": 1
                      },
                      "children": [{
                          "pip": "paragraph",
                          "props": {
                              "className": "i b",
                              "defaultFontSize": "fontSize2",
                              "content": "<p>Jane Doe - Another Company, LLC</p>",
                              "uid": "fa9bb0d54fe04774815fbf9be0fd8047",
                              "defaultFont": "font2",
                              "requiresCustomization": true,
                              "fontRequired": [],
                              "websafeFonts": [],
                              "paragraphWrappedContent": true
                          },
                          "assets": [{
                              "propertyPath": ["props", "content"],
                              "assetPath": ["text", "paragraphs", "2", "content"]
                          }, {
                              "propertyPath": ["props", "lineHeightClassName"],
                              "assetPath": ["text", "paragraphs", "2", "lineHeightClassName"]
                          }]
                      }],
                      "assets": [{
                          "propertyPath": ["props", "hidden"],
                          "assetPath": ["rows", "2", "hidden"]
                      }]
                  }]
              }, {
                  "pip": "col",
                  "props": {
                      "className": "flex-1 dn flex-ns",
                      "uid": "0d5abb50ba824da0aaa6a4798f8f45d0"
                  },
                  "children": [{
                      "pip": "paragraph",
                      "props": {
                          "className": "serif tl-ns",
                          "readOnly": true,
                          "defaultColor": "accent1",
                          "defaultFontSize": "size10",
                          "content": "<p><b>”</b></p>",
                          "uid": "d596ea957dc04e45a95478eab744cf80",
                          "defaultFont": "font2",
                          "requiresCustomization": true,
                          "fontRequired": [],
                          "websafeFonts": [],
                          "paragraphWrappedContent": true
                      },
                      "assets": [{
                          "propertyPath": ["props", "content"],
                          "assetPath": ["text", "paragraphs", "3", "content"]
                      }, {
                          "propertyPath": ["props", "lineHeightClassName"],
                          "assetPath": ["text", "paragraphs", "3", "lineHeightClassName"]
                      }]
                  }]
              }]
          }],
          "assets": [{
              "propertyPath": ["displayName"],
              "assetPath": ["displayName"]
          }, {
              "propertyPath": ["props", "background"],
              "assetPath": ["background"]
          }, {
              "propertyPath": ["props", "userHeight"],
              "assetPath": ["userHeight"]
          }],
          "displayName": "Quote",
          "lessSheet": "",
          "props": {
              "instanceLess": "",
              "layouts": null,
              "background": {
                  "imageTransparency": true,
                  "color": {
                      "value": "color4",
                      "opacity": 1
                  },
                  "backgroundType": "color"
              }
          },
          "_uid": "e221fa5873094308b91478033707f5b9",
          "version": 2
      }, {
          "children": [{
              "pip": "grid",
              "children": [{
                  "pip": "gridCol",
                  "props": {
                      "size": 12,
                      "contentPadding": {
                          "top": 10,
                          "right": 10,
                          "bottom": 10,
                          "left": 10
                      },
                      "uid": "fe8460878b4e4670909958ba71aa3460",
                      "alignment": "top",
                      "backgrounds": [],
                      "spacing": {},
                      "mobileOverrides": {
                          "contentPadding": {
                              "top": 10,
                              "right": 10,
                              "bottom": 10,
                              "left": 10
                          },
                          "spacing": {
                              "top": 0,
                              "right": 0,
                              "bottom": 0,
                              "left": 0
                          }
                      },
                      "pipToHighlight": [],
                      "pipToMoveIndex": []
                  },
                  "children": [{
                      "pip": "title",
                      "props": {
                          "level": 2,
                          "content": "<p>Click Here to Add a Title</p>",
                          "uid": "6595bcac0836459f84e73ce2f1bd227c",
                          "contentMargin": {
                              "top": 0,
                              "right": "auto",
                              "bottom": 5,
                              "left": "auto"
                          },
                          "tabletOverrides": {},
                          "mobileOverrides": {},
                          "defaultFont": "font1",
                          "requiresCustomization": true,
                          "contentBinding": null,
                          "fontRequired": [],
                          "websafeFonts": [],
                          "className": "",
                          "paragraphWrappedContent": true
                      }
                  }, {
                      "pip": "title",
                      "props": {
                          "level": 4,
                          "content": "<p><b>Click this text to edit. Tell users why they should click the button.</b></p>",
                          "uid": "9af0e3a22ee74f83a18e8002d340c345",
                          "contentMargin": {
                              "top": 0,
                              "right": "auto",
                              "bottom": 10,
                              "left": "auto"
                          },
                          "tabletOverrides": {},
                          "mobileOverrides": {},
                          "defaultFont": "font1",
                          "requiresCustomization": true,
                          "contentBinding": null,
                          "fontRequired": [],
                          "websafeFonts": [],
                          "className": "",
                          "paragraphWrappedContent": true
                      }
                  }, {
                      "pip": "button",
                      "props": {
                          "content": "<p>Learn More</p>",
                          "color": "color2",
                          "uid": "6647a84ee9684b5185fd331de790e74f",
                          "contentMargin": {
                              "top": 0,
                              "right": "auto",
                              "bottom": 20,
                              "left": "auto"
                          },
                          "tabletOverrides": {
                              "contentMargin": {
                                  "top": 0,
                                  "right": "auto",
                                  "left": "auto"
                              }
                          },
                          "mobileOverrides": {
                              "contentMargin": {
                                  "top": 0,
                                  "right": "auto",
                                  "left": "auto"
                              }
                          },
                          "href": "",
                          "defaultFont": "font2",
                          "defaultFontSize": "fontSize3",
                          "requiresCustomization": true,
                          "quarkClassName": "",
                          "isDonateButton": false,
                          "donateButtonCause": "",
                          "donateButtonAmount": -1,
                          "paragraphWrappedContent": true
                      }
                  }]
              }],
              "props": {
                  "uid": "9b1f5368474a42648929354aa5d56e47"
              }
          }],
          "props": {
              "background": {
                  "color": {
                      "value": "color4",
                      "opacity": 1
                  },
                  "imageTransparency": true,
                  "backgroundType": "color"
              },
              "userHeight": {
                  "top": 70,
                  "bottom": 70
              }
          },
          "slug": "grid-title-title-button-v2",
          "displayName": "Title, Title & Button",
          "version": 3,
          "_uid": "619b09e5c0c34bca8d1eb1fe7d84dc7e"
      }, {
          "children": [{
              "pip": "grid",
              "children": [{
                  "pip": "gridCol",
                  "props": {
                      "size": 6,
                      "alignment": "center",
                      "contentPadding": {
                          "left": 20,
                          "right": 20,
                          "top": 10,
                          "bottom": 10
                      },
                      "uid": "3aa5f224fc66476ab9ffe01874556e91",
                      "backgrounds": [],
                      "spacing": {},
                      "mobileOverrides": {
                          "contentPadding": {
                              "top": 10,
                              "right": 10,
                              "bottom": 10,
                              "left": 10
                          },
                          "spacing": {
                              "top": 0,
                              "right": 0,
                              "bottom": 0,
                              "left": 0
                          }
                      },
                      "pipToHighlight": [],
                      "pipToMoveIndex": []
                  },
                  "children": [{
                      "pip": "title",
                      "props": {
                          "level": 5,
                          "defaultFont": "font2",
                          "content": "<p>© 2019 My Small Business, LLC</p>",
                          "uid": "62caa59d8dd94325899a715a84d35156",
                          "contentMargin": {
                              "top": 0,
                              "right": "auto",
                              "bottom": 20,
                              "left": "auto"
                          },
                          "defaultAlignment": "left",
                          "tabletOverrides": {},
                          "mobileOverrides": {},
                          "requiresCustomization": true,
                          "contentBinding": null,
                          "fontRequired": [],
                          "websafeFonts": [],
                          "className": "",
                          "paragraphWrappedContent": true
                      }
                  }]
              }, {
                  "pip": "gridCol",
                  "props": {
                      "size": 6,
                      "contentPadding": {
                          "left": 20,
                          "right": 20,
                          "top": 10,
                          "bottom": 10
                      },
                      "uid": "c526ae89f9964d1aa3c104c537289ef1",
                      "alignment": "top",
                      "backgrounds": [],
                      "spacing": {},
                      "mobileOverrides": {
                          "contentPadding": {
                              "top": 10,
                              "right": 10,
                              "bottom": 10,
                              "left": 10
                          },
                          "spacing": {
                              "top": 0,
                              "right": 0,
                              "bottom": 0,
                              "left": 0
                          }
                      },
                      "pipToHighlight": [],
                      "pipToMoveIndex": []
                  },
                  "children": [{
                      "pip": "social",
                      "props": {
                          "links": [{
                              "service": "instagram",
                              "url": ""
                          }, {
                              "service": "facebook",
                              "url": ""
                          }, {
                              "service": "twitter",
                              "url": ""
                          }],
                          "iconType": "circle",
                          "uid": "e1d3b3c563c443e69effedb67347ad6c",
                          "contentMargin": {
                              "top": 0,
                              "right": 0,
                              "bottom": 20,
                              "left": "auto"
                          },
                          "tabletOverrides": {
                              "contentMargin": {
                                  "top": 0,
                                  "right": "auto",
                                  "left": "auto"
                              }
                          },
                          "mobileOverrides": {
                              "contentMargin": {
                                  "top": 0,
                                  "right": "auto",
                                  "left": "auto"
                              }
                          },
                          "outerSize": "42px",
                          "innerSizeNoBG": "26px",
                          "innerSizeWithBG": "16px",
                          "requiresCustomization": true
                      }
                  }]
              }],
              "props": {
                  "uid": "4f771d3c2af240deb56380d6dce6f446"
              }
          }],
          "props": {
              "nameable": false,
              "moveable": false,
              "position": "bottom",
              "positionOverlay": true,
              "background": {
                  "imageTransparency": true,
                  "color": {
                      "value": "color4",
                      "opacity": 1
                  },
                  "backgroundType": "color"
              },
              "userHeight": {
                  "bottom": 10,
                  "top": 10
              }
          },
          "slug": "grid-footer-social-links",
          "displayName": "Social Links Footer",
          "version": 3,
          "_uid": "0d381c1e892b488b86e28a793d9ff245"
      }],
      "title": "Home"
  },
  "service": {}
};
/*********/
window.doScroll = function scroll(element, change, easeAmount, callback) {

  // Maximum scroll duration to ensure that scrolling doesn't take forever on long sites
  var MAX_SCROLL_DURATION = 2500;

  if (typeof easeAmount === 'function') {
      callback = easeAmount;
      easeAmount = undefined;
  }

  if (easeAmount) {

      /*
       * We may not want to fully animate the scroll.
       * On long documents, this can be dizzying. Instead, we can
       *  jump to just before the element, then scroll the rest of the way.
       */
      if (Math.abs(change) < easeAmount) {
          easeAmount = change;
      }
      if (change < 0) {
          easeAmount = -easeAmount;
      }
      element.scrollTop += change - easeAmount;
      change = easeAmount;
  }

  var move = function move(amount) {
      element.scrollTop = amount;
  };

  // quadratic easing in/out - acceleration until halfway, then deceleration
  var ease = function ease(t, b, c, d) {
      t = t / (d / 2);
      if (t < 1) {
          return c / 2 * t * t + b;
      }
      t = t - 1;
      return -c / 2 * (t * (t - 2) - 1) + b;
  };

  var requestAnimationFrame = window.requestAnimationFrame || window.webkitRequestAnimationFrame || window.mozRequestAnimationFrame || function(cb) {
      window.setTimeout(cb, 1000 / 60);
  };

  var start = element.scrollTop;
  var currentTime = 0;
  var increment = 20;
  var duration = Math.abs(change) * 500 / 1000;
  if (duration > MAX_SCROLL_DURATION) {
      duration = MAX_SCROLL_DURATION;
  }
  var animateScroll = function animateScroll() {
      currentTime = currentTime + increment;
      // Don't call ease if currentTime > duration, it gives wacky results.
      if (currentTime < duration) {
          move(ease(currentTime, start, change, duration));
          requestAnimationFrame.call(window, animateScroll);
      } else {
          move(start + change);
          if (typeof callback === 'function') {
              callback();
          }
      }
  };
  requestAnimationFrame.call(window, animateScroll);
}