require import AllCore IntDiv.

from Jasmin require import JArray JWord.

type elem.
op N : int.

axiom N_spec : 0 <= N < W64.modulus.

clone import PolyArray as ArrayN with
  op size <- N.

module type Body = {
  proc body (e:elem) : elem
}.

theory MAP.

module Map(B:Body) = { 
  proc map (a : elem ArrayN.t) = { 
    var i : W64.t;
    var e : elem;
    i <- W64.of_int 0; 
    while (i \ult W64.of_int N) {
      e <- a.[W64.to_uint i];
      e <@ B.body(e);
      a.[W64.to_uint i] <- e;
      i <- i + W64.of_int 1;
    }
    return a;
  }
}.

lemma map_spec_i (B<:Body) (f: elem -> elem) : 
  (forall e_, hoare [B.body: e = e_ ==> res = f e_]) =>
  forall (a_: elem ArrayN.t),
  hoare [Map(B).map : a = a_ ==> 
      forall i, 0 <= i < N => res.[i] = f a_.[i]].
proof.
  move=> body_spec a_.
  have /= hN := N_spec.
  proc.
  while (0 <= to_uint i <= N /\ 
         forall j, a.[j] = if 0 <= j < to_uint i then f a_.[j] else a_.[j]).
  + wp; ecall (body_spec a.[to_uint i]); wp; skip => />.
    move=> &m h0i hiN hj.
    rewrite W64.ultE W64.to_uint_small // => hlt.
    rewrite W64.to_uintD_small /= 1:/#.
    smt(ArrayN.get_setE).
  wp; skip => />.
  split. smt().
  move=> a i; rewrite W64.ultE  W64.to_uint_small // /#.
qed.

lemma map_spec (B<:Body) (f: elem -> elem) : 
  (forall e_, hoare [B.body: e = e_ ==> res = f e_]) =>
  forall (a_: elem ArrayN.t),
  hoare [Map(B).map : a = a_ ==> res = ArrayN.map f a_].
proof.
  move=> body_spec a_.
  conseq (map_spec_i B f body_spec a_).
  move=> /> r heqi; apply /ArrayN.tP => i hi.
  rewrite heqi // ArrayN.mapiE //.
qed.

end MAP.

(* A more complex version *)

theory MAP_iter.

op iter : int.

axiom iter_spec : 0 < iter <= N.

module Map(B:Body) = { 
  proc map (a : elem ArrayN.t) = { 
    var i : W64.t;
    var e : elem;
    var j : int;

    i <- W64.of_int 0; 
    while (i \ult W64.of_int (N %/ iter * iter)) {
      j <- 0;
      while (j < iter) {
        e <- a.[W64.to_uint i + j];
        e <@ B.body(e);
        a.[W64.to_uint i + j] <- e;
        j <- j + 1;
      }
      i <- i + W64.of_int iter;
    }
    j <- 0;
    while (j < N %% iter) {
      e <- a.[W64.to_uint i + j];
      e <@ B.body(e);
      a.[W64.to_uint i + j] <- e;
      j <- j + 1;
    }
    return a;
  }
}.

lemma map_spec_i (B<:Body) (f: elem -> elem) : 
  (forall e_, hoare [B.body: e = e_ ==> res = f e_]) =>
  forall (a_: elem ArrayN.t),
  hoare [Map(B).map : a = a_ ==> 
      forall i, 0 <= i < N => res.[i] = f a_.[i]].
proof.
  move=> body_spec a_.
  have /= hN := N_spec. have hiter := iter_spec.
  proc.
  while (to_uint i = N %/iter * iter /\ 0 <= j <= N %% iter /\
         forall k, a.[k] = if 0 <= k < to_uint i + j then f a_.[k] else a_.[k]).
  + wp; ecall (body_spec a.[to_uint i + j]); wp; skip => />.
    move=> &m hi h0j hjN hk hlt; smt(divzE ArrayN.get_setE).
  wp; while (0 <= to_uint i <= N %/ iter * iter /\ 
         to_uint i %% iter = 0 /\ 
         forall k, a.[k] = if 0 <= k < to_uint i then f a_.[k] else a_.[k]).
  + wp; while (0 <= to_uint i < N %/ iter * iter /\ 
         to_uint i %% iter = 0 /\
         0 <= j <= iter /\
         forall k, a.[k] = if 0 <= k < to_uint i + j then f a_.[k] else a_.[k]).
    + wp; ecall (body_spec a.[to_uint i + j]); wp; skip => />.
      move=> &m h0i hiN hmod h0j hjit hk hlt. 
      by smt(edivzP ArrayN.get_setE).
    wp; skip => /> &m hoi hiN hmod hk.
    rewrite W64.ultE W64.to_uint_small 1:/# => /> ?. 
    by rewrite W64.to_uintD_small W64.to_uint_small /#.
  wp; skip => />.
  split; 1: smt().
  move=> a i; rewrite W64.ultE W64.to_uint_small 1:/# => *; smt(edivzP).
qed.

end MAP_iter.

