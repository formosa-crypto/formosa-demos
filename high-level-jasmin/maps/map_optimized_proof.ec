require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
require import Map_optimized Loop Array16.

clone import LOOP as L with 
  type elem <- W64.t,
  op N <- 16,
  theory ArrayN <- Array16.

clone import L.MAP_iter as I with
  op iter <- 4.

module Body = { 
  proc body = M.plus_one
}.

equiv map_optimized_map : 
  Map_optimized.M.__map_optimized_plus_one_u64_16_4 ~ 
  I.Map(Body).map_incr : ={arg} ==> ={res}.
proof. proc; inline *; sim. qed.

op oplus_one (x : W64.t) = x + W64.of_int 1.

hoare plus_one_spec x_ : M.plus_one : arg = x_ ==> res = oplus_one x_.
proof. proc; auto => />. qed.

hoare __map_optimized_plus_one_u64_16_spec a_ : 
  Map_optimized.M.__map_optimized_plus_one_u64_16_4 : 
    arg = a_ ==> 
    res = Array16.map oplus_one a_.
proof.
  conseq map_optimized_map (I.map_incr_spec Body oplus_one plus_one_spec a_) => // /#.
qed.
