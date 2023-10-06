require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
require import Map_simple Loop Array16.

clone import LOOP as L with 
  type elem <- W64.t,
  op N <- 16,
  theory ArrayN <- Array16.

module Body = { 
  proc body = M.plus_one
}.

equiv map_simple_map : 
  Map_simple.M.__map_simple_plus_one_u64_16 ~ 
  L.MAP.Map(Body).map : ={arg} ==> ={res}.
proof. by proc; inline *; sim. qed.

op oplus_one (x : W64.t) = x + W64.of_int 1.

hoare plus_one_spec x_ : M.plus_one : arg = x_ ==> res = oplus_one x_.
proof. proc; auto => />. qed.

hoare __map_simple_plus_one_u64_16_spec a_ : 
  Map_simple.M.__map_simple_plus_one_u64_16 : 
    arg = a_ ==> 
    res = Array16.map oplus_one a_.
proof.
  conseq map_simple_map (MAP.map_spec Body oplus_one plus_one_spec a_) => // /#.
qed.
(* 
  conseq map_simple_map (_:  arg = a_ ==> res = Array16.map oplus_one a_) => />.
  smt().
  conseq (MAP.map_spec Body oplus_one plus_one_spec a_) => />.
qed.
*)
  
