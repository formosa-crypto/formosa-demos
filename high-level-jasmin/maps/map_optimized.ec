require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array16.
require import WArray128.



module M = {
  proc plus_one (a:W64.t) : W64.t = {
    
    
    
    a <- (a + (W64.of_int 1));
    return (a);
  }
  
  proc __map_optimized_plus_one_u64_16_4 (a:W64.t Array16.t) : W64.t Array16.t = {
    var aux: int;
    
    var i:W64.t;
    var elem:W64.t;
    var j:int;
    
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int ((16 %/ 4) * 4)))) {
      j <- 0;
      while (j < 4) {
        elem <- a.[(W64.to_uint i)];
        elem <@ plus_one (elem);
        a.[(W64.to_uint i)] <- elem;
        i <- (i + (W64.of_int 1));
        j <- j + 1;
      }
    }
    aux <- (16 %% 4);
    j <- 0;
    while (j < aux) {
      elem <- a.[(W64.to_uint i)];
      elem <@ plus_one (elem);
      a.[(W64.to_uint i)] <- elem;
      i <- (i + (W64.of_int 1));
      j <- j + 1;
    }
    return (a);
  }
}.

