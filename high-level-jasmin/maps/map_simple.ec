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
  
  proc __map_simple_plus_one_u64_16 (a:W64.t Array16.t) : W64.t Array16.t = {
    
    var i:W64.t;
    var elem:W64.t;
    
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int 16))) {
      elem <- a.[(W64.to_uint i)];
      elem <@ plus_one (elem);
      a.[(W64.to_uint i)] <- elem;
      i <- (i + (W64.of_int 1));
    }
    return (a);
  }
}.

