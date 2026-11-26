import PEqualNP.Outside.L_meta_20042

namespace FourProductBound

open PEqualNP.Outside.L_meta_20042_aux

theorem upper : PEqualNP.Represents.RepSizeAtMost
    (fun u v : Fin 8 => (7093347072485314830 : ℕ).testBit (8 * u.val + v.val)) 25 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end FourProductBound
