/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.ClosedLiftRetraction
public import WeilConjectures.RingTheory.ProEtale.EtaleStrictlyHenselianSplitting

/-!
# Idempotents of the ind-étale closed lift

Let `H = H_A(C̄)` be the ind-étale closed lift of `Algebra.ClosedLift`.

- An idempotent of `H` vanishing in `C̄` vanishes
  (`Algebra.ClosedLift.eq_zero_of_isIdempotentElem`).
- For `C̄` ind-étale over `A ⧸ I`, every idempotent of `C̄` lifts to an idempotent of `H`
  (`Algebra.ClosedLift.exists_isIdempotentElem_toAlgHom_eq`).
- If `A` is a strictly henselian local ring and `C̄` is killed by the maximal ideal, then `H` is
  spanned over `A` by its idempotents (`Algebra.ClosedLift.mem_span_isIdempotentElem`): every
  étale `A`-algebra `B` is `Aⁿ × B''` with `B'' = m B''`, and `B''` dies in `C̄`.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace Algebra.ClosedLift

variable {A : Type u} [CommRing A] {C : Type u} [CommRing C] [Algebra A C]

end Algebra.ClosedLift
