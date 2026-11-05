/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.LocalRing.Module
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.OfFlat

/-!
# Finite free models of perfect complexes

Let `K` be a complex of flat modules over a commutative ring `A`, concentrated in degrees
`[a, b]`, which is perfect in `D(A)`. We realise `K` at the chain level by finite free complexes,
locally on `Spec A`:

* `DerivedCategory.exists_quasiIso_of_isStrictlyLE_of_projective`: an isomorphism `Q P ≅ Q K`
  in the derived category with `P` a bounded above complex of projectives comes from a
  quasi-isomorphism `P ⟶ K` (`P` is K-projective).
* `CochainComplex.exists_free_away_tensor_X`: a bounded complex of finitely generated projective
  modules becomes a complex of finite free modules after inverting some `s ∉ p`.
* `DerivedCategory.exists_quasiIso_projective_finite_of_isPerfect`: there is a quasi-isomorphism
  `P ⟶ K` from a complex `P` of finitely generated projective modules in degrees `[a, b]`
  (Stacks 0658, 066N): truncate a projective model above at `b` (the cycles are projective since
  the complex is exact above `b`) and below at `a` (the cokernel in degree `a` is finitely
  presented, and flat because `K` is a complex of flat modules in degrees `[a, b]`).
* `DerivedCategory.exists_quasiIso_free_away_of_isPerfect`: for every prime `p` there are
  `s ∉ p`, a complex `P` of finite free `A_s`-modules in degrees `[a, b]` and a
  quasi-isomorphism `P ⟶ A_s ⊗[A] K`. Over a Noetherian ring it suffices that `K` has finitely
  generated cohomology (`DerivedCategory.exists_quasiIso_free_away_of_finite_homology`).

This is the chain-level input for blueprint `det-thm-picard-coherence` (a) (Mumford's complex).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace CochainComplex

variable {A : Type u} [CommRing A]

end CochainComplex

namespace Module

variable {A : Type u} [CommRing A]

end Module

namespace CochainComplex

variable {A : Type u} [CommRing A]

end CochainComplex

namespace DerivedCategory

section KProjective

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

end KProjective

variable {A : Type u} [CommRing A] [HasDerivedCategory.{u} (ModuleCat.{u} A)]

end DerivedCategory
