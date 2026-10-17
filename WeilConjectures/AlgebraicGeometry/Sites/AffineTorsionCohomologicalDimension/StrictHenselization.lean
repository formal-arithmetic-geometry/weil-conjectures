/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension.Algebra

/-!
# The strict henselization of a regular domain

Let `P` be a regular domain and `s : Spec Ω ⟶ Spec P` a geometric point. The strict
henselization `R = 𝒪^{sh}_{Spec P, s}` is the colimit of the rings of the pointed étale
neighbourhoods `Spec A ⟶ Spec P` of `s`. We show:

* `R` is a domain: the local rings of the étale `P`-algebras `A` at the image of `s` are regular,
  hence domains, and an element of `A` which vanishes in such a local ring already vanishes in
  `R`, being killed by an element invertible in `R`;
* `P ⟶ R` is injective, and `R` is algebraic over `P` (étale algebras over a domain are
  algebraic);
* if `s` lies over the generic point of `Spec P`, then `R` is a field.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P : CommRingCat.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Spec P)

/-- The canonical ring homomorphism `P ⟶ 𝒪^{sh}_{Spec P, s}` from a ring to the strict
henselization at a geometric point of its spectrum. -/
noncomputable def toStrictHenselization : P ⟶ strictHenselization s :=
  Spec.preimage (strictLocalizationToBase s)

lemma toStrictHenselization_comp_strictHenselizationEval :
    toStrictHenselization s ≫ strictHenselizationEval s = Spec.preimage s :=
  sorry

theorem isDomain_strictHenselization [IsDomain P] [IsRegularRing P] :
    IsDomain (strictHenselization s) :=
  sorry

theorem injective_toStrictHenselization [IsDomain P] [IsRegularRing P] :
    Function.Injective (toStrictHenselization s) :=
  sorry

theorem isAlgebraic_strictHenselization [IsDomain P] :
    letI := (toStrictHenselization s).hom.toAlgebra
    Algebra.IsAlgebraic P (strictHenselization s) :=
  sorry

/-- If the geometric point `s` lies over the generic point of `Spec P`, i.e. `P ⟶ Ω` is
injective, then the strict henselization is a field. -/
theorem isField_strictHenselization [IsDomain P] [IsRegularRing P]
    (hs : Function.Injective (Spec.preimage s)) :
    IsField (strictHenselization s) :=
  sorry

end AlgebraicGeometry.Scheme
