/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The strict localization of a smooth surface at a rational point

Let `S` be a smooth surface over an algebraically closed field `k` and `t` a `k`-point of `S`,
with strict localization `T = Spec R`, `R = 𝒪^{sh}_{S,t}`. Then `R` is a regular local ring of
dimension `2` with residue field `k`.

## Main definitions

- `AlgebraicGeometry.Scheme.strictHenselizationAlgebra`: the `k`-algebra structure on `R`.

## Main results

- `AlgebraicGeometry.Scheme.isRegularLocalRing_strictHenselization_of_smooth`: `R` is regular.
- `AlgebraicGeometry.Scheme.ringKrullDim_strictHenselization_of_smooth`: `R` has dimension `2`.
- `AlgebraicGeometry.Scheme.bijective_residue_algebraMap_strictHenselization`: `k ≅ R/𝔪`.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (S : Over (Spec (.of k)))
  (t : Spec (.of k) ⟶ S.left)

/-- The `k`-algebra structure of the strict henselization `R = 𝒪^{sh}_{S,t}` of a `k`-scheme `S`,
from the structure morphism `Spec R ⟶ S ⟶ Spec k`. -/
@[instance_reducible]
noncomputable def strictHenselizationAlgebra : Algebra k (strictHenselization t) :=
  (Spec.preimage (strictLocalizationToBase t ≫ S.hom)).hom.toAlgebra

variable [SmoothOfRelativeDimension 2 S.hom]

/-- The strict henselization of a smooth surface at a `k`-point is a regular local ring. -/
theorem isRegularLocalRing_strictHenselization_of_smooth (ht : t ≫ S.hom = 𝟙 _) :
    IsRegularLocalRing (strictHenselization t) :=
  sorry

/-- The strict henselization of a smooth surface at a `k`-point has dimension `2`. -/
theorem ringKrullDim_strictHenselization_of_smooth (ht : t ≫ S.hom = 𝟙 _) :
    ringKrullDim (strictHenselization t) = 2 :=
  sorry

/-- The residue field of the strict henselization of a `k`-scheme at a `k`-point is `k`. -/
theorem bijective_residue_algebraMap_strictHenselization (ht : t ≫ S.hom = 𝟙 _) :
    letI := strictHenselizationAlgebra S t
    Function.Bijective (IsLocalRing.residue (strictHenselization t) ∘
      algebraMap k (strictHenselization t)) :=
  sorry

end AlgebraicGeometry.Scheme
