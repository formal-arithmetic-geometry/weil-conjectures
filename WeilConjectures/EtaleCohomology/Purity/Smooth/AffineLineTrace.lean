/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.SfAffineLineCanonicalDuality
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange

/-!
# The trace map of the affine line

For a finite coefficient ring `Λ` whose exponent is invertible on `S`, the projection
`p : 𝔸¹_S ⟶ S` factors as the open immersion `j : 𝔸¹_S ⟶ ℙ¹_S` followed by the proper projection
`q : ℙ¹_S ⟶ S`, so that `Rp_! = Rq_* j_!`. The *trace map of the affine line* is the composite

`Tr_p : Rp_! Λ(1)[2] = Rq_* j_! Λ(1)[2] ⟶ Rq_* Λ_{ℙ¹_S}(1)[2] ⟶ Λ_S`

of `Rq_*` applied to the counit `j_! j^* ⟶ 𝟭` and of the trace `Tr_q` of the projective line
(`AlgebraicGeometry.Etale.projectiveLineTrace`).

## Main definitions

- `AlgebraicGeometry.Etale.affineLineTraceOfCompactification`: the trace on the compactly supported
  direct image of the compactification `𝔸¹_S ⊆ ℙ¹_S`.
- `AlgebraicGeometry.Etale.affineLineTrace`: the trace on `R(p)_!`, read through the independence
  of the compactification.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] (S : Scheme.{u}) [HasInvertibleExponent Λ S]

/-- The trace map of the affine line `p : 𝔸¹_S ⟶ S`, on the compactly supported direct image
`Rp_! = Rq_* j_!` of the compactification `j : 𝔸¹_S ⟶ ℙ¹_S`, `q : ℙ¹_S ⟶ S`: the composite

`Rq_* j_! Λ(1)[2] ≅ Rq_* j_! Lj^*(Λ(1)[2]) ⟶ Rq_* Λ_{ℙ¹_S}(1)[2] ⟶ Λ_S`

of the counit of `j_! ⊣ j^*` and the trace `Tr_q` of the projective line. -/
noncomputable def affineLineTraceOfCompactification :
    (Rf_!(sfAffineLineCompactification S)[ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ 𝔸(ULift.{u} (Fin 1); S) 1)⟦(2 : ℤ)⟧) ⟶ constantComplex Λ S :=
  (R(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_*[ModuleCat.{u + 1} Λ])).map
      ((D((AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)_!open[
          ModuleCat.{u + 1} Λ])).map
        (leftDerivedUpperStarTateTwoIso Λ
          (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)).inv ≫
        (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ
          (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)).counit.app _) ≫
    projectiveLineTrace Λ S

/-- The trace map of the affine line `Tr_p : Rp_! Λ(1)[2] ⟶ Λ_S`, on the compactly supported
direct image `R(p)_!`: the trace `AlgebraicGeometry.Etale.affineLineTraceOfCompactification` of
the compactification `𝔸¹_S ⊆ ℙ¹_S`, read through the identification `Rp_! ≅ Rq_* j_!` of
compactly supported direct images attached to different compactifications. -/
noncomputable def affineLineTrace :
    (R((𝔸(ULift.{u} (Fin 1); S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ 𝔸(ULift.{u} (Fin 1); S) 1)⟦(2 : ℤ)⟧) ⟶ constantComplex Λ S :=
  (rightDerivedLowerShriekIso Λ (sfAffineLineCompactification S)).inv.app _ ≫
    affineLineTraceOfCompactification Λ S

end Etale

end AlgebraicGeometry
