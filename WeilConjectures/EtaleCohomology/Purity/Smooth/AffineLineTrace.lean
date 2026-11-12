/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.SfAffineLineCanonicalDuality
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomology

/-!
# The trace map of the affine line

Let `Λ` be a finite coefficient ring and `p : 𝔸¹_S ⟶ S` the affine line, factored as
`p = q ∘ j` through the standard chart `j : 𝔸¹_S ⟶ ℙ¹_S`, the complement of the section at
infinity, and the projection `q : ℙ¹_S ⟶ S`
(`AlgebraicGeometry.Etale.sfAffineLineCompactification`).
The *trace map of the affine line* (blueprint `definition-trace-map-affine-line`) is the
composite

`Tr_p : Rp_! Λ(1)[2] = Rq_* j_! Λ(1)[2] ⟶ Rq_* Λ(1)[2] ⟶ Λ_S`,

where the first arrow is induced by the counit of `j_! ⊣ j^*` and the second is the trace of the
projective line (`AlgebraicGeometry.Etale.projectiveLineTrace`, blueprint
`lemma-cohomology-projective-line-trace`). With the compactification `(j, q)`, the identification
`Rp_! = Rq_* j_!` holds by definition of `Rp_!`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`).

## Main definitions

- `AlgebraicGeometry.Etale.affineLineTrace`: the trace map `Tr_p` of the affine line, for finite
  coefficients.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] (S : Scheme.{u}) [HasInvertibleExponent Λ S]

/-- Blueprint `definition-trace-map-affine-line`: *the trace map of the affine line*, for finite
coefficients. For the affine line `p : 𝔸¹_S ⟶ S` with its standard compactification
`p = q ∘ j` (`AlgebraicGeometry.Etale.sfAffineLineCompactification`), it is the composite

`Tr_p : Rp_! Λ(1)[2] = Rq_* j_! Λ(1)[2] ⟶ Rq_* Λ(1)[2] ⟶ Λ_S`

of `Rq_*` applied to the counit of the derived adjunction `j_! ⊣ Lj^*` at `Λ_{ℙ¹}(1)[2]` (read
through `Lj^*(Λ_{ℙ¹}(1)[2]) ≅ Λ_{𝔸¹}(1)[2]`) and the trace `Tr_q` of the projective line
(`AlgebraicGeometry.Etale.projectiveLineTrace`, the map (6.5) of blueprint
`lemma-cohomology-projective-line-trace`). -/
noncomputable def affineLineTrace :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (sfAffineLineCompactification S)).obj
      ((tateObject Λ 𝔸(ULift.{u} (Fin 1); S) 1)⟦(2 : ℤ)⟧) ⟶ constantComplex Λ S :=
  (R(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_*[ModuleCat.{u + 1} Λ])).map
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
          (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)).mapDerivedCategory.map
          (leftDerivedUpperStarTateTwoIso Λ
            (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)).inv ≫
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
          (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)).ofNatIsoRight
            (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ)
              (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)).symm).counit.app
          ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧)) ≫
    projectiveLineTrace Λ S (isIso_projectiveLineDecompositionMap Λ S)

end Etale

end AlgebraicGeometry
