/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.SfAffineLineCanonicalDuality
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek

/-!
# The trace map of the affine line

For the projection `p : 𝔸¹_S ⟶ S`, compactified by the standard chart `j : 𝔸¹_S ⟶ ℙ¹_S` and the
projection `q : ℙ¹_S ⟶ S` (`AlgebraicGeometry.Etale.sfAffineLineCompactification`), the
compactly supported direct image is `Rp_! = Rq_* j_!`, and the *trace map of the affine line* is
the composite

`Tr_p : Rp_! Λ_{𝔸¹_S}(1)[2] = Rq_* j_! Λ_{𝔸¹_S}(1)[2] ⟶ Rq_* Λ_{ℙ¹_S}(1)[2] ⟶ Λ_S`

of the counit `j_! j^* ⟶ id`, read through `j^* Λ_{ℙ¹_S}(1)[2] ≅ Λ_{𝔸¹_S}(1)[2]`, and the trace
of the projective line (`AlgebraicGeometry.Etale.projectiveLineTrace`). This is blueprint
`definition-trace-map-affine-line` for a finite coefficient ring `Λ`.

## Main definitions

- `AlgebraicGeometry.Etale.affineLineTateShiftRestrictionIso`:
  `j^* Λ_{ℙ¹_S}(1)[2] ≅ Λ_{𝔸¹_S}(1)[2]`.
- `AlgebraicGeometry.Etale.affineLineTrace`: the trace `Rp_! Λ_{𝔸¹_S}(1)[2] ⟶ Λ_S`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] (S : Scheme.{u})
  [HasInvertibleExponent Λ S]

/-- The restriction of the twisted constant complex of the projective line to the standard chart
`j : 𝔸¹_S ⟶ ℙ¹_S`: `j^* Λ_{ℙ¹_S}(1)[2] ≅ Λ_{𝔸¹_S}(1)[2]`, through `D(j^*) ≅ Lj^*`, the shift
compatibility of `Lj^*` and the identification `Lj^* Λ(1) ≅ Λ(1)` of the Tate twist datum. -/
noncomputable def affineLineTateShiftRestrictionIso :
    (D((AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)^*[ModuleCat.{u + 1} Λ])).obj
        ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧) ≅
      (tateObject Λ 𝔸(ULift.{u} (Fin 1); S) 1)⟦(2 : ℤ)⟧ :=
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); S) := .of_hom (𝔸(ULift.{u} (Fin 1); S) ↘ S)
  ((leftDerivedUpperStarIsoMapDerivedCategory _ _).app _).symm ≪≫
    (Functor.commShiftIso
      (L((AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)^*[ModuleCat.{u + 1} Λ]))
      (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso (leftDerivedUpperStarTateObjectIso _ 1)

/-- Blueprint `definition-trace-map-affine-line`: *the trace map of the affine line.* For the
projection `p : 𝔸¹_S ⟶ S` with the compactification `𝔸¹_S ⟶[j] ℙ¹_S ⟶[q] S`, so that
`Rp_! = Rq_* j_!`, the trace is the composite

`Tr_p : Rp_! Λ_{𝔸¹_S}(1)[2] ≅ Rq_* j_! j^* Λ_{ℙ¹_S}(1)[2] ⟶ Rq_* Λ_{ℙ¹_S}(1)[2] ⟶ Λ_S`

of the counit of `j_! ⊣ j^*` and the trace `Tr_q` of the projective line
(`AlgebraicGeometry.Etale.projectiveLineTrace`, the map (6.5) of
`lemma-cohomology-projective-line-trace`). The coefficient ring `Λ` is finite; the trace for
`ℓ`-adic coefficients is not part of this definition. -/
noncomputable def affineLineTrace [HasKummerClass.IsNormalized Λ] :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (sfAffineLineCompactification S)).obj ((tateObject Λ 𝔸(ULift.{u} (Fin 1); S) 1)⟦(2 : ℤ)⟧) ⟶
      constantComplex Λ S :=
  (R(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_*[ModuleCat.{u + 1} Λ])).map
      ((D((AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)_!open[
        ModuleCat.{u + 1} Λ])).map
          (affineLineTateShiftRestrictionIso Λ S).inv ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
          (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)).counit.app _) ≫
    projectiveLineTrace Λ S (isIso_projectiveLineDecompositionMap Λ S)

end AlgebraicGeometry.Etale
