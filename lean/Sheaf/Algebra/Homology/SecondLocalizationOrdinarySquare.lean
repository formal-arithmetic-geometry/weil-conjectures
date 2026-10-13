/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.SecondLocalizationMap
/-! # Ordinary comparison for second localization
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-ordinary-square). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

variable (R A B Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra B Bp] [Algebra R Bp]
  [tRB : IsScalarTower R B Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[R] Bp) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

include tRB in
/-- The ordinary counit comparison commutes with flat change of the second coefficient.
Source: Stacks Project, Tag 06Y6, lemma-derived-base-change; Tag 0DJ8.
(blueprint: lem-pc-second-localization-ordinary-square).

Proof: exact extension of scalars from B to Bp preserves homology. The defining
leftDerivedLift factorization of secondLocalizationDerivedMap makes its composite
with K.counit equal L.counit extended to Bp and followed by the ordinary scalar
extension associator. Evaluate at the restriction of Q to R and apply degree-i
homology. Naturality of flatDerivedHomologyIso, and of the homotopy and derived
homology factorization isomorphisms, identifies this with the ordinary coefficient
map b tensor x to image(b) tensor x. Transpose the B-to-Bp scalar extension
adjunction: its unit evaluates at 1 tensor x, giving exactly
secondLocalizationCohomologyMap. Substitute comparison_eq for both models and
cancel cohomologyIso. The ordinaryIso_tmul equations identify the coefficient
chain map with φ: precompose with L.ordinaryIso and use tensor induction in each
degree. Exact restriction and forgetting scalars commute with homology, by
naturality of mapHomologyIso and its composition identity (compare their maps on
cycles and the surjective homology projection). This gives the displayed
additive square. This argument precedes extension to D: it uses neither
ordinaryToLocalized nor localizedComparison, and makes no invertibility claim
about either comparison. Identity coefficient maps and zero complexes give the
same counit identity; no flatness of D is required. -/
theorem secondLocalization_ordinary_square (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
    (φ : ((forget₂ (ModuleCat.{u} (A ⊗[R] B)) AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj (((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
          (.up ℤ)).obj Q) ⟶
      ((forget₂ (ModuleCat.{u} (A ⊗[R] Bp)) AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj (((ModuleCat.extendScalars (algebraMap A (A ⊗[R] Bp))).mapHomologicalComplex
          (.up ℤ)).obj Q))
    (hφ : ∀ (j : ℤ) (b : B) (x : Q.X j),
      φ.f j (L.ordinaryIso.hom.f j (b ⊗ₜ[R,algebraMap R B] x)) =
        K.ordinaryIso.hom.f j (algebraMap B Bp b ⊗ₜ[R,algebraMap R Bp] x)) :
    (forget₂ (ModuleCat.{u} (A ⊗[R] B)) AddCommGrpCat.{u}).map (L.comparison i) ≫
      (((((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
        (.up ℤ)).obj Q).sc i).mapHomologyIso
          (forget₂ (ModuleCat.{u} (A ⊗[R] B)) AddCommGrpCat.{u})).inv ≫
      HomologicalComplex.homologyMap φ i =
    (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).map
      (secondLocalizationCohomologyMap R A B Bp D hflat Q L K i) ≫
      (forget₂ (ModuleCat.{u} (A ⊗[R] Bp)) AddCommGrpCat.{u}).map (K.comparison i) ≫
        (((((ModuleCat.extendScalars (algebraMap A (A ⊗[R] Bp))).mapHomologicalComplex
          (.up ℤ)).obj Q).sc i).mapHomologyIso
            (forget₂ (ModuleCat.{u} (A ⊗[R] Bp)) AddCommGrpCat.{u})).inv := by
  sorry

end RingTensorCohomology
