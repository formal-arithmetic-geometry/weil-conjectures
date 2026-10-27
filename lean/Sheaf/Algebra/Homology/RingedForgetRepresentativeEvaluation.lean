/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.Algebra.Homology.RingedForgetTensorDescent
import all Sheaf.Algebra.Homology.RingedSliceRepresentativeEvaluation
import all Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import Sheaf.Algebra.Homology.RingedForgetChainUncurry
import Sheaf.Algebra.Homology.RingedForgetHomRepresentative

/-! # Evaluation compatibility on K-flat and K-injective representatives

Source: Stacks 08J9, 070I; steps 5--8 of ringed tensor transposition
(blueprint: lem-sf-ringed-forget-representative-evaluation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe b vb a va c v r d vd s wb wa

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures

namespace CategoryTheory.RingedForgetTensorTransposition

-- Reuse the small-site transport directly when elaborating coefficient-ring compositions.
attribute [local instance 1000001] RingedDerivedNative.cachedCompose
attribute [local instance 20000] siteAbelianHasSheafify siteAbelianWEqualsLocallyBijective


variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

variable [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  [U.PreservesKInjectiveComplexes]
  (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
  (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
    _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)

variable (χ : RingedForgetTwoInjective.Comparison.{wb, wa, c, v, r, d, vd, s}
    J R J' R' U u.hom)

attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolution coefficientHomResolutionIso coefficientHomResolutionInverse
  coefficientTotalTensor coefficientTensorGenerator CoefficientTensorModels.iso

private def makeComparisonData
    {B : Type b} [Category.{vb} B] {A : Type a} [Category.{va} A]
    (HB : Bᵒᵖ × B ⥤ B) (HA : Aᵒᵖ × A ⥤ A) (F : B ⥤ A)
    (S : CoefficientClosedStructure HB) (T : CoefficientClosedStructure HA)
    (β : @SymmetricCategory B _ S.monoidal)
    (γ : @SymmetricCategory A _ T.monoidal)
    (μ : S.tensor ⋙ F ≅ (F.prod F) ⋙ T.tensor)
    (η : HB ⋙ F ≅ (F.op.prod F) ⋙ HA) :
    RingedSliceEvaluationComparisons HB HA F S T True where
  rho M K := μ.app (M, K)
  eta K L := η.app (op K, L)
  rho_naturality M K M' K' f g :=
    μ.hom.naturality (X := (M, K)) (Y := (M', K')) (f, g)
  eta_naturality K L K' L' f g :=
    η.hom.naturality (X := (op K, L)) (Y := (op K', L')) (f.op, g)
  sigma M K := β.toBraidedCategory.braiding M K
  sigma_naturality M K M' K' f g := by
    let := S.monoidal
    let := β
    exact BraidedCategory.braiding_naturality f g
  sigmaU M K := γ.toBraidedCategory.braiding M K
  sigmaU_naturality M K M' K' f g := by
    let := T.monoidal
    let := γ
    exact BraidedCategory.braiding_naturality f g
  kflat := True.intro

private def comparisonData
    (m : TensorComparison.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U u SB TB βB cB SA TA βA cA) :
    RingedSliceEvaluationComparisons
      (derivedInternalHomOfUniverses.{c, v, r, wb} J R)
      (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R')
      U.mapDerivedCategory SB SA True :=
  makeComparisonData _ _ U.mapDerivedCategory SB SA βB βA m.derived χ.derived

set_option maxHeartbeats 800000 in
-- Compare model isomorphisms without unfolding the total tensor or chosen Hom resolution.
/-- The specified tensor and Hom comparisons preserve evaluation on a flat-term
K-flat source and a K-injective target.
Source: Stacks 06YU and 08J9; step 2 of normalized ringed uncurrying
(blueprint: lem-sf-ringed-forget-representative-evaluation).

Proof: choose a flat-term K-flat resolution q:Q to Hom(P,I). The model
normalization identifies the evaluations with the localized ordinary uncurries
of q and U(q) followed by the Hom comparison. The proved chain comparison
identifies these maps. The normalized Hom representative formula and the given
tensor representative square identify the two model maps; the generic
model-evaluation lemma cancels their isomorphisms to give the result. -/
theorem ringed_forget_representative_evaluation
    (m : TensorComparison.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U u SB TB βB cB SA TA βA cA)
    (preserves_flat_models :
      ∀ P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
        P.IsKFlatIndependentCoefficients →
        (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (R := R) (P.X p)) →
        CochainComplex.IsKFlatIndependentCoefficients (R := R')
          ((U.mapHomologicalComplex (.up ℤ)).obj P) ∧
        ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{d, vd, max d vd s, max d vd s}
          (R := R') (U.obj (P.X p)))
    (P I : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (fP : ∀ n, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (R := R) (P.X n))
    [I.IsKInjective] :
    m.derived.inv.app ((derivedInternalHomOfUniverses.{c, v, r, wb} J R).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I), DerivedCategory.Q.obj P) ≫
        U.mapDerivedCategory.map (SB.evaluation (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj I)) =
      SA.tensor.map
        (X := (U.mapDerivedCategory.obj ((derivedInternalHomOfUniverses.{c, v, r, wb} J R).obj
          (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I)),
          U.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
        (Y := ((derivedInternalHomOfUniverses.{d, vd, s, wa} J' R').obj
          (op (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P)),
            U.mapDerivedCategory.obj (DerivedCategory.Q.obj I)),
          U.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
        (χ.derived.hom.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I), 𝟙 _) ≫
          SA.evaluation (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
          (U.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) := by
  let rC := U.mapHomologicalComplex (.up ℤ)
  let α := U.mapDerivedCategoryFactors
  let κ := χ.source.iso P I
  let κA := χ.target.iso (rC.obj P) (rC.obj I)
  obtain ⟨Q, q, hQ, fQ, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := R) (homComplex (R := R) P I)
  have fQ' (n : ℤ) : SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (R := R) (Q.X n) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (Q.X n)).symm (fQ n)
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  let qA := rC.map q ≫ χ.chain.hom.app (op P, I)
  let f := (RingedDerivedNative.chainEquiv.{c, v, r} J R Q P I).symm q
  let fA := (RingedDerivedNative.chainEquiv.{d, vd, s} J' R'
    (rC.obj Q) (rC.obj P) (rC.obj I)).symm qA
  apply evaluation_of_models SB SA (comparisonData J R J' R' U u SB TB βB cB SA TA βA cA χ m)
    (TB.iso J R SB Q P hQ hP)
    (TA.iso J' R' SA (rC.obj Q) (rC.obj P)
      (preserves_flat_models Q hQ fQ').1 (preserves_flat_models P hP fP).1)
    (α.app Q) (α.app P) (α.app I)
    (α.app ((coefficientTotalTensor.{r, c, v} J R).obj (Q, P)) ≪≫
      DerivedCategory.Q.mapIso (m.chain.app (Q, P)))
    (asIso (DerivedCategory.Q.map q) ≪≫ κ.symm)
    (DerivedCategory.Q.map qA ≫ κA.inv)
    (DerivedCategory.Q.map f) (DerivedCategory.Q.map fA)
  · exact model_evaluation.{c, v, r, wb} J R SB TB Q P I hQ hP κ
      (χ.source.normalization P I) q
  · exact model_evaluation.{d, vd, s, wa} J' R' SA TA
      (rC.obj Q) (rC.obj P) (rC.obj I)
      (preserves_flat_models Q hQ fQ').1 (preserves_flat_models P hP fP).1 κA
      (χ.target.normalization (rC.obj P) (rC.obj I)) qA
  · have hm := m.representative Q P hQ hP
      (preserves_flat_models Q hQ fQ').1 (preserves_flat_models P hP fP).1 fQ' fP
    simpa only [comparisonData, makeComparisonData, Iso.app_hom, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc] using hm
  · exact ringed_forget_hom_representative J R J' R' U u χ Q P I q
  · have hc := ringed_forget_chain_uncurry J R J' R' U u Q P I
      (m.chain.app (Q, P)) (m.summand Q P) (χ.chain.app (op P, I)) (χ.projection P I)
      q f fA
      (fun a b V x y ↦ RingedDerivedNative.chainEquiv_symm_pure.{c, v, r, wb}
        J R Q P I q a b (a + b) rfl (add_comm b a) V x y)
      (fun a b V x y ↦ RingedDerivedNative.chainEquiv_symm_pure.{d, vd, s, wa}
        J' R' (rC.obj Q) (rC.obj P) (rC.obj I) qA
        a b (a + b) rfl (add_comm b a) V x y)
    have hn := α.hom.naturality f
    dsimp only [Functor.comp_map] at hn
    change U.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫ α.hom.app I = _
    rw [hn]
    change α.hom.app _ ≫ DerivedCategory.Q.map (rC.map f) = _
    rw [hc]
    simp only [Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Category.assoc, fA, qA, rC]

end CategoryTheory.RingedForgetTensorTransposition
