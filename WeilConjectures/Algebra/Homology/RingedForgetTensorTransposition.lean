/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedForgetTwoInjectiveHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement

public import WeilConjectures.Algebra.Homology.RingedForgetTensorTranspositionData
import WeilConjectures.Algebra.Homology.RingedForgetNormalizedUncurry

/-! # Normalized tensor and transposition under ringed forgetting

Source: the internal-Hom/evaluation/transposition paragraph of
blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md;
Stacks Project, Tags 015F, 06YS, 06YU, 0G7D, 0A90, 0A96, 070I, 08J9 and 0FPT
(blueprint: lem-sf-ringed-forget-tensor-transposition).

The auxiliary data below specify the comparisons on actual total-tensor summands.
The double-dual arrow is the transpose of symmetric evaluation, with no invertibility claim.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe b vb a va c v r d vd s wb wa

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures

namespace CategoryTheory.RingedForgetTensorTransposition

section FormalLaws

variable {B : Type b} [Category.{vb} B] {A : Type a} [Category.{va} A]
  {H : Bᵒᵖ × B ⥤ B} (S : CoefficientClosedStructure H)

private theorem uncurry_eq (T P Q : B) (g : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm g =
      S.tensor.map (X := (T, P)) (Y := (H.obj (op P, Q), P))
        (g, 𝟙 P) ≫ S.evaluation P Q := by
  let := S.monoidal
  simp [CoefficientClosedStructure.transpose, CoefficientClosedStructure.evaluation,
    CoefficientClosedStructure.tensor, Adjunction.homEquiv, MonoidalCategory.tensor]

private theorem uncurry_left (T T' P Q : B) (f : T' ⟶ T)
    (g : T ⟶ H.obj (op P, Q)) :
    (S.transpose T' P Q).symm (f ≫ g) =
      S.tensor.map (X := (T', P)) (Y := (T, P)) (f, 𝟙 P) ≫
        (S.transpose T P Q).symm g := by
  let := S.monoidal
  rw [uncurry_eq, uncurry_eq]
  change ((f ≫ g) ⊗ₘ 𝟙 P) ≫ _ = (f ⊗ₘ 𝟙 P) ≫ ((g ⊗ₘ 𝟙 P) ≫ _)
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]

private theorem uncurry_hom (T P P' Q : B) (f : P' ⟶ P)
    (g : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P' Q).symm
        (g ≫ H.map (X := (op P, Q)) (Y := (op P', Q)) (f.op, 𝟙 Q)) =
      S.tensor.map (X := (T, P')) (Y := (T, P)) (𝟙 T, f) ≫
        (S.transpose T P Q).symm g := by
  let := S.monoidal
  have he :
      (H.map (X := (op P, Q)) (Y := (op P', Q)) (f.op, 𝟙 Q) ⊗ₘ 𝟙 P') ≫
          S.evaluation P' Q =
        (𝟙 (H.obj (op P, Q)) ⊗ₘ f) ≫ S.evaluation P Q := by
    simpa [CoefficientClosedStructure.evaluation] using S.evaluation_naturality P P' Q f
  simp only [uncurry_eq]
  change ((g ≫ _) ⊗ₘ 𝟙 P') ≫ _ = (𝟙 T ⊗ₘ f) ≫ ((g ⊗ₘ 𝟙 P) ≫ _)
  calc
    _ = (g ⊗ₘ 𝟙 P') ≫
        ((H.map (X := (op P, Q)) (Y := (op P', Q)) (f.op, 𝟙 Q) ⊗ₘ 𝟙 P') ≫
          S.evaluation P' Q) := by simp
    _ = (g ⊗ₘ 𝟙 P') ≫ ((𝟙 (H.obj (op P, Q)) ⊗ₘ f) ≫ S.evaluation P Q) := by
      rw [he]
    _ = _ := by
      simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]

private theorem delta_uncurry (β : @SymmetricCategory B _ S.monoidal) (W K : B) :
    (S.transpose K (H.obj (op K, W)) W).symm (delta S β W K) =
      (β.toBraidedCategory.braiding K (H.obj (op K, W))).hom ≫ S.evaluation K W :=
  (S.transpose _ _ _).symm_apply_apply _

private theorem delta_natural (β : @SymmetricCategory B _ S.monoidal)
    (W K K' : B) (f : K ⟶ K') :
    delta S β W K ≫
        H.map (X := (op (H.obj (op K, W)), W))
          (Y := (op (H.obj (op K', W)), W))
          ((H.map (X := (op K', W)) (Y := (op K, W)) (f.op, 𝟙 W)).op, 𝟙 W) =
      f ≫ delta S β W K' := by
  let := S.monoidal
  let := β
  apply (S.transpose K (H.obj (op K', W)) W).symm.injective
  rw [uncurry_hom, uncurry_left, delta_uncurry, delta_uncurry]
  change (𝟙 K ⊗ₘ H.map (f.op, 𝟙 W)) ≫
      ((β_ K (H.obj (op K, W))).hom ≫ S.evaluation K W) =
    (f ⊗ₘ 𝟙 (H.obj (op K', W))) ≫
      ((β_ K' (H.obj (op K', W))).hom ≫ S.evaluation K' W)
  have he : (H.map (f.op, 𝟙 W) ⊗ₘ 𝟙 K) ≫ S.evaluation K W =
      (𝟙 (H.obj (op K', W)) ⊗ₘ f) ≫ S.evaluation K' W := by
    simpa [CoefficientClosedStructure.evaluation] using S.evaluation_naturality K' K W f
  simp only [BraidedCategory.braiding_naturality_assoc]
  rw [he]

private theorem braid_natural (β : @SymmetricCategory B _ S.monoidal)
    {X X' Y Y' : B} (f : X ⟶ Y) (g : X' ⟶ Y') :
    S.tensor.map (X := (X, X')) (Y := (Y, Y')) (f, g) ≫
        (β.toBraidedCategory.braiding Y Y').hom =
      (β.toBraidedCategory.braiding X X').hom ≫
        S.tensor.map (X := (X', X)) (Y := (Y', Y)) (g, f) := by
  let := S.monoidal
  let := β
  exact BraidedCategory.braiding_naturality f g

private theorem laws_of_uncurry
    {HB : Bᵒᵖ × B ⥤ B} {HA : Aᵒᵖ × A ⥤ A}
    (SB : CoefficientClosedStructure HB) (SA : CoefficientClosedStructure HA)
    (βB : @SymmetricCategory B _ SB.monoidal)
    (βA : @SymmetricCategory A _ SA.monoidal) (F : B ⥤ A)
    (χ : HB ⋙ F ≅ (F.op.prod F) ⋙ HA)
    (μ : SB.tensor ⋙ F ≅ (F.prod F) ⋙ SA.tensor)
    (hσ : ∀ X Y : B,
      F.map (βB.toBraidedCategory.braiding X Y).hom ≫ μ.hom.app (Y, X) =
        μ.hom.app (X, Y) ≫ (βA.toBraidedCategory.braiding (F.obj X) (F.obj Y)).hom)
    (hu : ∀ (M K L : B) (f : M ⟶ HB.obj (op K, L)),
      (SA.transpose (F.obj M) (F.obj K) (F.obj L)).symm
          (F.map f ≫ χ.hom.app (op K, L)) =
        μ.inv.app (M, K) ≫ F.map ((SB.transpose M K L).symm f)) :
    TranspositionLaws HB HA SB SA βB βA F χ μ := by
  have he (K L : B) :
      μ.hom.app (HB.obj (op K, L), K) ≫
          SA.tensor.map
            (X := (F.obj (HB.obj (op K, L)), F.obj K))
            (Y := (HA.obj (op (F.obj K), F.obj L), F.obj K))
            (χ.hom.app (op K, L), 𝟙 _) ≫ SA.evaluation (F.obj K) (F.obj L) =
        F.map (SB.evaluation K L) := by
    have h := hu (HB.obj (op K, L)) K L (𝟙 _)
    have hi : (SB.transpose (HB.obj (op K, L)) K L).symm (𝟙 _) =
        SB.evaluation K L := (SB.adjunction K).homEquiv_symm_id L
    rw [Functor.map_id, Category.id_comp, hi, uncurry_eq] at h
    rw [h]
    simp
  refine ⟨hu, he, delta_natural SB βB, delta_natural SA βA, ?_⟩
  intro W K
  let := SA.monoidal
  let := βA
  apply (SA.transpose (F.obj K) (HA.obj (op (F.obj K), F.obj W)) (F.obj W)).symm.injective
  rw [← Category.assoc, uncurry_hom, hu, delta_uncurry, delta_uncurry, Functor.map_comp]
  have hs :
      μ.inv.app (K, HB.obj (op K, W)) ≫
          F.map (βB.toBraidedCategory.braiding K (HB.obj (op K, W))).hom =
        (β_ (F.obj K) (F.obj (HB.obj (op K, W)))).hom ≫
          μ.inv.app (HB.obj (op K, W), K) := by
    apply (cancel_mono (μ.hom.app (HB.obj (op K, W), K))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [hσ]
    simp only [Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  have hev : μ.inv.app (HB.obj (op K, W), K) ≫ F.map (SB.evaluation K W) =
      SA.tensor.map
        (X := (F.obj (HB.obj (op K, W)), F.obj K))
        (Y := (HA.obj (op (F.obj K), F.obj W), F.obj K))
        (χ.hom.app (op K, W), 𝟙 _) ≫ SA.evaluation (F.obj K) (F.obj W) := by
    rw [← he K W]
    simp
  rw [← Category.assoc (μ.inv.app _) _, hs]
  simp only [Category.assoc]
  rw [hev]
  let a : F.obj (HB.obj (op K, W)) ≅ HA.obj (op (F.obj K), F.obj W) :=
    χ.app (op K, W)
  let e : SA.tensor.obj (HA.obj (op (F.obj K), F.obj W), F.obj K) ⟶ F.obj W :=
    SA.evaluation (F.obj K) (F.obj W)
  let p : SA.tensor.obj (F.obj K, HA.obj (op (F.obj K), F.obj W)) ⟶
      SA.tensor.obj (F.obj K, F.obj (HB.obj (op K, W))) :=
    SA.tensor.map (𝟙 (F.obj K), a.inv)
  let b : SA.tensor.obj (F.obj K, F.obj (HB.obj (op K, W))) ⟶
      SA.tensor.obj (F.obj (HB.obj (op K, W)), F.obj K) :=
    (βA.toBraidedCategory.braiding (F.obj K) (F.obj (HB.obj (op K, W)))).hom
  let b' : SA.tensor.obj (F.obj K, HA.obj (op (F.obj K), F.obj W)) ⟶
      SA.tensor.obj (HA.obj (op (F.obj K), F.obj W), F.obj K) :=
    (βA.toBraidedCategory.braiding (F.obj K) (HA.obj (op (F.obj K), F.obj W))).hom
  let q : SA.tensor.obj (F.obj (HB.obj (op K, W)), F.obj K) ⟶
      SA.tensor.obj (HA.obj (op (F.obj K), F.obj W), F.obj K) :=
    SA.tensor.map (a.hom, 𝟙 (F.obj K))
  let r : SA.tensor.obj (HA.obj (op (F.obj K), F.obj W), F.obj K) ⟶
      SA.tensor.obj (F.obj (HB.obj (op K, W)), F.obj K) :=
    SA.tensor.map (a.inv, 𝟙 (F.obj K))
  change p ≫ b ≫ q ≫ e = b' ≫ e
  have hp : p ≫ b = b' ≫ r := braid_natural SA βA (𝟙 (F.obj K)) a.inv
  have hc : r ≫ q = 𝟙 _ := by
    change SA.tensor.map (X := (HA.obj (op (F.obj K), F.obj W), F.obj K))
        (Y := (F.obj (HB.obj (op K, W)), F.obj K)) (a.inv, 𝟙 (F.obj K)) ≫
      SA.tensor.map (X := (F.obj (HB.obj (op K, W)), F.obj K))
        (Y := (HA.obj (op (F.obj K), F.obj W), F.obj K)) (a.hom, 𝟙 (F.obj K)) = 𝟙 _
    rw [← SA.tensor.map_comp]
    change SA.tensor.map (X := (HA.obj (op (F.obj K), F.obj W), F.obj K))
      (Y := (HA.obj (op (F.obj K), F.obj W), F.obj K))
      (a.inv ≫ a.hom, 𝟙 (F.obj K) ≫ 𝟙 (F.obj K)) = 𝟙 _
    simp only [a.inv_hom_id, Category.id_comp]
    exact SA.tensor.map_id _
  calc
    p ≫ b ≫ q ≫ e = (p ≫ b) ≫ (q ≫ e) := (Category.assoc p b (q ≫ e)).symm
    _ = (b' ≫ r) ≫ (q ≫ e) := congrArg (fun z ↦ z ≫ (q ≫ e)) hp
    _ = b' ≫ ((r ≫ q) ≫ e) := by simp only [Category.assoc]
    _ = b' ≫ e := by rw [hc, Category.id_comp]

end FormalLaws

section Sites


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
  [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
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
  (χ : RingedForgetTwoInjective.Comparison.{wb, wa, c, v, r, d, vd, s}
    J R J' R' U u.hom)

/-- Exact ringed forgetting preserves the normalized tensor-Hom transposition and delta.
Source: the blueprint internal-Hom/evaluation/transposition paragraph; Stacks 015F,
06YS, 06YU, 0G7D, 0A90, 0A96, 070I, 08J9 and 0FPT
(blueprint: lem-sf-ringed-forget-tensor-transposition).

Proof (the ten DAG steps):
1. Exact additivity gives D(U), its termwise factorization, and preservation of
quasi-isomorphisms (lem-weil-pbc-exact-functor-derived-factorization).
2. Take the coproduct of the underived tensor comparisons. Naturality and additivity
commute with both signed differentials on each summand (def-pc-tensor-complex-sheaves).
3. On flat-term K-flat pairs, descend this chain isomorphism and its inverse. The
extension theorem gives existence and uniqueness (lem-weil-pbc-site-derived-tensor-descent).
4. Check associativity, unit and symmetry on triple summands and then localize;
lem-pur-kflat-total-tensor-model and lem-pc-kflat-resolution provide the models.
5. Represent a by a map from a K-flat P to Hom(S,I), with S K-flat and I K-injective:
use prop-pur-kinjective-resolutions-exist, lem-coef-hom-kflat-into-kinjective-independent-
coefficients and lem-sc-kinjective-quasi-iso-comparison.
6. The fixed adjunction uncurries this map by phi(x)(y) and the inverse localized
augmentation (def-coef-ringed-tensor-hom-model). The underived evaluation square and
the product projection formula for chi give the chain evaluation square
(lem-sf-ringed-forget-two-injective-hom, def-pur-hom-complex).
7. Compare UI to the fixed target replacement I' by a quasi-isomorphism j whose
composite with U eta is homotopic to eta'. Target-replacement compatibility of chi
and q(eta') inverse q(j) = q(U eta) inverse identify the two normalized uncurries.
8. K-injective localization bijectivity removes all lift choices; unique tensor descent
and naturality remove all resolution choices. Set a = identity to obtain evaluation.
9. Define delta as the transpose of evaluation after symmetry. Naturality of evaluation,
symmetry and the adjunction gives its naturality, by injectivity of transposition.
10. Uncurry the iterated chi applied to F delta. Symmetry coherence moves the inverse
chi across the swap; the evaluation equation cancels chi with its inverse. What remains
is exactly symmetric evaluation on the target. Injectivity gives the delta equation.
No double-dual arrow is assumed or concluded invertible. -/
theorem ringed_forget_tensor_transposition
    [∀ I : Type (max c v r), PreservesColimitsOfShape (Discrete I) U]
    (_preserves_flat_models :
      ∀ P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
        P.IsKFlatIndependentCoefficients →
        (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (R := R) (P.X p)) →
        CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P) ∧
          ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{d, vd, max d vd s, max d vd s}
            (R := R') (U.obj (P.X p))) :
    ∃ m : Comparison.{c, v, r, d, vd, s, wb, wa} J R J' R' U u SB TB βB cB SA TA βA cA χ,
      UniqueExtension.{c, v, r, d, vd, s, wb, wa} J R J' R' U u SB TB βB cB SA TA βA cA χ m := by
  obtain ⟨t, ht⟩ := ringed_forget_tensor_descent J R J' R' U u
    SB TB βB cB SA TA βA cA _preserves_flat_models
  have htrans := laws_of_uncurry SB SA βB βA U.mapDerivedCategory χ.derived t.derived
    t.coherence.symmetry
    (ringed_forget_normalized_uncurry J R J' R' U u
      SB TB βB cB SA TA βA cA χ t _preserves_flat_models)
  let m : Comparison.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U u SB TB βB cB SA TA βA cA χ :=
    { chain := t.chain
      summand := t.summand
      derived := t.derived
      representative := t.representative
      coherence := t.coherence
      unit_normalization := t.unit_normalization
      transposition := htrans }
  exact ⟨m, ht⟩


end Sites
end CategoryTheory.RingedForgetTensorTransposition
