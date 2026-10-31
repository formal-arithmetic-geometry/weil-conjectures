/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicNativeBidual
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleSliceHomComparison
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.Bidual
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-! # Invertibility of lisse adic bidual evaluation

The statement concerns underlying adic modules, with no Frobenius structure.
Source: Stacks Project, Tag 08JJ, and the finite-projective internal-Hom blueprint proof
(blueprint: lem-sf-adic-lisse-bidual-invertible).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

-- The coordinate argument below follows PresheafOfModules.bidual_app_bijective
-- (WeilConjectures/Algebra/Category/ModuleCat/Presheaf/Bidual.lean), with evaluation
-- supplied by its section formula. Its two site universes may differ, as on X.ProEt.
-- The total-retraction equation suffices; orthogonality is not needed.
section Coordinates

variable {C : Type (u + 1)} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u + 1}}
    {A : PresheafOfModules.{u + 1} (R ⋙ forget₂ _ _)} {U : C}

open PresheafOfModules

private lemma unit_app_smul (s : (restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj A)
    (W : (Over U)ᵒᵖ) (r : R.obj (op W.unop.left)) :
    s.app W r = r • (show A.obj (op W.unop.left) from
      A.map W.unop.hom.op (s.app (op (Over.mk (𝟙 U))) (1 : R.obj (op U)))) := by
  have h1 : s.app W (1 : R.obj (op W.unop.left)) =
      A.map W.unop.hom.op (s.app (op (Over.mk (𝟙 U))) (1 : R.obj (op U))) :=
    (congrArg (s.app W) (unit_map_one (R := R ⋙ forget₂ _ _) W.unop.hom.op).symm).trans
      (naturality_apply s
        (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 U)).op _)
  refine (congrArg (s.app W) (mul_one r).symm).trans ?_
  refine ((s.app W).hom.map_smul r (1 : R.obj (op W.unop.left))).trans ?_
  exact congrArg (fun y : A.obj (op W.unop.left) ↦ r • y) h1

private lemma evaluation_bijective {ι : Type*} [Fintype ι]
    (δ : A.obj (op U) ⟶ (homObj (homObj A (unit _)) (unit _)).obj (op U))
    (hb : ∀ (x : A.obj (op U)) (W : (Over U)ᵒᵖ)
      (φ : (homObj A (unit _)).obj (op W.unop.left)),
      (δ x).app W φ = φ.app (op (Over.mk (𝟙 W.unop.left))) (A.map W.unop.hom.op x))
    (s : ι → ((restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj A))
    (c : ι → ((restrictOver R U).obj A ⟶ (restrictOver R U).obj (unit _)))
    (htot : ∑ i, c i ≫ s i = 𝟙 _) : Function.Bijective δ := by
  let T : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let m : ι → A.obj (op U) := fun i ↦ (s i).app T (1 : R.obj (op U))
  -- Every section of `A` over `W ⟶ U` is a combination of the restrictions of the `m i`.
  have hspan (W : (Over U)ᵒᵖ) (x : A.obj (op W.unop.left)) :
      x = ∑ i, (show R.obj (op W.unop.left) from (c i).app W x) •
        (show A.obj (op W.unop.left) from A.map W.unop.hom.op (m i)) := by
    have h : ∑ i, (c i ≫ s i).app W x = x :=
      (PresheafOfModules.sum_app_apply Finset.univ (fun i ↦ c i ≫ s i) W x).symm.trans
        (congrArg (fun f ↦ f.app W x) htot)
    exact h.symm.trans (Finset.sum_congr rfl fun i _ ↦ unit_app_smul (s i) W _)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hc (i : ι) : (c i).app T x = 0 := by
      have h := congrArg (fun Φ ↦ Φ.app T (c i)) hx
      refine Eq.trans ?_ h
      rw [hb]
      change (c i).app T x = (c i).app T (A.map (𝟙 (op U)) x)
      rw [A.map_id]
      rfl
    refine (hspan T x).trans (Finset.sum_eq_zero fun i _ ↦ ?_)
    change (show R.obj (op U) from (c i).app T x) • _ = (0 : A.obj (op U))
    dsimp only
    rw [hc]
    exact zero_smul _ _
  · intro Ψ
    let a : ι → R.obj (op U) := fun i ↦ Ψ.app T (c i)
    refine ⟨∑ i, a i • m i, ?_⟩
    refine hom_ext (M₁ := (restrictOver R U).obj (homObj A (unit _)))
      (M₂ := (restrictOver R U).obj (unit _)) fun W ↦ ?_
    ext ψ
    let T' : (Over W.unop.left)ᵒᵖ := op (Over.mk (𝟙 W.unop.left))
    let b : ι → R.obj (op W.unop.left) := fun i ↦ ψ.app T' (A.map W.unop.hom.op (m i))
    -- `ψ` is a combination of the restrictions of the `c i`.
    have hψ : ψ = ∑ i, b i • (homObj A (unit _)).map W.unop.hom.op (c i) := by
      refine hom_ext (M₁ := (restrictOver R W.unop.left).obj A)
        (M₂ := (restrictOver R W.unop.left).obj (unit _)) fun W' ↦ ?_
      ext y
      let W'' : (Over U)ᵒᵖ := op ((Over.map W.unop.hom).obj W'.unop)
      refine (congrArg (ψ.app W') (hspan W'' y)).trans ?_
      refine (map_sum (ψ.app W').hom _ _).trans ?_
      refine Eq.trans ?_ (PresheafOfModules.sum_app_apply _ _ W' y).symm
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hn : ψ.app W' (A.map W''.unop.hom.op (m i)) = R.map W'.unop.hom.op (b i) := by
        refine (congrArg (ψ.app W') (A.map_comp_apply W.unop.hom.op W'.unop.hom.op (m i))).trans ?_
        exact naturality_apply ψ
          (Over.homMk W'.unop.hom (Category.comp_id _) : W'.unop ⟶ Over.mk (𝟙 W.unop.left)).op _
      refine ((ψ.app W').hom.map_smul _ _).trans ?_
      refine Eq.trans ?_ (restrictOver_smul_app_apply (b i) _ W' y).symm
      change (show R.obj (op W'.unop.left) from (c i).app W'' y) *
          (show R.obj (op W'.unop.left) from ψ.app W' (A.map W''.unop.hom.op (m i))) =
        R.map W'.unop.hom.op (b i) * (show R.obj (op W'.unop.left) from (c i).app W'' y)
      dsimp only
      rw [hn]
      exact mul_comm _ _
    -- The value of `Ψ` at a restriction of `c i` is the restriction of `a i`.
    have hΨ (i : ι) : Ψ.app W ((homObj A (unit _)).map W.unop.hom.op (c i)) =
        R.map W.unop.hom.op (a i) :=
      naturality_apply Ψ
        (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 U)).op (c i)
    have hL : (δ (∑ i, a i • m i)).app W ψ =
        ∑ i, R.map W.unop.hom.op (a i) * b i := by
      rw [hb]
      change ψ.app T' (A.map W.unop.hom.op (∑ i, a i • m i)) = _
      refine (congrArg (fun y : A.obj (op W.unop.left) ↦ ψ.app T' y)
        (map_sum (A.map W.unop.hom.op).hom _ _)).trans ?_
      refine (map_sum (ψ.app T').hom _ _).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
      refine (congrArg (fun y : A.obj (op W.unop.left) ↦ ψ.app T' y)
        (A.map_smul W.unop.hom.op (a i) (m i))).trans ?_
      exact (ψ.app T').hom.map_smul _ _
    have hR : Ψ.app W ψ = ∑ i, b i * R.map W.unop.hom.op (a i) := by
      refine (congrArg (Ψ.app W) hψ).trans ?_
      refine (map_sum (Ψ.app W).hom _ _).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
      exact ((Ψ.app W).hom.map_smul _ _).trans (congrArg (b i * ·) (hΨ i))
    rw [hL, hR]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm (R.map W.unop.hom.op (a i)) (b i)

end Coordinates

private lemma comparison_bidual_eq {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : AdicModuleSectionComparison l X) (M : AdicSheaf l X) :
    P.bidual M = adicNativeBidual M := by
  apply Mod.uncurryHom_injective
  exact (P.bidual_transpose M).trans (adicNativeBidual_transpose M).symm

private noncomputable def comparisonDualIso {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : AdicModuleSectionComparison l X) (M : AdicSheaf l X) :
    P.E.functor.obj ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)) ≅
      SheafOfModules.homObj (R := P.R) (P.E.functor.obj M) (SheafOfModules.unit P.ring) :=
  (P.homIso M).app (AdicSheaf.unit l X) ≪≫
    ((SheafOfModules.homFunctor P.R).obj (op (P.E.functor.obj M))).mapIso P.unitIso

private noncomputable def comparisonDoubleDualIso {l : ℕ} [Fact l.Prime]
    {X : Scheme.{u}} (P : AdicModuleSectionComparison l X) (M : AdicSheaf l X) :
    P.E.functor.obj ((AdicSheaf.ihom
      ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X))).obj (AdicSheaf.unit l X)) ≅
      SheafOfModules.homObj (R := P.R)
        (SheafOfModules.homObj (R := P.R) (P.E.functor.obj M) (SheafOfModules.unit P.ring))
        (SheafOfModules.unit P.ring) :=
  comparisonDualIso P ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)) ≪≫
    ((SheafOfModules.homFunctor P.R).flip.obj (SheafOfModules.unit P.ring)).mapIso
      (comparisonDualIso P M).symm.op

private lemma comparison_bidual_apply {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : AdicModuleSectionComparison l X) (M : AdicSheaf l X)
    (V : X.ProEtᵒᵖ) (x : (P.E.functor.obj M).val.obj V) (W : Over V.unop)
    (φ : (SheafOfModules.homObj (R := P.R) (P.E.functor.obj M)
      (SheafOfModules.unit P.ring)).val.obj (op W.left)) :
    (((P.E.functor.map (P.bidual M) ≫ (comparisonDoubleDualIso P M).hom).val.app V x).app
      (op W)) φ = φ.app (op (Over.mk (𝟙 W.left)))
        ((P.E.functor.obj M).val.map W.hom.op x) := by
  obtain ⟨x, rfl⟩ := (P.sectionsEquiv M V).surjective x
  let z := (P.sectionsEquiv
    ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)) (op W.left)).symm
      ((comparisonDualIso P M).inv.val.app (op W.left) φ)
  have hz : (comparisonDualIso P M).hom.val.app (op W.left)
      (P.sectionsEquiv _ (op W.left) z) = φ := by
    dsimp only [z]
    rw [AddEquiv.apply_symm_apply]
    exact congrArg (fun f ↦ f.val.app (op W.left) φ) (comparisonDualIso P M).inv_hom_id
  rw [← hz]
  change P.unitIso.hom.val.app (op W.left)
      (((((P.homIso ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X))).hom.app
        (AdicSheaf.unit l X)).val.app V
          ((P.E.functor.map (P.bidual M)).val.app V (P.sectionsEquiv M V x))).app (op W))
            ((comparisonDualIso P M).inv.val.app (op W.left)
              ((comparisonDualIso P M).hom.val.app (op W.left)
                (P.sectionsEquiv _ (op W.left) z)))) = _
  have hi : (comparisonDualIso P M).inv.val.app (op W.left)
      ((comparisonDualIso P M).hom.val.app (op W.left)
        (P.sectionsEquiv _ (op W.left) z)) = P.sectionsEquiv _ (op W.left) z :=
    congrArg (fun f ↦ f.val.app (op W.left) (P.sectionsEquiv _ (op W.left) z))
      (comparisonDualIso P M).hom_inv_id
  rw [hi, ← P.section_map, P.bidual_sections, P.evaluation, P.section_restriction]
  rfl

private lemma comparison_isIso_of_free {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : AdicModuleSectionComparison l X) (M : AdicSheaf l X) {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l X) : IsIso (P.bidual M) := by
  classical
  let e' := P.E.functor.mapIso (e ≪≫ biproduct.isoCoproduct _ ≪≫
    Sigma.whiskerEquiv (f := fun _ : Fin n ↦ AdicSheaf.unit l X)
      (g := fun _ : ULift.{u + 1} (Fin n) ↦ AdicSheaf.unit l X)
      (Equiv.ulift.symm : Fin n ≃ ULift.{u + 1} (Fin n))
      (fun _ ↦ Iso.refl _)) ≪≫ P.freeIso n
  let b := P.E.functor.map (P.bidual M) ≫ (comparisonDoubleDualIso P M).hom
  have htotal : ∑ j : ULift.{u + 1} (Fin n),
      (e'.hom ≫ SheafOfModules.freeπ j) ≫ (SheafOfModules.ιFree j ≫ e'.inv) = 𝟙 _ := by
    calc
      _ = e'.hom ≫ (∑ j, SheafOfModules.freeπ j ≫ SheafOfModules.ιFree j) ≫ e'.inv := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = 𝟙 _ := by
        rw [SheafOfModules.sum_freeπ_ιFree, Category.id_comp, Iso.hom_inv_id]
  have hbij (V : X.ProEtᵒᵖ) : Function.Bijective (b.val.app V) := by
    let F := PresheafOfModules.restrictOver P.R.obj V.unop
    refine evaluation_bijective (b.val.app V) (fun x W φ ↦ comparison_bidual_apply P M V x W.unop φ)
      (fun j ↦ F.map (SheafOfModules.ιFree j ≫ e'.inv).val)
      (fun j ↦ F.map (e'.hom ≫ SheafOfModules.freeπ j).val) ?_
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    rw [PresheafOfModules.sum_app_apply]
    exact (SheafOfModules.sum_val_app_apply Finset.univ
      (fun j : ULift.{u + 1} (Fin n) ↦
        (e'.hom ≫ SheafOfModules.freeπ j) ≫ (SheafOfModules.ιFree j ≫ e'.inv))
      (op W.unop.left) x).symm.trans
        (congrArg (fun f ↦ f.val.app (op W.unop.left) x) htotal)
  have hiso (V : X.ProEtᵒᵖ) : IsIso (b.val.app V) :=
    (ConcreteCategory.isIso_iff_bijective (b.val.app V)).2 (hbij V)
  let eb := PresheafOfModules.isoMk (fun V ↦ asIso (b.val.app V))
    (fun {_ _} f ↦ b.val.naturality f)
  have : IsIso ((SheafOfModules.forget P.ring).map b) := by
    change IsIso eb.hom
    infer_instance
  have : IsIso b := isIso_of_reflects_iso b (SheafOfModules.forget P.ring)
  have : IsIso (P.E.functor.map (P.bidual M)) :=
    IsIso.of_isIso_comp_right _ (comparisonDoubleDualIso P M).hom
  exact isIso_of_reflects_iso (P.bidual M) P.E.functor

private lemma isIso_comparisonDualSlice {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (U : X.ProEt) (M : AdicSheaf l X) : IsIso (adicComparisonDualSlice U M) := by
  unfold adicComparisonDualSlice
  infer_instance

/-- Evaluation into the double coefficient dual is invertible for a lisse adic module.
Source: Stacks Project, Tag 08JJ, the degree-zero finite-free evaluation calculation;
blueprint `lem-sf-hom-finite-projective`, finite locally free duality paragraph
(blueprint: lem-sf-adic-lisse-bidual-invertible).

Proof: choose the pro-etale finite-free trivializing cover in the definition of lisse.
Use `adicModuleSliceHomComparison` to identify native internal Hom and evaluation with
sectionwise slice Hom and its evaluation on the same coefficient ring. Its slice and
finite-free comparisons take each chosen trivialization to a finite-free trivialization
of the sectionwise module. The covering sieve on every further object contains the
base-changed cover. Apply `locallyFreeEvaluationBiduality`: in finite-free coordinates,
evaluation takes a basis to its double dual basis, so its matrix is the identity,
including at rank zero. The coordinate inverses agree on overlaps because each inverts
the same global evaluation; the sheaf axiom glues them to an inverse. The normalized
bidual comparison identifies this evaluation with `adicNativeBidual`, the transpose of
the identity. The native/sectionwise equivalence reflects isomorphisms and therefore
gives the required invertibility. No choice of a duality isomorphism is assumed. -/
theorem isIso_adicNativeBidual_of_isLisse {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M : AdicSheaf l X) (hM : IsAdicLisseSheaf M) :
    IsIso (adicNativeBidual M) := by
  obtain ⟨P⟩ := adicModuleSliceHomComparison l
  rw [← comparison_bidual_eq (P.base X) M]
  obtain ⟨R, hR, hRM⟩ := hM
  obtain ⟨ι, V, g, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : WeaklyEtale (g i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  have hg (i : ι) : IsIso ((adicUpperStar l (g i)).map ((P.base X).bidual M)) := by
    obtain ⟨n, ⟨e⟩⟩ := hRM (g i) (.mk i)
    have := comparison_isIso_of_free (P.base (V i)) _ e
    let U := Scheme.ProEt.mk (g i)
    have hdual := isIso_comparisonDualSlice U M
    have hdual' := isIso_comparisonDualSlice U
      ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X))
    have hmap : IsIso ((Mod.ihomMap (adicComparisonDualSlice U M)).app
        (AdicSheaf.unit l U.left)) := by
      change IsIso ((Mod.ihomMapIso (asIso (adicComparisonDualSlice U M))).hom.app _)
      infer_instance
    have h := P.bidual_slice X U M
    have : IsIso ((adicUpperStar l (g i)).map ((P.base X).bidual M) ≫
        adicComparisonDualSlice U ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X))) := by
      change IsIso ((adicUpperStar l U.hom).map ((P.base X).bidual M) ≫ _)
      rw [h]
      change IsIso ((P.base (V i)).bidual ((adicUpperStar l (g i)).obj M) ≫ _)
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (adicComparisonDualSlice U ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)))
  have : IsIso ((AdicSheaf.forget _).map ((P.base X).bidual M)) := by
    apply isIso_of_isIso_localizationRestriction _ _ g hR
    intro i
    have h1 : IsIso ((g i)^*[WeilCoefficients.{u} l].map ((P.base X).bidual M).hom) :=
      inferInstanceAs (IsIso ((AdicSheaf.forget _).map
        ((adicUpperStar l (g i)).map ((P.base X).bidual M))))
    exact (NatIso.isIso_map_iff (upperStarIsoLocalizationRestriction
      (WeilCoefficients.{u} l) (g i) inferInstance) ((P.base X).bidual M).hom).1 h1
  exact isIso_of_reflects_iso _ (AdicSheaf.forget _)

end AlgebraicGeometry.ProEtale
