/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Paper.CompletionMateComparison
public import Sheaf.Paper.CompleteCoefficientDatum
import Sheaf.Paper.CompletionUnitFiniteProjection
import all Sheaf.Paper.ConstantDirectImagePreservesComplete
import Sheaf.Paper.RestrictionSectionCompleteness
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction

/-! # Finite reduction of the normalized quotient completion

Source: Stacks Tags 099M and 091N; blueprint order 1260.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.AdicSites

private theorem sequential_nilpotent_colimit
    {C : Type*} [Category C] [Preadditive C] [HasColimitsOfShape ℕ C]
    (M : C) (f : M ⟶ M) (k : ℕ) (hf : (End.of f) ^ k = 0) :
    IsZero (colimit (Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ f))) := by
  let F := Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ f)
  have hm (n j : ℕ) : F.map (homOfLE (Nat.le_add_right n j)) = (End.of f) ^ j := by
    induction j with
    | zero =>
      simp only [Nat.add_zero, homOfLE_refl, CategoryTheory.Functor.map_id,
        pow_zero, End.one_def]
      rfl
    | succ j ih =>
      have he : homOfLE (Nat.le_add_right n (j + 1)) =
          homOfLE (Nat.le_add_right n j) ≫ homOfLE (Nat.le_succ (n + j)) := rfl
      rw [he, CategoryTheory.Functor.map_comp, ih]
      dsimp only [F]
      rw [Functor.ofSequence_map_homOfLE_succ]
      change ((End.of f) ^ j) ≫ f = (End.of f) ^ (j + 1)
      rw [pow_succ', End.mul_def]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  intro n
  have h := colimit.w F (homOfLE (Nat.le_add_right n k))
  rw [hm, hf] at h
  simpa only [zero_comp, Category.comp_id, comp_zero] using h.symm

private theorem sectionLocalization_nilpotent
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) (f : R.obj.obj (op U))
    (k : ℕ) (hf : f ^ k = 0) :
    IsZero (ringedSiteSectionLocalization R U f) := by
  let M := SheafOfModules.unit (R.over U)
  let μ : M ⟶ M := M.unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun V ↦ R.obj.map V.unop.hom.op f)
      (fun {V W} a ↦ ringedSiteSectionLocalization_compatible R U f V W a))
  have hp (j : ℕ) (V : (Over U)ᵒᵖ) (m : R.obj.obj (op V.unop.left)) :
      (((End.of μ) ^ j : End M).val.app V) m =
        m * (R.obj.map V.unop.hom.op f) ^ j := by
    induction j generalizing m with
    | zero => simp only [pow_zero, End.one_def]; exact (mul_one m).symm
    | succ j ih =>
      rw [pow_succ', End.mul_def]
      change ((μ.val.app V) ((((End.of μ) ^ j : End M).val.app V) m)) = _
      rw [ih]
      change (m * (R.obj.map V.unop.hom.op f) ^ j) * R.obj.map V.unop.hom.op f = _
      rw [mul_assoc, ← pow_succ]
  have hμ : (End.of μ) ^ k = 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext
    erw [hp]
    have hz : (R.obj.map V.unop.hom.op f) ^ k = 0 := by
      rw [← map_pow, hf, map_zero]
    rw [hz, mul_zero]
    rfl
  exact sequential_nilpotent_colimit M μ k hμ

open CategoryTheory.Pretriangulated.Opposite in
private theorem completeElement_nilpotent
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (ConstantCompletion.Mod R)]
    [∀ U : C, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      ((siteModuleRings R).over U))]
    (K : DerivedCategory (ConstantCompletion.Mod R)) (U : C)
    (f : R.obj.obj (op U)) (k : ℕ) (hf : f ^ k = 0) :
    IsRingedSiteCompleteElement J R K U f := by
  let O := siteModuleRings R
  let L := (DerivedCategory.singleFunctor (SheafOfModules.{u} (O.over U)) 0).obj
    (ringedSiteSectionLocalization O U f)
  let N := ringedSiteDerivedRestriction O U K
  let : HasDerivedCategory.{u + 1} (ringedSiteModules.{u}
      (siteModuleRings (R.over U))) := inferInstanceAs
    (HasDerivedCategory.{u + 1} (SheafOfModules.{u} (O.over U)))
  obtain ⟨s, hs⟩ := (ringedInternalHom_exact (J.over U) (R.over U)).2 N
  let := s
  have := hs
  have hL : IsZero L := (DerivedCategory.singleFunctor _ 0).map_isZero
    (sectionLocalization_nilpotent O U f k hf)
  exact ((Functor.curry.obj (derivedInternalHom (J.over U) (R.over U))).flip.obj N).map_isZero
    hL.op

private theorem complete_iso (S : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A)
    {M N : S.derived A} (e : M ≅ N) (hM : S.IsComplete A I M) :
    S.IsComplete A I N := by
  intro U f hf
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      ((siteModuleRings (S.ring A)).over U)) := HasDerivedCategory.standard _
  let H := derivedInternalHom (S.topology.over U) ((S.ring A).over U)
  let L := (DerivedCategory.singleFunctor _ 0).obj
    (ringedSectionLocalization ((S.ring A).over U)
      (ringedSliceSection (S.ring A) U f))
  let eH := H.mapIso ((Iso.refl L).op.prod
    ((ringedDerivedRestriction (S.ring A) U).mapIso e))
  exact (hM U f hf).of_iso eH.symm

private theorem finiteRestriction_complete (S : Site.{u}) (A : Type u) [CommRing A]
    (d : AlgebraicGeometry.Scheme.CompleteCoefficientDatum A) (n : ℕ)
    (M : S.derived (quotientRing A d.ideal n)) :
    S.IsComplete A d.ideal ((S.finiteRestriction A d.ideal n).obj M) := by
  let := d.noetherian
  let R := S.ring A
  let B := S.ring (quotientRing A d.ideal n)
  let φ := ConstantCompletion.quotient S.topology A d.ideal n
  let : HasDerivedCategory.{u + 1} (ConstantCompletion.Mod R) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} (ConstantCompletion.Mod B) :=
    HasDerivedCategory.standard _
  let : ∀ U : S.objects, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((siteModuleRings R).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : ∀ U : S.objects, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((siteModuleRings B).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let P := DerivedCategory.Q.objPreimage M
  let L := (ConstantCompletion.Q R).obj
    (((ConstantCompletion.res φ).mapHomologicalComplex (.up ℤ)).obj P)
  have hL : S.IsComplete A d.ideal L := by
    apply (ConstantCompletion.complete_iff_constantElements S.topology A d.ideal L).mpr
    intro a ha U
    apply (restrictScalars_completeElement_iff S.topology R B φ M U _).mpr
    apply completeElement_nilpotent S.topology B M U _ (n + 1)
    rw [← map_pow]
    apply RingHom.mem_ker.mp
    rw [(ConstantCompletion.flat_and_quotients S.topology A d.ideal).2.2 n U |>.2]
    apply Ideal.subset_span
    refine ⟨⟨a ^ (n + 1), Ideal.pow_mem_pow ha (n + 1)⟩, ?_⟩
    simp only [ConstantCompletion.constantSection, map_pow]
  let e : L ≅ (S.finiteRestriction A d.ideal n).obj M :=
    (ConstantCompletion.resFactors φ).app P ≪≫
      (ConstantCompletion.dres φ).mapIso (DerivedCategory.Q.objObjPreimageIso M)
  exact complete_iso S A d.ideal e hL

private theorem finiteReduction_unit_isIso (S : Site.{u}) (A : Type u) [CommRing A]
    (d : AlgebraicGeometry.Scheme.CompleteCoefficientDatum A)
    (N : S.derived A) (n : ℕ) :
    IsIso ((S.finiteReduction A d.ideal n).map ((S.unit A d.ideal).app N)) := by
  let := d.noetherian
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  obtain ⟨_, _, _, hh, _⟩ :=
    ConstantCompletion.koszul_quotient_reflector S.topology A d.ideal false r a ha
  apply isIso_of_coyoneda_map_bijective
  intro M
  have hbij := hh N ((S.finiteRestriction A d.ideal n).obj M)
    (finiteRestriction_complete S A d n M)
  let adj := S.finiteAdjunction A d.ideal n
  constructor
  · intro x y hxy
    apply (adj.homEquiv _ _).injective
    apply hbij.injective
    change (S.unit A d.ideal).app N ≫ (adj.homEquiv _ _) x =
      (S.unit A d.ideal).app N ≫ (adj.homEquiv _ _) y
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left]
    exact congrArg (adj.homEquiv _ _) hxy
  · intro y
    obtain ⟨x, hx⟩ := hbij.surjective ((adj.homEquiv _ _).toFun y)
    refine ⟨(adj.homEquiv _ _).symm x, ?_⟩
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hx

/-- The completion unit becomes invertible after finite scalar extension, and its
composite with the normalized limit projection is the finite scalar-extension unit.

Source: Stacks 099M, and the finite-reduction calculation of blueprint order 1260
(blueprint: lem-sf-completion-finite-reduction).

Proof: every complex over A/I^(n+1), viewed over A, is derived I-complete.
Indeed each element of I acts nilpotently, so its localization is zero: the
sequential localization colimit vanishes because a sufficiently long transition
is zero. The sectionwise internal-Hom criterion then gives derived completeness.
The unit-preserving Koszul/quotient reflector identifies maps from C(N) into any
such restricted object with maps from N into it. By the finite scalar adjunction,
precomposition by the finite reduction of eta_N is therefore bijective against
every finite-coefficient target. Coyoneda detects that it is invertible.
For the second assertion apply completionUnitFiniteProjection: the normalized
strict-limit counit projects the completion unit to the quotient augmentation,
and finiteAdjunction identifies that augmentation with its scalar-extension unit.
The proof includes I = 0, I = A, and the zero ring: nilpotence in the quotient is
the only assertion about the quotient used here. -/
theorem completionFiniteReduction (S : Site.{u}) (A : Type u) [CommRing A]
    (d : AlgebraicGeometry.Scheme.CompleteCoefficientDatum A)
    (N : S.derived A) (n : ℕ) :
    IsIso ((S.finiteReduction A d.ideal n).map ((S.unit A d.ideal).app N)) ∧
      (S.unit A d.ideal).app N ≫
          (show S.delta A ⋙ S.evaluate A n ≅ 𝟭 (S.derived A) from
            (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
            Functor.mapDerivedCategoryNatIso
              (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)) ≪≫
            Functor.mapDerivedCategoryIdIso (S.modules A)).inv.app
              ((S.completion A d.ideal).obj N) ≫
          (S.evaluate A n).map ((S.deltaAdjunction A).counit.app
            ((S.reduction A d.ideal).obj N)) ≫
          (S.finiteEvaluationIso A d.ideal n).hom.app N =
        (S.finiteAdjunction A d.ideal n).unit.app N := by
  exact ⟨finiteReduction_unit_isIso S A d N n,
    completionUnitFiniteProjection S A d.ideal N n⟩

end CategoryTheory.AdicSites
