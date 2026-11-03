/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeTerminalSectionsComparison
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.SixFunctors.PointSectionsTensor.PointSectionsModuleTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! Right-inverse part of the K-flat point tensor comparison.
Source: Stacks 07A4 and 03EL; the point tensor of the trace-cup construction
(blueprint: lem-pod-condensed-point-tensor-right-inverse).

The statement is about the exact sections functor at the algebraically closed point,
and about cup data normalized on pure tensors. It is false for an arbitrary exact
functor (restriction of scalars along ℤ → ℤ[X] already gives a derived tensorator with
neither inverse), so the point and the normalization are both needed.

Proof plan.
1. Every covering sieve of the final object `Spec k` of the pro-étale site contains its
   identity (k is algebraically closed, so every pro-étale cover of `Spec k` has a
   section). Hence sheafification does not change sections at `Spec k`, and the section
   module of a relative tensor is the tensor of the section modules: the normalized
   ordinary tensorator `x ⊗ y ↦ (λ_ _).inv ≫ (x ⊗ₘ y)` is an isomorphism.
2. The local equational criterion and the split-cover property show that sections
   preserve flat modules. They also preserve countable colimits. A functorial flat
   resolution `L` of the second input is therefore K-flat both before and after
   sections. The native localization tensor maps are invertible on `K, L`, with `K`
   arbitrary. The inverse ordinary comparison induces an invertible total-complex
   comparison, whose inverse is `d.chain` by its formula on every total summand.
3. The field `tensor_normalization` writes `d.derived.μ` at `Q K, Q L` as a composite of
   these isomorphisms with the exact-functor localization factors. Naturality transports
   this to all `M, N`, and the inverse of the composite gives the displayed right inverse.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open CategoryTheory.InternalAbelianSheafModule Opposite
open scoped TensorProduct ChangeOfRings CategoryTheory.Obj
section Localization
universe a b r w z
variable {B : Type a} [Category.{b} B] [Abelian B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalClosed B] [BraidedCategory B]
  [HasColimitsOfSize.{0, 0} B] [IsGrothendieckAbelian.{b} B]
  [Abelian.HasFunctorialFlatResolution B]
  {S : Type r} [CommRing S]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{z} (ModuleCat.{r} S)]
  (G : B ⥤ ModuleCat.{r} S) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesColimitsOfSize.{0, 0} G]

omit [HasColimitsOfSize.{0, 0} B] in
private theorem cup_chain_isIso (d : ExactSectionsDerivedCup G)
    (hμ : ∀ P Q, IsIso (d.ordinary.μ P Q)) (K L : CochainComplex B ℤ) :
    IsIso (d.chain K L) := by
  let _ := d.ordinary
  have (P Q : B) : IsIso (Functor.LaxMonoidal.μ G P Q) := hμ P Q
  have (P Q : B) : IsIso (((Functor.LaxMonoidal.μNatTrans G).app P).app Q) := hμ P Q
  have (P : B) : IsIso ((Functor.LaxMonoidal.μNatTrans G).app P) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.LaxMonoidal.μNatTrans G) := NatIso.isIso_of_isIso_app _
  let τ := inv (Functor.LaxMonoidal.μNatTrans G)
  let t := HomologicalComplex.mapBifunctorComparison τ (.up ℤ) K L
  have : IsIso t := inferInstance
  have ht : d.chain K L ≫ t = 𝟙 _ := by
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change (HomologicalComplex.ιTensorObj _ _ p q n hpq ≫ (d.chain K L).f n) ≫
      t.f n = HomologicalComplex.ιTensorObj _ _ p q n hpq ≫ 𝟙 _
    rw [d.chain_summand, Category.assoc]
    change _ ≫ G.map (HomologicalComplex.ιTensorObj K L p q n hpq) ≫
      HomologicalComplex.mapBifunctorComparisonX τ (.up ℤ) K L n = _
    rw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
    simp only [HomologicalComplex.mapBifunctorComparisonApp, τ, NatIso.isIso_inv_app,
      Functor.LaxMonoidal.μNatTrans_app_app,
      ← Category.assoc, IsIso.hom_inv_id, Category.id_comp, Category.comp_id]
  exact IsIso.of_isIso_fac_right ht

private theorem cup_tensor_isIso (d : ExactSectionsDerivedCup G)
    [G.PreservesFlat] (hμ : ∀ P Q, IsIso (d.ordinary.μ P Q))
    (M N : DerivedCategory B) : IsIso (d.derived.μ M N) := by
  have : HasExactColimitsOfShape ℤ B := by
    have := AB5OfSize_of_univLE.{0, 0, b, b} B
    infer_instance
  have : HasExactColimitsOfShape ℤ (ModuleCat.{r} S) := by
    have := AB5OfSize_of_univLE.{0, 0, r, r} (ModuleCat.{r} S)
    infer_instance
  have (X : ModuleCat.{r} S) :
      PreservesColimitsOfShape ℤ ((curriedTensor (ModuleCat.{r} S)).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  let R := (inferInstance : Abelian.HasFunctorialFlatResolution B).some.reduced
  let K := DerivedCategory.Q.objPreimage M
  let P := DerivedCategory.Q.objPreimage N
  let L := R.resolutionFunctor.obj P
  have hL := R.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le P
  have hGL := G.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj R
    ObjectProperty.flat.essImage_ι_le P
  let eK := DerivedCategory.Q.objObjPreimageIso M
  have : QuasiIso (R.resolutionNatTrans.app P) := R.quasiIso_resolutionNatTrans_app P
  let eL : DerivedCategory.Q.obj L ≅ N :=
    asIso (DerivedCategory.Q.map (R.resolutionNatTrans.app P)) ≪≫
      DerivedCategory.Q.objObjPreimageIso N
  have sourceIso : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q K L) := by
    have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient B (.up ℤ)).obj K)
        ((HomotopyCategory.quotient B (.up ℤ)).obj L)) :=
      DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
        (HomotopyCategory.quasiIso B (.up ℤ)) _ _
        ((HomotopyCategory.kFlat_quotient_obj_iff L).2 hL)
    change IsIso ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
    infer_instance
  have targetIso : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((G.mapHomologicalComplex (.up ℤ)).obj K)
      ((G.mapHomologicalComplex (.up ℤ)).obj L)) := by
    have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient (ModuleCat.{r} S) (.up ℤ)).obj
          ((G.mapHomologicalComplex (.up ℤ)).obj K))
        ((HomotopyCategory.quotient (ModuleCat.{r} S) (.up ℤ)).obj
          ((G.mapHomologicalComplex (.up ℤ)).obj L))) :=
      DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleCat.{r} S) (.up ℤ)) _ _
        ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hGL)
    change IsIso ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
    infer_instance
  have := cup_chain_isIso G d hμ K L
  have key : IsIso (d.derived.μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)) :=
    IsIso.of_isIso_fac_right (d.tensor_normalization K L)
  have hn := @Functor.LaxMonoidal.μ_natural _ _ _ _ _ _
    G.mapDerivedCategory d.derived _ _ _ _ eK.hom eL.hom
  exact IsIso.of_isIso_fac_left hn
end Localization

namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint
/-- Full faithfulness at the geometric point preserves the ring of global scalars. -/
private theorem point_scalar_bijective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    Function.Bijective (condensedRingScalarSections Λ (Spec (.of k))) := by
  have : (upperStarFromPoint (Spec (.of k))).Additive :=
    Functor.additive_of_preserves_binary_products _
  unfold condensedRingScalarSections
  apply globalMapFunctor_bijective
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- Apply the local flatness criterion to the identity in the covering sieve. -/
private theorem point_eval_flat (k : Type u) [Field k] [IsAlgClosed k]
    (R : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    (M : ringedSiteModules.{u + 1} ((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (hM : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := R) M) :
    Module.Flat (R.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
      (M.val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro n a x h
  obtain ⟨S, hS, hrel⟩ :=
    SheafOfModules.local_equationalCriterion_of_isFlatOnSite.{u + 1, u, u + 1, 0}
      R M hM (Scheme.ProEt.mk (𝟙 (Spec (.of k)))) n a x h
  have hid := Scheme.ProEt.id_mem_of_mem_topology_of_iso (Iso.refl (Spec (.of k))) hS
  obtain ⟨l, b, t, hx, ha⟩ := hrel _ (𝟙 _) hid
  exact ⟨l, b, t, by simpa using hx, by simpa using ha⟩

/-- Transport each finite trivial relation along the inverse scalar ring isomorphism. -/
private theorem restrict_flat {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (α : R →+* S) (hα : Function.Bijective α) (M : ModuleCat.{u + 1} S)
    [Module.Flat S M] : Module.Flat R ((ModuleCat.restrictScalars α).obj M) := by
  let e := RingEquiv.ofBijective α hα
  have he (z : S) : α (e.symm z) = z := e.apply_symm_apply z
  apply Module.Flat.of_forall_isTrivialRelation
  intro n a x h
  have h' : ∑ i, α (a i) • (x i : M) = 0 := h
  obtain ⟨l, b, t, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (R := S) (M := M) h'
  refine ⟨l, fun i j ↦ e.symm (b i j), t, ?_, ?_⟩
  · intro i
    change (x i : M) = ∑ j, α (e.symm (b i j)) • t j
    simpa only [he] using hx i
  · intro j
    apply hα.injective
    simpa only [map_sum, map_mul, map_zero, he] using ha j
end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint
namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
private abbrev pointJ := Scheme.ProEt.topology (Spec (.of k))
private abbrev pointO := condensedRingObj Λ (Spec (.of k))
private abbrev pointU := Scheme.ProEt.mk (𝟙 (Spec (.of k)))
private abbrev pointR := sectionRingSheaf.{u + 1, u + 1, u} (pointJ k) (pointO Λ k)
private abbrev pointE := sectionModuleEquivalence.{u + 1, u + 1, u} (pointJ k) (pointO Λ k)
private abbrev pointα := (sectionGlobalEval (pointJ k) (pointO Λ k) (pointU k)).comp
  (condensedRingScalarSections Λ (Spec (.of k)))
private theorem pointα_bijective : Function.Bijective (pointα Λ k) :=
  (sectionGlobalEval_bijective (pointJ k) (pointO Λ k) (pointU k)
    (Scheme.ProEt.isTerminalMkId _)).comp (point_scalar_bijective Λ k)

/-- The concrete evaluation-at-one comparison; its underlying function is fixed. -/
private def pointEvalIso (M : Mod (Sheaf (pointJ k) Ab.{u + 1}) (pointO Λ k)) :
    (condensedRingCoefficientSections Λ (Spec (.of k))).obj M ≅
      (ModuleCat.restrictScalars.{u + 1} (pointα Λ k)).obj
        ((Evaluation.sections (pointJ k) (pointO Λ k) (pointU k)).obj M) :=
  LinearEquiv.toModuleIso (LinearEquiv.ofBijective
    (terminal_linear (pointJ k) (pointO Λ k)
      (condensedRingScalarSections Λ (Spec (.of k))) (pointU k) M)
    (terminal_eval_bijective (pointJ k) (pointO Λ k)
      (condensedRingScalarSections Λ (Spec (.of k))) (pointU k)
      (Scheme.ProEt.isTerminalMkId _) M))

private theorem point_sections_flat :
    (condensedRingCoefficientSections Λ (Spec (.of k))).PreservesFlat := by
  constructor
  intro M hM
  let E := pointE Λ k
  have hf := (flat_iff_sectionModule (pointJ k) (pointO Λ k) M).1 hM
  have he := point_eval_flat k (pointR Λ k) (E.functor.obj M) hf
  have : Module.Flat ((pointR Λ k).obj.obj (op (pointU k)))
      ((Evaluation.sections (pointJ k) (pointO Λ k) (pointU k)).obj M) := he
  have := restrict_flat (pointα Λ k) (pointα_bijective Λ k)
    ((Evaluation.sections (pointJ k) (pointO Λ k) (pointU k)).obj M)
  apply (ModuleCat.flat_iff_flat _).2
  exact Module.Flat.of_linearEquiv (pointEvalIso Λ k M).toLinearEquiv

/-- Evaluate the characterized internal tensor comparison and the sheafification unit. -/
private def pointTensorIso (M N : Mod (Sheaf (pointJ k) Ab.{u + 1}) (pointO Λ k)) :
    ((Evaluation.sections (pointJ k) (pointO Λ k) (pointU k)).obj M) ⊗
        ((Evaluation.sections (pointJ k) (pointO Λ k) (pointU k)).obj N) ≅
      (Evaluation.sections (pointJ k) (pointO Λ k) (pointU k)).obj (M ⊗ N) := by
  let E := pointE Λ k
  let e := (exists_sectionTensorIso (pointJ k) (pointO Λ k) M N).choose
  let unitMap := ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
    ((E.functor.obj M).val ⊗ (E.functor.obj N).val)).app (op (pointU k))
  have : IsIso unitMap := WeilConjectures.PointSectionsTensor.unit_eval_isIso k
    (pointR Λ k) ((E.functor.obj M).val ⊗ (E.functor.obj N).val)
  exact asIso unitMap ≪≫ (pointModuleSections k (pointR Λ k)).mapIso e.symm

set_option maxHeartbeats 1000000 in
-- The section/internal comparison involves several equivalences of module categories.
private theorem pointTensorIso_tmul
    (M N : Mod (Sheaf (pointJ k) Ab.{u + 1}) (pointO Λ k))
    (x : M.X.obj.obj (op (pointU k))) (y : N.X.obj.obj (op (pointU k))) :
    (pointTensorIso Λ k M N).hom (x ⊗ₜ[(pointR Λ k).obj.obj (op (pointU k))] y) =
      comparison_internalTmul (pointJ k) (pointO Λ k) M N (op (pointU k)) x y := by
  let e := (exists_sectionTensorIso (pointJ k) (pointO Λ k) M N).choose
  let F := pointModuleSections k (pointR Λ k)
  apply ((F.mapIso e).toLinearEquiv).injective
  change (F.map e.hom) ((F.map e.inv) _) = (F.map e.hom) _
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, ModuleCat.id_apply]
  exact ((exists_sectionTensorIso (pointJ k) (pointO Λ k) M N).choose_spec
    (op (pointU k)) x y).symm

omit [IsAlgClosed k]
set_option maxHeartbeats 1000000 in
-- Concrete evaluation at the unit of the regular module.
private theorem pointEvalIso_pairing
    (M N : Mod (Sheaf (pointJ k) Ab.{u + 1}) (pointO Λ k))
    (x : (condensedRingCoefficientSections Λ (Spec (.of k))).obj M)
    (y : (condensedRingCoefficientSections Λ (Spec (.of k))).obj N) :
    (pointEvalIso Λ k (M ⊗ N)).hom ((λ_ _).inv ≫ (x ⊗ₘ y)) =
      comparison_internalTmul (pointJ k) (pointO Λ k) M N (op (pointU k))
        ((pointEvalIso Λ k M).hom x) ((pointEvalIso Λ k N).hom y) := by
  let R := Mod.regular (pointO Λ k)
  let ev := Evaluation.sections (pointJ k) (pointO Λ k) (pointU k)
  have hone : (ev.map (λ_ R).inv) (1 : (pointR Λ k).obj.obj (op (pointU k))) =
      comparison_internalTmul (pointJ k) (pointO Λ k) R R (op (pointU k))
        (1 : (pointR Λ k).obj.obj (op (pointU k)))
        (1 : (pointR Λ k).obj.obj (op (pointU k))) := by
    apply (ev.mapIso (λ_ R)).toLinearEquiv.injective
    change (ev.map (λ_ R).hom) ((ev.map (λ_ R).inv)
        (1 : (pointR Λ k).obj.obj (op (pointU k)))) =
      (ev.map (λ_ R).hom) (comparison_internalTmul (pointJ k) (pointO Λ k) R R
        (op (pointU k)) (1 : (pointR Λ k).obj.obj (op (pointU k)))
        (1 : (pointR Λ k).obj.obj (op (pointU k))))
    have h := comparison_internalTmul_leftUnitor (pointJ k) (pointO Λ k) R
      (op (pointU k)) (1 : (pointR Λ k).obj.obj (op (pointU k)))
        (1 : (pointR Λ k).obj.obj (op (pointU k)))
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, Iso.inv_hom_id]
    change (1 : (pointR Λ k).obj.obj (op (pointU k))) = _
    convert h.symm using 1
    · rfl
    · simp only [one_smul]
    · rfl
  change ((ev.map (x ⊗ₘ y)) ((ev.map (λ_ R).inv)
    (1 : (pointR Λ k).obj.obj (op (pointU k))))) = _
  rw [hone]
  exact comparison_internalTmul_natural (pointJ k) (pointO Λ k) x y
    (op (pointU k)) (1 : (pointR Λ k).obj.obj (op (pointU k)))
        (1 : (pointR Λ k).obj.obj (op (pointU k)))
end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint

namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
/-- Reflect colimits from abelian sections, then transfer across terminal evaluation. -/
private theorem point_sections_colimits :
    PreservesColimitsOfSize.{0, 0} (condensedRingCoefficientSections Λ (Spec (.of k))) := by
  have hc : PreservesColimitsOfSize.{u + 1, u + 1}
      (Evaluation.sections (pointJ k) (pointO Λ k) (pointU k)) := by
    constructor
    intro I hI
    let R := (sheafCompose (pointJ k) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (pointR Λ k)
    let E := (sheafSections (pointJ k) Ab.{u + 1}).obj (op (pointU k))
    let V := SheafOfModules.evaluation.{u + 1} R (op (pointU k))
    have : PreservesColimitsOfShape I E :=
      preservesColimitsOfShape_sheafSections_of_iso (Iso.refl (Spec (.of k))) I
    have : PreservesColimitsOfShape I (SheafOfModules.toSheaf R) :=
      ((moduleSheaves_colimits_forgetful.{u + 1, u, u + 1, u + 1} R).2.2.2.2.2 I).2.1
    let U := forget₂ (ModuleCat.{u + 1} (R.obj.obj (op (pointU k)))) Ab.{u + 1}
    have : PreservesColimitsOfShape I (V ⋙ U) :=
      inferInstanceAs (PreservesColimitsOfShape I (SheafOfModules.toSheaf R ⋙ E))
    have : PreservesColimitsOfShape I V :=
      preservesColimitsOfShape_of_reflects_of_preserves V U
    exact inferInstanceAs (PreservesColimitsOfShape I ((pointE Λ k).functor ⋙ V))
  obtain ⟨e⟩ := native_terminalSectionsIso (pointJ k) (pointO Λ k)
    (condensedRingScalarSections Λ (Spec (.of k))) (pointU k)
    (Scheme.ProEt.isTerminalMkId _)
  have : (ModuleCat.restrictScalars.{u + 1} (pointα Λ k)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} (pointα Λ k)).isLeftAdjoint
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (Evaluation.sections (pointJ k) (pointO Λ k) (pointU k) ⋙
        ModuleCat.restrictScalars.{u + 1} (pointα Λ k)) := inferInstance
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (condensedRingCoefficientSections Λ (Spec (.of k))) :=
    preservesColimits_of_natIso e.symm
  exact preservesColimitsOfSize_shrink _

attribute [local irreducible] pointEvalIso pointTensorIso

set_option maxHeartbeats 1000000 in
-- Normalize the concrete evaluations before cancelling the three tensor isomorphisms.
private theorem point_ordinary_tensor_isIso
    [PreservesFiniteLimits (condensedRingCoefficientSections Λ (Spec (.of k)))]
    [PreservesFiniteColimits (condensedRingCoefficientSections Λ (Spec (.of k)))]
    (d : ExactSectionsDerivedCup (condensedRingCoefficientSections Λ (Spec (.of k))))
    (hd : ∀ (P Q : Mod (Sheaf (pointJ k) Ab.{u + 1}) (pointO Λ k))
      (x : (condensedRingCoefficientSections Λ (Spec (.of k))).obj P)
      (y : (condensedRingCoefficientSections Λ (Spec (.of k))).obj Q),
      (d.ordinary.μ P Q).hom (x ⊗ₜ[Γ Λ] y) = (λ_ _).inv ≫ (x ⊗ₘ y))
    (P Q : Mod (Sheaf (pointJ k) Ab.{u + 1}) (pointO Λ k)) :
    IsIso (d.ordinary.μ P Q) := by
  let ev := Evaluation.sections (pointJ k) (pointO Λ k) (pointU k)
  let S := ModuleCat.restrictScalars.{u + 1} (pointα Λ k)
  let t := WeilConjectures.PointSectionsTensor.scalarTensorIso
    (pointα Λ k) (pointα_bijective Λ k).2 (ev.obj P) (ev.obj Q)
  have he : d.ordinary.μ P Q ≫ (pointEvalIso Λ k (P ⊗ Q)).hom =
      ((pointEvalIso Λ k P).hom ⊗ₘ (pointEvalIso Λ k Q).hom) ≫
        t.hom ≫ S.map (pointTensorIso Λ k P Q).hom := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change (pointEvalIso Λ k (P ⊗ Q)).hom
      ((d.ordinary.μ P Q).hom (x ⊗ₜ[Γ Λ] y)) = _
    rw [hd, pointEvalIso_pairing]
    change _ = (pointTensorIso Λ k P Q).hom
      (t.hom (((pointEvalIso Λ k P).hom x) ⊗ₜ[Γ Λ] ((pointEvalIso Λ k Q).hom y)))
    rw [WeilConjectures.PointSectionsTensor.scalarTensorIso_tmul, pointTensorIso_tmul]
  exact IsIso.of_isIso_fac_right he
end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint


namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint
theorem tensorData_tensor_right_inverse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    [PreservesFiniteLimits (condensedRingCoefficientSections Λ (Spec (.of k)))]
    [PreservesFiniteColimits (condensedRingCoefficientSections Λ (Spec (.of k)))]
    (d : ExactSectionsDerivedCup (condensedRingCoefficientSections Λ (Spec (.of k))))
    (hd : ∀ (P Q : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of k))))
      (x : (condensedRingCoefficientSections Λ (Spec (.of k))).obj P)
      (y : (condensedRingCoefficientSections Λ (Spec (.of k))).obj Q),
      (d.ordinary.μ P Q).hom (x ⊗ₜ[Γ Λ] y) = (λ_ _).inv ≫ (x ⊗ₘ y))
    (M N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of k))))) :
    ∃ r,
      d.derived.μ M N ≫ r = 𝟙 _ := by
  have : PreservesColimitsOfSize.{0, 0}
      (condensedRingCoefficientSections Λ (Spec (.of k))) := point_sections_colimits Λ k
  have : (condensedRingCoefficientSections Λ (Spec (.of k))).PreservesFlat :=
    point_sections_flat Λ k
  have : IsIso (d.derived.μ M N) :=
    cup_tensor_isIso (condensedRingCoefficientSections Λ (Spec (.of k))) d
      (point_ordinary_tensor_isIso Λ k d hd) M N
  exact ⟨inv (d.derived.μ M N), IsIso.hom_inv_id _⟩
end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint
