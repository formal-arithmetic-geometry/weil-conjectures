/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedWeaklyContractible
import Mathlib.CategoryTheory.Sites.LocalSite
import WeilConjectures.SixFunctors.RingedSitePoint
import WeilConjectures.Algebra.Homology.RingedSitePointFlat
import all WeilConjectures.SmoothPurity.RingedSitePointTensor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeTerminalSectionsComparison
import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal

/-! Left-inverse part of the K-flat point tensor comparison.
Source: Stacks 07A4 and 03EL; the point tensor of the trace-cup construction
(blueprint: lem-pod-condensed-point-tensor-left-inverse).

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
2. Terminal evaluation is the inverse image at the canonical point of this local
   site. Its module functor preserves colimits and flatness. The native terminal
   section comparison identifies it with the given coefficient sections, using the
   actual scalar ring isomorphism. Functorial flat resolutions therefore give K-flat
   complexes whose sections are also K-flat. The chain comparison is invertible by
   `chain_summand`, using the inverse ordinary comparison on each total summand.
3. The field `tensor_normalization` writes `d.derived.μ` at `Q K, Q L` as a composite of
   these isomorphisms with the exact-functor localization factors. Naturality transports
   this to all `M, N`, and the inverse of the composite gives the displayed left inverse.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct ChangeOfRings CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint
private theorem final_cover_eq_top
    (k : Type u) [Field k] [IsAlgClosed k]
    (S : Sieve (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))
    (hS : S ∈ Scheme.ProEt.topology (Spec (.of k)) _) : S = ⊤ := by
  letI : Unique ↥(Scheme.ProEt.mk (𝟙 (Spec (.of k)))).left :=
    inferInstanceAs (Unique (PrimeSpectrum k))
  obtain ⟨idx, O, _, hcover, hmem⟩ :=
    Scheme.ProEt.exists_disjoint_opens_of_forall_exists_retraction
      (R := .of k) (fun T _ _ _ _ ↦ by
        have : Nontrivial (k ⊗[k] T) := Module.FaithfullyFlat.rTensor_nontrivial k T k
        have : Nontrivial T := (TensorProduct.lid k T).symm.toEquiv.nontrivial
        obtain ⟨φ⟩ := Algebra.WeaklyEtale.nonempty_algHom_of_isSepClosed (K := k) (R := T)
        exact ⟨φ.toRingHom, RingHom.ext fun x ↦ φ.commutes x⟩)
      (Iso.refl _) hS
  obtain ⟨i, hi⟩ := hcover default
  have hO : O i = ⊤ := by
    apply top_unique
    intro x _
    simpa only [Subsingleton.elim x default] using hi
  have hι : IsIso (O i).ι := by rw [hO]; exact (Scheme.topIso _).isIso_hom
  let f := Scheme.ProEt.ofOpenImmersionHom
    (Scheme.ProEt.mk (𝟙 (Spec (.of k)))) (O i).ι
  let g : Scheme.ProEt.mk (𝟙 (Spec (.of k))) ⟶
      Scheme.ProEt.ofOpenImmersion (Scheme.ProEt.mk (𝟙 (Spec (.of k)))) (O i).ι :=
    MorphismProperty.Over.homMk (inv (O i).ι) (by
      change inv (O i).ι ≫ ((O i).ι ≫ 𝟙 _) = 𝟙 _
      simp)
  have hgf : g ≫ f = 𝟙 _ := by
    apply MorphismProperty.Over.Hom.ext
    change inv (O i).ι ≫ (O i).ι = 𝟙 _
    simp
  apply S.id_mem_iff_eq_top.mp
  rw [← hgf]
  exact S.downward_closed (hmem i) g

private theorem localSite_of_final
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (U : C) (hU : IsTerminal U) (h : ∀ S ∈ J U, S = ⊤) : J.IsLocalSite := by
  letI : HasTerminal C := hU.hasTerminal
  refine { eq_top_of_mem := ?_ }
  intro S hS
  let e := terminalIsoIsTerminal hU
  have hs : Sieve.pullback e.inv S = ⊤ := h _ (J.pullback_stable e.inv hS)
  apply S.id_mem_iff_eq_top.mp
  have hi : (Sieve.pullback e.inv S) (𝟙 _) := by rw [hs]; trivial
  have hi' : S e.inv := by simpa using hi
  simpa using S.downward_closed hi' e.hom

private def terminalPoint
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [J.IsLocalSite] (U : C) (hU : IsTerminal U) :
    GeometricMorphism (Type (u + 1)) (Sheaf J (Type (u + 1))) where
  inverse := sheafToPresheaf J (Type (u + 1)) ⋙
    (evaluation Cᵒᵖ (Type (u + 1))).obj (Opposite.op U)
  direct := GrothendieckTopology.IsLocalSite.coconstantSheaf.{u} J (Type (u + 1))
  adj := (GrothendieckTopology.IsLocalSite.ΓCoconstantSheafAdj.{u}
    J (Type (u + 1))).ofNatIsoLeft (Sheaf.ΓNatIsoSheafSections J (Type (u + 1)) hU)
  leftExact := inferInstance

private def terminalModulePoint
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [J.IsLocalSite]
    (R : Sheaf J CommRingCat.{u + 1}) (U : C) (hU : IsTerminal U)
    {A : Type (u + 1)} [CommRing A] (a : A ≃+* R.obj.obj (Opposite.op U)) :
    RingedSitePoint R (terminalPoint J U hU) where
  ring := CommRingCat.of A
  ringUnderlying := a.symm.toEquiv.toIso
  ringAdd T b c t h x := by
    change a.symm (t.hom.app _ x) = a.symm (b.hom.app _ x) + a.symm (c.hom.app _ x)
    change T.obj.obj (Opposite.op U) at x
    simpa only [id, map_add] using congrArg a.symm (h _ x)
  ringMul T b c t h x := by
    change a.symm (t.hom.app _ x) = a.symm (b.hom.app _ x) * a.symm (c.hom.app _ x)
    change T.obj.obj (Opposite.op U) at x
    simpa only [id, map_mul] using congrArg a.symm (h _ x)
  ringZero T b h x := by
    change a.symm (b.hom.app _ x) = 0
    change T.obj.obj (Opposite.op U) at x
    simpa only [id, map_zero] using congrArg a.symm (h _ x)
  ringOne T b h x := by
    change a.symm (b.hom.app _ x) = 1
    change T.obj.obj (Opposite.op U) at x
    simpa only [id, map_one] using congrArg a.symm (h _ x)
  modules := SheafOfModules.evaluation _ (Opposite.op U) ⋙ ModuleCat.restrictScalars a.toRingHom
  moduleUnderlying := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)
  moduleAdd M T b c t h x := h _ x
  moduleZero M T b h x := h _ x
  moduleSMul M T b c t h x := by
    change T.obj.obj (Opposite.op U) at x
    change (@id (M.val.obj (Opposite.op U)) (t.hom.app _ x)) =
      a (a.symm (b.hom.app _ x)) • (@id (M.val.obj (Opposite.op U)) (c.hom.app _ x))
    rw [a.apply_symm_apply]
    exact h _ x
  modules_additive := ⟨by intros; rfl⟩

private theorem local_sheafification_unit_isIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [J.IsLocalSite] (P : Cᵒᵖ ⥤ Ab.{u + 1}) (U : C) (hU : IsTerminal U) :
    IsIso ((toSheafify J P).app (Opposite.op U)) := by
  let p := GrothendieckTopology.IsLocalSite.point.{u} J
  let e := terminalIsoIsTerminal hU
  let unitMap := toSheafify J P
  haveI hpoint : IsIso (p.presheafFiber.map unitMap) := inferInstance
  haveI ht : IsIso (unitMap.app (Opposite.op (⊤_ C))) := by
    have hn := GrothendieckTopology.IsLocalSite.pointPresheafFiberIso_naturality.{u} J unitMap
    haveI hc : IsIso
        ((GrothendieckTopology.IsLocalSite.pointPresheafFiberIso.{u} J P).hom ≫
          unitMap.app (Opposite.op (⊤_ C))) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (GrothendieckTopology.IsLocalSite.pointPresheafFiberIso.{u} J P).hom
      (unitMap.app (Opposite.op (⊤_ C)))
  haveI he : IsIso (unitMap.app (Opposite.op U) ≫ (sheafify J P).map e.op.hom) := by
    rw [← unitMap.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right (unitMap.app (Opposite.op U))
    ((sheafify J P).map e.op.hom)

private theorem local_module_unit_isIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [J.IsLocalSite]
    (R : Sheaf J CommRingCat.{u + 1})
    (P : PresheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
    (U : C) (hU : IsTerminal U) :
    IsIso (((PresheafOfModules.sheafificationAdjunction (𝟙
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
        P).app (Opposite.op U)) := by
  haveI := local_sheafification_unit_isIso J P.presheaf U hU
  let f := (((PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
      P).app (Opposite.op U))
  haveI : IsIso ((forget₂ (ModuleCat.{u + 1} (R.obj.obj (Opposite.op U)))
      AddCommGrpCat.{u + 1}).map f) := by
    change IsIso ((toSheafify J P.presheaf).app (Opposite.op U))
    infer_instance
  exact isIso_of_reflects_iso f (forget₂
    (ModuleCat.{u + 1} (R.obj.obj (Opposite.op U))) AddCommGrpCat.{u + 1})

set_option maxHeartbeats 1200000 in
-- The inherited coefficient and derived structures require substantial elaboration.
set_option synthInstance.maxHeartbeats 100000 in
private def pointScalarEquiv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    Γ Λ ≃+* (InternalAbelianSheafModule.sectionRingSheaf
      (Scheme.ProEt.topology (Spec (.of k))) (condensedRingObj Λ (Spec (.of k)))).obj.obj
        (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) := by
  letI := Functor.additive_of_preserves_binary_products (upperStarFromPoint (Spec (.of k)))
  refine RingEquiv.ofBijective
    ((InternalAbelianSheafModule.sectionGlobalEval.{u + 1, u + 1, u}
      _ _ _).comp
      (condensedRingScalarSections Λ (Spec (.of k)))) ?_
  exact (InternalAbelianSheafModule.sectionGlobalEval_bijective.{u + 1, u + 1, u}
    (Scheme.ProEt.topology (Spec (.of k))) (condensedRingObj Λ (Spec (.of k)))
    (Scheme.ProEt.mk (𝟙 (Spec (.of k))))
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale (Spec (.of k)))).comp
      (InternalAbelianSheafModule.globalMapFunctor_bijective
        (upperStarFromPoint (Spec (.of k))) (Functor.FullyFaithful.ofFullyFaithful _) Λ)

set_option maxHeartbeats 1200000 in
-- The inherited coefficient and derived structures require substantial elaboration.
set_option synthInstance.maxHeartbeats 100000 in
private theorem point_sections_colimits_flat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    PreservesColimitsOfSize.{0, 0} (condensedRingCoefficientSections Λ (Spec (.of k))) ∧
      (condensedRingCoefficientSections Λ (Spec (.of k))).PreservesFlat := by
  let J := Scheme.ProEt.topology (Spec (.of k))
  let O := condensedRingObj Λ (Spec (.of k))
  let U := Scheme.ProEt.mk (𝟙 (Spec (.of k)))
  let hU := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale
    (Spec (.of k))
  letI : J.IsLocalSite := localSite_of_final J U hU (final_cover_eq_top k)
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J O
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O
  let s := terminalModulePoint J R U hU (pointScalarEquiv Λ k)
  obtain ⟨e⟩ := CondensedRing.native_terminalSectionsIso
    J O (condensedRingScalarSections Λ (Spec (.of k))) U hU
  have he : condensedRingCoefficientSections Λ (Spec (.of k)) ≅ E.functor ⋙ s.modules := e
  haveI : PreservesColimits s.modules := RingedSitePoint.preservesColimits s
  haveI : PreservesColimitsOfSize.{0, 0} s.modules :=
    preservesSmallestColimits_of_preservesColimits s.modules
  constructor
  · exact preservesColimits_of_natIso he.symm
  · constructor
    intro M hM
    have hf := s.flat (E.functor.obj M)
      ((InternalAbelianSheafModule.flat_iff_sectionModule J O M).mp hM)
    apply (ModuleCat.flat_iff_flat _).mpr
    exact (Module.Flat.equiv_iff ((he.app M).toLinearEquiv)).mpr hf

private theorem regular_tensor_section
    {C : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    (O : C) [MonObj O] [IsCommMonObj O] (M N : Mod C O)
    (x : Mod.regular O ⟶ M) (y : Mod.regular O ⟶ N) :
    η[O] ≫ ((λ_ (Mod.regular O)).inv ≫ (x ⊗ₘ y)).hom =
      (λ_ (𝟙_ C)).inv ≫ ((η[O] ≫ x.hom) ⊗ₘ (η[O] ≫ y.hom)) ≫
        Mod.tensorObjπ M N := by
  have hu : η[O] ≫ (λ_ (Mod.regular O)).inv.hom =
      (λ_ (𝟙_ C)).inv ≫ (η[O] ⊗ₘ η[O]) ≫
        Mod.tensorObjπ (Mod.regular O) (Mod.regular O) := by
    apply (cancel_mono (λ_ (Mod.regular O)).hom.hom).mp
    rw [Category.assoc, ← Mod.comp_hom', Iso.inv_hom_id, Mod.id_hom']
    change η[O] ≫ 𝟙 O = _
    rw [Category.comp_id]
    rw [Category.assoc, Category.assoc, Mod.tensorObjπ_regular_leftUnitor_hom]
    change η[O] = (λ_ (𝟙_ C)).inv ≫ (η[O] ⊗ₘ η[O]) ≫ μ[O]
    rw [MonObj.one_mul_hom, Iso.inv_hom_id_assoc]
  have hp : Mod.tensorObjπ (Mod.regular O) (Mod.regular O) ≫ (x ⊗ₘ y).hom =
      (x.hom ⊗ₘ y.hom) ≫ Mod.tensorObjπ M N := by
    simp only [MonoidalCategory.tensorHom_def, Mod.comp_hom', Category.assoc]
    rw [Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft]
  rw [Mod.comp_hom', ← Category.assoc, hu, Category.assoc, Category.assoc, hp]
  simp only [← tensorHom_comp_tensorHom_assoc]

private theorem lax_global_tensor
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] {M N : C} (a : 𝟙_ C ⟶ M) (b : 𝟙_ C ⟶ N) :
    Functor.LaxMonoidal.ε F ≫ F.map ((λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b)) =
      (λ_ (𝟙_ D)).inv ≫
        ((Functor.LaxMonoidal.ε F ≫ F.map a) ⊗ₘ
          (Functor.LaxMonoidal.ε F ≫ F.map b)) ≫ Functor.LaxMonoidal.μ F M N := by
  calc
    _ = Functor.LaxMonoidal.ε F ≫ F.map (λ_ (𝟙_ C)).inv ≫ F.map (a ⊗ₘ b) := by
      simp only [F.map_comp]
    _ = Functor.LaxMonoidal.ε F ≫ (λ_ (F.obj (𝟙_ C))).inv ≫
        (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ C)) ≫
        Functor.LaxMonoidal.μ F (𝟙_ C) (𝟙_ C) ≫ F.map (a ⊗ₘ b) := by
      rw [Functor.LaxMonoidal.left_unitality_inv_assoc]
    _ = (λ_ (𝟙_ D)).inv ≫
        (Functor.LaxMonoidal.ε F ⊗ₘ Functor.LaxMonoidal.ε F) ≫
        Functor.LaxMonoidal.μ F (𝟙_ C) (𝟙_ C) ≫ F.map (a ⊗ₘ b) := by
      rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
        leftUnitor_inv_naturality]
      simp only [MonoidalCategory.tensorHom_def', Category.assoc]
    _ = (λ_ (𝟙_ D)).inv ≫
        (Functor.LaxMonoidal.ε F ⊗ₘ Functor.LaxMonoidal.ε F) ≫
        (F.map a ⊗ₘ F.map b) ≫ Functor.LaxMonoidal.μ F M N := by
      rw [← Functor.LaxMonoidal.μ_natural]
    _ = _ := by rw [← tensorHom_comp_tensorHom_assoc]

private theorem terminal_eval_tensor
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    {A : Type (u + 1)} [CommRing A] (s : A →+* Γ O) (U : C)
    (M N : Mod (Sheaf J Ab.{u + 1}) O)
    (x : Mod.regular O ⟶ M) (y : Mod.regular O ⟶ N) :
    CondensedRing.terminal_eval J O s U (M ⊗ N) ((λ_ _).inv ≫ (x ⊗ₘ y)) =
      InternalAbelianSheafModule.comparison_internalTmul J O M N (Opposite.op U)
        (CondensedRing.terminal_eval J O s U M x)
        (CondensedRing.terminal_eval J O s U N y) := by
  let F := CondensedRing.site_eval J U
  change ((Functor.LaxMonoidal.ε F ≫
    F.map (η[O] ≫ ((λ_ (Mod.regular O)).inv ≫ (x ⊗ₘ y)).hom)).hom) (ULift.up 1) = _
  rw [regular_tensor_section]
  have h := congrArg (fun f ↦ ((f ≫ F.map (Mod.tensorObjπ M N)).hom) (ULift.up 1))
    (lax_global_tensor F (η[O] ≫ x.hom) (η[O] ≫ y.hom))
  have hu (X : Ab.{u + 1}) (x : X) :
      (λ_ X).inv.hom x = (ULift.up 1) ⊗ₜ[ℤ] x := by
    apply (ConcreteCategory.bijective_of_isIso (λ_ X).hom).1
    change (λ_ X).hom.hom ((λ_ X).inv.hom x) =
      (λ_ X).hom.hom ((ULift.up 1) ⊗ₜ[ℤ] x)
    simp only [Iso.inv_hom_id_apply,
      AddCommGrpCat.MonoidalCategory.leftUnitor_hom_tmul, one_zsmul]
  change _ = (F.map (Mod.tensorObjπ M N)).hom
    ((Functor.LaxMonoidal.μ F M.X N.X).hom
      (((Functor.LaxMonoidal.ε F ≫ F.map (η[O] ≫ x.hom)) ⊗ₘ
        (Functor.LaxMonoidal.ε F ≫ F.map (η[O] ≫ y.hom))).hom
          ((λ_ (𝟙_ Ab.{u + 1})).inv.hom (ULift.up 1)))) at h
  rw [hu, AddCommGrpCat.MonoidalCategory.tensorHom_tmul] at h
  have hμ : Functor.LaxMonoidal.μ F M.X N.X =
      (Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1}) M.X N.X).app
        (Opposite.op U) := by rfl
  have hπ : F.map (Mod.tensorObjπ M N) =
      (Mod.tensorObjπ M N).hom.app (Opposite.op U) := rfl
  dsimp only [InternalAbelianSheafModule.comparison_internalTmul, CondensedRing.terminal_eval]
  rw [← hπ, ← hμ]
  change _ = (F.map (Mod.tensorObjπ M N)).hom
    ((Functor.LaxMonoidal.μ F M.X N.X).hom
      (((Functor.LaxMonoidal.ε F ≫ F.map (η[O] ≫ x.hom)).hom (ULift.up 1)) ⊗ₜ[ℤ]
        ((Functor.LaxMonoidal.ε F ≫ F.map (η[O] ≫ y.hom)).hom (ULift.up 1))))
  simpa only [Category.assoc, ← F.map_comp] using h


set_option maxHeartbeats 1200000 in
-- The inherited coefficient and derived structures require substantial elaboration.
set_option synthInstance.maxHeartbeats 100000 in
private theorem ordinary_isIso
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
    (M N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k)))) : IsIso (d.ordinary.μ M N) := by
  let J := Scheme.ProEt.topology (Spec (.of k))
  let O := condensedRingObj Λ (Spec (.of k))
  let U := Scheme.ProEt.mk (𝟙 (Spec (.of k)))
  let hU := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale
    (Spec (.of k))
  letI : J.IsLocalSite := localSite_of_final J U hU (final_cover_eq_top k)
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J O
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O
  let G := condensedRingCoefficientSections Λ (Spec (.of k))
  let a := pointScalarEquiv Λ k
  let s := condensedRingScalarSections Λ (Spec (.of k))
  letI : RingHomInvPair a.toRingHom a.symm.toRingHom := by
    simpa only [RingEquiv.toRingHom_eq_coe] using RingHomInvPair.of_ringEquiv a
  letI : RingHomInvPair a.symm.toRingHom a.toRingHom := by
    simpa only [RingEquiv.toRingHom_eq_coe] using RingHomInvPair.of_ringEquiv_symm a
  let linearX (P : Mod (Sheaf J Ab.{u + 1}) O) :
      G.obj P →ₛₗ[a.toRingHom] (E.functor.obj P).val.obj (Opposite.op U) :=
    { toFun := CondensedRing.terminal_eval J O s U P
      map_add' := by
        intro z w
        have h := (CondensedRing.terminal_linear J O s U P).map_add z w
        exact h
      map_smul' := by
        intro r z
        have h := (CondensedRing.terminal_linear J O s U P).map_smul r z
        exact h }
  let eX (P : Mod (Sheaf J Ab.{u + 1}) O) :
      G.obj P ≃ₛₗ[a.toRingHom] (E.functor.obj P).val.obj (Opposite.op U) :=
    LinearEquiv.ofBijective (linearX P) (CondensedRing.terminal_eval_bijective J O s U hU P)
  obtain ⟨_, t, _, hpure, _⟩ :=
    InternalAbelianSheafModule.internal_section_tensor_comparison.{u + 1, u + 1, u} J O
  let P : PresheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj :=
    (E.functor.obj M).val ⊗ (E.functor.obj N).val
  let f := ((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
      P).app (Opposite.op U)
  haveI : IsIso f := local_module_unit_isIso J R P U hU
  let g := (SheafOfModules.tensorObjIsoSheafification
    (E.functor.obj M) (E.functor.obj N)).inv.val.app (Opposite.op U)
  haveI : IsIso g := by
    change IsIso ((SheafOfModules.evaluation _ (Opposite.op U)).map
      (SheafOfModules.tensorObjIsoSheafification
        (E.functor.obj M) (E.functor.obj N)).inv)
    infer_instance
  let i := (SheafOfModules.evaluation _ (Opposite.op U)).mapIso (t M N)
  let e := TensorProduct.congr (eX M) (eX N)
  have hc : ∀ z, eX (M ⊗ N) ((d.ordinary.μ M N).hom z) = i.inv (g (f (e z))) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul x y =>
      rw [hd]
      change CondensedRing.terminal_eval J O s U (M ⊗ N)
        ((λ_ _).inv ≫ (x ⊗ₘ y)) =
          i.inv (g (f ((eX M x) ⊗ₜ[R.obj.obj (Opposite.op U)] (eX N y))))
      rw [terminal_eval_tensor]
      apply (ConcreteCategory.bijective_of_isIso i.hom).1
      rw [Iso.inv_hom_id_apply]
      have h := hpure M N (Opposite.op U) (eX M x) (eX N y)
      change i.hom (InternalAbelianSheafModule.comparison_internalTmul J O M N
        (Opposite.op U) (eX M x) (eX N y)) =
          g (f ((eX M x) ⊗ₜ[R.obj.obj (Opposite.op U)] (eX N y))) at h
      exact h
  have hb := (ConcreteCategory.bijective_of_isIso i.inv).comp
    ((ConcreteCategory.bijective_of_isIso g).comp
      ((ConcreteCategory.bijective_of_isIso f).comp e.bijective))
  have hh : eX (M ⊗ N) ∘ (d.ordinary.μ M N).hom = i.inv ∘ g ∘ f ∘ e := funext hc
  rw [← hh] at hb
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ((eX (M ⊗ N)).bijective.of_comp_iff' _).mp hb

section Generic
variable {B : Type*} [Category B] [Abelian B]
  [MonoidalCategory B] [MonoidalPreadditive B]
  [∀ (X Y : GradedObject ℤ B), X.HasTensor Y]
  [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X)]
  [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X)]
  [∀ (W X Y Z : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  {S : Type*} [CommRing S]
  [HasDerivedCategory B] [HasDerivedCategory (ModuleCat S)]
  [MonoidalCategory (DerivedCategory B)]
  [(DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B).LaxMonoidal]
  (G : B ⥤ ModuleCat S) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
attribute [local irreducible] Functor.mapDerivedCategory HasDerivedCategory.standard
set_option maxHeartbeats 1200000 in
-- The inherited coefficient and derived structures require substantial elaboration.
set_option synthInstance.maxHeartbeats 100000 in
private theorem chain_isIso_of_ordinary
    [PreservesColimitsOfSize.{0, 0} G]
    (d : ExactSectionsDerivedCup G)
    (hμ : ∀ M N, IsIso (d.ordinary.μ M N))
    (K L : CochainComplex B ℤ) : IsIso (d.chain K L) := by
  letI := d.ordinary
  letI : ∀ M N, IsIso (d.ordinary.μ M N) := hμ
  haveI : IsIso (Functor.LaxMonoidal.μNatTrans G) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    exact hμ M N
  let e := asIso (Functor.LaxMonoidal.μNatTrans G)
  let c := HomologicalComplex.mapBifunctorComparison e.inv (.up ℤ) K L
  haveI hc : IsIso c := inferInstance
  have he : d.chain K L ≫ c = 𝟙 _ := by
    ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    rw [← Category.assoc, d.chain_summand, Category.assoc]
    erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
    simp only [HomologicalComplex.mapBifunctorComparisonApp, e, asIso_inv,
      NatIso.isIso_inv_app, Functor.LaxMonoidal.μNatTrans_app_app,
      IsIso.hom_inv_id_assoc]
    exact (Category.comp_id _).symm
  exact isIso_of_comp_hom_eq_id c he

set_option maxHeartbeats 1200000 in
-- The inherited coefficient and derived structures require substantial elaboration.
set_option synthInstance.maxHeartbeats 100000 in
private theorem tensor_isIso_of_representatives
    (d : ExactSectionsDerivedCup G)
    (W : ObjectProperty (CochainComplex B ℤ))
    (hmodels : ∀ M, ∃ K, W K ∧ Nonempty (DerivedCategory.Q.obj K ≅ M))
    (hchain : ∀ K L, W K → W L → IsIso (d.chain K L))
    (hsource : ∀ K L, W K → W L →
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q K L))
    (himage : ∀ K L, W K → W L →
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
        ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L)))
    (M N : DerivedCategory B) : IsIso (d.derived.μ M N) := by
  letI := d.derived
  obtain ⟨K, hK, ⟨eK⟩⟩ := hmodels M
  obtain ⟨L, hL, ⟨eL⟩⟩ := hmodels N
  letI := hchain K L hK hL
  letI := hsource K L hK hL
  letI := himage K L hK hL
  haveI ht : IsIso (d.derived.μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
      G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q K L) ≫
      G.mapDerivedCategoryFactors.hom.app (K ⊗ L)) := by
    rw [d.tensor_normalization]
    infer_instance
  haveI hm : IsIso (d.derived.μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)) :=
    IsIso.of_isIso_comp_right _
      (G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q K L) ≫
        G.mapDerivedCategoryFactors.hom.app (K ⊗ L))
  have hn := Functor.LaxMonoidal.μ_natural G.mapDerivedCategory eK.hom eL.hom
  haveI hc : IsIso ((G.mapDerivedCategory.map eK.hom ⊗ₘ
      G.mapDerivedCategory.map eL.hom) ≫ d.derived.μ M N) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (G.mapDerivedCategory.map eK.hom ⊗ₘ G.mapDerivedCategory.map eL.hom)
    (d.derived.μ M N)

end Generic

set_option maxHeartbeats 1200000 in
-- The inherited coefficient and derived structures require substantial elaboration.
set_option synthInstance.maxHeartbeats 100000 in
theorem tensorData_tensor_left_inverse
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
    ∃ l,
      l ≫ d.derived.μ M N = 𝟙 _ := by
  let A := Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
    (condensedRingObj Λ (Spec (.of k)))
  let G := condensedRingCoefficientSections Λ (Spec (.of k))
  obtain ⟨hc, hf⟩ := point_sections_colimits_flat Λ k
  letI : PreservesColimitsOfSize.{0, 0} G := hc
  letI : G.PreservesFlat := hf
  let R := (inferInstance : Abelian.HasFunctorialFlatResolution A).some.reduced
  let W : ObjectProperty (CochainComplex A ℤ) := fun K ↦
    (HomologicalComplex.quasiIso A (.up ℤ)).kFlat K ∧
      (HomologicalComplex.quasiIso (ModuleCat.{u + 1} (Γ Λ)) (.up ℤ)).kFlat
        ((G.mapHomologicalComplex (.up ℤ)).obj K)
  have hmodels : ∀ X, ∃ K, W K ∧ Nonempty (DerivedCategory.Q.obj K ≅ X) := by
    intro X
    let K := DerivedCategory.Q.objPreimage X
    haveI : QuasiIso (R.resolutionNatTrans.app K) := R.quasiIso_resolutionNatTrans_app K
    refine ⟨R.resolutionFunctor.obj K, ⟨?_, ?_⟩, ?_⟩
    · exact R.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K
    · exact G.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj R
        ObjectProperty.flat.essImage_ι_le K
    · exact ⟨asIso (DerivedCategory.Q.map (R.resolutionNatTrans.app K)) ≪≫
        DerivedCategory.Q.objObjPreimageIso X⟩
  haveI : IsIso (d.derived.μ M N) :=
    tensor_isIso_of_representatives G d W hmodels
      (fun K L _ _ ↦ chain_isIso_of_ordinary G d (ordinary_isIso Λ k d hd) K L)
      (fun K L _ hL ↦ RingedDerivedNative.localization_isIso_mu K L
        (Or.inr ((HomotopyCategory.kFlat_quotient_obj_iff L).mpr hL.1)))
      (fun K L _ hL ↦ RingedDerivedNative.localization_isIso_mu _ _
        (Or.inr ((HomotopyCategory.kFlat_quotient_obj_iff _).mpr hL.2))) M N
  exact ⟨inv (d.derived.μ M N), IsIso.inv_hom_id _⟩
end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint
