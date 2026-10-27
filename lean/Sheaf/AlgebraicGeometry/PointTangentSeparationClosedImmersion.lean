/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.GeneratingSectionsStalkSpan
import WeilConjectures.AlgebraicGeometry.InvertibleStalkLinearEquiv
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberSections
import Sheaf.AlgebraicGeometry.RationalUnramifiedCotangentCriterion
import Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed
import WeilConjectures.AlgebraicGeometry.FiniteUnramifiedOnePointClosed
import Sheaf.AlgebraicGeometry.ClosedFibreSingleton
import Sheaf.AlgebraicGeometry.CotangentSurjectiveOfTangentInjective
import Sheaf.AlgebraicGeometry.ProperFiniteFibreFiniteNeighbourhood
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-!
# Sections separating points and tangent vectors give a closed immersion

Source: Stacks Project, varieties.tex, Tag 0E8S, Lemma 33.23.1; coherent.tex,
Tag 02O5, Proposition 30.19.1
(blueprint: lem-sc-point-tangent-separation-closed-immersion).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

private theorem finiteDimensional_sections (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
    (L : X.Modules) [L.IsInvertible] :
    FiniteDimensional k ((ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
        (L.val.obj (Opposite.op ⊤))) := by
  let := Scheme.Modules.moduleHOfSpec f L 0
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  have := SheafOfModules.IsInvertible.isFiniteLocallyFree L
  have := SheafOfModules.IsFiniteLocallyFree.isFinitePresentation L
  have := Scheme.Modules.hasFiniteH_of_isProper f L 0
  let e : L.H 0 ≃ₗ[k] ((ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
        (L.val.obj (Opposite.op ⊤))) :=
    { (Scheme.Modules.H.zeroLinearEquiv L).toAddEquiv with
      map_smul' := fun a x ↦ (Scheme.Modules.H.zeroLinearEquiv L).map_smul _ x }
  exact Module.Finite.equiv e

private theorem basis_nonvanishing_at_closed (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (L : X.Modules) [L.IsInvertible]
    (V : Submodule k ((ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj (L.val.obj (Opposite.op ⊤))))
    (hgen : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ s : V, x ∈ Scheme.Modules.nonvanishingLocus L s.val)
    {I : Type u} (b : Module.Basis I k V) (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ i, x ∈ Scheme.Modules.nonvanishingLocus L (b i).val := by
  classical
  let P := (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
    (⊤ : Submodule (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk L.val.presheaf x))
  let W : Submodule k V :=
    { carrier := {s | TopCat.Presheaf.germ L.val.presheaf ⊤ x trivial s.val ∈ P}
      zero_mem' := by simp [P]
      add_mem' := by
        intro a c ha hc
        change TopCat.Presheaf.germ L.val.presheaf ⊤ x trivial (a.val + c.val) ∈ P
        rw [map_add]
        exact P.add_mem ha hc
      smul_mem' := by
        intro a t ht
        change TopCat.Presheaf.germ L.val.presheaf ⊤ x trivial
          ((((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom a) • t.val) ∈ P
        rw [PresheafOfModules.germ_smul]
        exact P.smul_mem _ ht }
  by_contra! hn
  have hW : W = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact not_not.mp (hn i)
  obtain ⟨t, ht⟩ := hgen x hx
  exact ht (show t ∈ W from hW ▸ Submodule.mem_top)

private theorem basis_generates (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
    (L : X.Modules) [L.IsInvertible]
    (V : Submodule k ((ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj (L.val.obj (Opposite.op ⊤))))
    (hgen : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ s : V, x ∈ Scheme.Modules.nonvanishingLocus L s.val)
    {I : Type u} [Finite I] (b : Module.Basis I k V)
    (s : I → L.sections) (hs : ∀ i, (s i).val (Opposite.op ⊤) = (b i).val) :
    Epi (L.freeHomEquiv.symm s) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let U : X.Opens := ⨆ i, Scheme.Modules.generatingLocus ((b i).val)
  have hU : U = ⊤ := by
    by_contra hn
    have hne : (U : Set X)ᶜ.Nonempty := by
      rw [Set.nonempty_compl]
      intro h
      apply hn
      exact SetLike.coe_injective h
    obtain ⟨x, hxU, hx⟩ := U.isOpen.isClosed_compl.exists_closed_singleton hne
    obtain ⟨i, hi⟩ := basis_nonvanishing_at_closed k X f L V hgen b x hx
    apply hxU
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨i, (Scheme.Modules.mem_nonvanishingLocus_iff_generatesAt L _ x).mp hi⟩
  apply (Scheme.Modules.generating_sections_iff_stalk_span X L s).mpr
  intro x
  have hx : x ∈ U := hU ▸ Set.mem_univ x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hnonvan := (Scheme.Modules.mem_nonvanishingLocus_iff_generatesAt L _ x).mpr hi
  rw [← hs i] at hnonvan
  obtain ⟨e⟩ := Scheme.Modules.invertible_stalk_linearEquiv X L x
  let v := TopCat.Presheaf.germ L.val.presheaf ⊤ x trivial ((s i).val (Opposite.op ⊤))
  have hu : IsUnit (e v) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro h
    apply hnonvan
    have hm : ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk L.val.presheaf x))).map
        e.toLinearMap = IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
      simp only [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range,
        Ideal.smul_eq_mul, Ideal.mul_top]
    rw [← hm] at h
    obtain ⟨z, hz, hez⟩ := h
    change v ∈ _
    exact e.injective hez ▸ hz
  obtain ⟨a, ha⟩ := hu
  apply top_unique
  intro z _
  have heq : z = (e z * (↑a⁻¹ : X.presheaf.stalk x)) • v := by
    apply e.injective
    rw [e.map_smul, smul_eq_mul, ← ha, mul_assoc, Units.inv_mul, mul_one]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

private theorem residue_bijective (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    Function.Bijective (f.residueFieldMap x).hom := by
  let p := pointOfClosedPoint f x hx
  let c := IsLocalRing.closedPoint k
  have h : Function.Surjective ((p ≫ f).residueFieldMap c).hom := by
    rw [pointOfClosedPoint_comp, Scheme.residueFieldMap_id]
    exact Function.surjective_id
  rw [Scheme.residueFieldMap_comp, CommRingCat.hom_comp] at h
  have hsurj : Function.Surjective (f.residueFieldMap (p c)).hom := by
    intro z
    obtain ⟨a, ha⟩ := h ((p.residueFieldMap c).hom z)
    exact ⟨a, (p.residueFieldMap c).hom.injective ha⟩
  have hpc : p c = x := pointOfClosedPoint_apply f x hx c
  rw [hpc] at hsurj
  exact ⟨(f.residueFieldMap x).hom.injective, hsurj⟩

open Scheme.Modules ProjectiveSpace in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coordinate_inj (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (L : X.Modules) [L.IsInvertible]
    (V : Submodule k ((ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj (L.val.obj (Opposite.op ⊤))))
    (hpoint : ∀ x y : X, IsClosed ({x} : Set X) → IsClosed ({y} : Set X) → x ≠ y →
      ∃ s : V, x ∉ nonvanishingLocus L s.val ∧ y ∈ nonvanishingLocus L s.val)
    {I : Type u} [Finite I] (b : Module.Basis I k V) (s : I → L.sections)
    (hsval : ∀ i, (s i).val (Opposite.op ⊤) = (b i).val)
    (hs : Epi (L.freeHomEquiv.symm s)) :
    Set.InjOn (homOfGeneratingSections I f L s hs) (closedPoints X) := by
  classical
  let := Fintype.ofFinite I
  let φ := homOfGeneratingSections I f L s hs
  obtain ⟨ε, hε⟩ := generatingSections_pair f L s hs
  have hφ := (homOfGeneratingSections_spec I f L s hs).1
  intro x hx y hy hxy
  by_contra hn
  obtain ⟨t, htx, hty⟩ := hpoint x y hx hy hn
  let c : ULift.{u} Unit → I → Γ(Spec (.of k), ⊤) :=
    fun _ i ↦ (Scheme.ΓSpecIso (.of k)).inv (b.repr t i)
  let a : I → Γ(L, ⊤) := fun i ↦ (s i).val (Opposite.op ⊤)
  let v : ULift.{u} Unit → Γ(L, ⊤) := fun _ ↦ t.val
  have hv : ∀ l, v l = ∑ i, f.appTop (c l i) • a i := by
    intro l
    calc
      v l = ∑ i, ((b.repr t i) • b i).val := by
        simpa only [Submodule.coe_sum] using
          congrArg (fun z : V ↦ z.val) (b.sum_repr t).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [a]
        rw [hsval]
        rfl
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_standardOpen I (Spec (.of k))).ge (Set.mem_univ (φ x)))
  have hxU : x ∈ φ ⁻¹ᵁ standardOpen I (Spec (.of k)) i := hi
  have hyU : y ∈ φ ⁻¹ᵁ standardOpen I (Spec (.of k)) i := by
    change φ y ∈ standardOpen I (Spec (.of k)) i
    exact hxy ▸ hi
  have hrel := map_eq_linearRatio_smul (c := c) ε.hom hε hφ hv i ⟨()⟩
  have he := isFreeGenerator_of_twistRestrict_iso ε.hom hε i
  have hiff (z : X) (hz : z ∈ φ ⁻¹ᵁ standardOpen I (Spec (.of k)) i) :
      z ∈ nonvanishingLocus L t.val ↔
        φ z ∈ (ℙ(I; Spec (.of k))).basicOpen (linearRatio c i ⟨()⟩) := by
    rw [mem_nonvanishingLocus_iff_generatesAt,
      generatesAt_iff_mem_basicOpen he hrel hz, ← Scheme.preimage_basicOpen]
    rfl
  apply htx
  apply (hiff x hxU).mpr
  rw [hxy]
  exact (hiff y hyU).mp hty

open Scheme.Modules in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_zero_of_factor_point
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (θ : Z ⟶ X) (y : Y)
    (a : Z ⟶ Spec (Y.residueField y))
    (hfac : θ ≫ g = a ≫ Y.fromSpecResidueField y)
    {U : Y.Opens} (hy : y ∈ U) (hpre : θ ⁻¹ᵁ g ⁻¹ᵁ U = ⊤)
    (L : X.Modules) (t : Γ(L, ⊤)) (e : Γ(L, g ⁻¹ᵁ U)) (r : Γ(Y, U))
    (ht : L.presheaf.map (homOfLE le_top).op t = g.app U r • e)
    (hr : Y.evaluation U y hy r = 0) : pullbackSection θ t = 0 := by
  have hp : (Y.fromSpecResidueField y).appLE U ⊤
      (Y.preimage_fromSpecResidueField hy).ge r = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).1
    rw [map_zero, ← CommRingCat.comp_apply,
      Y.fromSpecResidueField_appLE_ΓSpecIso_hom y U hy]
    exact hr
  have aux (w : Z ⟶ Y) (hw : w = a ≫ Y.fromSpecResidueField y)
      (hU : ⊤ ≤ w ⁻¹ᵁ U) : w.appLE U ⊤ hU r = 0 := by
    subst w
    rw [← Scheme.Hom.appLE_comp_appLE a (Y.fromSpecResidueField y) U ⊤ ⊤
      (Y.preimage_fromSpecResidueField hy).ge (by simp)]
    simp only [CommRingCat.comp_apply, hp, map_zero]
  have hc := aux (θ ≫ g) hfac hpre.ge
  have hc' : θ.appLE (g ⁻¹ᵁ U) ⊤ hpre.ge (g.app U r) = 0 := by
    simpa only [Scheme.Hom.comp_appLE, CommRingCat.comp_apply] using hc
  change Z.presheaf.map (homOfLE hpre.ge).op (θ.app _ (g.app U r)) = 0 at hc'
  have ht' := congrArg (fun z ↦
    ((pullback θ).obj L).presheaf.map (homOfLE hpre.ge).op (pullbackSection θ z)) ht
  rw [pullbackSection_smul, Scheme.Modules.map_smul, hc', zero_smul] at ht'
  rw [pullbackSection_map, presheaf_map_map_apply] at ht'
  simpa only [Scheme.Hom.preimage_top, presheaf_map_id_apply] using ht'

open Scheme.Modules ProjectiveSpace in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coordinate_tangent_inj (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (L : X.Modules) [L.IsInvertible]
    (V : Submodule k ((ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj (L.val.obj (Opposite.op ⊤))))
    (htangent : ∀ x : X, IsClosed ({x} : Set X) →
      ∀ θ : schemeTangentSpace k X f x, θ ≠ 0 →
        ∃ s : V, x ∉ nonvanishingLocus L s.val ∧
          ((Classical.choose (exists_tensorPullbackAdjunction θ.val)).unit.app
            L).val.app (Opposite.op ⊤) s.val ≠ 0)
    {I : Type u} [Finite I] (b : Module.Basis I k V) (s : I → L.sections)
    (hsval : ∀ i, (s i).val (Opposite.op ⊤) = (b i).val)
    (hs : Epi (L.freeHomEquiv.symm s)) (x : X) (hx : IsClosed ({x} : Set X))
    (he : Function.Bijective
      ((homOfGeneratingSections I f L s hs).residueFieldMap x).hom) :
    Function.Injective (schemeTangentMap k X (ℙ(I; Spec (.of k))) f
      (ℙ(I; Spec (.of k)) ↘ Spec (.of k)) (homOfGeneratingSections I f L s hs)
      (homOfGeneratingSections_spec I f L s hs).1 x he) := by
  classical
  let := Fintype.ofFinite I
  let Y := ℙ(I; Spec (.of k))
  let φ := homOfGeneratingSections I f L s hs
  let pY := Y ↘ Spec (.of k)
  let hφ := (homOfGeneratingSections_spec I f L s hs).1
  let e := RingEquiv.ofBijective (φ.residueFieldMap x).hom he
  let E : DualNumber (X.residueField x) ≃+* DualNumber (Y.residueField (φ x)) :=
    { DualNumber.mapRingHom e.symm.toRingHom with
      invFun := DualNumber.mapRingHom e.toRingHom
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp }
  let d := Spec.map E.toCommRingCatIso.hom
  have : IsIso d := inferInstanceAs (IsIso (Spec.map E.toCommRingCatIso.hom))
  let q := Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.inlHom (Y.residueField (φ x)) (Y.residueField (φ x))))
  let : Module (X.residueField x) (schemeTangentSpace k Y pY (φ x)) :=
    Module.compHom (schemeTangentSpace k Y pY (φ x)) e.symm.toRingHom
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro θ hθ
  by_contra hn
  obtain ⟨t, htx, htθ⟩ := htangent x hx θ hn
  have hval : d ≫ θ.val ≫ φ = q ≫ Y.fromSpecResidueField (φ x) := by
    have hm := Classical.choose_spec (exists_tangentMap_linear k X Y f pY φ hφ x he) θ
    have hz := (Classical.choose_spec
      (Classical.choose_spec (exists_tangentVectors_vectorSpace k Y pY (φ x)).2.2.2)).1
    exact hm.symm.trans ((congrArg Subtype.val hθ).trans hz)
  have hfac : θ.val ≫ φ = (inv d ≫ q) ≫ Y.fromSpecResidueField (φ x) := by
    calc
      θ.val ≫ φ = inv d ≫ (d ≫ θ.val ≫ φ) := by simp
      _ = (inv d ≫ q) ≫ Y.fromSpecResidueField (φ x) := by
        rw [hval, Category.assoc]
  obtain ⟨ε, hε⟩ := generatingSections_pair f L s hs
  let c : ULift.{u} Unit → I → Γ(Spec (.of k), ⊤) :=
    fun _ i ↦ (Scheme.ΓSpecIso (.of k)).inv (b.repr t i)
  let a : I → Γ(L, ⊤) := fun i ↦ (s i).val (Opposite.op ⊤)
  let v : ULift.{u} Unit → Γ(L, ⊤) := fun _ ↦ t.val
  have hv : ∀ l, v l = ∑ i, f.appTop (c l i) • a i := by
    intro l
    calc
      v l = ∑ i, ((b.repr t i) • b i).val := by
        simpa only [Submodule.coe_sum] using
          congrArg (fun z : V ↦ z.val) (b.sum_repr t).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [a]
        rw [hsval]
        rfl
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_standardOpen I (Spec (.of k))).ge (Set.mem_univ (φ x)))
  have hxU : x ∈ φ ⁻¹ᵁ standardOpen I (Spec (.of k)) i := hi
  have hrel := map_eq_linearRatio_smul (c := c) ε.hom hε hφ hv i ⟨()⟩
  have hfree := isFreeGenerator_of_twistRestrict_iso ε.hom hε i
  have hr : Y.evaluation _ (φ x) hi (linearRatio c i ⟨()⟩) = 0 := by
    apply (Y.evaluation_eq_zero_iff_notMem_basicOpen _ hi _).mpr
    intro h
    apply htx
    rw [mem_nonvanishingLocus_iff_generatesAt,
      generatesAt_iff_mem_basicOpen hfree hrel hxU, ← Scheme.preimage_basicOpen]
    exact h
  have hclosed : θ.val (IsLocalRing.closedPoint (DualNumber (X.residueField x))) = x := by
    have h := congrArg (fun z ↦ z (IsLocalRing.closedPoint (X.residueField x))) θ.property.1
    change θ.val (PrimeSpectrum.comap
      (TrivSqZeroExt.fstHom (X.residueField x) (X.residueField x)
        (X.residueField x)).toRingHom (IsLocalRing.closedPoint (X.residueField x))) =
      X.fromSpecResidueField x (IsLocalRing.closedPoint (X.residueField x)) at h
    rw [IsLocalRing.comap_closedPoint, Scheme.fromSpecResidueField_apply] at h
    exact h
  have hpre : θ.val ⁻¹ᵁ φ ⁻¹ᵁ standardOpen I (Spec (.of k)) i = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem θ.val (by rw [hclosed]; exact hxU)
  have hzero : pullbackSection θ.val t.val = 0 :=
    pullback_zero_of_factor_point φ θ.val (φ x) (inv d ≫ q) hfac hi hpre L t.val
      _ (linearRatio c i ⟨()⟩) hrel hr
  let adj := Classical.choose (exists_tensorPullbackAdjunction θ.val)
  let C := (adj.leftAdjointUniq (pullbackPushforwardAdjunction θ.val)).app L
  have hC : C.hom.app ⊤ ((adj.unit.app L).val.app (Opposite.op ⊤) t.val) =
      pullbackSection θ.val t.val := by
    exact congrArg (fun z ↦ z.val.app (Opposite.op ⊤) t.val)
      (adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction θ.val) L)
  apply htθ
  apply (ConcreteCategory.bijective_of_isIso (C.hom.app ⊤)).1
  simpa only [map_zero] using hC.trans hzero

private theorem opens_cover_of_closed_points {T : Type u} [TopologicalSpace T]
    [T0Space T] [CompactSpace T] {A : Type*} (U : A → TopologicalSpace.Opens T)
    (h : ∀ x : T, IsClosed ({x} : Set T) → ∃ a, x ∈ U a) : ⨆ a, U a = ⊤ := by
  by_contra hn
  have hne : ((⨆ a, U a : TopologicalSpace.Opens T) : Set T)ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro heq
    exact hn (SetLike.coe_injective heq)
  obtain ⟨x, hx, hc⟩ := (⨆ a, U a).isOpen.isClosed_compl.exists_closed_singleton hne
  obtain ⟨a, ha⟩ := h x hc
  exact hx (TopologicalSpace.Opens.mem_iSup.mpr ⟨a, ha⟩)

private theorem closedImmersion_of_cotangent (k : Type u) [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsProper pX] [IsProper pY] (g : X ⟶ Y) (hg : g ≫ pY = pX)
    (hinj : Set.InjOn g (closedPoints X))
    (hcot : ∀ x : X, IsClosed ({x} : Set X) →
      Function.Surjective
        (Ideal.mapCotangent (IsLocalRing.maximalIdeal (Y.presheaf.stalk (g x)))
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (g.stalkMap x).hom.toIntAlgHom
          (Ideal.map_le_iff_le_comap.mp
            (IsLocalRing.map_maximalIdeal_le (g.stalkMap x).hom)))) :
    IsClosedImmersion g := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace pX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace pY
  have : IsProper (g ≫ pY) := hg ▸ inferInstance
  have : IsProper g := IsProper.of_comp g pY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  let : X.Over (Spec (.of k)) := ⟨pX⟩
  let : Y.Over (Spec (.of k)) := ⟨pY⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType pX)
  have hfib (y : Y) (hy : IsClosed ({y} : Set Y)) :=
    preimage_singleton_eq_empty_or_singleton_of_injOn_closedPoints k X Y g hinj y hy
  let A := {U : Y.Opens // IsFinite (g ∣_ U)}
  have hA : ⨆ a : A, a.val = ⊤ := by
    apply opens_cover_of_closed_points
    intro y hy
    have hfin : (g ⁻¹' ({y} : Set Y)).Finite := by
      rcases hfib y hy with he | ⟨x, _, he⟩ <;> rw [he] <;> simp
    obtain ⟨U, hyU, hU⟩ := exists_open_isFinite_restrict_of_isProper_of_finite_fibre g y hfin
    exact ⟨⟨U, hU⟩, hyU⟩
  have : IsFinite g := IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @IsFinite) (fun a : A ↦ a.val) hA fun a ↦ a.property
  let B := {U : X.Opens // FormallyUnramified (U.ι ≫ g)}
  have hB : ⨆ b : B, b.val = ⊤ := by
    apply opens_cover_of_closed_points
    intro x hx
    have hy : IsClosed ({g x} : Set Y) := by
      simpa only [Set.image_singleton] using g.isClosedMap _ hx
    obtain ⟨U, hxU, hft, hu⟩ :=
      (rational_unramified_iff_cotangent_surjective k X Y pX pY g hg x hx hy
        (residue_bijective k pX x hx) (residue_bijective k pY (g x) hy)).mpr (hcot x hx)
    have : IsOpenImmersion (CategoryTheory.Limits.pullback.diagonal (U.ι ≫ g)) := hu
    exact ⟨⟨U, inferInstance⟩, hxU⟩
  have : FormallyUnramified g := IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @FormallyUnramified) (fun b : B ↦ b.val) hB fun b ↦ b.property
  let C := {U : Y.Opens // IsClosedImmersion (g ∣_ U)}
  have hC : ⨆ c : C, c.val = ⊤ := by
    apply opens_cover_of_closed_points
    intro y hy
    rcases hfib y hy with he | ⟨x, hx, he⟩
    · let U : Y.Opens := ⟨(Set.range g)ᶜ, g.isClosedMap.isClosed_range.isOpen_compl⟩
      have hyU : y ∈ U := by
        rintro ⟨x, hxy⟩
        have : x ∈ g ⁻¹' ({y} : Set Y) := hxy
        simp only [he, Set.mem_empty_iff_false] at this
      have : IsEmpty (g ⁻¹ᵁ U).toScheme := ⟨fun z ↦ z.property ⟨z.val, rfl⟩⟩
      exact ⟨⟨U, inferInstance⟩, hyU⟩
    · have hxy : g x = y := by
        have : x ∈ g ⁻¹' ({y} : Set Y) := he ▸ Set.mem_singleton x
        exact this
      have hsurj : Function.Surjective (g.residueFieldMap x).hom := by
        have hp := (residue_bijective k pX x hx).2
        rw [← hg, Scheme.residueFieldMap_comp, CommRingCat.hom_comp] at hp
        exact Function.Surjective.of_comp hp
      let := (g.residueFieldMap x).hom.toAlgebra
      have hpure : IsPurelyInseparable (Y.residueField (g x)) (X.residueField x) :=
        ⟨Algebra.isIntegral_of_surjective hsurj, fun z _ ↦ hsurj z⟩
      obtain ⟨U, hyU, hU⟩ := finite_unramified_one_point_closed g y x hxy
        (fun z hz ↦ Set.mem_singleton_iff.mp (he ▸ hz)) inferInstance
        ⟨inferInstance, inferInstance⟩ hpure
      exact ⟨⟨U, hU⟩, hyU⟩
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun c : C ↦ c.val) hC fun c ↦ c.property

/-- A generating subspace separating closed points and tangent vectors is finite-dimensional.
Every basis defines a closed immersion whose pullback of `O(1)` is `L`; for the full
section space this is the complete linear system, and `L` is very ample.
The coordinate space for a basis of `V` identifies with `P(V^dual)`.

Source: Stacks Project, varieties.tex, Tag 0E8S, Lemma 33.23.1; coherent.tex,
Tag 02O5, Proposition 30.19.1
(blueprint: lem-sc-point-tangent-separation-closed-immersion).

Proof:
1. Proper coherent cohomology makes `H^0(X,L)` finite-dimensional, hence also `V`.
2. Condition (0) makes the basis generate `L`. The projective-space construction gives
   the coordinate morphism and the identification of its pullback of `O(1)` with `L`.
3. The coordinate morphism is proper because its composite to `Spec k` is proper and
   projective space is separated (Tag 01W6).
4. Point separation gives injectivity on closed points. The closed-fibre singleton
   lemma uses the Jacobson property of a finite-type scheme over a field to show
   that each closed fibre is empty or a singleton closed point.
5. Projective space is locally Noetherian. Tag 02OH gives a finite neighbourhood of
   every closed target point. Their union is all the target: a nonempty closed complement
   would contain a closed point. Hence the coordinate morphism is finite.
6. Tangent separation makes the differential injective. On a standard chart, every
   section in `V` is a coordinate ratio times a generating basis section. A tangent
   vector with zero differential factors through the image point after composition
   with the coordinate map, hence pulls back every vanishing ratio to zero. This
   contradicts the nonzero section pullback supplied by tangent separation.
7. Rational tangent/cotangent duality makes the cotangent map surjective. The rational
   unramified criterion supplies unramified neighbourhoods of every closed source
   point. Their union is the source, so the coordinate morphism is unramified.
8. Each nonempty closed fibre is one rational point. The finite unramified one-point
   criterion gives a closed immersion near that target point. Near an empty fibre,
   use the complement of the closed image. These target opens cover, proving that
   the morphism is a closed immersion.
9. For `V = top` the morphism is the complete linear system. Its closed-immersion and
   pullback properties imply `IsVeryAmple f L`.
-/
theorem point_tangent_separation_closed_immersion
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
    (L : X.Modules) [L.IsInvertible]
    (V : Submodule k ((ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj (L.val.obj (Opposite.op ⊤))))
    (hgen : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ s : V, x ∈ Scheme.Modules.nonvanishingLocus L s.val)
    (hpoint : ∀ x y : X, IsClosed ({x} : Set X) → IsClosed ({y} : Set X) → x ≠ y →
      ∃ s : V, x ∉ Scheme.Modules.nonvanishingLocus L s.val ∧
        y ∈ Scheme.Modules.nonvanishingLocus L s.val)
    (htangent : ∀ x : X, IsClosed ({x} : Set X) →
      ∀ θ : schemeTangentSpace k X f x, θ ≠ 0 →
        ∃ s : V, x ∉ Scheme.Modules.nonvanishingLocus L s.val ∧
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction θ.val)).unit.app
            L).val.app (Opposite.op ⊤) s.val ≠ 0) :
    FiniteDimensional k V ∧
    (∀ (I : Type u) [Finite I] (b : Module.Basis I k V),
      ∃ s : I → L.sections,
        (∀ i, (s i).val (Opposite.op ⊤) = (b i).val) ∧
        ∃ hs : Epi (L.freeHomEquiv.symm s),
          IsClosedImmersion (ProjectiveSpace.homOfGeneratingSections I f L s hs) ∧
          Nonempty (ProjectiveSpace.twistRestrict
            (ProjectiveSpace.homOfGeneratingSections I f L s hs) 1 ≅ L)) ∧
    (V = ⊤ → IsVeryAmple f L) := by
  classical
  have := finiteDimensional_sections k X f L
  have hfin : FiniteDimensional k V := inferInstance
  refine ⟨hfin, ?_⟩
  have hcoord : ∀ (I : Type u) [Finite I] (b : Module.Basis I k V),
      ∃ s : I → L.sections,
        (∀ i, (s i).val (Opposite.op ⊤) = (b i).val) ∧
        ∃ hs : Epi (L.freeHomEquiv.symm s),
          IsClosedImmersion (ProjectiveSpace.homOfGeneratingSections I f L s hs) ∧
          Nonempty (ProjectiveSpace.twistRestrict
            (ProjectiveSpace.homOfGeneratingSections I f L s hs) 1 ≅ L) := by
    intro I _ b
    let s (i : I) : L.sections :=
      L.unitHomEquiv (Scheme.Modules.homOfGlobalSection L (b i).val)
    have hsval (i : I) : (s i).val (Opposite.op ⊤) = (b i).val := by
      exact (Scheme.Modules.homOfGlobalSection_app_one L (b i).val ⊤).trans
        (Scheme.Modules.presheaf_map_id_apply _ _)
    have hs := basis_generates k X f L V hgen b s hsval
    let Y := ℙ(I; Spec (.of k))
    let pY := Y ↘ Spec (.of k)
    let φ := ProjectiveSpace.homOfGeneratingSections I f L s hs
    have hφ : φ ≫ pY = f :=
      (ProjectiveSpace.homOfGeneratingSections_spec I f L s hs).1
    have : IsProper (φ ≫ pY) := hφ ▸ inferInstance
    have : IsProper φ := IsProper.of_comp φ pY
    have hinj := coordinate_inj k X f L V hpoint b s hsval hs
    have hcot (x : X) (hx : IsClosed ({x} : Set X)) :
        Function.Surjective
          (Ideal.mapCotangent (IsLocalRing.maximalIdeal (Y.presheaf.stalk (φ x)))
            (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (φ.stalkMap x).hom.toIntAlgHom
            (Ideal.map_le_iff_le_comap.mp
              (IsLocalRing.map_maximalIdeal_le (φ.stalkMap x).hom))) := by
      have hy : IsClosed ({φ x} : Set Y) := by
        simpa only [Set.image_singleton] using φ.isClosedMap _ hx
      have he : Function.Bijective (φ.residueFieldMap x).hom := by
        constructor
        · exact (φ.residueFieldMap x).hom.injective
        · have hp := (residue_bijective k f x hx).2
          rw [← hφ, Scheme.residueFieldMap_comp, CommRingCat.hom_comp] at hp
          exact Function.Surjective.of_comp hp
      exact cotangent_surjective_of_tangent_injective k X Y f pY φ hφ x hx hy
        (residue_bijective k f x hx) (residue_bijective k pY (φ x) hy)
        ⟨he, coordinate_tangent_inj k X f L V htangent b s hsval hs x hx he⟩
    exact ⟨s, hsval, hs, closedImmersion_of_cotangent k f pY φ hφ hinj hcot,
      ⟨(generatingSections_pair f L s hs).choose⟩⟩
  refine ⟨hcoord, ?_⟩
  intro _
  let b := Module.Free.chooseBasis k V
  have : Finite (Module.Free.ChooseBasisIndex k V) := Module.Finite.finite_basis b
  obtain ⟨s, _, hs, hc, he⟩ := hcoord _ b
  exact ⟨_, ProjectiveSpace.homOfGeneratingSections _ f L s hs, inferInstance, hc,
    (ProjectiveSpace.homOfGeneratingSections_spec _ f L s hs).1, he⟩

end AlgebraicGeometry
