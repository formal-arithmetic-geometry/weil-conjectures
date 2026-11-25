/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSupport
public import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.AlgebraicGeometry.GeometricStalkSupport
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Support of a constructible etale module sheaf

## References

* Stacks Project, Tags 09YS, 04FS and 04FN
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem constructible_image_clopen {Y : Type u} [TopologicalSpace Y]
    {X : Type u} [TopologicalSpace X] [SpectralSpace X] {f : Y → X}
    (hf : Topology.IsEmbedding f) (hE : Topology.IsConstructible (Set.range f))
    {t : Set Y} (ht : IsClopen t) : Topology.IsConstructible (f '' t) := by
  have hEc : IsCompact (Set.range f) := by
    have h := isCompact_iInter_of_isConstructible
      (s := fun _ : Unit ↦ Set.range f) (fun _ ↦ hE)
    simpa only [Set.iInter_const] using h
  have hY : IsCompact (Set.univ : Set Y) := by
    apply hf.isCompact_iff.mpr
    simpa using hEc
  have htc : IsCompact (f '' t) := by
    simpa using (hY.inter_right ht.1).image hf.continuous
  obtain ⟨U, hU, htU⟩ := hf.isInducing.image_eq_isOpen_inter_range ht.2
  obtain ⟨W, hWc, hWo, htW, hWU⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between htc hU
      (by rw [htU]; exact Set.inter_subset_left)
  have heq : f '' t = Set.range f ∩ W := by
    rw [htU] at htW ⊢
    exact Set.Subset.antisymm (fun x hx ↦ ⟨hx.2, htW hx⟩)
      (fun x hx ↦ ⟨hWU hx.2, hx.1⟩)
  rw [heq]
  exact hE.inter (hWc.isConstructible hWo)

/-- The value on a trivializing cover member detects support at every point in its image,
including after pullback along an arbitrary scheme morphism (Stacks, Tags 09YS, 03Q1 and 04FN). -/
private theorem etaleModuleSupport_on_trivializing_cover
    {X Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (f : Y ⟶ X)
    (d : LocallyConstantDatum ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G))
    (M : d.cover.I₀ → ModuleCat.{u + 1} Λ)
    (hM : ∀ i : d.cover.I₀, Finite (M i) ∧
      Nonempty ((((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G).over
          (d.cover.etalePrecoverageToEtale i)) ≅
        (constantSheaf (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} Λ)).obj (M i))) :
    ∀ (i : d.cover.I₀) (y : d.cover.X i),
      f (d.cover.f i y) ∈ etaleSheafSupport
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) ↔
        ¬ IsZero (M i) := by
  let : PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u, u} Λ
  intro i y
  let K := (d.cover.X i).residueField y
  let Ω := AlgebraicClosure K
  let s : Spec (.of Ω) ⟶ d.cover.X i :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ (d.cover.X i).fromSpecResidueField y
  let t := (s ≫ d.cover.f i) ≫ f
  let F := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
  have ht : t default = f (d.cover.f i y) := by
    change f (d.cover.f i ((d.cover.X i).fromSpecResidueField y
      ((Spec.map (CommRingCat.ofHom (algebraMap K Ω))) default))) = _
    rw [Scheme.fromSpecResidueField_apply]
  obtain ⟨e⟩ := (finite_locally_constant_module_values_iff
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G)).2.2 d M hM i Ω s
  let e' := (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ)
    f (s ≫ d.cover.f i)).app G
  let E : sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
          (pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      (pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ) ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
    (pointSmallEtale t).sheafFiberCompIso.{u, u, u + 1, u + 1, u + 1, u + 2, u + 2}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let eF := E.app G
  let eM := eF ≪≫ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso
    (e'.symm ≪≫ e)
  have hz : IsZero ((pointSmallEtale t).sheafFiber.obj F) ↔ IsZero (M i) := by
    refine eM.isZero_iff.trans ?_
    rw [AddCommGrpCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
    rfl
  constructor
  · rintro ⟨Ω', hfield, hclosed, t', ht', hn⟩ hzM
    exact hn ((isZero_sheafFiber_iff_of_same_image t t' (ht.trans ht'.symm) F).mp
      (hz.mpr hzM))
  · intro hn
    exact ⟨Ω, inferInstance, inferInstance, t, ht, fun h ↦ hn (hz.mp h)⟩


/-- The zero-stalk condition is independent of the geometric point over a point of `X`;
a single zero stalk excludes that point from the support. The support is constructible.
Stalks and support are taken for the underlying abelian sheaf (Stacks, Tags 09YS, 04FS and 04FN). -/
theorem constructibleEtaleModuleSupport {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {Λ : Type (u + 1)}
    [CommRing Λ] [Finite Λ] (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsConstructibleEtaleModuleSheaf G) :
    let F := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
    (∀ (x : X) (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
      (s : Spec (.of Ω) ⟶ X) (s' : Spec (.of Ω') ⟶ X),
      s default = x → s' default = x →
        (IsZero (((pointSmallEtale s).sheafFiber).obj F) ↔
          IsZero (((pointSmallEtale s').sheafFiber).obj F))) ∧
    (∀ (x : X) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      s default = x → IsZero (((pointSmallEtale s).sheafFiber).obj F) →
        x ∉ etaleSheafSupport F) ∧
    Topology.IsConstructible (etaleSheafSupport F) := by
  dsimp only
  let F := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
  have hind (x : X) (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω]
      [Field Ω'] [IsAlgClosed Ω'] (s : Spec (.of Ω) ⟶ X) (s' : Spec (.of Ω') ⟶ X)
      (hs : s default = x) (hs' : s' default = x) :
      IsZero ((pointSmallEtale s).sheafFiber.obj F) ↔
        IsZero ((pointSmallEtale s').sheafFiber.obj F) :=
    isZero_sheafFiber_iff_of_same_image s s' (hs.trans hs'.symm) F
  refine ⟨hind, ?_, ?_⟩
  · intro x Ω _ _ s hs hz hmem
    obtain ⟨Ω', hfield, hclosed, s', hs', hnz⟩ := hmem
    exact hnz ((hind x Ω Ω' s s' hs hs').mp hz)
  · classical
    obtain ⟨S, hS⟩ := hG
    have hSc := S.isConstructible_stratum
    have hpart (k : Fin S.n) :
        Topology.IsConstructible (etaleSheafSupport F ∩ S.stratum k) := by
      obtain ⟨d, hd⟩ := hS k
      choose M hM using hd
      have hvalue := etaleModuleSupport_on_trivializing_cover G (S.immersion k) d M hM
      let A : Set (S.domain k) := (S.immersion k) ⁻¹' etaleSheafSupport F
      have hrange (i : d.cover.I₀) : IsOpen (Set.range (d.cover.f i)) := by
        let : Etale (d.cover.f i) := d.cover.map_prop i
        simpa only [Set.image_univ] using (d.cover.f i).isOpenMap _ isOpen_univ
      have hpos : A = ⋃ (i : d.cover.I₀) (_ : ¬ IsZero (M i)),
          Set.range (d.cover.f i) := by
        ext y
        constructor
        · intro hy
          obtain ⟨i, z, rfl⟩ := d.cover.exists_eq y
          exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
            ⟨(hvalue i z).mp hy, ⟨z, rfl⟩⟩⟩
        · intro hy
          simp only [Set.mem_iUnion, Set.mem_range] at hy
          obtain ⟨i, hi, z, rfl⟩ := hy
          exact (hvalue i z).mpr hi
      have hneg : Aᶜ = ⋃ (i : d.cover.I₀) (_ : IsZero (M i)),
          Set.range (d.cover.f i) := by
        ext y
        constructor
        · intro hy
          obtain ⟨i, z, rfl⟩ := d.cover.exists_eq y
          have hz : IsZero (M i) := by
            by_contra hn
            exact hy ((hvalue i z).mpr hn)
          exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hz, ⟨z, rfl⟩⟩⟩
        · intro hy
          simp only [Set.mem_iUnion, Set.mem_range] at hy
          obtain ⟨i, hi, z, rfl⟩ := hy
          exact fun hz ↦ (hvalue i z).mp hz hi
      have hcl : IsClopen A := by
        constructor
        · rw [← isOpen_compl_iff, hneg]
          exact isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ hrange i
        · rw [hpos]
          exact isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ hrange i
      let := S.isImmersion k
      let : SpectralSpace X := {}
      have hc := constructible_image_clopen (S.immersion k).isEmbedding
        (by rw [S.range_immersion k]; exact hSc k) hcl
      simpa only [A, Set.image_preimage_eq_range_inter, S.range_immersion k,
        Set.inter_comm] using hc
    have heq : etaleSheafSupport F =
        ⋃ k : Fin S.n, etaleSheafSupport F ∩ S.stratum k := by
      rw [← Set.inter_iUnion, S.iUnion_stratum_eq_univ, Set.inter_univ]
    rw [heq]
    exact Topology.IsConstructible.iUnion hpart

end AlgebraicGeometry.Scheme
