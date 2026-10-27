/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import Mathlib.Topology.Connected.Clopen
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import WeilConjectures.AlgebraicGeometry.UnramifiedOverFieldDiscrete
import Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular

/-! # Base change and the unramified singular subscheme of a nodal family

Source: Stacks Project, Tags 0C59 and 0C5B (blueprint:
`lem-trf-projective-nodal-family-geometry`).

## Main statement

* `projective_nodal_family_geometry`: the smooth locus of a projective flat nodal
  family is open and its canonical singular closed subscheme is unramified with
  finite fibres, with the stated base-change properties.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical map `S ×_Y Y₁ ⟶ X ×_Y Y₁` induced by `i : S ⟶ X`.
Source: Stacks Tag 0C5B, base change of the singular closed subscheme
(blueprint: lem-trf-projective-nodal-family-geometry). -/
noncomputable def nodalSingularBaseChangeMap
    {S X Y Y₁ : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ X) (g : Y₁ ⟶ Y) :
    pullback (i ≫ f) g ⟶ pullback f g :=
  pullback.map (i ≫ f) g f g i (𝟙 Y₁) (𝟙 Y)
    (Category.comp_id (i ≫ f))
    ((Category.comp_id g).trans (Category.id_comp g).symm)

private theorem pure_dimension_one_of_connected
    (C : Scheme.{u}) [IsNoetherian C] [ConnectedSpace C]
    (hdim : topologicalKrullDim C = 1) : C.IsPureDimension 1 := by
  classical
  intro Z hZ
  apply le_antisymm
  · exact (topologicalKrullDim_subspace_le C Z).trans hdim.le
  · by_contra h
    have hzero : topologicalKrullDim Z ≤ 0 := by
      have hlt : topologicalKrullDim Z < (0 : WithBot ℕ∞) + 1 := by
        simpa using lt_of_not_ge h
      exact ENat.WithBot.lt_add_one_iff.mp hlt
    have hclosed := isClosed_of_mem_irreducibleComponents Z hZ
    have : IrreducibleSpace Z := isIrreducible_iff_irreducibleSpace.mp hZ.1
    have hsub : Subsingleton Z := by
      constructor
      intro x y
      have key (z : Z) : closure {z} = (Set.univ : Set Z) := by
        let A : TopologicalSpace.IrreducibleCloseds Z :=
          ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
        let B : TopologicalSpace.IrreducibleCloseds Z :=
          ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩
        have he := Order.krullDim_nonpos_iff_forall_isMax.mp hzero A
        exact congrArg (fun W : TopologicalSpace.IrreducibleCloseds Z ↦ (W : Set Z))
          (he.eq_of_le (show A ≤ B from Set.subset_univ _))
      exact (inseparable_iff_closure_eq.mpr ((key x).trans (key y).symm)).eq
    have hclopen : IsClopen Z := by
      refine ⟨hclosed, ?_⟩
      obtain ⟨U, hU, hUne, hUZ⟩ :=
        TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
      have hZU : Z ⊆ U := by
        obtain ⟨x, hx⟩ := hUne
        intro y hy
        have he : y = x := congrArg Subtype.val (hsub.elim ⟨y, hy⟩ ⟨x, hUZ hx⟩)
        exact he ▸ hx
      exact (Set.Subset.antisymm hUZ hZU) ▸ hU
    have huniv := hclopen.eq_univ hZ.1.nonempty
    have : Subsingleton C := by
      constructor
      intro x y
      have hx : x ∈ Z := huniv ▸ Set.mem_univ x
      have hy : y ∈ Z := huniv ▸ Set.mem_univ y
      exact congrArg Subtype.val (hsub.elim ⟨x, hx⟩ ⟨y, hy⟩)
    have hd := topologicalKrullDim_zero_of_discreteTopology C
    rw [hdim] at hd
    exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hd

private theorem nodal_point_of_iso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {C D : Scheme.{u}} (e : C ≅ D) (x : C)
    (hx : IsGeometricOrdinaryDoublePoint Ω D (e.hom x)) :
    IsGeometricOrdinaryDoublePoint Ω C x := by
  let r := (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
  obtain ⟨E, _⟩ := AdicCompletion.exists_ringEquiv
    (IsLocalRing.maximalIdeal (D.presheaf.stalk (e.hom x)))
    (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) r
    (IsLocalRing.map_ringEquiv_maximalIdeal r).symm
  exact ⟨E.symm.trans hx.some⟩

private theorem nodal_geometric_fibres_base_change
    {X Y Y₁ : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (hN : HasNodalGeometricFibres f) (g : Y₁ ⟶ Y) :
    HasNodalGeometricFibres (pullback.snd f g) := by
  intro Ω _ _ a
  let e := pullbackLeftPullbackSndIso f g a
  obtain ⟨hc, hd, hn⟩ := hN Ω (a ≫ g)
  refine ⟨e.hom.homeomorph.connectedSpace_iff.mpr hc, ?_, ?_⟩
  · exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).trans hd
  · intro x hx
    apply nodal_point_of_iso Ω e x
    apply hn
    intro hmem
    apply hx
    have hs := e.hom.preimage_smoothLocus_eq (pullback.snd f (a ≫ g))
    simp only [e, pullbackLeftPullbackSndIso_hom_snd] at hs
    change x ∈ (pullback.snd (pullback.snd f g) a).smoothLocus
    rw [← hs]
    exact hmem

/-- Projective nodal families have an unramified closed singular subscheme with finite
fibres, compatibly with every Noetherian base change.
Source: Stacks Tags 0C59 and 0C5B
(blueprint: lem-trf-projective-nodal-family-geometry).

Proof:
1. A connected Noetherian space of dimension one is pure of dimension one: a
   zero-dimensional irreducible component would be a singleton and open, hence the
   whole connected space. Apply `nodal_family_fitting_singular` and take its canonical
   first-Fitting closed subscheme.
2. The singular subscheme is quasi-compact over the base, since its inclusion is
   closed and the family is projective. Its scheme-theoretic fibres are compact and,
   by unramifiedness, discrete. Thus they are finite; the fibre homeomorphism gives
   finite underlying fibres.
3. Projectivity, flatness and local finite presentation survive base change. Pullback
   pasting transports connectedness and dimension by a homeomorphism and transports
   the ordinary-double-point condition through the induced stalk and completion
   isomorphisms.
4. The fitting theorem's isomorphism over the base-changed total space identifies the
   pulled-back singular inclusion with the new fitting inclusion. This proves closed
   immersion and the support identity. The pullback-map range formula then gives the
   smooth-locus equality by taking complements. Unramifiedness survives base change.
-/
theorem projective_nodal_family_geometry
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian Y] [IsHProjective f] [Flat f]
    [LocallyOfFinitePresentation f] (hN : HasNodalGeometricFibres f) :
    IsOpen (f.smoothLocus : Set X) ∧
      ∃ (S : Scheme.{u}) (i : S ⟶ X),
        IsClosedImmersion i ∧
        (LocallyOfFiniteType (i ≫ f) ∧ IsOpenImmersion (pullback.diagonal (i ≫ f))) ∧
        Set.range i = (f.smoothLocus : Set X)ᶜ ∧
        (∀ y : Y, Set.Finite ((i ≫ f) ⁻¹' {y})) ∧
        ∀ (Y₁ : Scheme.{u}) (g : Y₁ ⟶ Y) [IsNoetherian Y₁],
          IsHProjective (pullback.snd f g) ∧ Flat (pullback.snd f g) ∧
          LocallyOfFinitePresentation (pullback.snd f g) ∧
          HasNodalGeometricFibres (pullback.snd f g) ∧
          (pullback.fst f g) ⁻¹ᵁ f.smoothLocus = (pullback.snd f g).smoothLocus ∧
          IsClosedImmersion (nodalSingularBaseChangeMap f i g) ∧
          (LocallyOfFiniteType (pullback.snd (i ≫ f) g) ∧
            IsOpenImmersion (pullback.diagonal (pullback.snd (i ≫ f) g))) ∧
          Set.range (nodalSingularBaseChangeMap f i g) =
            ((pullback.snd f g).smoothLocus : Set (pullback f g : Scheme.{u}))ᶜ := by
  classical
  have hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Y), Nonempty ↥(pullback f g) →
        (pullback f g).IsPureDimension 1 ∧
          ∀ x : ↥(pullback f g), x ∉ (pullback.snd f g).smoothLocus →
            IsGeometricOrdinaryDoublePoint Ω (pullback f g) x := by
    intro Ω _ _ g _
    obtain ⟨hc, hd, hn⟩ := hN Ω g
    have : ConnectedSpace ↥(pullback f g) := hc
    have : IsNoetherian (pullback f g) := by
      have := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g)
      have : CompactSpace ↥(pullback f g) :=
        HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)
          (f := pullback.snd f g) |>.mp inferInstance
      constructor
    exact ⟨pure_dimension_one_of_connected _ hd, hn⟩
  obtain ⟨hopen, hrange, hunr, hbc⟩ := nodal_family_fitting_singular f hgeom
  let i := Scheme.firstFittingSingularSubscheme f
  have : LocallyOfFiniteType (i ≫ f) := hunr.1
  have : IsOpenImmersion (pullback.diagonal (i ≫ f)) := hunr.2
  refine ⟨hopen, _, i, inferInstance, hunr, hrange, ?_, ?_⟩
  · intro y
    have hbase := unramified_baseChange_restrict_open (i ≫ f) hunr
      (Y.fromSpecResidueField y)
    have : LocallyOfFiniteType ((i ≫ f).fiberToSpecResidueField y) := hbase.1
    have : IsOpenImmersion
        (pullback.diagonal ((i ≫ f).fiberToSpecResidueField y)) := hbase.2.1
    have : DiscreteTopology ((i ≫ f).fiber y) :=
      discreteTopology_of_unramified_over_field ((i ≫ f).fiberToSpecResidueField y)
    have : Finite ((i ≫ f).fiber y) := finite_of_compact_of_discrete
    exact Set.finite_coe_iff.mp
      (Finite.of_equiv ((i ≫ f).fiber y) ((i ≫ f).fiberHomeo y).toEquiv)
  · intro Y₁ g _
    have : IsProjective f := IsHProjective.isProjective f
    have := projective_base_change f g
    have hN₁ := nodal_geometric_fibres_base_change f hN g
    obtain ⟨⟨e⟩, hrange₁⟩ := hbc Y₁ g
    have he : e.hom.left ≫ Scheme.firstFittingSingularSubscheme (pullback.snd f g) =
        nodalSingularBaseChangeMap f i g := Over.w e.hom
    have hi₁ : IsClosedImmersion (nodalSingularBaseChangeMap f i g) := by
      rw [← he]
      infer_instance
    have hr : Set.range (nodalSingularBaseChangeMap f i g) =
        ((pullback.snd f g).smoothLocus : Set ↥(pullback f g))ᶜ := by
      have hsur : Function.Surjective e.hom.left := e.hom.left.homeomorph.surjective
      rw [← he]
      calc
        _ = Set.range (Scheme.firstFittingSingularSubscheme (pullback.snd f g)) := by
          ext x
          constructor
          · rintro ⟨z, rfl⟩
            exact ⟨e.hom.left z, (Scheme.Hom.comp_apply _ _ _).symm⟩
          · rintro ⟨z, rfl⟩
            obtain ⟨w, rfl⟩ := hsur z
            exact ⟨w, Scheme.Hom.comp_apply _ _ _⟩
        _ = _ := hrange₁
    have hpre : (pullback.fst f g) ⁻¹ᵁ f.smoothLocus =
        (pullback.snd f g).smoothLocus := by
      have hm : Set.range (nodalSingularBaseChangeMap f i g) =
          (pullback.fst f g) ⁻¹' Set.range i := by
        dsimp [nodalSingularBaseChangeMap]
        rw [Scheme.Pullback.range_map]
        simp
      rw [hrange] at hm
      apply TopologicalSpace.Opens.ext
      exact compl_injective (by
        simpa only [Scheme.Hom.coe_preimage, Set.preimage_compl] using hm.symm.trans hr)
    have hbase := unramified_baseChange_restrict_open (i ≫ f) hunr g
    exact ⟨inferInstance, inferInstance, inferInstance, hN₁, hpre, hi₁,
      ⟨hbase.1, hbase.2.1⟩, hr⟩

end AlgebraicGeometry
