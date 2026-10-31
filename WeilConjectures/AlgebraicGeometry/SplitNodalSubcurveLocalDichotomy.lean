/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import WeilConjectures.ZetaSeries

import WeilConjectures.AlgebraicGeometry.SplitNodalBoundaryLocalRings
import WeilConjectures.AlgebraicGeometry.RegularSeparableResidueSmooth
import WeilConjectures.PointCount
import WeilConjectures.AlgebraicGeometry.ComplementaryPureSubcurveComponents
import WeilConjectures.TraceFormula.ReducedSchemeImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The local branch dichotomy for a pure subcurve

Source: Stacks Project, Curves, Tag 0E38, the local component and completed-branch argument.
(blueprint: lem-trf-split-nodal-subcurve-local-dichotomy).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

private theorem split_nodal_boundary_branch
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    (hX : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = 1)
    (i : Y ⟶ X) [IsClosedImmersion i] [IsReduced Y]
    (hY : ∀ C ∈ irreducibleComponents Y, topologicalKrullDim C = 1)
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hboundary : i y ∈ Set.range (Scheme.openComplementOfIsClosedImmersion i).ι.imageι)
    (hseparable : @Algebra.IsSeparable k (X.residueField (i y)) _ _
      (f.residueFieldAlgebraMap (i y)).toAlgebra)
    (hcompletion : Nonempty
      (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk (i y)))
        (X.presheaf.stalk (i y)) ≃+*
        (MvPowerSeries (Fin 2) (X.residueField (i y)) ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2)
            (X.residueField (i y))) * MvPowerSeries.X 1}))) :
    (∃ U : Y.Opens, y ∈ U ∧ Smooth (U.ι ≫ i ≫ f)) ∧
      ∀ t : pullback (C := Scheme.{u}) i
          (Scheme.openComplementOfIsClosedImmersion i).ι.imageι,
        pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t = y →
        IsField ((pullback (C := Scheme.{u}) i
          (Scheme.openComplementOfIsClosedImmersion i).ι.imageι).presheaf.stalk t) := by
  obtain ⟨hregular, hfield⟩ := split_nodal_boundary_local_rings f hX i hY y hy
    hboundary hcompletion
  have := hregular
  refine ⟨regular_separable_residue_smooth (i ≫ f) y ?_, hfield⟩
  have := i.isIso_residueFieldMap y
  let := (f.residueFieldAlgebraMap (i y)).toAlgebra
  let := ((i ≫ f).residueFieldAlgebraMap y).toAlgebra
  let e : X.residueField (i y) ≃ₐ[k] Y.residueField y :=
    { (asIso (i.residueFieldMap y)).commRingCatIsoToRingEquiv with
      commutes' a := by
        change _ = (i ≫ f).residueFieldAlgebraMap y a
        rw [Scheme.Hom.residueFieldAlgebraMap_comp]
        rfl }
  have := hseparable
  exact AlgEquiv.Algebra.isSeparable e


private theorem agreement_of_open_range
    {X Y : Scheme.{u}} [IsReduced X] (i : Y ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) (hU : (U : Set X) ⊆ Set.range i) (y : Y) (hy : i y ∈ U) :
    IsIso (i.stalkMap y) := by
  have : Surjective (i ∣_ U) := ⟨fun z ↦ by
    obtain ⟨w, hw⟩ := hU z.property
    refine ⟨⟨w, by change i w ∈ U; rw [hw]; exact z.property⟩, ?_⟩
    apply Subtype.ext
    simpa only [morphismRestrict_base_coe] using hw⟩
  have : IsIso (i ∣_ U) := isIso_of_isClosedImmersion_of_surjective (i ∣_ U)
  let z : i ⁻¹ᵁ U := ⟨y, hy⟩
  have : IsIso (((i ∣_ U) ≫ U.ι).stalkMap z) := inferInstance
  rw [morphismRestrict_ι, Scheme.Hom.stalkMap_comp] at this
  have hcomp : IsIso (i.stalkMap y ≫ (i ⁻¹ᵁ U).ι.stalkMap z) := this
  exact IsIso.of_isIso_comp_right (i.stalkMap y) ((i ⁻¹ᵁ U).ι.stalkMap z)

private theorem open_range_outside_complement
    {X Y : Scheme.{u}} [IsReduced X] (i : Y ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) (hU : (U : Set X) ⊆ Set.range i) :
    ∀ x ∈ U, x ∉ Set.range (Scheme.openComplementOfIsClosedImmersion i).ι.imageι := by
  let V := Scheme.openComplementOfIsClosedImmersion i
  have him := schemeTheoreticImage_reduced V X V.ι
  have hr : Set.range V.ι.imageι = closure ((Set.range i)ᶜ) := by
    rw [him.2.2.2.1, Scheme.Opens.range_ι]
    rfl
  intro x hx
  rw [hr]
  intro hc
  have hsub : closure ((Set.range i)ᶜ) ⊆ (U : Set X)ᶜ :=
    closure_minimal (fun z hz hzU ↦ hz (hU hzU)) U.isOpen.isClosed_compl
  exact hsub hc hx

private theorem smooth_ambient_agreement
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    (hX : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = 1)
    (i : Y ⟶ X) [IsClosedImmersion i] [IsReduced Y]
    (hY : ∀ C ∈ irreducibleComponents Y, topologicalKrullDim C = 1)
    (y : Y) (hsm : ∃ U : X.Opens, i y ∈ U ∧ Smooth (U.ι ≫ f)) :
    IsIso (i.stalkMap y) ∧
      (∃ U : Y.Opens, y ∈ U ∧ Smooth (U.ι ≫ i ≫ f)) ∧
      i y ∉ Set.range (Scheme.openComplementOfIsClosedImmersion i).ι.imageι := by
  obtain ⟨U, hyU, hsm⟩ := hsm
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  let x : U := ⟨i y, hyU⟩
  let V : U.toScheme.Opens := ⟨connectedComponent x, isOpen_connectedComponent⟩
  have : ConnectedSpace V := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have : Smooth (V.ι ≫ U.ι ≫ f) := inferInstance
  have : IrreducibleSpace V := irreducibleSpace_of_isDomain_stalk V (fun z ↦ by
    have := Smooth.isRegularLocalRing_stalk (V.ι ≫ U.ι ≫ f) z
    infer_instance)
  let W := U.ι ''ᵁ V
  have hW : IsOpenImmersion (V.ι ≫ U.ι) := inferInstance
  have hWr : Set.range (V.ι ≫ U.ι) = (W : Set X) := by
    simp [W, Scheme.Hom.comp_base, Set.range_comp]
  have : IrreducibleSpace W := by
    have e := (V.ι ≫ U.ι).isOpenEmbedding.toHomeomorph
    exact ((e.trans (Homeomorph.setCongr hWr)).irreducibleSpace_iff).mp inferInstance
  have hyW : i y ∈ W := ⟨x, mem_connectedComponent, rfl⟩
  let Z := (Scheme.openComplementOfIsClosedImmersion i).ι.image
  let j : Z ⟶ X := (Scheme.openComplementOfIsClosedImmersion i).ι.imageι
  have him := schemeTheoreticImage_reduced _ X
    (Scheme.openComplementOfIsClosedImmersion i).ι
  have : IsReduced Z := him.2.1
  have hrj : Set.range j = closure ((Set.range i)ᶜ) := by
    rw [him.2.2.2.1, Scheme.Opens.range_ι]
    rfl
  obtain ⟨I, hI, hi, _, _⟩ := complementary_pure_subcurve_components hX i hY j hrj
  obtain ⟨C, hCI, hyC⟩ := Set.mem_sUnion.mp (hi ▸ Set.mem_range_self y)
  have hCW : (Subtype.val : W → X) ⁻¹' C ∈ irreducibleComponents W :=
    preimage_mem_irreducibleComponents (hI hCI) W.isOpenEmbedding' ⟨i y, hyC, ⟨⟨i y, hyW⟩, rfl⟩⟩
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hCW
  have hWi : (W : Set X) ⊆ Set.range i := by
    intro z hz
    rw [hi]
    apply Set.mem_sUnion_of_mem (t := C) ?_ hCI
    have := Set.eq_univ_iff_forall.mp hCW (⟨z, hz⟩ : W)
    exact this
  have hiso := agreement_of_open_range i W hWi y hyW
  refine ⟨hiso, ?_, open_range_outside_complement i W hWi (i y) hyW⟩
  have hWsm : Smooth (W.ι ≫ f) := by
    have hcomp : Smooth ((V.ι ≫ U.ι) ≫ f) := by
      simpa only [Category.assoc] using
        (inferInstance : Smooth (V.ι ≫ U.ι ≫ f))
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (V.ι ≫ U.ι) W.ι
      (by simpa only [Scheme.Opens.range_ι] using hWr), Category.assoc]
    infer_instance
  have : Surjective (i ∣_ W) := ⟨fun z ↦ by
    obtain ⟨w, hw⟩ := hWi z.property
    refine ⟨⟨w, by change i w ∈ W; rw [hw]; exact z.property⟩, ?_⟩
    apply Subtype.ext
    simpa only [morphismRestrict_base_coe] using hw⟩
  have : IsIso (i ∣_ W) := isIso_of_isClosedImmersion_of_surjective (i ∣_ W)
  refine ⟨i ⁻¹ᵁ W, hyW, ?_⟩
  rw [← Category.assoc, ← morphismRestrict_ι i W, Category.assoc]
  infer_instance

/-- At a closed point of a reduced pure subcurve of a curve which is smooth or split nodal,
either the subcurve agrees locally with the ambient curve and misses its complementary
closure, or it selects one of two branches, is smooth, and has a field intersection stalk.

Source: Stacks Project, Curves, Tag 0E38, proof paragraphs 1--3.
(blueprint: lem-trf-split-nodal-subcurve-local-dichotomy).

Proof: The subcurve and the complementary reduced closure are unions of complementary
subsets of the ambient irreducible components. The local ring of a smooth ambient point
is a regular local domain, so exactly one component passes through the point; it belongs
to the subcurve. Removing the finitely many other components identifies the two reduced
schemes near the point and excludes the complementary closure. The same conclusion holds
at a node when all incident components belong to the subcurve, including a self-node.
For the remaining case, the nodal completed local ring F[[u,v]]/(uv) has precisely the
primes (u), (v), (u,v): its axis quotients are dimension-one local domains. Faithful
flatness of completion therefore bounds the number of incident components by two. Their
minimal primes p,q are distinct and nonzero. The completions of A/p and A/q are reduced
of dimension one by normalization of local algebraic curves. Quotient compatibility for
completion makes pC,qC radical. The prime list, dimension, and faithfully flat contraction
identify them with the two axis ideals. Their sum is the completed maximal ideal, hence
p+q is the original maximal ideal by contraction. The intersection stalk is consequently
F. The completed subcurve stalk is F[[u]], which is regular, and regularity descends from
completion. Its residue field is finite separable over k, so the finite-type separable
residue criterion gives a smooth neighbourhood in the subcurve. This case cannot occur
at a smooth ambient point. -/
theorem split_nodal_subcurve_local_dichotomy
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    (hX : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = 1)
    (i : Y ⟶ X) [IsClosedImmersion i] [IsReduced Y]
    (hY : ∀ C ∈ irreducibleComponents Y, topologicalKrullDim C = 1)
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hlocal : (∃ U : X.Opens, i y ∈ U ∧ Smooth (U.ι ≫ f)) ∨
      ((f.residueFieldAlgebraMap (i y)).Finite ∧
        @Algebra.IsSeparable k (X.residueField (i y)) _ _
          (f.residueFieldAlgebraMap (i y)).toAlgebra ∧
        Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk (i y)))
          (X.presheaf.stalk (i y)) ≃+*
          (MvPowerSeries (Fin 2) (X.residueField (i y)) ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2)
              (X.residueField (i y))) * MvPowerSeries.X 1})))) :
    (IsIso (i.stalkMap y) ∧
      ((∃ U : X.Opens, i y ∈ U ∧ Smooth (U.ι ≫ f)) →
        ∃ U : Y.Opens, y ∈ U ∧ Smooth (U.ι ≫ i ≫ f)) ∧
      i y ∉ Set.range (Scheme.openComplementOfIsClosedImmersion i).ι.imageι) ∨
    ((¬ ∃ U : X.Opens, i y ∈ U ∧ Smooth (U.ι ≫ f)) ∧
      (∃ U : Y.Opens, y ∈ U ∧ Smooth (U.ι ≫ i ≫ f)) ∧
      ∀ t : pullback (C := Scheme.{u}) i
          (Scheme.openComplementOfIsClosedImmersion i).ι.imageι,
        pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t = y →
        IsField ((pullback (C := Scheme.{u}) i
          (Scheme.openComplementOfIsClosedImmersion i).ι.imageι).presheaf.stalk t)) := by
  classical
  by_cases hsm : ∃ U : X.Opens, i y ∈ U ∧ Smooth (U.ι ≫ f)
  · obtain ⟨hiso, hs, hout⟩ := smooth_ambient_agreement f hX i hY y hsm
    exact Or.inl ⟨hiso, fun _ ↦ hs, hout⟩
  by_cases hb : i y ∈ Set.range (Scheme.openComplementOfIsClosedImmersion i).ι.imageι
  · obtain ⟨_, hsep, he⟩ := hlocal.resolve_left hsm
    exact Or.inr ⟨hsm, split_nodal_boundary_branch f hX i hY y hy hb hsep he⟩
  · let j := (Scheme.openComplementOfIsClosedImmersion i).ι.imageι
    let U : X.Opens := ⟨(Set.range j)ᶜ, j.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have hU : (U : Set X) ⊆ Set.range i := by
      intro x hx
      by_contra hnot
      apply hx
      have him := schemeTheoreticImage_reduced _ X
        (Scheme.openComplementOfIsClosedImmersion i).ι
      change x ∈ Set.range (Scheme.openComplementOfIsClosedImmersion i).ι.imageι
      rw [him.2.2.2.1, Scheme.Opens.range_ι]
      exact subset_closure hnot
    exact Or.inl ⟨agreement_of_open_range i U hU y hb, fun h ↦ False.elim (hsm h), hb⟩

end AlgebraicGeometry
