/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
import Sheaf.AlgebraicGeometry.ComplementaryPureSubcurveComponents
import Sheaf.TraceFormula.ReducedSchemeImage
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.Topology.JacobsonSpace

/-!
# Finiteness of the boundary of a pure subcurve

Source: Stacks Project, Curves, Tag 0E38, first paragraph.
(blueprint: lem-trf-complementary-pure-subcurve-boundary-finite).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

private theorem finite_inter_distinct_curve_components
    (X : Scheme.{u}) [IsNoetherian X]
    (hX : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = 1)
    {C D : Set X} (hC : C ∈ irreducibleComponents X)
    (hD : D ∈ irreducibleComponents X) (hne : C ≠ D) : (C ∩ D).Finite := by
  let V : Set C := (Subtype.val : C → X) ⁻¹' Dᶜ
  have hV : IsOpen V :=
    (isClosed_of_mem_irreducibleComponents D hD).isOpen_compl.preimage continuous_subtype_val
  have hVne : V.Nonempty := by
    by_contra h
    have hCD : C ⊆ D := by
      intro x hx
      by_contra hnot
      exact h ⟨⟨x, hx⟩, hnot⟩
    exact hne (hC.eq_of_ge hD.1 hCD).symm
  have : IrreducibleSpace C := Subtype.irreducibleSpace hC.1
  have : QuasiSober C :=
    (isClosed_of_mem_irreducibleComponents C hC).isClosedEmbedding_subtypeVal.quasiSober
  have hfin := hV.finite_compl_of_topologicalKrullDim_le_one (by rw [hX C hC]) hVne
  convert hfin.image (Subtype.val : C → X) using 1
  ext x
  simp [V]

/-- The boundary between complementary reduced pure subcurves is finite and discrete, and
its points are closed in the ambient Jacobson curve.

Source: Stacks Project, Curves, Tag 0E38, first paragraph and its finite-type specialization.
(blueprint: lem-trf-complementary-pure-subcurve-boundary-finite).

Proof: The reduced complementary image and the subcurve are unions of complementary subsets
of the finite set of components. For distinct components C,D, the complement of C intersect D
in C is nonempty and open; its complement is finite since C is irreducible Noetherian of dimension
one. Thus the boundary is a finite union of finite pairwise component intersections. It is closed
in the ambient scheme. A finite closed subset of a Jacobson space has closed points. The closed
immersion of the boundary into the ambient scheme is injective, so its source is finite and T1,
and consequently discrete. This includes either subcurve being empty. -/
theorem complementary_pure_subcurve_boundary_finite
    {X Y : Scheme.{u}} [IsReduced X] [IsNoetherian X] [JacobsonSpace X]
    (hX : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = 1)
    (i : Y ⟶ X) [IsClosedImmersion i] [IsReduced Y]
    (hY : ∀ C ∈ irreducibleComponents Y, topologicalKrullDim C = 1) :
    let j := (Scheme.openComplementOfIsClosedImmersion i).ι.imageι
    Finite (pullback (C := Scheme.{u}) i j) ∧ DiscreteTopology (pullback (C := Scheme.{u}) i j) ∧
      ∀ t : pullback (C := Scheme.{u}) i j, IsClosed ({i (pullback.fst i j t)} : Set X) := by
  classical
  dsimp only
  let V := Scheme.openComplementOfIsClosedImmersion i
  let j := V.ι.imageι
  have him := schemeTheoreticImage_reduced V X V.ι
  have : IsReduced V.ι.image := him.2.1
  have hrj : Set.range j = closure ((Set.range i)ᶜ) := by
    rw [him.2.2.2.1, Scheme.Opens.range_ι]
    rfl
  obtain ⟨I, hI, hi, hj, _⟩ := complementary_pure_subcurve_components hX i hY j hrj
  let B : Set X := Set.range i ∩ Set.range j
  have hBfin : B.Finite := by
    have hIfin := (finite_irreducibleComponents_of_isNoetherian (X := X)).subset hI
    have hJfin := (finite_irreducibleComponents_of_isNoetherian (X := X)).sdiff (t := I)
    have hcover : B ⊆ ⋃ C ∈ I, ⋃ D ∈ irreducibleComponents X \ I, C ∩ D := by
      intro x hx
      obtain ⟨C, hCI, hxC⟩ := Set.mem_sUnion.mp (hi ▸ hx.1)
      obtain ⟨D, hDJ, hxD⟩ := Set.mem_sUnion.mp (hj ▸ hx.2)
      exact Set.mem_iUnion.mpr ⟨C, Set.mem_iUnion.mpr ⟨hCI,
        Set.mem_iUnion.mpr ⟨D, Set.mem_iUnion.mpr ⟨hDJ, hxC, hxD⟩⟩⟩⟩
    apply Set.Finite.subset (hIfin.biUnion fun C hCI ↦ hJfin.biUnion fun D hDJ ↦ ?_) hcover
    exact finite_inter_distinct_curve_components X hX (hI hCI) hDJ.1
      (fun e ↦ hDJ.2 (e ▸ hCI))
  have hBclosed : IsClosed B :=
    i.isClosedEmbedding.isClosed_range.inter j.isClosedEmbedding.isClosed_range
  let b : pullback i j ⟶ X := pullback.fst i j ≫ i
  have hrb : Set.range b = B := Scheme.Pullback.range_fst_comp i j
  have hclosed (t : pullback (C := Scheme.{u}) i j) : IsClosed ({b t} : Set X) :=
    isClosed_singleton_of_mem_of_finite hBclosed hBfin (hrb ▸ Set.mem_range_self t)
  have hfin : Finite (pullback (C := Scheme.{u}) i j) := by
    have : Finite B := hBfin.to_subtype
    exact Finite.of_injective (fun t : pullback (C := Scheme.{u}) i j ↦ (⟨b t,
      hrb ▸ Set.mem_range_self t⟩ : B))
      (fun _ _ h ↦ b.isClosedEmbedding.injective (congrArg Subtype.val h))
  have : T1Space (pullback (C := Scheme.{u}) i j) := ⟨fun t ↦ by
    have h := (hclosed t).preimage b.continuous
    have heq : b ⁻¹' {b t} = {t} := by
      ext z
      exact b.isClosedEmbedding.injective.eq_iff
    rwa [heq] at h⟩
  exact ⟨hfin, inferInstance, hclosed⟩

end AlgebraicGeometry
