/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Construction
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Boundary data of an open subcurve

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over a finite
field, `U₀` geometrically connected. This file constructs a `AlgebraicGeometry.BoundaryDatum` for
`j` (`AlgebraicGeometry.WeilGroup.boundaryDatumOfPath`), on top of the restriction of Weil groups
`AlgebraicGeometry.WeilGroup.restrictionOfPath`.

The boundary `C₀ \ U₀` is finite and consists of closed points, since `C₀` is irreducible of
dimension at most one. The genuine inertia groups need the henselization of `C₀` at a boundary
point, which is not available; the structure only pins them down jointly, through
`ker_restrict_eq`, and here every inertia group is taken to be the whole kernel of the
restriction `W(U₀) → W(C₀)`. A residue Frobenius lift at a boundary point `s` is a preimage of
the local Frobenius at `s` under the (surjective) restriction.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  [GeometricallyConnected p] [ConnectedSpace C] [Smooth p] {pU : U ⟶ Spec (.of K)} [IsCurve pU]
  [GeometricallyConnected pU] [ConnectedSpace U] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]

section Boundary

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
include p in
lemma irreducibleSpace_of_smooth : IrreducibleSpace C := by
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := IsRegular.of_smooth p
  exact IsRegular.irreducibleSpace C

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
include p in
/-- The boundary of a nonempty open of a smooth connected curve is finite. -/
lemma finite_boundary : (Set.range j.base)ᶜ.Finite := by
  have := irreducibleSpace_of_smooth (p := p)
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian C := {}
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  exact j.isOpenEmbedding.isOpen_range.finite_compl_of_topologicalKrullDim_le_one
    (IsCurve.krullDim_le_one (f := p)) ⟨_, u, rfl⟩

omit [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU] [GeometricallyConnected pU] in
include p in
/-- The boundary points of a nonempty open of a smooth connected curve are closed points, with
finite residue fields. -/
lemma boundary_subset_finitePoints : (Set.range j.base)ᶜ ⊆ C.finitePoints := by
  intro z hz
  have := irreducibleSpace_of_smooth (p := p)
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  exact p.finite_residueField_of_isClosed
    (j.isOpenEmbedding.isOpen_range.isClosed_singleton_of_mem_compl
      (IsCurve.krullDim_le_one (f := p)) ⟨_, u, rfl⟩ hz)

end Boundary

variable (hj : j ≫ p = pU) {sU : Spec (.of (AlgebraicClosure K)) ⟶ U}
  {sC : Spec (.of (AlgebraicClosure K)) ⟶ C} (τ : fiber (sU ≫ j) ≅ fiber sC)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]
  (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC] [CompactSpace GC]
  [∀ P, MulAction GC ((fiber sC).obj P)] [IsFundamentalGroup (fiber sC) GC]

include hj

lemma isClosed_ker_restrictionHom :
    IsClosed ((restrictionHom j hj τ GU GC).ker : Set (weilGroup pU sU GU)) := by
  have : T2Space GC := (toAutHomeo (fiber sC) GC).isEmbedding.t2Space
  have hc : Continuous (restrictionHom j hj τ GU GC) :=
    (restrictionOfPath j hj τ GU GC).continuous_restrict
  exact (isClosed_singleton (x := (1 : weilGroup p sC GC))).preimage hc

omit [IsCurve p] [GeometricallyConnected p] [Smooth p] [IsCurve pU] [GeometricallyConnected pU]
  [Nonempty U] in
lemma restrictionHom_injective_of_isEmpty (h : IsEmpty ↥((Set.range j.base)ᶜ)) :
    Function.Injective (restrictionHom j hj τ GU GC) := by
  have : Surjective j := ⟨fun x ↦ by
    by_contra hx
    exact h.false ⟨x, hx⟩⟩
  have : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).2 ⟨inferInstance, inferInstance⟩
  have hinj := fundamentalGroupMap_injective (pullbackFiberIso j sU ≪≫ τ) GC GU
  intro w w' hww'
  have := congrArg (fun w : weilGroup p sC GC ↦ (w : GC × Multiplicative ℤ)) hww'
  simp only [restrictionHom_apply, Prod.mk.injEq] at this
  exact Subtype.ext (Prod.ext (hinj this.1) this.2)

lemma ker_restrictionHom_eq :
    (restrictionHom j hj τ GU GC).ker = (Subgroup.normalClosure
      (⋃ _ : ↥((Set.range j.base)ᶜ),
        ((restrictionHom j hj τ GU GC).ker : Set _))).topologicalClosure := by
  have hcl := isClosed_ker_restrictionHom j hj τ GU GC
  rcases isEmpty_or_nonempty ↥((Set.range j.base)ᶜ) with h | h
  · rw [Set.iUnion_of_empty, Subgroup.normalClosure_empty,
      (MonoidHom.ker_eq_bot_iff _).2 (restrictionHom_injective_of_isEmpty j hj τ GU GC h)]
    have : T2Space GU := (toAutHomeo (fiber sU) GU).isEmbedding.t2Space
    refine le_antisymm bot_le (Subgroup.topologicalClosure_minimal _ le_rfl ?_)
    exact isClosed_singleton
  · rw [Set.iUnion_const, Subgroup.normalClosure_eq_self]
    exact le_antisymm (Subgroup.le_topologicalClosure _)
      (Subgroup.topologicalClosure_minimal _ le_rfl hcl)

/-- A residue Frobenius lift at a boundary point: a preimage under the restriction of the local
Frobenius at that point. -/
noncomputable def residueFrobenius (z : ↥((Set.range j.base)ᶜ)) : weilGroup pU sU GU :=
  (restrictionHom_surjective j hj τ GU GC
    (weilFrobenius p sC GC ⟨z.1, boundary_subset_finitePoints (p := p) j z.2⟩)).choose

omit [GeometricallyConnected p] [IsCurve pU] in
lemma restrictionHom_residueFrobenius (z : ↥((Set.range j.base)ᶜ)) :
    restrictionHom j hj τ GU GC (residueFrobenius j hj τ GU GC z) =
      weilFrobenius p sC GC ⟨z.1, boundary_subset_finitePoints (p := p) j z.2⟩ :=
  (restrictionHom_surjective j hj τ GU GC _).choose_spec

/-- **A boundary datum for a nonempty open of a smooth curve**: the restriction of Weil groups
`AlgebraicGeometry.WeilGroup.restrictionOfPath`, with every inertia group the kernel of the
restriction and residue Frobenius lifts chosen as preimages of the local Frobenius elements.
(blueprint `sk-d-real-boundary`) -/
noncomputable def boundaryDatumOfPath :
    BoundaryDatum j (ofFundamentalGroup pU sU GU) (ofFundamentalGroup p sC GC) where
  toRestriction := restrictionOfPath j hj τ GU GC
  finite_boundary := finite_boundary (p := p) j
  boundary_subset_finitePoints := boundary_subset_finitePoints (p := p) j
  inertia _ := (restrictionHom j hj τ GU GC).ker
  inertia_le _ w hw := by
    have h := congrArg (fun w : weilGroup p sC GC ↦ (w : GC × Multiplicative ℤ).2) hw
    exact h
  ker_restrict_eq := ker_restrictionHom_eq j hj τ GU GC
  residueFrobenius := residueFrobenius j hj τ GU GC
  deg_residueFrobenius z :=
    congrArg (fun w : weilGroup p sC GC ↦ (w : GC × Multiplicative ℤ).2)
      (restrictionHom_residueFrobenius j hj τ GU GC z)
  restrict_residueFrobenius z := by
    change IsConj _ (restrictionHom j hj τ GU GC _)
    rw [restrictionHom_residueFrobenius]
    exact IsConj.refl _
  normalizes_inertia _ := Subgroup.Normal.map_conj_eq _ _

omit hj in
/-- A nonempty open `j : U₀ ⟶ C₀` of a smooth geometrically connected curve over a finite field,
itself geometrically connected, has a boundary datum. -/
theorem BoundaryDatum.nonempty (hj : j ≫ p = pU) :
    ∃ (WU : WeilGroup pU) (WC : WeilGroup p), Nonempty (BoundaryDatum j WU WC) := by
  obtain ⟨sU⟩ := pU.nonempty_algebraicClosure_point
  obtain ⟨sC⟩ := p.nonempty_algebraicClosure_point
  obtain ⟨GU, _, _⟩ := exists_isFundamentalGroup sU
  obtain ⟨GC, _, _⟩ := exists_isFundamentalGroup sC
  obtain ⟨τ⟩ := nonempty_iso_of_fiberFunctor (fiber (sU ≫ j)) (fiber sC)
  exact ⟨_, _, ⟨boundaryDatumOfPath j hj τ GU GC⟩⟩

end AlgebraicGeometry.WeilGroup
