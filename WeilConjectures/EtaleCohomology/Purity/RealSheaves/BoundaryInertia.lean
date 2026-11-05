/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.BoundaryNeighbourhood
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ExtendOverInertia
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroupDense
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryConstruction
public import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Decomposition and inertia groups at the boundary points of an open subcurve

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over a finite
field, `U₀` geometrically connected, and `z` a boundary point. Fix a separable closure `Ω` of
the function field `k(C)`, so that `Spec Ω ⟶ U₀` is a geometric generic point, and a path from it
to the base point of `π₁(U₀)`; this gives `ρ : Gal(Ω / k(C)) → π₁(U₀)`.

An affine chart `W ∋ z` of `U₀ ∪ {z}` on which `z` is cut out by one section
(`AlgebraicGeometry.WeilGroup.BoundaryChart`) and a maximal ideal `Q` over `z` of the integral
closure `B` of `Γ(C, W)` in `Ω` are a compatible system of points over `z` on the normalizations
of `C₀` in the covers of `U₀`. The decomposition group `D_z` is the stabiliser of `Q`, the inertia
group `I_z` the subgroup acting trivially on `B ⧸ Q`, and `D_z / I_z` is the automorphism group of
`(B ⧸ Q) / κ(z)` (`Ideal.Quotient.stabilizerQuotientInertiaEquivIntegralClosure`), `B ⧸ Q` being an
algebraic closure of `κ(z)`.

The image of `I_z` in `π₁(U₀)` (`AlgebraicGeometry.WeilGroup.inertiaGroup`) is the inertia group at
`z`:

- it acts trivially on the covers extending over `z`
  (`AlgebraicGeometry.WeilGroup.inertiaGroup_le_localKernel`);
- conversely the kernel of `π₁(U₀) → π₁(U₀ ∪ {z})` is the closed normal subgroup it generates
  (`AlgebraicGeometry.WeilGroup.localKernel_le_topologicalClosure_normalClosure`), since a cover on
  which `I_z` acts trivially extends over `z`.

A lift in `D_z` of the inverse arithmetic Frobenius of `κ(z)` restricts to a Frobenius element at
`z` in `π₁(C₀)`
(`BoundaryChart.exists_mem_stabilizer_isFrobeniusElement_restrictionMap`).
Together with the density of the Weil group in `π₁(U₀)`, this builds the boundary datum of
`d-real-boundary` (`AlgebraicGeometry.WeilGroup.boundaryDatum`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory
open scoped Pointwise

namespace AlgebraicGeometry.WeilGroup

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  [GeometricallyConnected p] [ConnectedSpace C] [Smooth p] {pU : U ⟶ Spec (.of K)} [IsCurve pU]
  [GeometricallyConnected pU] [ConnectedSpace U] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]

section Chart

open scoped Classical in
/-- The open `U₀ ∪ {z}` of `C₀`, for a boundary point `z`. -/
noncomputable abbrev boundaryOpen (z : C) : C.Opens :=
  complOpens (boundaryFinset (p := p) j) (isClosed_of_mem_boundaryFinset j) {z}

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma mem_boundaryOpen_iff {z x : C} :
    x ∈ boundaryOpen (p := p) j z ↔ x ∈ Set.range j.base ∨ x = z := by
  classical
  rw [mem_complOpens, ← Finset.mem_coe, coe_boundaryFinset, Finset.mem_singleton,
    Set.mem_compl_iff, not_not]

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma opensRange_le_boundaryOpen (z : C) : j.opensRange ≤ boundaryOpen (p := p) j z :=
  fun _ hx ↦ (mem_boundaryOpen_iff j).2 (Or.inl hx)

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma connectedSpace_boundaryOpen (z : C) : ConnectedSpace (boundaryOpen (p := p) j z) := by
  have := irreducibleSpace_of_smooth (p := p)
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  have hne : ((boundaryOpen (p := p) j z : C.Opens) : Set C).Nonempty :=
    ⟨j u, opensRange_le_boundaryOpen j z ⟨u, rfl⟩⟩
  have hirr : IsIrreducible ((boundaryOpen (p := p) j z : C.Opens) : Set C) :=
    ⟨hne, (IrreducibleSpace.isIrreducible_univ C).isPreirreducible.open_subset
      (boundaryOpen (p := p) j z).isOpen (Set.subset_univ _)⟩
  exact isConnected_iff_connectedSpace.1 hirr.isConnected

variable (p) in
/-- An affine chart at a boundary point `z`: an affine open `W ∋ z` of `U₀ ∪ {z}` on which `z` is
the zero locus of a single section `ϖ`, i.e. `W ∖ {z} = D(ϖ)`. -/
structure BoundaryChart (z : C) where
  /-- The affine open. -/
  W : C.Opens
  isAffineOpen : IsAffineOpen W
  mem : z ∈ W
  le : W ≤ boundaryOpen (p := p) j z
  /-- The section cutting out `z`. -/
  ϖ : Γ(C, W)
  mem_basicOpen_iff : ∀ x ∈ W, x ∈ C.basicOpen ϖ ↔ x ≠ z

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma nonempty_boundaryChart [SmoothOfRelativeDimension 1 p] [IsIntegral C] {z : C}
    (hz : z ∈ (Set.range j.base)ᶜ) : Nonempty (BoundaryChart p j z) := by
  have hzS : z ∈ boundaryFinset (p := p) j := by
    rw [← Finset.mem_coe, coe_boundaryFinset]
    exact hz
  obtain ⟨W, hW, hzW, ϖ, hle, h⟩ := exists_isAffineOpen_basicOpen_eq p
    (isClosed_of_mem_boundaryFinset j z hzS) (boundaryOpen (p := p) j z)
    ((mem_boundaryOpen_iff j).2 (Or.inr rfl))
  exact ⟨⟨W, hW, hzW, hle, ϖ, h⟩⟩

namespace BoundaryChart

variable {j} {z : C} (c : BoundaryChart p j z)

instance : Nonempty c.W := ⟨⟨z, c.mem⟩⟩

/-- The prime ideal of `Γ(C, W)` at `z`. -/
noncomputable abbrev ideal : Ideal Γ(C, c.W) := (c.isAffineOpen.primeIdealOf ⟨z, c.mem⟩).asIdeal

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma ϖ_mem : c.ϖ ∈ c.ideal := by
  by_contra h
  exact ((c.mem_basicOpen_iff z c.mem).1
    ((IsAffineOpen.mem_basicOpen_iff c.isAffineOpen ⟨z, c.mem⟩ c.ϖ).2 h)) rfl

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
/-- `z` is the only zero of `ϖ` on `W`. -/
lemma eq_ideal (P : Ideal Γ(C, c.W)) (hP : P.IsPrime) (hϖ : c.ϖ ∈ P) : P = c.ideal := by
  have hU := c.isAffineOpen
  let q : Spec Γ(C, c.W) := ⟨P, hP⟩
  have hqW : hU.fromSpec q ∈ c.W := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨q, rfl⟩
  let x : c.W := ⟨_, hqW⟩
  have hx : hU.primeIdealOf x = q :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf x)
  have hxz : x = ⟨z, c.mem⟩ := by
    refine Subtype.ext (not_not.1 fun hne ↦ ?_)
    have := (c.mem_basicOpen_iff x x.2).2 hne
    rw [IsAffineOpen.mem_basicOpen_iff hU x, hx] at this
    exact this hϖ
  calc P = (hU.primeIdealOf x).asIdeal := by rw [hx]
    _ = c.ideal := by rw [hxz]

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma isMaximal_ideal : c.ideal.IsMaximal := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal c.ideal Ideal.IsPrime.ne_top'
  rwa [c.eq_ideal M hM.isPrime (hle c.ϖ_mem)] at hM

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma opensRange_inf (hz : z ∉ Set.range j.base) : j.opensRange ⊓ c.W = C.basicOpen c.ϖ := by
  apply le_antisymm
  · rintro x ⟨hxj, hxW⟩
    exact (c.mem_basicOpen_iff x hxW).2 (by rintro rfl; exact hz hxj)
  · intro x hx
    have hxW : x ∈ c.W := C.basicOpen_le c.ϖ hx
    refine ⟨?_, hxW⟩
    rcases (mem_boundaryOpen_iff j).1 (c.le hxW) with h | h
    · exact h
    · exact absurd h ((c.mem_basicOpen_iff x hxW).1 hx)

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma boundaryOpen_le : boundaryOpen (p := p) j z ≤ j.opensRange ⊔ c.W := by
  intro x hx
  rcases (mem_boundaryOpen_iff j).1 hx with h | rfl
  · exact Or.inl h
  · exact Or.inr c.mem

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma ϖ_ne_zero (hz : z ∉ Set.range j.base) : c.ϖ ≠ 0 := by
  have := irreducibleSpace_of_smooth (p := p)
  intro h0
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  obtain ⟨x, hxj, hxW⟩ := nonempty_preirreducible_inter j.opensRange.isOpen c.W.isOpen
    ⟨j u, u, rfl⟩ ⟨z, c.mem⟩
  have : x ∈ C.basicOpen c.ϖ := by
    rw [← c.opensRange_inf hz]
    exact ⟨hxj, hxW⟩
  rw [h0, Scheme.basicOpen_zero] at this
  exact this

end BoundaryChart

end Chart

variable [IsIntegral C]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

namespace BoundaryChart

variable {j} {z : C} (c : BoundaryChart p j z)

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma exists_isMaximal_liesOver :
    ∃ Q : Ideal (integralClosure Γ(C, c.W) Ω), Q.IsMaximal ∧ Q.LiesOver c.ideal := by
  have := c.isMaximal_ideal
  have : IsFractionRing Γ(C, c.W) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C c.W c.isAffineOpen
  have : FaithfulSMul Γ(C, c.W) (integralClosure Γ(C, c.W) Ω) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h ↦ ?_
    have h' : algebraMap Γ(C, c.W) Ω a = algebraMap Γ(C, c.W) Ω b := congrArg Subtype.val h
    rw [IsScalarTower.algebraMap_apply Γ(C, c.W) C.functionField Ω,
      IsScalarTower.algebraMap_apply Γ(C, c.W) C.functionField Ω b] at h'
    exact IsFractionRing.injective Γ(C, c.W) C.functionField ((algebraMap _ Ω).injective h')
  have : Algebra.IsIntegral Γ(C, c.W) (integralClosure Γ(C, c.W) Ω) :=
    integralClosure.AlgebraIsIntegral
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := integralClosure Γ(C, c.W) Ω)
    c.ideal

/-- A maximal ideal over `z` of the integral closure of `Γ(C, W)` in the separable closure of the
function field: a geometric point over the local field at `z`. -/
noncomputable def point : Ideal (integralClosure Γ(C, c.W) Ω) :=
  c.exists_isMaximal_liesOver.choose

instance : c.point.IsMaximal := c.exists_isMaximal_liesOver.choose_spec.1

instance : c.point.LiesOver c.ideal := c.exists_isMaximal_liesOver.choose_spec.2

end BoundaryChart

variable (sU : Spec (.of (AlgebraicClosure K)) ⟶ U)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]

section Groups

variable {j} {z : C} (c : BoundaryChart p j z)

variable {sC : Spec (.of (AlgebraicClosure K)) ⟶ C} (τ : fiber (sU ≫ j) ≅ fiber sC)
  (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC] [CompactSpace GC]
  [∀ P, MulAction GC ((fiber sC).obj P)] [IsFundamentalGroup (fiber sC) GC]

end Groups

section Datum

variable [SmoothOfRelativeDimension 1 p] (hj : j ≫ p = pU)
  {sC : Spec (.of (AlgebraicClosure K)) ⟶ C} (τ : fiber (sU ≫ j) ≅ fiber sC)
  (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC] [CompactSpace GC]
  [∀ P, MulAction GC ((fiber sC).obj P)] [IsFundamentalGroup (fiber sC) GC]

end Datum

end AlgebraicGeometry.WeilGroup
