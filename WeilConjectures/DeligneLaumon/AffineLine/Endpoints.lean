/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.CohomologicalRange
public import WeilConjectures.WeilSheaf.CohomologySequence
public import WeilConjectures.WeilSheaf.CurveTopCohomology
public import WeilConjectures.WeilSheaf.GeometricCoinvariants
public import WeilConjectures.WeilSheaf.OpenClosedTriangle
public import WeilConjectures.WeilSheaf.UpperStarLowerStar

/-!
# The two endpoints of the compactly supported cohomology of a middle extension

For a dense open immersion `j : U₀ ↪ C₀` into a smooth geometrically connected affine curve
and a lisse Weil sheaf `F` on `U₀`, all the compactly supported cohomology of the ordinary
direct image `j_*F` outside degrees `0, 1, 2` vanishes, degree zero vanishes as well because a
nonzero global section of a lisse sheaf on a connected open has full support on a nonproper
curve, and degree two is the geometric coinvariants `V_{π₁(U)}` Tate-twisted by `(-1)`, by
global Verdier duality on the smooth nonproper curve `U`. Purity of `F` of weight `w`
therefore makes degree two pure of weight `w + 2`.

This leaves degree one, which is the only place where the Fourier argument of
`WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` is needed.

## Main statements

- `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage`: vanishing outside
  degrees `0, 1, 2`.
- `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero`: vanishing in
  degree zero.
- `AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage_two`: the
  coinvariant description of degree two.
- `AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two`: its
  purity.
- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_two`: the top
  compactly supported cohomology of a pure lisse sheaf on a smooth affine curve has weights at
  most `w + 2`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]

/-- A smooth affine curve `C₀` is locally of finite type over `k₀`, being smooth over `k₀`. -/
local instance : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  inferInstance

/-- *Top compact-support bound on a curve.* If `C₀` is a smooth affine curve and `G` is a lisse
Weil sheaf on `C₀`, punctually `ι`-pure of weight `w`, then `H_c^2(C, G)` has weights at most
`w + 2`: it is a Frobenius-equivariant quotient of the generic fibre, pure of weight `w`, twisted
by `(-1)`.
(blueprint: `lem-a1-curve-hc2-bound`) -/
theorem WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_two
    (ι : PadicAlgCl l →+* ℂ) (G : WeilSheaf k₀ l C) (hG : G.IsLisse) {w : ℝ}
    (hw : G.IsPunctuallyPureOfWeight ι w) :
    (G.compactlySupportedCohomology 2).HasWeightsAtMostOver k₀ ι (w + 2) := by
  -- TODO(adic): prove once Weil sheaves carry genuine `ℓ`-adic coefficients
  sorry

section Complement

omit [Finite k₀] [IsAffine C] in
/-- A smooth geometrically connected curve is irreducible. -/
lemma irreducibleSpace_of_geometricallyConnected
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] : IrreducibleSpace C := by
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  have : GeometricallyIrreducible (C ↘ Spec (CommRingCat.of k₀)) :=
    .of_smooth_of_geometricallyConnected _
  exact GeometricallyIrreducible.irreducibleSpace_of_subsingleton
    (f := C ↘ Spec (CommRingCat.of k₀))

omit [Finite k₀] in
include k₀ in
/-- A smooth affine curve is a noetherian topological space. -/
lemma noetherianSpace_of_curve : NoetherianSpace C := by
  have := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k₀))
  have : IsNoetherian C := {}
  infer_instance

omit [Finite k₀] [IsAffine C] in
include k₀ in
/-- A smooth curve has dimension at most one. -/
lemma topologicalKrullDim_le_one_of_curve : topologicalKrullDim C ≤ 1 := by
  exact_mod_cast
    topologicalKrullDim_le_of_smoothOfRelativeDimension (C ↘ Spec (CommRingCat.of k₀)) 1

variable {U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j] [IsDominant j]

omit [Finite k₀] [IsAffine C] [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [IsOpenImmersion j] in
include k₀ j in
/-- A dense open of a nonempty scheme is nonempty. -/
lemma nonempty_of_isDominant [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] :
    Nonempty U := by
  have : Surjective (C ↘ Spec (CommRingCat.of k₀)) := inferInstance
  obtain ⟨c, -⟩ := (C ↘ Spec (CommRingCat.of k₀)).surjective
    (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of k₀))))
  by_contra hU
  rw [not_nonempty_iff] at hU
  have hd := j.denseRange
  rw [DenseRange, Set.range_eq_empty] at hd
  have h := hd.closure_eq
  rw [closure_empty] at h
  have hc : c ∈ (Set.univ : Set C) := trivial
  rw [← h] at hc
  exact hc


omit [Finite k₀] in
include k₀ in
/-- The complement of a dense open of a smooth geometrically connected curve is finite. -/
lemma finite_compl_range_of_isDominant [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] :
    (Set.range j.base)ᶜ.Finite := by
  have := irreducibleSpace_of_geometricallyConnected (k₀ := k₀) (C := C)
  have := noetherianSpace_of_curve (k₀ := k₀) (C := C)
  have := nonempty_of_isDominant (k₀ := k₀) j
  exact j.isOpenEmbedding.isOpen_range.finite_compl_of_topologicalKrullDim_le_one
    (topologicalKrullDim_le_one_of_curve (k₀ := k₀)) (Set.range_nonempty _)

omit [Finite k₀] in
include k₀ j in
/-- A dense open of a smooth geometrically connected affine curve is affine. -/
lemma isAffine_of_isDominant [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] :
    IsAffine U := by
  have := irreducibleSpace_of_geometricallyConnected (k₀ := k₀) (C := C)
  have := noetherianSpace_of_curve (k₀ := k₀) (C := C)
  have := nonempty_of_isDominant (k₀ := k₀) j
  exact isAffine_of_isOpenImmersion_of_topologicalKrullDim_le_one j
    (topologicalKrullDim_le_one_of_curve (k₀ := k₀))

omit [Finite k₀] in
/-- The closed complement of a dense open of a smooth geometrically connected affine curve, as a
finite `k₀`-scheme. -/
lemma exists_isClosedImmersion_range_eq_compl
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] :
    ∃ (Z : Scheme.{u}) (_ : Z.Over (Spec (CommRingCat.of k₀))) (i : Z ⟶ C)
      (_ : IsClosedImmersion i) (_ : i.IsOver (Spec (CommRingCat.of k₀)))
      (_ : IsFinite (Z ↘ Spec (CommRingCat.of k₀))), Set.range i.base = (Set.range j.base)ᶜ := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ : Closeds C)
  have hI : Set.range I.subschemeι.base = (Set.range j.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  let : I.subscheme.Over (Spec (CommRingCat.of k₀)) := ⟨I.subschemeι ≫ C ↘ _⟩
  have : I.subschemeι.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have hfin : Finite I.subscheme := by
    have := (finite_compl_range_of_isDominant (k₀ := k₀) j).to_subtype
    rw [← hI] at this
    exact Finite.of_equiv _ (Equiv.ofInjective _ I.subschemeι.isClosedEmbedding.injective).symm
  have : LocallyOfFiniteType (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    show LocallyOfFiniteType (I.subschemeι ≫ C ↘ _) from inferInstance
  have : LocallyQuasiFinite (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    .of_finite_preimage_singleton _ fun _ ↦ Set.toFinite _
  refine ⟨I.subscheme, inferInstance, I.subschemeι, inferInstance, inferInstance,
    IsFinite.of_locallyQuasiFinite _, hI⟩

end Complement

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
  [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
  (F : WeilSheaf k₀ l U)

/-- For a dense open immersion `j : U₀ ↪ C₀` with `C₀` a smooth geometrically connected affine
curve and `F` lisse on `U₀`, the compactly supported cohomology `H_c^r(C, j_*F)` vanishes for
every `r` outside `{0, 1, 2}`. (blueprint: `sk-l-dl-a1-endpoints`) -/
theorem subsingleton_compactlySupportedCohomology_directImage (hF : F.IsLisse) {r : ℤ}
    (hr : r < 0 ∨ 2 < r) :
    Subsingleton
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology r).carrier := by
  -- TODO(adic): prove once Weil sheaves carry genuine `ℓ`-adic coefficients
  sorry

/-- In the situation of `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage`
the degree-zero compactly supported cohomology `H_c^0(C, j_*F)` vanishes, because a nonzero
global section of a lisse sheaf on a connected open has full support on a nonproper curve.
(blueprint: `sk-l-dl-a1-endpoints`) -/
theorem subsingleton_compactlySupportedCohomology_directImage_zero (hF : F.IsLisse) :
    Subsingleton
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 0).carrier := by
  -- TODO(adic): prove once Weil sheaves carry genuine `ℓ`-adic coefficients
  sorry

/--
In degree two, global Verdier duality on the smooth nonproper curve `U` identifies
`H_c^2(C, j_*F)` with the geometric coinvariants `V_{π₁(U)}` of `F`, Tate-twisted by `(-1)`:
the Frobenius of the cohomology is `q` times the Frobenius of the coinvariants.

```
  H_c²(C, j_*F) ──e──▶ V_{π₁(U)}
        │                 │
   Frob │                 │ q · Frob
        ▼                 ▼
  H_c²(C, j_*F) ──e──▶ V_{π₁(U)}
```
(blueprint: `sk-l-dl-a1-endpoints`)
-/
theorem nonempty_equiv_compactlySupportedCohomology_directImage_two
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] (hF : F.IsLisse) :
    Nonempty ((((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).Equiv
      ((F.geometricCoinvariants hF).tateTwist (Nat.card k₀) (-1))) := by
  sorry

/-- If `F` is moreover punctually `ι`-pure of weight `w`, then `H_c^2(C, j_*F)` is pure of
weight `w + 2`: the Tate twist of
`AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage_two` raises weights
by two. (blueprint: `sk-l-dl-a1-endpoints`) -/
theorem isPureOfWeightOver_compactlySupportedCohomology_directImage_two
    (ι : PadicAlgCl l →+* ℂ) (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) :
    (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).IsPureOfWeightOver
      k₀ ι (w + 2) := by
  -- TODO(adic): prove once Weil sheaves carry genuine `ℓ`-adic coefficients
  sorry

end AlgebraicGeometry
