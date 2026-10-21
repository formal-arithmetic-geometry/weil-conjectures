module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.TensorProduct.Maps
import Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest
import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import Sheaf.FieldTheory.ValueGroupDivisible
import Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange
import Sheaf.TraceFormula.ValuationFiniteTypeModulePresentation
import Sheaf.AlgebraicGeometry.SepClosedValuationGeometricComponents
import Sheaf.RingTheory.GrauertRemmertPowerbounded
import Sheaf.TraceFormula.ValuationArbitraryHeightLimit
import Sheaf.TraceFormula.ValuationFiniteHeightComposition
import Sheaf.TraceFormula.ValuationRankOneFormalComparison

/-!
# Relative integral closure over a separably closed valuation field

Source: Temkin, *Stable modification of relative curves*, Theorem 3.5.5,
Steps 2--5, printed pp. 22--24 (blueprint: lem-trf-valuation-reduced-fibre-normalization).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

open scoped TensorProduct

/-- Relative integral closure over a separably closed valuation field.

Source: Temkin, *Stable modification of relative curves*, Theorem 3.5.5,
Steps 2--5, printed pp. 22--24 (blueprint: lem-trf-valuation-reduced-fibre-normalization).

The hypothesis `hgeom` quantifies over fields `E` in the universe `u` of `K`; this contains
`AlgebraicClosure K`, which suffices by the algebraic-closure test for geometric reducedness.

Proof (node steps):
1. Flatness makes `A → A_K` injective; every ring `A ⊆ D ⊆ A_K` is `V`-torsion-free, hence
   flat (lem-trf-valuation-torsionfree-flat); a finite-type such `D` is finitely presented over
   `V` (lem-trf-valuation-finite-type-module-presentation, cyclic-kernel argument), and finitely
   presented as an `A`-module when finite over `A`. The cases `A = 0` and `V = K` are direct.
2. Localising integral closure, `B` over a prime `q ≠ 0` is `E = B_{V∖q}` over `W = V_q`; the
   residue field of `W` is separably closed and perfect (root of `X^p + tX - c`), hence
   algebraically closed.
3. If `a^n ∈ mE`, divisibility of the value group gives `y` with `(a/y)^n ∈ E`, so `a/y ∈ E`
   by transitivity; thus `E/mE` is reduced, hence geometrically reduced; for `q = 0` use
   `hgeom`. Every `V → Ω` factors through such a residue field.
4. Height one: with `π`-adic completion, the formal comparison gives `Ĉ = Â[1/π]` reduced
   affinoid over algebraically closed `K̂`; Grauert--Remmert makes `C°` finite over `Â`, and
   `C°` is the relative integral closure of the image of `Â`.
5. Approximate generators `â_i/s_i` by `a_i/s_i` with `a_i ∈ A`; scalar saturation gives monic
   equations over `A`; `D = A[a_i/s_i]` is finite over `A`, flat and finitely presented.
6. `D̂ = C°`; any `b = a/s ∈ B` has `a ∈ sD̂`, so `a ∈ sD` and `b ∈ D`: `B = D` finite.
7. Height `h > 1`: take the minimal nonzero prime `p`, `T = V ∖ p`; `B_T` is finite over `A_T`
   by height one; adjoin cleared generators to get `A'` finite over `A` with `A'_T = B_T`.
8. The finite-height composition lemma gives `pB = pA'` and `B/pB` as the relative integral
   closure of `A'/pA'` over `W = V/p`; induction makes it finite, so `B` is finite over `A`.
9. Arbitrary height: the valuation-limit lemma gives a finite-height `V_0`, `A_0`; the finite
   model `D = B_0 ⊗_{V_0} V` is finite, flat, finitely presented, with reduced geometric fibres
   (base change of the fibre locus) and `D ⊆ B`.
10. For `b = d/s ∈ B`, `Spec D[b] → Spec D` is a finite `η`-modification; the eta-normality
    lemma makes it an isomorphism, so `B = D`.
11. `B` is finite over `A`, so flat and finitely presented over `V` by step 1; `B_K = A_K`
    canonically; steps 2--3 give reduced geometric fibres. -/
theorem valuation_reduced_fibre_normalization
    (K V A : Type u) [Field K] [CommRing V] [CommRing A]
    [Algebra V K] [Algebra V A] [IsDomain V] [ValuationRing V]
    [IsFractionRing V K] [IsSepClosed K]
    [Module.Flat V A] [Algebra.FinitePresentation V A]
    (hgeom : ∀ (E : Type u) [Field E] [Algebra K E],
      letI : Algebra K (A ⊗[V] K) := Algebra.TensorProduct.rightAlgebra
      IsReduced (TensorProduct K (A ⊗[V] K) E)) :
    let AK := A ⊗[V] K
    let B := integralClosure A AK
    let canonical : B ⊗[V] K →ₐ[V] AK :=
      Algebra.TensorProduct.lift ((Subalgebra.val B).restrictScalars V)
        Algebra.TensorProduct.includeRight
        (fun _ _ => Commute.all _ _)
    Module.Finite A B ∧
      Function.Bijective canonical.toRingHom ∧
      RingHom.Flat (algebraMap V B) ∧
      Algebra.FinitePresentation V B ∧
      (∀ (Ω : Type v) [Field Ω] [Algebra V Ω] [IsAlgClosed Ω],
        IsReduced (TensorProduct V B Ω)) := by
  sorry
