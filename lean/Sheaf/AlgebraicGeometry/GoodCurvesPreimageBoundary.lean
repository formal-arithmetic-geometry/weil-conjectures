/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H5
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ProperCoproduct
import Sheaf.AlgebraicGeometry.GoodCurvesBoundaryQuasiFinite

/-!
# Geometric compactification of the inverse image of a good-curves open

Source: Stacks Project, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`, proof after
replacing the dense open by its inverse image under the finite good-curves cover.
(blueprint: lem-weil-pbc-good-curves-preimage-boundary)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The inverse image of a fibrewise dense open has a quasi-finite boundary in the
finite disjoint union of proper good-curve models.

Source: Stacks Project, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`, the second
boundary Zprime. (blueprint: lem-weil-pbc-good-curves-preimage-boundary)

Proof: Pullback distributes over the finite disjoint union Y. On each component
its inverse image W_i is an open of Y_i. Composing its open immersion with j_i gives
an open immersion into Ybar_i. Their disjoint union identifies the pullback with an
open O in the disjoint union C of the Ybar_i. The compatibility hcomm gives the
stated equality of the two maps to V. Each p_i followed by t_i is proper, since t_i
is finite, so C to V is proper by finite coproducts. It is of finite type over the
Noetherian V; hence C is Noetherian. Surjectivity of Y_i to T_i makes each fibre
nonempty, and hWi makes its open W_i fibre nonempty. A smooth geometrically connected
fibre of p_i is regular and connected, hence irreducible, so this open is dense
in that fibre. The good-curves-boundary quasi-finiteness theorem now applies to the
open component inclusions W_i into Ybar_i. Take Z with its embedding i to be the
canonical reduced closed complement of O. Its image is the complement of O. This
proves quasi-finiteness of its map to V, including empty families and
zero-dimensional fibres. -/
theorem goodCurvesPreimage_boundary
    {X V : Scheme.{u}} [IsNoetherian X] [IsNoetherian V]
    (f : X ⟶ V) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (n : ℕ) (T Y Ybar : Fin n → Scheme.{u})
    (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i) (p : ∀ i, Ybar i ⟶ T i)
    (ν : (∐ Y) ⟶ X) [IsFinite ν] [Surjective ν]
    (hcomm : ∀ i, Limits.Sigma.ι Y i ≫ ν ≫ f = j i ≫ p i ≫ t i)
    (ht : ∀ i, IsFinite (t i) ∧ AlgebraicGeometry.Etale (t i))
    (hj : ∀ i, IsOpenImmersion (j i))
    (hjp : ∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i))
    (hp : ∀ i, Smooth (p i) ∧ IsProper (p i) ∧
      ∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
        topologicalKrullDim ((p i).fiber s) ≤ 1)
    (W : X.Opens)
    (hWi : ∀ (i : Fin n) (s : T i),
      Dense (((j i ≫ p i).fiberι s ≫ Limits.Sigma.ι Y i ≫ ν) ⁻¹' (W : Set X)))
    : IsNoetherian (∐ Ybar) ∧
      IsProper (Limits.Sigma.desc fun i ↦ p i ≫ t i) ∧
      ∃ (O : (∐ Ybar : Scheme.{u}).Opens)
        (e : Limits.pullback ν W.ι ≅ O.toScheme)
        (Z : Scheme.{u}) (i : Z ⟶ (∐ Ybar)),
        IsClosedImmersion i ∧ Set.range i.base = (O : Set (∐ Ybar : Scheme.{u}))ᶜ ∧
        e.hom ≫ O.ι ≫ (Limits.Sigma.desc fun k ↦ p k ≫ t k) =
          Limits.pullback.snd ν W.ι ≫ W.ι ≫ f ∧
        (i ≫ (Limits.Sigma.desc fun k ↦ p k ≫ t k)).IsQuasiFinite := by
  sorry

end AlgebraicGeometry.Etale
