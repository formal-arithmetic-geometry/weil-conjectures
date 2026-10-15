/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import WeilConjectures.ZetaSeries
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso

/-!
# Dimension of an irreducible closed subset

Source: Stacks Project, Varieties, Tags 0A21 and 0B1C,
`lemma-dimension-locally-algebraic` (6), applied to the reduced induced closed subscheme
(blueprint: lem-sc-closed-irreducible-dimension-trdeg).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A nonempty irreducible closed subset of a finite type scheme over a field has dimension
 equal to the transcendence degree of its generic residue field. Both are represented by
 the same natural number, with their respective casts.
Source: Stacks Project, Varieties, Tags 0A21 and 0B1C, part (6).
(blueprint: lem-sc-closed-irreducible-dimension-trdeg)

Proof:
1. Give `C` its reduced induced closed subscheme structure `Y` using
   `lem-weil-pbc-reduced-induced-closed-subscheme`. The closed immersion identifies `Y`
   homeomorphically with `C` (`def-weil-closed-immersion`), so `Y` is integral
   (`def-pc-integral-scheme`) and its generic point lies over `η`. The dimensions agree by
   `lem-weil-pbc-homeomorphism-krull-dimension`.
2. The closed immersion is locally of finite type by
   `lem-weil-pbc-immersion-base-change-lft`. Composing with the structure morphism preserves
   this property by `lem-weil-pbc-proper-fp-permanence` (e).
3. Choose a nonempty affine neighbourhood `Spec A` of the generic point in `Y`. Its ring is
   a finite type domain over `K` (`def-weil-finite-type-morphism`, `def-pc-integral-scheme`).
   By `lem-sc-integral-locally-algebraic-opens-dimension` it has dimension `dim Y`; use
   `lem-weil-pbc-homeomorphism-krull-dimension` and `def-weil-pbc-krull-dimension-ring` to
   identify this with `dim A`.
4. By `lem-sc-integral-function-field-affine-fraction`, the generic stalk is a fraction
   field of `A`, compatibly with `K`. It is a field, so quotienting by its maximal ideal
   zero identifies it with the generic residue field (`def-weil-residue-field`).
5. Apply `lem-weil-pbc-finite-type-domain-dimension-trdeg` to obtain the finite common
   value of `dim A` and the transcendence degree of that fraction field.
6. The isomorphism of generic residue fields from
   `lem-weil-pbc-closed-immersion-residue-field-iso` respects `K`. It preserves polynomial
   relations, hence algebraic independence and transcendence degree
   (`def-kun-transcendence-degree`). Substitute into step 5. -/
theorem topologicalKrullDim_closed_irreducible_eq_trdeg
    {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    (C : Set X) (hC : IsClosed C) (hCi : IsIrreducible C)
    (η : X) (hηC : η ∈ C) (hη : closure ({η} : Set X) = C) :
    ∃ d : ℕ, topologicalKrullDim C = (d : WithBot ℕ∞) ∧
      @Algebra.trdeg K (X.residueField η) _ _
        ((X ↘ Spec (.of K)).residueFieldAlgebraMap η).toAlgebra = (d : Cardinal) := sorry

end AlgebraicGeometry
