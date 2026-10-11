/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.KrullDimension

/-!# Integral zero-dimensional schemes over algebraically closed fields

Source: Stacks Project, Varieties, Lemma 06LH.
(blueprint: lem-weil-pbc-zero-dim-integral-point)
-/


universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An integral finite-type scheme of dimension zero over an algebraically closed field
is the point `Spec k`.

Source: Stacks Project, Varieties, Lemma 06LH; Algebra, Theorem 00FV; Fields, Lemma 09GR.
(blueprint: lem-weil-pbc-zero-dim-integral-point)

Proof:
1. Integrality gives a nonempty irreducible space (def-pc-integral-scheme). By sobriety
(lem-weil-pbc-scheme-sober), it has a unique generic point. Every point's closure is
irreducible (def-weil-irreducible-components). A proper inclusion of such a closure in Z
would give a chain of length one (def-kun-topological-krull-dimension), contradicting
zero dimension. Thus all points are generic, and Z has exactly one point.
2. Finite type (def-weil-pbc-scheme-conventions, def-weil-finite-type-morphism) gives an
affine open Spec A containing that point, hence equal to Z (def-weil-affine-spectrum).
Integrality makes A a nonzero domain; its zero ideal is its only prime. Any nonzero
nonunit would lie in a nonzero maximal ideal, so A is a field.
3. Since A is a field finitely generated over k, Zariski's lemma
(lem-weil-pbc-zariski-lemma) makes it a finite extension. Algebraic closedness
(def-weil-algebraic-closure, lem-weil-pbc-alg-closed-finite-extension-trivial) makes the
structure ring map k → A bijective.
4. The structure morphism is Spec of this ring isomorphism. Functoriality of Spec
(def-weil-affine-spectrum) gives an inverse from the inverse ring map.
-/
theorem isIso_structure_of_integral_zero_dim
    {k : Type u} [Field k] [IsAlgClosed k] (Z : Scheme.{u})
    [Z.Over (Spec (.of k))] [IsIntegral Z]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    (h_dim : topologicalKrullDim Z = 0) :
    IsIso (Z ↘ Spec (.of k)) := by
  sorry

end AlgebraicGeometry
