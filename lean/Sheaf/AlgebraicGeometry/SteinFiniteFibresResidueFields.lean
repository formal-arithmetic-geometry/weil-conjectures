/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.AlgebraicGeometry.SteinFactorizationAffine
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Separation.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Finite fibres and residue extensions of the affine Stein factor

Source: Stacks Project, More on Morphisms, Tag 0E0M,
`lemma-stein-universally-closed-residue-fields`
(blueprint: lem-weil-pbc-stein-finite-fibres-residue-fields).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The affine Stein factor of a proper morphism has finite point fibres and finite
residue-field extensions, without a Noetherian assumption on the base ring.
Source: Stacks Project, Tag 0E0M, `lemma-stein-universally-closed-residue-fields`.
(blueprint: lem-weil-pbc-stein-finite-fibres-residue-fields)

Here `f.steinFactorizationBase` is the canonical map from `Spec Γ(X, ⊤)` to `Spec A`.
For a point `b` over `s`, its residue-field map has source `κ(f.steinFactorizationBase b)`,
which is `κ(s)`. Ring-hom finiteness is module finiteness for that very map, hence finite
vector-space dimension, since these rings are fields.

Proof:
1. Apply `lem-weil-pbc-stein-factorization-affine`: the second map is integral and the
   first map is proper and surjective. Integral incomparability
   (`lem-weil-pbc-integral-incomparability`) makes every singleton of the point fibre closed.
2. The scheme fibre `Y = X_s` is proper over `κ(s)` by
   `lem-weil-pbc-proper-fp-permanence`, hence finite type and quasi-compact. It is Noetherian
   by `lem-weil-pbc-finite-type-over-noetherian`. The fibre homeomorphism
   (`def-pc-scheme-fibre`) and surjectivity of the first map give a continuous surjection
   from `Y` to the point fibre of the second map.
3. By `lem-sc-noetherian-closed-subset-finite-components`, `Y` has finitely many
   irreducible components. By `lem-weil-pbc-scheme-sober` each has a generic point.
   Its image is a singleton, since all singletons of the target fibre are closed.
   Surjectivity therefore makes the target fibre finite, also when `Y` is empty.
4. For any point `b` of this fibre, its inverse image in `Y` is nonempty and closed.
   Schemes are Kolmogorov by sobriety; apply
   `lem-sc-quasi-compact-kolmogorov-closed-point` to choose a point `x` closed in `Y` over `b`.
5. On a finite-type affine neighbourhood of `x`, its residue field is the quotient of
   a finitely generated `κ(s)`-algebra by a maximal ideal. Zariski's lemma
   (`lem-weil-pbc-zariski-lemma`) makes `κ(x)` finite-dimensional over `κ(s)`.
6. The canonical field map `κ(b) → κ(x)` is injective. Functoriality of stalk maps and
   reduction modulo maximal ideals identify the composite with the structure map from
   `κ(s)`. Thus `κ(b)` is a `κ(s)`-linear subspace of `κ(x)` and is finite-dimensional.
-/
theorem Scheme.Hom.steinFactorizationBase_finite_fibres_residueFields
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (s : Spec (CommRingCat.of A)) :
    (f.steinFactorizationBase ⁻¹' {s}).Finite ∧
      ∀ b : Spec Γ(X, ⊤), f.steinFactorizationBase b = s →
        (f.steinFactorizationBase.residueFieldMap b).hom.Finite := by
  sorry

end AlgebraicGeometry
