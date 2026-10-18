/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Sober
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso
import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-!
# Geometric irreducibility and the generic residue field

Source: Stacks Project, Varieties, Tag 054Q, equivalence (1) and (2)
(blueprint: lem-zl-generic-point-geometric-irreducibility).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An irreducible scheme over a field is geometrically irreducible if and only if the
spectrum of its generic residue field is geometrically irreducible. The composite
`X.fromSpecResidueField ξ ≫ X ↘ Spec (.of k)` supplies the induced structure over `k`.
No reducedness or finite-type hypothesis is needed.

Source: Stacks Project, Varieties, Tag 054Q, equivalence (1) and (2).
(blueprint: lem-zl-generic-point-geometric-irreducibility)

Proof:
1. Replace `X` by its reduction `Y`. By
   `lem-weil-pbc-reduction-universal-homeomorphism`, the reduction map is a surjective
   closed immersion that induces a homeomorphism after every base change. Thus `Y` is
   irreducible, the point `η` above `ξ` is generic, and geometric irreducibility of `Y`
   and `X` agrees. By `lem-weil-pbc-closed-immersion-residue-field-iso`, the induced
   residue-field map identifies `κ(ξ)` with `κ(η)` over `k`.
2. The reduced irreducible scheme `Y` is integral (`def-pc-integral-scheme`). Its
   generic stalk `K` is a field and is the fraction field of every nonempty affine
   open's coordinate ring, with injective germ maps
   (`lem-sc-integral-function-field-affine-fraction`). Hence `K = κ(η)`, compatibly
   with `k`. The nonempty affine neighbourhoods of `η`, ordered by reverse inclusion,
   form a nonempty directed system: the intersection of two contains `η` and hence
   an affine neighbourhood of `η`. They are cofinal among all neighbourhoods of `η`.
   The stalk construction (`def-weil-pbc-module-stalk`) identifies `K` with the
   filtered colimit of their coordinate `k`-algebras, since every germ has an affine
   representative and equality of germs can be checked on a smaller affine open.
3. If `Y` is geometrically irreducible, every nonempty affine open has geometrically
   irreducible coordinate algebra (`lem-zl-geometric-irreducibility-affine-local`).
   Clause (2) of `lem-zl-geometric-irreducibility-subalgebra-colimit` makes their
   filtered colimit `K = κ(η)` geometrically irreducible.
4. Conversely, if `Spec κ(η)` is geometrically irreducible, each nonempty affine
   coordinate algebra of `Y` embeds into `K = κ(η)`. Clause (1) of
   `lem-zl-geometric-irreducibility-subalgebra-colimit` makes these subalgebras
   geometrically irreducible. The converse affine-local criterion
   (`lem-zl-geometric-irreducibility-affine-local`) makes `Y` geometrically irreducible.
5. Transfer both implications from `Y` to `X` using the universal homeomorphism
   and the `k`-linear residue-field isomorphism from step 1. -/
theorem geometricallyIrreducible_iff_genericResidueField
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IrreducibleSpace X] (ξ : X) (hξ : IsGenericPoint ξ (Set.univ : Set X)) :
    GeometricallyIrreducible (X ↘ Spec (.of k)) ↔
      GeometricallyIrreducible (X.fromSpecResidueField ξ ≫ X ↘ Spec (.of k)) := by
  sorry

end AlgebraicGeometry
