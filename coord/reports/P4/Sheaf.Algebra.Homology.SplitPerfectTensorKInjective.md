## What changed

Proved `CochainComplex.isKInjective_mapBifunctor_of_bounded_splitFree` in
`Sheaf.Algebra.Homology.SplitPerfectTensorKInjective`, preserving its entire signature
and all public imports. Added one proved private helper for dualizability of finite
powers, including the empty product. No definitions or other modules changed.

The shorter route uses the already proved source-library categorical duality:
`IsDualizable.of_retract`, `CochainComplex.rightDual`, `exactPairingRightDual`,
`IsDualizable.flat`, and `ExactPairing.map`. The bounded dual complex is K-flat by
`isKFlat_of_boundedAbove_flat`. In the homotopy category, the tensor adjunction
identifies maps from an acyclic complex into `I tensor P` with maps from its tensor
with the dual into `I`; right orthogonality of `I` makes these zero. Equality in
the quotient then gives the required actual null homotopy.

Proof-only imports supply these source duality results, the monoidal homotopy
category, additive sheaf tensor functors, and the bounded-above flat criterion.
The node's proof, proof dependencies, and proof origin follow this argument.

## Proved and sorry left

Closed 1 of 1 holes:
`CochainComplex.isKInjective_mapBifunctor_of_bounded_splitFree`
(node `lem-weil-pbc-split-perfect-tensor-kinjective`).

Added 0 holes; 0 remain in the delivered Lean module. No split-offs.
The private helper `isDualizable_finite_power` is fully proved.
Remote compilation with `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound` for the delivered theorem.

The rank-zero, zero-complex, and potentially empty support cases require no
extra hypotheses: the induction handles the empty product, and the source
bounded-dual construction uses only the stated vanishing outside the interval.
The theorem does not assume a zero differential or boundedness of `I`.

## No longer needed

Removed the following direct proof-only imports from the assigned module:

- `Sheaf.Algebra.Homology.HomComplex`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`

The proof no longer needs these former proof-dependency nodes:

- `def-pur-hom-complex`: no internal Hom complex is constructed.
- `def-pur-sheaf-hom`: no componentwise internal Hom comparison is needed.
- `lem-pur-hom-kflat-into-kinjective`: the tensor adjunction and right
  orthogonality prove the result directly.

Removed `lem-pur-hom-kflat-into-kinjective` from the node's top-level
`tool_uses`; the bounded-above-flat tool remains. These are removals from this
proof's dependency route, not claims that no other target path uses the modules.
The unit's statement and proof-step nodes remain intact.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or definition was found. The DAG's proposed explicit
signed tensor-to-Hom isomorphism is unnecessary: the existing generic bounded
dual-complex construction already proves the differential and triangle
identities, and the monoidal homotopy quotient transports them. This route is
below the proper-base-change unit and preserves its required steps. No consumer
adaptations, statement repairs, or new DAG nodes are needed.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
