## What changed

Proved `AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomFiniteRootUnit_isIso`
without changing its statement or the public imports. All Lean changes are in
`Sheaf.Paper.BottomFiniteRootUnitIsIso`; all added helpers are private and proved.

The proof identifies the bottom-field quotient with `ZMod (l^(n+1))` using the
existing integral bottom-field ring equivalence, transport of principal ideals,
and `PadicInt.ker_toZModPow`. The existing finite discrete condensed-ring and
scheme-pullback comparisons give a unital coefficient isomorphism. For any group
killed by N, the tensor insertion has the explicit inverse induced by scalar
multiplication: integer representatives show both inverse identities. Apply
this sectionwise, use strong monoidal sheafification, and transport along the
coefficient isomorphism. The last step identifies the actual free/forget unit,
rather than choosing an arbitrary isomorphism between its source and target.

Updated the item's proof steps, dependencies and proof origin to record these
constructions. The three coefficient comparison nodes used as generic tools
already have complete proofs. The diagonal unit route is preserved.

Validation: the complete module compiled cleanly through `lcompile.py` in
10.7 seconds, with no errors or warnings. A source comparison confirms the
public theorem signature is byte-for-byte unchanged, all Lean lines are at most
100 characters, and the only changed node fields are `proof`, `proof_deps` and
`proof_origin`.

The algebra calculation works for every N, including N=0 and N=1. Its application
uses N=l^(n+1). No invertibility of l on X, choice of root generator, nonempty
scheme hypothesis, inverse limit, or local-freeness assertion enters the proof.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomFiniteRootUnit_isIso`
(node `lem-diagonal-bottom-finite-root-unit-is-iso`).

Added 0 holes. There are no remaining sorry declarations in this delivery.
No statements were split off.

## No longer needed

No original Lean import was removed and no library module was withdrawn.
`def-sfb-diagonal-coefficient-diagrams` is no longer a proof dependency: the finite
unit calculation uses the coefficient and root constructions directly. It remains
in the node's statement dependencies, which were not changed. The completed
coefficient comparison, inverse-limit theory, local root bases, and the
unnormalized `ConstantZModScalarTensor` comparison are not required as proof
steps. The existing public import of `ProEtaleTateTwists` is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. The original mathematical plan was valid,
but its elementary tensor step needed an explicit unit calculation and transport
through the strong monoidal sheafification functor. Both are now proved here;
there is no further renaming or decomposition of this obligation.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
