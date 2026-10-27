## What changed

Reduced `Profinite.TameInertiaScalarMate.scalar_mate_isomorphism` using the existing
`Profinite.TameInertiaKoszul.continuous_koszul` theorem, instantiated with `ZMod p`.
The ordinary finite-free tensor computation and the normalized derived-tensor
computation are isolated as two independent, strictly smaller statements.

The main module proves the pure-section multiplication formula directly from the
ordinary adjunction inverse identity, linearity, and the recorded coordinate formula.
It proves the derived transpose from the actual unit equation and exact-functor
comparison naturality, and applies it to the Koszul coefficient square. Finally it
cancels the isomorphism T(kappa_E) from the composite of comparison isomorphisms.

Existing definitions tensor, tensorGenerator, DerivedTensor, tensorMap and mate move
unchanged to the new publicly reexported TameInertiaScalarMateData module. This permits
both smaller lemmas to import their actual definitions without an import cycle.
Computes and the main theorem keep their signatures. No existing consumer imports the
item, so there are no consumer adaptations. The change record is
`coord/changes/C6-tame-inertia-scalar-mate-data.md`.

## Proved and sorry left

One original hole is closed: `Profinite.TameInertiaScalarMate.scalar_mate_isomorphism`
(node `lem-sfb-tame-inertia-scalar-mate-isomorphism`). The item has zero remaining holes.

Two holes are added, so this is a decomposition, with net holes closed minus added -1:

- `Profinite.TameInertiaScalarMate.derived_tensor_computation`, node
  `lem-sfb-tame-inertia-derived-tensor-computation`: existence of the normalized derived
  scalar tensor and its invertible comparison on the finite Koszul model.
- `Profinite.TameInertiaScalarMate.scalar_tensor_computation`, node
  `lem-sfb-tame-inertia-scalar-tensor-computation`: invertibility of the ordinary scalar
  adjunct between Koszul complexes.

Both holes are entire public theorem proofs in separate modules, with complete proof
plans and sources. Neither asserts invertibility of the derived invariant mate, the
coefficient-square transpose, or the main theorem under another name. The first does
not mention an Omega-invariant comparison; the second does not mention derived tensor.
The data module adds no holes and chooses no object from an unproved existence theorem.

## No longer needed

No mathematical node or library module is withdrawn or globally pruned. The existing
continuous Koszul comparison remains required, including its coefficient square.
The original generic tensor/K-flat proof dependencies are now reached through the
smaller computation theorems; the parent proof_deps lists those statements and the
shared data. Its generic-tool approvals are retained.

The item's former private proof imports CochainTensorUniverses, FlatOnSite and
BoundedAboveFlatSheafKFlat are no longer direct imports of the main module. The generic derived-adjunction result remains publicly available through the unchanged
data imports. The bounded-flat theorem remains a declared proof dependency of the
new derived computation; its eventual proof will import it when applying it.
All original public imports remain reexported by the shared data module.

## Where the brief, the DAG or earlier work was wrong

The original DAG labels the finite-coordinate arguments elementary, but the current
Lean interfaces do not provide the basis-to-continuous-module transport or the
transport of the universal derived pair to internal modules in ready-to-apply form.
These are isolated as the two computation statements; no missing source declaration
is duplicated. The existing ringed-site free-matrix scalar extension theorem supplies
the ordinary free-module calculation after that basis transport.

The blueprint's latest paragraph (3) gives proper/open direct-image assembly, while
this finite-coordinate calculation is already recorded as an agent-extracted
supporting argument. This delivery preserves that distinction and the unit route.
Edge cases checked in the statement and proof plans: r=0, zero fixed subspace, empty
coordinate sets in degrees outside [0,r], and arbitrary normed coefficient fields.
No completeness, locally constant sections, or coefficient-union replacement is used.

## New nodes

`def-sfb-tame-inertia-scalar-mate-data` records the unchanged extracted definitions,
including the universal property and exact unit equation of DerivedTensor.

`lem-sfb-tame-inertia-derived-tensor-computation` records steps 1-2 and the derived
existence/computation portion of step 4 of the original argument, using the existing
internal/sectionwise equivalence, bounded-flat K-flat theorem, and normalized derived
coefficient adjunction.

`lem-sfb-tame-inertia-scalar-tensor-computation` records step 3 of that argument: in a
basis the inverse sums y_(I,j) tensor e_(I,j), and the identical E-matrices make the
map a chain isomorphism. The existing free-matrix theorem supplies its free case.
All new nodes record the actual LeanFinder, LeanSearch and grep searches run for this
item. Blueprint searches found no matching statement; the generic purity result
returned by the derived-tensor search does not state either computation.

Validation: the main module compiles without warnings in 13.3 seconds. All original
signatures and definition bodies were compared mechanically and are identical. The
delivery tool performs the final compilation and axiom checks on all four modules.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
