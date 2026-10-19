## What changed

Proved both theorem holes in `lean/Sheaf/Paper/SfRationalizationKaroubi.lean`, preserving
all existing signatures, definitions, public imports and instances. Added proof-only imports
of `Mathlib.LinearAlgebra.TensorProduct.Map`, `Mathlib.Algebra.Group.Units.Equiv` and
`Sheaf.CategoryTheory.SemilinearScalarLocalization`.

The Hom coordinates are the tensor product of the canonical coefficient equivalence and
the identity, followed by tensor commutativity. Tensor induction proves uniqueness.
The scalar extension uses the existing generic semilinear localization of the actual
completed integral scalar functor. Its semilinearity follows from the recorded intrinsic
scalar-action and integral-extension declarations. The canonical coefficient maps agree by
localization uniqueness, and tensor induction with endpoint transport proves functor
uniqueness. No new existence witness without a uniquely determining formula is introduced.

Updated the owning node's proof, proof dependencies and proof origin to describe this route.
The generic semilinear lemma is used as a tool for changing coefficient rings; the unit's
linear endofunctor localization alone does not provide this operation. Its exactness and
coherence clauses are not used. The unit record has no realized steps to bypass.

Searches run with msearch.py: LeanFinder for tensor additive equivalences, Loogle for
TensorProduct.congr, and grep for scalar-localization maps/scalar-extension uniqueness.
Direct source searches found the existing SemilinearScalarLocalization interface. The
current blueprint's raw-localization display and scalar-extension paragraph were read.

Revalidated the retained work against the current shared sources: the diff changes only
the two theorem proofs and the three proof-only imports. A fresh single-file lcompile.py
check succeeded in 22.4 seconds with no diagnostics. The import-direction check also
confirmed that the generic semilinear dependency introduces no cycle. The required delivery
dry run passed compilation and preflight (review class CODEX, because the node file changes).
No definition or statement repair or consumer adaptation is needed.

## Proved and sorry left

Closed 2 of 2 original holes:
- `WeilConjectures.sfRationalHomCoordinates_existsUnique`.
- `WeilConjectures.sfRationalScalarExtension_existsUnique`.

Both belong to `def-weil-rationalization-karoubi`. No textual sorry remains in the item;
no holes or modules were added. These are proofs from existing declared dependencies,
including their still-unproved theorems, rather than claims that the full dependency
closure is axiom-free. No split-offs.

## No longer needed

None. No imports, modules or dependency nodes were pruned. The original public imports
support the unchanged interface and remain intact. The proof reuses the generic
semilinear localization instead of introducing a second tensor-functor construction.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The owning definition node had an empty proof
plan although its Lean interface contains two theorem obligations. Its new proof records
those arguments and the generic semilinear tool that already exists in the library.
The assigned module was briefly absent during shared-tree synchronization and subsequently
became available. An initial compile-server request timed out; subsequent compiles ran.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
