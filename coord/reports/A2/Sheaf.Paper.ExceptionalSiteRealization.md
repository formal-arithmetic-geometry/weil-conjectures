## What changed

Completed both existence-and-uniqueness proofs in
`Sheaf.Paper.ExceptionalSiteRealization`, preserving every existing statement and definition.
The direct comparison is built from the recorded underlying comparison: its adjunction
transpose normalization transports addition and constant scalar multiplication through the
algebraic inverse-image graph equations. Scalar restriction gives linear maps in the fixed
quotient coordinates; sectionwise bijectivity gives the natural isomorphism and sectionwise
extensionality its uniqueness. Two proved private helpers evaluate constant sections and
compare the ring sheafification units. The inverse comparison uses the existing proved
inverse-mate equivalence lemma; its unit identity gives the full transpose equation and
uniqueness. Added proof-only imports of `WeilConjectures.CategoryTheory.InverseMateEquivalence`
and `Mathlib.CategoryTheory.Sites.CartesianMonoidal`. Updated the item's DAG proof to match.

## Proved and sorry left

Closed 2 of 2 original holes:
- `WeilConjectures.integralExceptionalSiteRight_existsUnique`.
- `WeilConjectures.integralExceptionalSiteInverse_existsUnique`.

Added 0 holes; split off 0 statements; no sorry remains in the delivered module.
The existing dependencies remain usable with their currently stated properties; the
finite realizations' equivalence instances are used by the inverse-mate theorem.

## No longer needed

None. No existing import, node, or module was removed. The original node had empty
`proof` and `proof_deps` arrays, so there was no declared proof dependency to prune.
The full unit route is preserved; its `realized` lists impose no additional node-level route.
No new module or copied generic theorem is needed: the library already proves inverse-mate
invertibility along equivalences.

## Where the brief, the DAG or earlier work was wrong

The node had no numbered proof plan despite the general brief describing one. The theorem
docstrings and the actual ordinary comparison structure give the needed proof: the
underlying comparison must be shown additive and linear using `levelTranspose`,
`moduleAdd`, `moduleSMul`, and `constants`; its section functions cannot simply be
assumed linear. The interrupted sandbox contained that argument but did not yet compile:
its constant-section adjunction target needed specifying, scalar actions needed explicit
module carriers, and one naturality equation had the reverse orientation. These are
proof elaboration repairs, with no statement or definition change.

Validation: the complete proof compiled in 24.8 seconds. A subsequent cleanup scopes
the heartbeat option directly to the theorem, explains its need, and replaces tensor
notation with its qualified name to avoid the nested-command style warning. Both
original theorem signatures were checked unchanged; the DAG changes only `proof`,
`proof_deps`, and `proof_origin`, with dependencies equal to the union of step uses.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
