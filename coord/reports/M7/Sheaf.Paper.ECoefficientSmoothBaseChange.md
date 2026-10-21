## What changed

Completed both proofs in `Sheaf.Paper.ECoefficientSmoothBaseChange`, preserving every
existing public signature, definition body, and public import. The global-to-stalk
unit lemma maps units through global sections and germs. The main theorem applies the
existing adic smooth-base-change theorem to the given lattice, localizes its integral
exchange, and uses naturality for transport and lattice independence.

Proved private comparison helpers identify the function-ring, constant-ring, and
fixed-scalar coefficient presentations. They compare both finite derived operations
with the witness operations, transfer intrinsic constructibility and vanishing in the
same interval, and supply the conditional constructible endpoint representation.
The endpoint equation follows from the pure-tensor localization formula and naturality.
No definition, consumer, or target statement was changed.

Updated the existing DAG node's proof, proof dependencies, and proof origin to describe
this argument. All added imports are private proof imports. The five new instance declarations
are private local instances, so they do not add instance registrations to importers.
The two transparency options are file-local and placed after all existing public
definitions. Preflight requested a command-context record:
`coord/changes/M7-sbc-private-proof-environment.md`.

Validation: `lcompile.py` compiled the completed proof cleanly, with no warnings.
After making the five instance declarations local, it compiled cleanly in 19.4 seconds. Direct comparison confirms the original theorem signatures, all six
existing definition bodies, and public imports are unchanged. The updated node has
no dependency cycle, and its proof-dependency list is exactly the union of step uses.

## Proved and sorry left

Closed 2 of the original 2 holes:

- `WeilConjectures.sbcPrimeUnitOnSource`.
- `WeilConjectures.eCoefficientSmoothBaseChange`.

No `sorry` remains in the item, and no holes or admitted intermediate statements were
added. The main proof uses the already declared `WeilConjectures.adicSmoothBaseChange`;
its separate unfinished proof remains the existing downstream item. Every new private
helper in this delivery is fully proved.

## No longer needed

Removed these original private imports:

- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`.
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`.
- `Sheaf.CategoryTheory.ScalarLocalization`.
- `Sheaf.Paper.IntegralUniformCoefficient`.
- `Sheaf.Paper.PbcRationalCategory`.

The scalar-localization and rational-category interfaces remain available through the
unchanged public imports. The other removed imports are not used directly by this proof.
No source-library declaration or module is withdrawn.

Removed direct proof dependencies `lem-weil-valued-dvr-finite-quotients` and
`def-pc-perfect-ring-complex`. The coefficient datum already supplies finiteness and
perfection; only the invertibility of quotient cardinalities needed a fresh argument.
Annihilation by a power of l and Mathlib's finite l-group cardinality theorem suffice,
so the precise residue-field cardinality and quotient-filtration count are unnecessary.
These removals concern this node's direct route and do not assert that those modules
are unreachable from every other target or dependency.

Removed the following obsolete direct tool approvals from this node; the adic
theorem retains its own downstream route:

- `lem-weil-valued-dvr-finite-quotients`.
- `prop-weil-pbc-direct-image-limits`.
- `lemma-weil-pbc-completed-pullback-reduction`.
- `lem-weil-pbc-constant-completion-equivalence`.
- `lem-weil-pbc-normalized-constructible-local-effectivity`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `thm-weil-pbc-site-comparison`.

## Where the brief, the DAG or earlier work was wrong

The final proof step calls the interval hypotheses "exactly" the same, but the existing
Lean statements use different coefficient presentations and different finite-operation
functors. The delivery proves the required equivalences and cohomology comparisons,
including reflection of zero objects, rather than treating those expressions as equal.
The arithmetic plan also proves more than the adic theorem needs: an unspecified power
of l for the quotient cardinality is enough. The unit route and all four conclusions
are retained unchanged. Preflight identified the original finite-level site-comparison
import as a required unit-route import; it is retained even though the main proof
accesses finite-level base change through the adic theorem.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
