## What changed

`Sheaf.RingTheory.QuasiFiniteFourRings` now proves
`Algebra.finiteType_and_isQuasiFiniteAtPrime_of_four_rings` completely, with its original
signature unchanged. The finite-generator proof from the first worker is retained.
The second reader closes the quasi-finiteness remainder using Mathlib's
`Algebra.QuasiFiniteAt.baseChange` and `Algebra.QuasiFiniteAt.of_surjectiveOnStalks`.
The canonical fibre-spectrum homeomorphisms and
`Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber` bridge the project's predicate in both
directions. The tensor map is constructed, and its surjectivity and the contraction of its
prime are proved explicitly.

The proof-only import `Sheaf.RingTheory.IsolatedPrimeResidueFinite` is replaced by the
proof-only import `Mathlib.RingTheory.ZariskisMainTheorem`. Both existing public imports
are needed by the signature and are unchanged. The draft's split-off core module and its
new node have been removed from the delivery. No change record is needed.

## Proved and sorry left

Hole closed: `Algebra.finiteType_and_isQuasiFiniteAtPrime_of_four_rings`, node
`lem-weil-pbc-quasi-finite-four-rings`. One of one original holes closed; zero holes added;
no `sorry` remains in the delivered module. The draft's
`Algebra.isQuasiFiniteAtPrime_of_four_rings_of_finiteType` was proved experimentally, then
its proof was integrated into the existing declaration; it is not delivered as a new theorem.
This delivery is a complete proof, not a decomposition. The scratch `#print axioms` check
reports only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed proof import: `Sheaf.RingTheory.IsolatedPrimeResidueFinite`. The following old
`proof_deps` are no longer used by this proof (global reachability is the maintainer's ledger):

- `def-weil-pbc-localization-at-prime`
- `lem-weil-pbc-isolated-prime-finite-type-algebra-residue-finite`
- `lem-weil-pbc-spec-clopen-idempotent`
- `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`
- `lem-weil-pbc-finite-type-algebra-dim-zero-finite`
- `def-weil-affine-spectrum`
- `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`

The finite-type definition, quasi-finiteness definition, fibre-prime correspondence, and
tensor universal property remain on the actual proof route. No unit-level node was bypassed.
The draft's `Sheaf.RingTheory.QuasiFiniteFourRingsCore` and
`lem-weil-pbc-quasi-finite-four-rings-core` are also removed; they never entered the repository.

## Where the brief, the DAG or earlier work was wrong

The first draft left the entire quasi-finiteness transfer as a new hole and described the
semilinear map from the source fibre ring to the target fibre ring as surjective. Only its
scalar extension is necessarily surjective (a proper field extension already distinguishes
these maps). The final proof avoids that claim and proves surjectivity of the original
base-change tensor map directly. The Mathlib route listed among the original node's
candidates works after bridging `IsQuasiFiniteAtPrime` with `QuasiFiniteAt`; the bridge is
already used in the library's `ZariskisMainAway` proof. The target node's proof and
`proof_deps` now record this route.

## Second reading by S2

1. Compared the delivered module against the repository with `diff`, and compared the
   existing theorem's complete signature byte for byte. Verdict: unchanged. No definitions,
   target statements, or public import visibility changed; no forced adaptations.
2. Compiled the original draft's two modules and then the final single module locally
   through `lcompile.py`. Verdict: clean compilation, no holes or forbidden declarations.
   A scratch copy with `#print axioms` confirms exactly the three permitted axioms.
3. Reviewed the proposed split against Stacks Tag 00PN, including the local copy of
   `algebra.tex` at `lemma-four-rings`. Identity squares, zero rings (vacuous prime condition),
   quotient squares, and residue-field extensions cause no missing hypotheses. Searched
   with fresh Lean Finder and Loogle queries, and searched Mathlib and both Lean roots with
   `rg`; read the base-change and surjective-on-stalks lemmas and the isolated-fibre bridge.
   Verdict: the proposed remainder is true but can be proved by existing Mathlib results;
   no split-off statement or new node remains in the delivery.
4. Checked the route from the top downward and the actual imports. Verdict: finite type
   is constructed directly, and quasi-finiteness follows by base change and quotient
   permanence in Mathlib. All removed old proof dependencies are listed above.
   `dag/units/sk-thm-p1.json` realizes this unit with other nodes; this auxiliary ring lemma
   is below the unit level, and no realized statement or step is changed or bypassed.
5. Compared the node with the final Lean proof. Verdict: `proof`, `proof_deps`, and
   `proof_origin` describe the finite-generation construction, both canonical predicate
   conversions, tensor surjectivity, contraction compatibility, and the two Mathlib
   permanence applications. Existing statement and all non-stage-3 fields are unchanged.

Changed in this reading: closed the fibre remainder, removed the core split and new node,
replaced its import with a proof-only Mathlib import, kept tensor notation local by using
fully qualified tensor constructors in the proof, updated the proof docstring and DAG
route, and rewrote the report to state the complete proof and precise pruning.
