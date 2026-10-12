## What changed

Proved `PrimeSpectrum.connectedSpace_zeroLocus_sup_of_henselian` with its existing
signature unchanged. The proof obtains the henselian structure on A/p from the
existing `henselianRing_of_isIntegral`, applies the proved domain lemma, and takes
a continuous image using Mathlib's quotient zero-locus identity.

Added `Sheaf.RingTheory.HenselianPairDomainConnected` with the proved theorem
`PrimeSpectrum.connectedSpace_zeroLocus_of_henselian_domain`. Its proof uses
simple-root lifting for X(X - 1), the proved upstream
`PrimeSpectrum.connectedSpace_of_isIdempotentElem`, and Mathlib's quotient image
identity. The two proof imports of the new module are plain `import`; its public
imports are precisely the signature's henselian predicate and spectrum topology.
The item adds only a plain proof import of the domain module.

Updated the item's DAG proof and dependencies and completed the domain node.
No definitions, instances or existing declaration signatures changed.

## Proved and sorry left

Closed the original item hole:
`PrimeSpectrum.connectedSpace_zeroLocus_sup_of_henselian`
(node `lem-weil-pbc-henselian-pair-prime-connected`). One of one original holes
closed; zero new holes added.

Also proved the new domain theorem
`PrimeSpectrum.connectedSpace_zeroLocus_of_henselian_domain`
(node `lem-weil-pbc-henselian-pair-prime-connected-domain`). There is no `sorry`
in either delivered module and no statement left split off with `sorry`.

The target still transitively depends on the existing, unmodified
`henselianRing_of_isIntegral` in `Sheaf.RingTheory.IntegralOverHenselianPair`
(node `lem-weil-pbc-integral-over-henselian-pair`). Accordingly `#print axioms`
shows `sorryAx` as well as the three standard axioms for the target; the domain
lemma shows only `propext`, `Classical.choice`, `Quot.sound`. This delivery closes
the item hole, but does not claim that the target is axiom-free.

Relative to the first worker's proposal, closed the domain hole and removed the
quotient-reduction hole by writing that argument directly in the target.

## No longer needed

No imports of the repository version were removed; no library module is claimed
pruned. Removed the proposed, never-landed
`Sheaf.RingTheory.HenselianPairPrimeConnectedReduction` and its reduction node
`lem-weil-pbc-henselian-pair-prime-connected-reduction`.

Old direct proof dependencies absent from the new item's `proof_deps`:
- `lem-weil-pbc-spec-quotient-closed-immersion`: the stronger scheme closed-immersion
  result is unnecessary; Mathlib's image-comap zero-locus identity suffices.
- `def-weil-pbc-henselian-terminology`: used inside the domain lemma and already
  incorporated in the integral-henselian theorem, rather than as a direct step.
- `lem-weil-pbc-spec-clopen-idempotent`: used through the proved upstream criterion
  in the domain lemma, rather than directly in the prime-case theorem.

These latter two nodes remain dependencies of the new domain node. The original
`def-weil-affine-spectrum`, `def-weil-connected-scheme`, and
`lem-weil-pbc-integral-over-henselian-pair` dependencies remain.

## Where the brief, the DAG or earlier work was wrong

The first proposal closed one upper hole by introducing two lower holes, and did
not update the item's DAG node. That was a decomposition, not a net proof gain.
Both lower arguments can be implemented using existing APIs. The domain argument
needs only simple-root lifting in B itself, not the full finite-algebra idempotent
lifting theorem. Properness follows directly from the Jacobson field of
`HenselianRing`. The prime-case transport needs only the continuous-image identity,
not a new quotient-spectrum homeomorphism theorem.

## New nodes

`lem-weil-pbc-henselian-pair-prime-connected-domain`, proved in
`Sheaf.RingTheory.HenselianPairDomainConnected`; no new sorry node remains.

## Second reading by P3

1. Compared the delivered target module with the repository using `diff` and
   checked the existing theorem signature byte for byte up to its proof delimiter:
   unchanged. Public imports and visibility of the existing file are unchanged.
   No definitions or data constructions were added or modified. PASS.
2. Compiled both modules locally in import order through `lcompile.py`, with no
   errors or warnings. No forbidden declarations or `sorry` occur in the delivered
   Lean. Compiled scratch copies with `#print axioms`: domain theorem uses only the
   three standard axioms; target additionally uses `sorryAx` from the existing
   integral-henselian dependency. No arbitrary witness is chosen from an unproved
   existence theorem. PASS with this explicit transitive limitation.
3. Checked both proposed split statements mathematically and then discharged them.
   The sole retained new theorem is strictly the domain case. J=top is excluded by
   the Jacobson condition and nontriviality; J=bottom gives the usual connected
   spectrum of a domain; fields and characteristic 2 satisfy the argument (the
   derivative square is still 1). For I=bottom and p=zero the quotient image
   identities remain valid, and a zero source ring has no prime ideal. Searched
   via Loogle, Lean Finder, msearch grep and local rg with alternative wording;
   LeanSearch was unavailable (Internal Server Error). Reused the upstream generic
   connected-spectrum criterion rather than duplicating it. PASS.
4. Followed the target downward, using the existing integral-henselian theorem,
   Mathlib quotient identities and the shorter polynomial lifting argument.
   Removed the unproved transport helper and its module. Listed every removed old
   proof dependency above. Read `dag/units/sk-thm-p1.json`: this item is below its
   realized unit statements and steps; none of that route is bypassed. Proof-only
   imports are plain imports and the new module's imports were minimized. PASS.
5. Rewrote the original node's `proof`, `proof_deps`, and `proof_origin` to match
   the actual argument. The new domain node has its full signature, source,
   searched alternatives and explicit proof steps; `proof_deps` equals the union
   of their uses. Removed the redundant reduction node. PASS.

Changed in this reading: proved the domain case; inlined and proved quotient
transport; renamed the new module to HenselianPairDomainConnected; removed both
proposed sorries, the redundant helper and its node; corrected docstrings, DAG
metadata and the report. Source checked against
[Stacks Tag 09Y6](https://stacks.math.columbia.edu/tag/09Y6).
