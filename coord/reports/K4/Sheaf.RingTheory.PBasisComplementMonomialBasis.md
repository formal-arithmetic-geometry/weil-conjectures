## What changed

Preserved `RingTheory.pBasisComplementMonomialBasis` verbatim in its signature.
Its proof constructs `Module.Basis.mk` from new spanning and independence
components, and uses `Module.Basis.mk_apply` for the specified values. All added
imports in the original module are proof-only. No definitions were introduced.

## Proved and sorry left

Closed the original hole `RingTheory.pBasisComplementMonomialBasis` by a
**decomposition**, not a complete proof: one hole closed and two holes added
(net -1). Added named holes `RingTheory.pBasisComplementMonomialBasis_spanning`
(node `lem-weil-pbc-p-basis-complement-monomial-basis-spanning`) and
`RingTheory.pBasisComplementMonomialBasis_linearIndependent`
(node `lem-weil-pbc-p-basis-complement-monomial-basis-linearIndependent`).
These are separate necessary components of basis existence.
Their docstrings now give complete natural-language proofs and the source.

## No longer needed

Removed the unused proof import of
`Sheaf.RingTheory.PBasisComplementMonomialBasisSpanning` from the independence
module. The original node's proof no longer directly invokes
`def-weil-field` or `def-weil-pbc-free-module`: those dependencies now occur in
the component nodes. No original library module is pruned. All original public
imports remain needed for the unchanged signature.

## Where the brief, the DAG or earlier work was wrong

The first worker left incomplete component docstrings, component DAG statements
without their hypotheses, no search records, and circular proof dependencies on
the theorem they were meant to prove. The original theorem's DAG proof was not
updated. The second reader repaired these faults. The earlier report overstated
a decomposition as a proof.

## New nodes

`lem-weil-pbc-p-basis-complement-monomial-basis-spanning` records regrouping
finitely many original basis coordinates into coefficients over the complement.
`lem-weil-pbc-p-basis-complement-monomial-basis-linearIndependent` records
expanding complement-field coefficients and applying the original independence.
Each carries the complete Lean signature, hypotheses, source, proof, and actual
search results. No change record is needed: existing signatures are unchanged.

## Second reading by K4

1. Compared the main module with the repository using diff: the existing
signature is byte-for-byte unchanged; only proof and proof-only imports differ.
There are no data definitions or interface adaptations. Verdict: pass.
2. Compiled the original delivered set locally successfully. Only the two
listed named theorem holes remain. No forbidden declarations occur. The repaired set compiles. The explicit final scratch axiom probe passed for all
three declarations, each using only `propext`, `Classical.choice`, `Quot.sound`,
and `sorryAx` from the two documented component holes. Verdict: decomposition, not a closed
axiom-free proof.
3. Read both statements and their mathematical arguments. For J empty the
family has one member, 1, and the original basis shows kJ=k; for empty I this
is the prime-power field case. For a singleton J, the two statements assert
span and independence of powers of its generator. The exponent-splitting and
coefficient-expansion arguments work for arbitrary I since supports are finite.
Repeated generators cannot satisfy the original basis hypothesis. Repeated
searches using purely inseparable field and span/adjoin queries returned no
exact attachment; Mathlib separable-power lemmas have inapplicable hypotheses.
Searched the library by p-basis, bounded monomial and complement terms, and read
the original plan and related power-series declarations. Verdict: true, needed,
strictly smaller components. Neither can be closed by an immediate generic lemma.
4. The assembly uses the generic Mathlib basis constructor. Removed an unused
local family and the unused spanning import from independence. The original
node is not among sk-thm-p1's realized statements or steps, and no unit step or
route is bypassed. Verdict: pass, no library module pruned.
5. Replaced circular component proof dependencies by the underlying field and
free-module notions, supplied complete hypotheses and verbatim Lean signatures,
added actual LeanFinder, Loogle, grep searches and the unavailable LeanSearch record, and updated the original node to the two
components and basis constructor. Verdict: DAG agrees with the reduction.

Second reading changed docstrings, DAG records, search metadata, report accuracy,
and removed unused proof code/import. It did not change any theorem signature.

Source checked against the official Stacks page [Tag 07P5](https://stacks.math.columbia.edu/tag/07P5):
its coefficient-field finiteness is expanded here by the original node's bounded-monomial argument. The new arguments do not claim that the page
already supplies the explicit Lean components.

Final explicit axiom probe: compiled successfully against the sandbox artifacts;
all three declarations have only the allowed standard axioms and the documented
`sorryAx`. The temporary probe was removed from the delivery source tree.
