## What changed

Replaced the first worker's pointwise restatement with the genuinely smaller
`Sheaf.AlgebraicGeometry.OpenRestrictedTensorChainTransportPure` geometric calculation.
The new theorem computes the open tensor restriction square on a pure tensor using
only the actual projection stalk map and inverse restriction of the input germ.
It assumes none of the auxiliary eA, eD, q, t choices or their normalization hypotheses.
The original theorem now uses tensor induction, additivity, and all three normalization
hypotheses to recover equality of additive morphisms. Its signature is unchanged.
The new proof dependency is a plain import; the existing public import remains necessary
for the original statement. No existing definition, visibility, or statement changed.

## Proved and sorry left

- Hole closed: `AlgebraicGeometry.SingleComplexBaseChange.openRestricted_tensor_chain_transport`
  (node `lem-pc-open-restricted-tensor-chain-transport`).
- Hole added: `AlgebraicGeometry.SingleComplexBaseChange.openRestricted_tensor_chain_transport_pure`
  (node `lem-pc-open-restricted-tensor-chain-transport-pure`). Its whole proof is `by sorry`.
- This is a decomposition: one upper hole closed, one strictly smaller geometric step
  added, net zero holes. The geometric calculation is not claimed proved. No data are
  chosen and no definition is added by this delivery.

## No longer needed

Removed the first worker's unlanded Pointwise module and pointwise node entirely.
The original direct proof dependencies `lem-weil-pbc-module-stalk-pullback` and
`def-pc-open-restricted-tensor-complex-iso` are now used through the pure-tensor node;
the latter module also remains a public statement import. Neither dependency is
pruned from the import closure. No existing library import or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's pointwise statement merely evaluated the original map equality
at an arbitrary element with identical hypotheses. That is a restatement, not a
strictly smaller obligation, and its report incorrectly described it as a generator
calculation. The repair isolates the actual pure-tensor calculation from the
original node's plan and formally supplies the tensor-induction and normalization
steps. The original plan itself already described these steps correctly.

## New nodes

`lem-pc-open-restricted-tensor-chain-transport-pure` is the pure-tensor geometric
step of the original argument, sourced to Stacks Tags 0098 and 0D5U and the specified
adjunction mate unit identities. Its docstring explains the section-germ calculation
and coefficient extension. LeanSearch was attempted but returned Internal Server Error. LeanFinder, Loogle
and grep found generic germ formulas,
not this tensor-square compatibility. Existing pinned-open formulas have different
schemes and comparison maps. No change record is needed: all existing interfaces stay.

## Second reading by S2

1. Compared the original module with the repository using diff. The existing theorem
   signature and docstring are byte-for-byte unchanged; only its proof and one plain
   proof import change. No existing data, definition, statement or visibility changes.
2. Compiled both modules locally through lcompile.py and checked forbidden constructs
   and direct sorry occurrences. The only added sorry is the named pure-tensor theorem.
   Axiom probes permit only propext, Classical.choice, Quot.sound and sorryAx, the
   last accounting for the explicitly reported open geometric theorem and imports.
3. Rejected and removed the original pointwise split. Checked the replacement against
   the tensor-pullback stalk unit formula and the composition-mate definitions: it is
   precisely the pure-tensor geometric step, independent of all auxiliary coordinates.
   Empty opens supply no point z0, zero coefficients and zero input give zero by
   additivity, and zero rings/complexes and arbitrary integer degrees need no extra
   assumptions. Repeated searches with different queries; no existing declaration
   states this square formula. The new node and full natural-language proof are present.
4. The parent proof uses extensionality, TensorProduct.induction_on and coordinate
   normalization, leaving only the genuine geometric calculation open. Both imports
   are used. No library module is pruned. Read dag/units/sk-thm-picard-semicon.json:
   its realized statement and step lists are empty; this repair retains the original
   unit, source, geometric route and existing dependencies through the new node.
5. Checked proof, proof_deps and proof_origin against the implemented induction and
   the pure calculation. New node dependencies match its plan, its Lean statement is
   verbatim, and its source, searches, provenance, chapter and unit are recorded.

Second reading changed the pointwise restatement into a pure-tensor obligation and
replaced the extensionality-only wrapper by tensor induction plus normalization;
updated both nodes and corrected the progress accounting. No complete geometric
proof is claimed.
