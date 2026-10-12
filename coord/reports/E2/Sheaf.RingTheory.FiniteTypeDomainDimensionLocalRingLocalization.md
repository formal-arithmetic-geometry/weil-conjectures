## What changed

Replaced the target sorry in
`lean/Sheaf/RingTheory/FiniteTypeDomainDimensionLocalRingLocalization.lean`
with the final dimension inference of Stacks Project, Algebra, Tag 00OS:
use `finiteTypeDomain_ringKrullDim_localizationAtMaximal_chains`, choose a
prime chain realizing the height of the maximal ideal, prove it saturated
and maximal, and identify its length with the common dimension. The target
signature and its three public imports are unchanged. The polynomial results
are now used through the sibling chain theorem rather than directly.

The repaired first-worker version proves saturation and maximality as local
facts inside the target proof, without duplicate private declarations.
The second reading preserves this proof and corrects the pruning report and
DAG's stale reference to private helpers.

## Proved and sorry left

Closed one original hole:
`finiteTypeDomain_ringKrullDim_localizationAtMaximal_localization`
(node `lem-weil-pbc-finite-type-domain-dimension-local-ring-localization`).
There are no remaining sorry declarations in the delivered module, and zero
holes or split-off statements were added. This is one hole closed, not a
new decomposition. The existing chain theorem is proved in the current source
but its compiled import closure still has open dependencies: the target and
chain theorem both print `[propext, sorryAx, Classical.choice, Quot.sound]`.
Thus the target body is proved, but its transitive proof is not yet closed.

## No longer needed

Removed direct proof imports:

- `Sheaf.RingTheory.PolynomialRingMaximalChainHeightDifference`
- `Sheaf.RingTheory.PolynomialRingMaximalLocalizationDimension`

Added proof imports `Mathlib.RingTheory.Ideal.Height` and
`Sheaf.RingTheory.FiniteTypeDomainDimensionLocalRingChains`.
The new proof does not directly use these seven old proof dependencies:

- `def-weil-pbc-finite-type-algebra`
- `def-weil-pbc-mv-polynomial-ring`
- `lem-weil-pbc-proper-ideal-contained-in-maximal`
- `def-weil-pbc-localization-at-prime`
- `def-weil-pbc-krull-dimension-ring`
- `lem-weil-pbc-polynomial-ring-maximal-localization-dimension`
- `lem-weil-pbc-polynomial-ring-maximal-chain-height-difference`

The three definition nodes remain statement dependencies where appropriate;
the polynomial results remain transitive dependencies of the chain theorem.
No claim is made that either polynomial module leaves the target closure.
The retained old proof dependency is
`lem-weil-pbc-localization-dimension-chains-below-prime`, a Mathlib leaf;
the added proof dependency is
`lem-weil-pbc-finite-type-domain-dimension-local-ring-chains`.
The former duplicate helper names `saturated_isMaxChain` and
`saturated_of_full_height` are absent from the delivery's declaration table.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery duplicated private helper statements from
`Sheaf.RingTheory.PolynomialRingMaximalChainHeightDifference`; the repaired
version uses local facts instead. The previous report incorrectly said no
imports or dependencies were removed and called the sibling chain theorem
itself holed. The second reader corrected these claims against the repository
and axiom output. The DAG also incorrectly called the local facts private
helpers; its proof text now matches the delivered Lean.

## Second reading by E2

1. Compared the only delivered Lean module with the repository by diff and
   checked the entire theorem signature byte for byte: unchanged, including
   both universes, the field, commutative ring, algebra, finite-type and domain
   hypotheses, the arbitrary maximal ideal and the equality conclusion.
   No definitions or other declarations were added or altered; no interface
   change record is needed. Read the statement and proof of
   [Stacks Tag 00OS](https://stacks.math.columbia.edu/tag/00OS): the Lean
   assertion is precisely its localization-dimension equality.
2. Compiled the module and a fresh scratch copy containing `#print axioms`.
   Compilation succeeds without warnings; no sorry or forbidden declaration
   occurs in the delivered file. The axiom list contains only propext,
   Classical.choice, Quot.sound and sorryAx from existing imports. Existential
   chain selection occurs inside a propositional proof, not in a definition
   choosing arbitrary data.
3. No split-off statement or node is added. Read the local saturation argument:
   the height-index theorem makes an intermediate prime force an impossible
   two-step increase between consecutive indices. Read the maximality argument:
   an extra element comparable with the chain must lie strictly above its head;
   induction with covers forces it above its last, contradicting maximality.
   For dimension zero the chain has one term, the cover condition is empty,
   and head/last extremality gives the same conclusion. A field is included;
   a zero ring is excluded by the original domain hypothesis.
4. Searched Mathlib and both library roots for finite-type localization
   dimension results and chain tools. Loogle query `IsMaxChain, LTSeries`
   returned no hit; LeanFinder's query about saturated finite chains returned
   `IsMaxChain.range_fin_of_covBy`, which requires a bounded ambient order
   and a top endpoint, absent for the full prime spectrum. The existing
   generic helpers in the polynomial module are private; the present short
   local arguments avoid adding library duplicates. Read Mathlib's
   `Ideal.exists_ltSeries_length_eq_height` and
   `Order.height_eq_index_of_length_eq_height_last` against their actual types.
   The imports needed only by proofs are plain imports. The pruning list now
   includes every old proof dependency not used directly. Checked
   `dag/units/sk-thm-p1.json`: this node is below the realized statement and
   steps, and the chain theorem retains the polynomial route of Tag 00OS;
   no realized unit step is bypassed or changed.
5. Compared the node JSON with the repository. Only proof, proof_deps and
   proof_origin differ. The proof_deps are exactly the union of step uses:
   the sibling chain theorem and the localization-height Mathlib leaf. The
   statement, statement dependencies, Lean signature, chapter and unit stay
   fixed. Corrected the second proof step to describe local facts rather than
   private helper declarations. No new node or change record is required.

Second-reading changes: corrected stale metadata and the incomplete pruning
report; the compiled Lean proof was retained unchanged.
