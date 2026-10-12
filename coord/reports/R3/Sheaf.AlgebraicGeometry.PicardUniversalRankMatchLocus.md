## What changed

Completed the target assembly proof and reduced the structural conjunct theorem to two
strictly smaller named obligations. The structural theorem now pairs the locally finite
presentation and quasi-compactness lemmas; the target then applies the core theorem and
assembles all fields.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.picardUniversalRankMatchLocus_structural` by a real Lean
proof from the two conjunct theorems. The target
`AlgebraicGeometry.Scheme.exists_picardUniversalRankMatchLocus` remains fully proved.

Two strictly smaller named holes remain:

- `AlgebraicGeometry.Scheme.picardUniversalRankMatchLocus_locallyOfFinitePresentation`,
  node `lem-sc-picard-universal-rank-match-locus-lfp`.
- `AlgebraicGeometry.Scheme.picardUniversalRankMatchLocus_quasiCompact`,
  node `lem-sc-picard-universal-rank-match-locus-qc`.

## No longer needed

No imports were pruned. The core theorem and all public imports remain required by the target
signatures or proof route.

## Where the brief, the DAG or earlier work was wrong

The original structural hole bundled two independent conclusions. Splitting it into its
locally finite presentation and quasi-compact conjuncts gives strictly smaller obligations
while preserving the exact existing interfaces and target statement.

## New nodes

Added `lem-sc-picard-universal-rank-match-locus-lfp` and
`lem-sc-picard-universal-rank-match-locus-qc`, each matching one conjunct and its dedicated
module. Updated the structural node's proof and dependencies to use both.

## Earlier second reading (a previous round; superseded)

Compiled all four sandbox modules with lcompile.py. The structural proof is a direct pair of
the two strictly smaller conjunct statements, and the target proof applies the core theorem and
structural theorem without changing any target signature. The two remaining sorry declarations
are named public intermediate results with matching nodes and complete proof descriptions.

## Second reading by R3

1. **Interfaces and accidental changes.** I compared the delivered target module with the
repository version. The existing declaration signatures, including the target, are byte-for-byte
unchanged. The only interface additions are the two explicitly split intermediate declarations,
and their matching node files.

2. **Compilation and proof status.** All four sandbox modules compile with `lcompile.py --all`.
There are no axioms, unsafe declarations, or sorries in definitions. The structural theorem is a
real pair of the two named conjunct theorems; the target is then assembled from the core theorem
and that structural result. The two remaining sorries are exactly the named split obligations.

3. **Truth and strength of split statements.** The locally-finite-presentation and quasi-compact
statements are precisely the two conjuncts of the existing structural statement, with identical
hypotheses and conclusion strength. Their docstrings and node proof steps record the rank-locus,
fibre-product, gluing, and finiteness arguments from Tag 0BDP. Neither duplicates an existing
library declaration.

4. **Pruning and route.** The unit route is preserved: the core representing immersion is still
used by the target, and the structural node now uses both strict conjunct nodes. I removed the
unused `PicardUniversalRankMatchLocusCore` imports from the two split-off modules; all remaining
imports are needed by their public signatures or by the target proof.

5. **DAG agreement.** The structural node's proof and `proof_deps` now match the Lean pair proof.
The two new nodes match their declarations, include source and proof routes, and are marked split.
No target or definition was changed.

The second reading therefore found no statement fault. Changes made were limited to the two
unused-import removals, fuller proof-route documentation for the split obligations, and this report.
