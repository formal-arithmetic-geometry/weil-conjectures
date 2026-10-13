## What changed

Proved `AlgebraicGeometry.Scheme.exists_picardRankMatchDirectImageNormalForm` without changing its statement. Added proved private helpers for tensor-pullback rank preservation, ranks on empty schemes, rank zero of zero modules, and the homogeneous comparison. The main proof constructs the open neighbourhoods and handles homogeneous, mixed, and empty fibres explicitly.

Added proof-only imports of `Sheaf.AlgebraicGeometry.PicardFiberRankClopen` (with `import all` to reuse its private local-rank API), `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank`, and `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`. Updated the existing node's proof route to match the Lean proof.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.exists_picardRankMatchDirectImageNormalForm` (node `lem-sc-picard-rank-match-direct-image-normal-form`). No `sorry` remains in the delivered module. No holes were added, and no new intermediate statements were split off. Existing dependencies are used as supplied by the project.

## No longer needed

No original import, node, or dependency module was removed: the local-rank and stalk-rank APIs of the original proof dependencies are used. The three invalid proposed intermediate nodes and their declarations from the earlier sandbox attempt were discarded; they were never part of the library.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox's `exists_picardRankMatchDirectImage_rankCases` incorrectly asserted universal local freeness of the direct image independently of the reference predicate; its alternative forced every test over a neighbourhood containing s to be empty. For example, the identity of a point with a rank-one reference and a rank-two second bundle contradicts the earlier homogeneous comparison: the direct-image condition holds in rank two, but the reference predicate fails. The proposed classification of direct images would require local freeness even at points where cohomology jumps, without any hypothesis imposing it. The earlier helpers also were left in the item rather than separate modules and had no complete proof docstrings. All three were removed. The original module's statement and geometric proof plan need no correction.

The empty-fibre case yields the rank-zero alternative, while the mixed-fibre case yields equivalence with test-scheme emptiness. The proof covers rank zero and arbitrary, including empty and nonreduced, test schemes. The unit record has no realized node bypassed by this route.

## Second reading by K2

1. PASS: compared the sole delivered module with the repository using `diff` and
   checked the existing theorem signature and docstring byte for byte. Both are
   unchanged. All added helpers are private; the three added imports are proof-only.
   No target, public definition, or public interface was changed.
2. PASS: the module compiles without errors or warnings. Scanned its complete source:
   no `sorry`, forbidden declaration, or skipped kernel check occurs. The comparison
   isomorphism comes from the proved tensor-pullback adjunction and uniqueness of left
   adjoints, not an arbitrary witness from an unproved existence theorem. The explicit
   axiom check and delivery probe are recorded below.
3. PASS: no statements were split off and no holes were added. Read every private
   helper and the imported local-rank API. The zero-module argument uses the actual
   free module on an empty index type. Empty schemes admit every rank by the empty
   cover; a nonempty source makes the comparison rank unique. Checked homogeneous
   rank zero, differing ranks on two fibre components, empty sources, empty tests,
   and arbitrary base change. Searched the library and Mathlib with alternate terms;
   no shorter exact normal-form theorem or reusable empty/zero-rank lemma was found.
4. PASS: the target is opened and proved by its three geometric cases. Existing
   local-rank, stalk-finrank, pullback-range, and local-freeness APIs supply the actual
   argument. Each added import supplies a used API or instance; original public
   imports supply the statement. No old proof dependency is discarded, so
   `## No longer needed` is complete. The unit `sk-prop-av-cube` has empty realized
   statement and step lists; this below-unit proof bypasses no realized node.
5. PASS: checked the node alongside the complete Lean proof and its dependency
   declarations. Only `proof` and `proof_origin` differ from the repository node;
   `proof_deps` equals the union of the steps' uses and retains the three used nodes.
   There are no new nodes or change records to audit.

Second reading changed only this report: the proof and node required no repair.
Closed one original hole, `AlgebraicGeometry.Scheme.exists_picardRankMatchDirectImageNormalForm`;
added zero holes and split off zero statements. This is a proof, not a decomposition.

Axiom evidence: a scratch copy with `#print axioms
AlgebraicGeometry.Scheme.exists_picardRankMatchDirectImageNormalForm` compiled and
reported exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
The delivery tool also checks the axioms of every delivered declaration.
