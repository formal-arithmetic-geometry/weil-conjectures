## What changed

The second reader rejected the original cycle subclaim: an arbitrary isomorphism f
need not be the canonical evaluation map. Replaced the new Cycles statement by
existence of canonical f,c with both identities and no invertibility claim, and
proved it using kernel lifting, boundary vanishing and cokernel descent. The proof
adapts the already proved private scheme argument of HomologyEvaluationCycleExistence
to an arbitrary small ringed site; zero source differentials simplify the last descent.
Replaced the new Iso statement by invertibility of a supplied compatible f,c. The
original target combines the proved construction with that remaining obligation.
No existing declaration signature or definition changed; no change record is needed.

## Proved and sorry left

Closed the original hole in CategoryTheory.finiteFreeZero_homologyEvaluation.
Also proved the new CategoryTheory.finiteFreeZero_homologyEvaluation_cycles
(new-v4-finite-free-zero-homology-evaluation-cycles) with no sorry.
Added exactly one hole: CategoryTheory.finiteFreeZero_homologyEvaluation_iso
(new-v4-finite-free-zero-homology-evaluation-iso), only invertibility of an already
constructed compatible map. The target still depends on this sorry. This is a
partial decomposition, not a completed proof: one original hole closed, one added,
net zero. The rejected two-hole decomposition is not delivered.

## No longer needed

No library module is pruned. All original target imports remain required by its
signature or its unchanged finiteFree_hom_preservesHomology helper. The old target
proof-dependency edges lem-sc-hom-complex-projections, def-pur-hom-complex and
def-weil-sheaf-of-modules-category are replaced by the two intermediate nodes;
they remain used in the new nodes and/or the target statement. The helper still
uses lem-sc-finite-free-internal-hom-exact, retained in target proof_deps.
The new Cycles module removes Free, FiniteFreeInternalHomExact and ExactFunctor:
its proof uses only the differential and the proved upstream MonoidalClosed API,
imported privately. The new Iso module drops ExactFunctor; finite-free exactness
remains its intended proof dependency.

## Where the brief, the DAG or earlier work was wrong

The earlier cycle subclaim is false, not strictly weaker: for degree-zero complexes
over the one-point site with ring Z and E=K=Z, both evaluation and its negative
are isomorphisms. The first identity determines c by the cycle inclusion; the
second forces f to be evaluation, so it cannot hold for the negative isomorphism.
The original search/report missed the proved scheme cycle-descent argument.
Both new nodes also had a dependency on the original target in stmt_deps, creating
a circular DAG after the target depended on them. Replaced those edges with the
actual definitions. Replaced vague statements/proofs and unsupported search claims
with self-contained statements, detailed proofs and searches actually run.

## New nodes

new-v4-finite-free-zero-homology-evaluation-cycles: canonical evaluation and descent
without finiteness, freeness or concentration; completely proved. Uses the fixed
Hom differential, upstream tensor-Hom adjunction, kernel and cokernel properties.

new-v4-finite-free-zero-homology-evaluation-iso: invertibility of a supplied map
satisfying both evaluation identities under the original finite-free hypotheses.
The complete docstring explains finite-product homology and identification with
the supplied map; this is the one remaining documented obligation.

## Second reading by K2

1. Compared the target module with the repository using diff. Existing declaration
signatures, the private helper and the original docstring are byte-for-byte unchanged.
Only new intermediate statements, private proof helpers and proof imports change.
No data definition is selected from an unproved existence statement.
2. Compiled every delivered module locally through lcompile.py; inspected all source
for forbidden declarations and sorry. The only direct sorry is the named Iso theorem.
The scratch #print axioms check shows Cycles uses only propext, Classical.choice
and Quot.sound; the original target and Iso additionally use sorryAx from the one
remaining Iso hole. The delivery probe checks every delivered declaration.
3. Rejected the false arbitrary-isomorphism cycle statement using the Z example above.
The replacement cycle construction is kernel/cokernel algebra and is proved; the
invertibility claim follows the finite-product argument. Checked zero ranks, zero
ring, degrees outside support and empty sites. Ran LeanSearch (unavailable: Internal Server Error), leanfinder, loogle and
grep with new queries; reused the existing private scheme proof rather than leaving its
construction as a new hole. The Iso obligation is only one part of the argument.
4. Canonical cycle evaluation is now proved before applying the invertibility step.
Proof-only imports are private; unused imports in the new modules are removed.
The target is below the unit level; sk-thm-picard-duality.realized (empty statement
and step lists) is unchanged and no unit route is bypassed. Old dependency edges
replaced by the construction and invertibility steps are listed above.
5. Updated target proof/proof_deps/proof_origin and both new nodes to describe the
actual reduction and the unchanged helper. New nodes have complete source, proof,
searches, creation/blueprint/Lean records and no circular stmt_deps. Their recorded
Lean statements match the new declarations verbatim.

Changed: repaired the false split, proved cycle descent, corrected DAG records and
search evidence, removed unused new-module imports, and corrected progress reporting.
