# Stage-1 report: lem-trf-total-site-simplex-free-resolution

## Files written

- dag/nodes/sec-trace-formula/lem-trf-total-site-simplex-free-resolution.json — statement, now split into four explicit elementary calculations; Mathlib verdict: related extra-degeneracy APIs, no exact or one-line exactness declaration found.
- citations.json — the single proof citation, with its verbatim statement excerpt.
- report.md — this report. searches.jsonl is maintained by msearch.py.

No new DAG nodes and no Mathlib leaves were created. The existing statement, statement dependencies, source, creation record and blueprint ancestry are preserved. The item has no lean_audit record; project-source searches found no matching declaration to attach.

## Attachments

None. Searched WeilConjectures/ for the exact blueprint tag and for total-site, simplex, simplicial and free-resolution vocabulary. The hits concern Cech cochains, Amitsur cosimplicial modules and unrelated flat models, not this augmented standard-simplex complex. The upstream master is not used as evidence of a finished proof.

## WANTED

None.

## Corrections and source comparison

The imported item had no proof. Stacks spaces-simplicial.tex Tag 0D7C (lemma-simplicial-resolution-augmentation-modules, lines 2109–2139) reduces its module assertion to the abelian argument of Tag 0D78 (lemma-simplicial-resolution-augmentation, lines 1712–1771). I read both: the component is precisely the direct sum over monotone maps [p] to [m], with differential deleting a vertex and fold augmentation. The source invokes homotopy equivalence of the simplex; I expanded it into an explicit vertex-zero homotopy with arbitrary M coefficients. The proof_origin is agent because this writes the elementary calculation out instead of invoking the source's homotopy theorem. No flatness assertion or tensor exactness is used.

The parent lem-trf-total-site-free-module-resolution was read to check the role of this componentwise lemma. I also read the current main-20261015 lem-trf-local-term-locality proof and sk-i-curve-zero unit: the current ancestor no longer mentions the old nearby-cycle/simplex route, whereas this worker-created item's recorded ancestry still does. The split records this discrepancy without changing maintainer-owned unit metadata or rewriting historical ancestry. It supplies exactly the componentwise claim its immediate parent requests.

The statement's optional parenthetical about later use with sheaves has no role in its mathematical assertion or proof. In particular def-weil-sheaf-of-modules-category defines sheaves of modules and their category, not a constant-coefficient construction; this split makes no inference about such a construction from that node. The ordinary-module exactness claim itself needs no correction. No statement was weakened or changed.

## Mathlib and duplicate searches

Retained the item's inherited searches verbatim; they belong to its creator NE. Appended only actual Q26 msearch.py calls recorded in searches.jsonl. Used two semantic phrasings, LeanSearch, unqualified then fully qualified Loogle, and grep. All services answered. The unqualified Loogle identifier was rejected, and the fully qualified retry found CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv. I read ExtraDegeneracy.lean:238–315 and 396–438, and SimplicialSet/Homology/Basic.lean:37–100. The former constructs the simplex extra degeneracy and gives the augmentation a homotopy equivalence after passing to a preadditive simplicial object. This does not itself assert the displayed augmented complex exact: one must supply the coefficient object, identify its complex and conclude exactness. The direct summand calculation is the smaller proof here. LeanSearch's ChainComplex.augment and HomologicalComplex.acyclic_iff and LeanFinder's alternatingConst_exactAt concern general constructions or different complexes, not a one-line match.

Searched the whole DAG for Tag 0D7C and simplex-contraction/resolution vocabulary, and the whole imported blueprint with blueprint_refs.py for simplex module and augmented chain; no equivalent blueprint node was found. Read lem-weil-pbc-power-set-complex-contractible and lem-weil-pbc-free-cech-complex-exact: the former is the free module on all tuples in an arbitrary set, not the monotone-tuple complex with arbitrary M coefficients here; the latter is a presheaf Cech complex. Neither is used as if it stated this item. The 0D7C nodes are the parent resolution and total-site constructions that use this component lemma. No duplicate node is introduced.

## Unfinished work

None within this item's stage-1 split. No Lean was written and no compiler, Lake or build tool was run.

## Review by Q26

I checked B–E of delivery-errors.md against the actual item, the Stacks passages and the existing node statements. There are no new statement-only leaves to audit and no implicit lemma has been moved into a renamed copy of the item. Every proof step is under 700 characters, and each is an explicit calculation on a summand followed by linearity.

Step 1 uses only def-weil-pbc-simplicial-object. I opened its statement and checked that its delta_i is exactly the increasing injection omitting i; citations.json quotes that phrase verbatim. The cancellation pairs are indexed by original positions i<j: delete j then i, or i then j-1, yielding opposite signs. This argument remains valid if distinct deletion pairs give the same resulting tuple. The separate augmentation calculation is x-x=0.

Step 2 uses no theorem: the formula prepends 0 to a nondecreasing tuple, and 0<=alpha(0) proves it is still monotone. The hypothesis m>=0 supplies that vertex. On each M summand it is the identity followed by a summand inclusion, so it extends linearly and preserves finite support. No basis of M, projectivity, flatness, nonzero coefficient ring or finite generation has been assumed. The augmentation section is explicit.

Step 3 uses the formulas already proved in steps 1 and 2, not an uncited contraction theorem. I checked deletion position 0 separately, and shifted i+1 to i in the remaining sum, giving exactly the negative of h d. I checked degree 0 separately because it uses h_{-1} epsilon rather than an ordinary face differential.

Step 4 applies the displayed identity to an arbitrary kernel element and writes its preimage h(z); the opposite containment is the explicit d d=0 calculation of step 1. Surjectivity at M follows from the explicit section of step 2. Thus it does not invoke a homology-preservation or homotopy-implies-exactness theorem as a hidden black box.

Edge cases: for m=0 there is one simplex in every degree, so d_p is identity for positive even p and zero for odd p, with epsilon identity; the contraction identity still holds. For m=1 the edge (0,1) has boundary (1)-(0), while (0,0) has boundary zero, as the formulas require. Repeated vertices were retained throughout; no normalized-complex assumption is made. For M=0, the zero ring, and torsion M such as Z/2, the same identities hold. The proof would fail for an empty target ordinal because h_{-1} could not be defined, and the hypothesis m>=0 excludes that case. Statement dependencies were read; the sheaf category is contextual only, and no unsupported assertion from it is used. No SGA source is cited.
