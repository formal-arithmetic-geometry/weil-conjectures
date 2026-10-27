# Stage-1 report: lem-trf-closure-isometric-field-extension

## Files written

- dag/nodes/sec-trace-formula/lem-trf-closure-isometric-field-extension.json: item, statement unchanged, split into five proof steps.
- dag/nodes/sec-trace-formula/lem-trf-subfield-topological-closure.json: statement, Mathlib leaf (Subfield.topologicalClosure and containment/closedness lemmas).
- dag/nodes/sec-trace-formula/lem-trf-dense-isometric-ring-hom-extension.json: statement, Mathlib leaf (IsDenseInducing.extendRingHom, uniform continuity and agreement on the dense subfield).
- dag/nodes/sec-trace-formula/lem-trf-dense-closed-predicate.json: statement, Mathlib leaf (DenseRange.induction_on and DenseRange.equalizer).
- citations.json: verbatim statement excerpts for every step citation.
- searches.jsonl: results logged by the authorized Mathlib search command.

## Attachments

None. Searches of lean/WeilConjectures for the item tag and the concepts, and for the selected Mathlib declaration names, found no project declaration stating this theorem. Mathlib declarations are recorded as leaves, not project attachments.

## WANTED

None for this item: all sources used in this split are locally available Mathlib source files. I do not claim to have read Temkin's absent PDF, and use no SGA source. This generic analytic lemma was already isolated in the inherited Temkin branch; its proof is explicitly agent-written from Mathlib's extension construction.

## Corrections and limitations

The original item has no statement error. Its completion candidates are useful but do not themselves identify concrete closures. I use dense extension directly into H instead. This is below the blueprint unit and preserves the surrounding nearby-parameter route; it does not replace a unit step. I read the latest blueprint local-term statement/proof and sk-i-curve-zero unit, together with the DAG chapter/unit records and the parent nearby-parameter proof. The latest blueprint does not explicitly contain this analytic supporting lemma, so the inherited exact ancestry is retained and the extra supporting inputs are named in blueprint.from.place. The item is not the unit's key statement, so no unit record is changed.

All five non-elementary steps are below 800 characters and explicitly cite their non-elementary input. No hidden comparison of abstract completions remains. No new unsplit lemma or inline proof inside a new statement is introduced. The three new statements are genuinely weaker generic tools: one constructs a subfield closure, one extends a homomorphism without asserting an isometric bijection onto a closure, and one is dense induction with no field content.

## Not duplicates

lem-trf-subfield-topological-closure vs def-weil-relative-algebraic-closure: metric/topological closure differs from the algebraic elements of an extension; no algebraicity is assumed here.
lem-trf-dense-isometric-ring-hom-extension vs lem-sfb-normed-field-completion: the existing leaf constructs the completion and its canonical embedding, whereas the new leaf extends an arbitrary uniformly continuous homomorphism along an already specified dense isometric embedding.
lem-trf-dense-isometric-ring-hom-extension vs lem-sfb-metric-completion-isometry: the existing result only proves that the canonical completion inclusion preserves distances for a normed Q_l-vector space; it gives no ring homomorphism extension.
lem-trf-dense-isometric-ring-hom-extension vs lem-sfb-rational-group-hom-extension: that result is about rational maps of smooth group schemes, not maps of metric fields.
lem-trf-dense-closed-predicate vs lem-sfb-continuous-ae-pointwise: the latter concerns Lebesgue almost everywhere equality on Euclidean opens, not arbitrary dense subsets in metric spaces or general closed predicates.

I searched the entire DAG by key concepts and declaration names, including statements rather than only titles. I also ran blueprint_refs search for isometric, topological closure of a subfield, isometric ring, dense subset, closed predicate, uniformly continuous ring, topological field, dense isometric, and closed predicates. None supplies the three statements. The two blueprint hits for topological field are coefficient definitions, not these theorems. No Stacks tag is used by these Mathlib facts, hence there are no same-tag pairs requiring a further comparison. The original item is the only matching concrete field-closure isomorphism statement.

## Review by O4

I read the item's original source, Mathlib/Topology/MetricSpace/Completion.lean:193–214, and then the actual direct-construction sources: Mathlib/Topology/Algebra/Field.lean:48–79; Topology/Algebra/UniformRing.lean:265–293; Topology/UniformSpace/UniformEmbedding.lean around 437–478; Topology/DenseEmbedding.lean:160–167 and 359–384; and Topology/MetricSpace/Isometry.lean:129–134. These support the new leaves with the hypotheses and line numbers recorded in each mathlib_match. In particular multiplication need only be continuous, not uniformly continuous. Completeness is imposed on C, not on A or B, in the extension leaf. A metric makes C Hausdorff, so the dense-inducing extension agreement theorem applies. The extension ring homomorphism's underlying function is definitionally the same dense extension whose uniform continuity is proved by uniformContinuous_uniformly_extend; no identification lemma is missing.

Step 1 cites the closure leaf for exactly its subfield, containment and closedness clauses. The absolute-value inequalities written in the step verify the topological-field hypotheses, including inversion only away from zero. The relative ball criterion verifies density in each closure and inclusion is literally distance preserving. Restricting the operations and metrics supplies the hypotheses needed in step 2. These elementary inequalities are not separate new nodes.

Step 2 cites the extension leaf twice with C=H. The displayed calculation proves isometry and uniform continuity of f; surjectivity of f gives the same property for its inverse. Both inclusions have the dense-isometry hypotheses verified in step 1. The result actually states a uniformly continuous unital ring homomorphism and agreement on the embedded original field, so it supplies T and S without taking anything from its proof.

Step 3 uses the closed-predicate clause of the density leaf. The truth set is the inverse image of the closed target closure under the continuous extension; on the dense original subfield the map equals f or its inverse. Thus the predicate is closed and true on the required dense set, which verifies all hypotheses. Corestriction into the subfield closure preserves both ring identities and continuity by the explicit subspace-open calculation. No surjectivity is asserted at this step.

Step 4 uses the equality clause of the density leaf twice, first for a fixed original a and arbitrary y, then for arbitrary x with fixed y. The codomain is R, a metric/Hausdorff space, and continuity of distance is justified by the displayed distance inequality. This avoids silently invoking density of a product. The extension sends zero to zero because it is a unital ring homomorphism, so the distance identity at zero gives precisely the absolute-value clause.

Step 5 again uses the equality clause, now into the metric subfields. Both compositions are continuous and their restrictions are the two inverse identities of f. This gives the inverse s and hence a field isomorphism, without separately assuming its image is surjective. A competing absolute-value-preserving field isomorphism preserves differences and therefore distances, so it is continuous; it agrees with t on F, exactly the hypothesis of the cited equality clause. This proves the stipulated uniqueness among norm-preserving field isomorphisms.

I checked the statements on the trivial absolute value (discrete, every subfield already closed), F=G and f=id, the cases F or G already closed, and archimedean examples Q inside R and Q(i) inside C with conjugation. No nontriviality of the norm, nonarchimedean assumption, density in all of H, or completeness of the original subfields is used. The generic dense-predicate leaf also covers empty X (vacuous) and does not claim an empty set dense in a nonempty space. The extension leaf remains correct when A=B and i=id, when h is not isometric, and when B is incomplete. New nodes have only statements, no proofs; all Mathlib searches in their records came from msearch.py and their actual logged responses were read. Existing searches of the item are preserved, with additional searches appended. citations.json was checked against the exact statement strings. The only corrected implementation choice was eliminating the unnecessary abstract-completion range identification in favour of the direct dense construction; no mathematical statement was changed.

## Unfinished

None in the stage-1 split. Lean writing and compilation are outside the authorized scope. Delivery verification is by the required server-side dry run.

## Dry-run repair

The first preflight rejected the general density leaf because its statement cited no definition node. I read def-kun-open-neighbourhood and used it for exactly the open-neighbourhood notion in the definition of density, adding it to stmt_deps. The metric-ball formulation was replaced by the equivalent neighbourhood formulation; no theorem or hypothesis changed. The corresponding verbatim quotes in citations.json were regenerated. This is a genuine notion dependency, not an unrelated citation.
