# Stage-1 delivery: lem-sfb-derived-pullback-tensor-comparison-iso

## Files written

- dag/nodes/sec-six-functors/lem-sfb-derived-pullback-tensor-comparison-iso.json — statement, split; the given comparison is invertible by constructing its reverse universal comparison. No new nodes and no Mathlib leaves.
- citations.json — verbatim statement extracts for both step citations.
- report.md — this report. searches.jsonl is the unmodified search-command log; prepare.py is the sandbox-only preparation script.

## Attachments

None. I searched lean/WeilConjectures by the blueprint id and by derived-tensor/pullback names. AlgebraicGeometry.ProEtale.CondensedRing.isIso_leftDerivedUpperStarTensor in WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/Monoidal.lean:278 has proof `sorry`. The generic CategoryTheory.Functor.isIso_leftDerivedTensorComparison at WeilConjectures/CategoryTheory/DerivedCategory/LeftDerivedFunctor/Monoidal.lean:254 is proved, but its transformation is not definitionally the item's specified comparison. The equality theorem in lean/Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/Monoidal.lean:505 uses the still-sorried isLeftDerivedFunctor₂_upperStarTensor. Thus these findings do not justify ATTACH.

## Literature wanted

None. No document was downloaded. The proof is marked agent-written: it is a formal universal-property deduction from two existing reviewed DAG statements, not a claim that Bhatt–Scholze states this comparison theorem verbatim.

## What needed repair

The item had an empty proof. Its statement is correct and unchanged. The original source is the statement-only main-20261015 blueprint file sk-prop-proper-image-localizing-open.md; that text does not contain a proof of this generic monoidality input. I read that file, the chapter and unit records, the main-20261015 lem-sfb-derived-monoidal.proof.md, and the relevant project Lean source and docstrings. The imported attribution to det-proper-image-localizing-open is retained, without inventing a source paragraph or changing the unit route.

A whole-DAG search found the already reviewed new-proetale-derived-module-pullback-monoidal, which explicitly states both counits and both two-variable derived properties, and lem-sfb-multivariable-derived-calculus, which explicitly states the natural-transformation bijection and uniqueness. Reusing them avoids new nodes for properties already present. The proof does not need to cite or re-prove the K-flat hypotheses hidden in the upstream docstring: the first existing node's statement supplies their resulting derived properties for precisely these module categories.

## Mathlib searches

The item's inherited maintainer searches are retained. All appended Q65 searches were run through the required msearch.py command and are recorded verbatim in searches.jsonl and mathlib_searches. LeanFinder was tried with two distinct phrasings. Its first results concern light condensed internal projectivity and its second concern exact derived-category maps, degreewise Tor and Ext. The grep found Tor.lean:45–53, which I read: those definitions are homology-valued Tor in a monoidal abelian category with projective resolutions. They do not give this unbounded module-object pullback comparison. LeanSearch and the corrected unary Loogle query found generic left-derived uniqueness; I read Mathlib/CategoryTheory/Functor/Derived/LeftDerived.lean:50–145. This does not itself provide the two derived bifunctors and the match of their actual tensor counits. The first Loogle query's unknown two-variable identifier is recorded as such, not as a successful theorem search. The item is therefore not a Mathlib leaf.

## Not duplicates

No new nodes were created. In particular, the overlap with new-proetale-derived-module-pullback-monoidal is resolved by citing that existing node. Searches included the whole DAG and tools/blueprint_refs.py search for “monoidal pullback” and “tensor comparison”; no imported blueprint node states the same universal module-object comparison. The item retains blueprint.same_as = []. The ancestor command returns None for this maintainer-created item because created.item is null; I retain its existing explicit blueprint.from.node = det-proper-image-localizing-open and create no descendant requiring an inferred ancestor.

## Review by Q65

I checked the statement against the actual condensed-module Monoidal.lean construction. The ring is an arbitrary commutative condensed ring, the schemes and morphism are arbitrary, and both sides use unbounded internal-module derived categories and their relative tensors. There is no finite coefficient, constructibility, smoothness or boundedness assumption. The comparison has the direction LF(K tensor L) to LFK tensor LFL.

For step 1 I opened new-proetale-derived-module-pullback-monoidal.json and read its entire statement and proof. Its categories are exactly Mod over p_T^*Lambda; its F is the complete extension-after-mapMod pullback, not the abelian-sheaf functor or a derived composite of its factors. Its displayed r is Q of the ordinary tensorator after the localization tensorator after the two derived counits. Its displayed l is the derived counit after LF of the source localization tensorator. I compared these formulas with leftDerivedUpperStarTensorRightCounit and leftDerivedUpperStarTensorLeftCounit in the project's source. They have the same order and target H(A,B)=Q_X(F_h(A tensor B)). The cited sentence explicitly says that both pairs are total left derived bifunctors; I use that sentence, rather than the proof of the node or merely a definition. This existing result has no extra hypotheses, and its reviewed split already treats preservation of actual K-flat complexes.

For step 2 I opened lem-sfb-multivariable-derived-calculus.json, read its entire statement and checked the n=2 universal-property clause. Only its natural-transformation bijection and injectivity are used; the proof does not assert the candidate criterion without checking prerequisites. Those prerequisites have already been discharged by the derived-property assertions in step 1. For (S,l) the transformation r supplies n:R to S with l(nq)=r. The comparison in the item satisfies r(mq)=l. I checked both composites with their correct counits: l((nm)q)=l and r((mn)q)=r. Injectivity for the appropriate target makes them identities, so neither cancellation of a possibly noninvertible counit nor a circular use of the desired theorem occurs.

Step 3 only evaluates these two natural-transformation identities at arbitrary K,L, giving two-sided component inverses. This is elementary and uses no uncited structural theorem. Every cited node has an exact verbatim sentence in citations.json. Both off-unit citations are declared as generic tools in split_report.tool_uses; they implement the inherited projection-formula monoidality input and do not change any unit or chapter statement.

I checked the delivery-error categories B–E: the only node written is the original item; there are no unstated new notions, new unsplit proofs, invented tags, duplicate new lemmas or displaced item clauses. I checked the entire dependency closure of the first tool (506 nodes) and found no path back to the item. The identity scheme morphism gives the identity comparison; zero objects and the zero coefficient ring give the same inverse equations in the zero case. The universal-property argument is independent of bounds and applies to unbounded inputs. No step exceeds 2000 characters. There is no statement dispute, no source from the prohibited SGA route, no Lean edit, and no compiler or build invocation.

## Unfinished work

None in this stage-1 item. The cited existing nodes remain responsible for their own downstream formalization. The required remote dry run and push are performed by deliver.py after this report is written.
