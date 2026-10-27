# Stage-1 delivery: lem-trf-kprojective-denominator-initial

## Files written

- dag/nodes/sec-trace-formula/lem-trf-kprojective-denominator-initial.json: existing statement, now split into three proof steps. Mathlib verdict: no exact match for all clauses. The existing Mathlib leaf lem-coef-kprojective-derived-hom-bijection supplies the substantive input.
- citations.json: one verbatim statement quotation for each node used by each proof step.
- searches.jsonl: msearch.py's actual results, retained unchanged.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No unit, chapter or Lean file changed.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and for K-projectivity, denominator initiality and essential constancy found no project declaration giving every clause. The project extension Mathlib/Algebra/Homology/DerivedCategory/KProjective.lean only gives chain-map representatives; the required Hom-bijection itself is already a Mathlib leaf in the DAG.

## WANTED

None.

## What was wrong and what changed

The item was statement-only. Its statement is correct and remains unchanged. The source location names the general denominator-diagram setup rather than a theorem explicitly stating the unbounded K-projective conclusion; accordingly the proof is marked agent-written. Stacks Tags 05S8 and 05S9 define the denominator diagram; Categories 05PU(2) gives the essential-pro-constancy criterion. The proof of derived.tex lemma-injective-acyclic motivates the dual construction, but its bounded-below injective hypothesis is not used as an unbounded projective theorem. The actual unbounded input is the existing Mathlib Hom-bijection node.

The inherited blueprint.from path is retained, and same_as is confirmed empty. Whole-blueprint searches for K-projective, denominator, incoming quasi-isomorphisms and essentially constant did not produce another node stating this item. The already-existing Hom-bijection node is a strictly smaller input, so it is cited rather than copied into a new node. The source route through the auxiliary bounded-above-derived-computation argument under the trace-formula ancestor is unchanged.

## Unfinished work

None in the requested one-level split. No new statements await splitting.

## Not duplicates

No new nodes were created. In particular, lem-coef-kprojective-derived-hom-bijection already gives exactly the unbounded Hom-bijection input and is reused. The generic observation that an initial index supplies the common stage is proved directly in Step 3 rather than made into a redundant node or a restatement of the item.

## Review by Q85

I read the assigned chapter and unit, the item and its creating node lem-trf-bounded-above-acyclic-derived-computation (especially its Step 2), and the current main-20261015 ancestor blueprint file. This is an auxiliary categorical input below the unit, not a change of its geometric route. I read Stacks derived.tex situation-derived-functor and definition-right-derived-functor-defined, identifying them as Tags 05S8 and 05S9 from tags/tags. I read categories.tex remark-right-localization-morphisms-colimit (05Q4), definition-essentially-constant-diagram (05PU), and lemma-characterize-essentially-constant-pro (05PZ). I also read the proof of derived.tex lemma-injective-acyclic to distinguish its bounded injective special case from the actual general K-projective argument. No SGA source is used.

Step 1 uses the complete statement of lem-coef-kprojective-derived-hom-bijection, which I opened: it gives bijectivity from Hom_K(P,E) to Hom_D(Q_hP,Q_hE) for every target E, under exactly the stated definition of K-projectivity and the chosen derived-category universe. I checked its Mathlib source, DerivedCategory/KProjective.lean:43-48, and the K-projective definition in HomotopyCategory/KProjective.lean:40-44. The statement needs no bound and no projectivity of Y. The other citation, def-weil-abstract-derived-category, explicitly defines Q_h as localization at quasi-isomorphisms, so Q_h(s) is invertible by that definition. Surjectivity lifts its inverse; injectivity with target P proves the section equation; cancellation in D and injectivity with target Y prove uniqueness. These applications have the same K-projective source P throughout. They do not assume Q_h is faithful on arbitrary sources, nor that every incoming quasi-isomorphism is already an isomorphism in K.

Step 2 uses only Step 1 and the explicit arrow definition in the item's statement. A morphism from the identity denominator is exactly a section, so the proved uniqueness is the initial-object property. For u:s→s', the displayed equation s'ut_s=1 proves compatibility by that same uniqueness. The cofilteredness check is written out: the identity supplies nonemptiness and common sources, and its unique map to the source of parallel arrows equalizes them. This avoids silently relying on a definition node for a theorem about multiplicative systems. No additional non-elementary input is hidden here.

Step 3 cites def-pc-essentially-constant-pro-diagram. I opened its statement and the recorded upstream EssentiallyConstantPro.lean definition and compared both with Categories 05PU(2). All have cone legs from the value to the stages. Functoriality of F sends the compatibility equation of Step 2 to naturality of the cone. At the identity denominator the cone leg and retraction are identities. For every s the common stage is the identity denominator, with arrows the identity and t_s; the required transition factorization is displayed, with precisely that direction of arrows. Cofilteredness has already been established. No limits or colimits, small-index existence theorem, exactness of F or additive structure in its target are assumed. F is any functor to any category, as required.

I checked B–E of delivery-errors.md against the files: there are no new statement-only nodes to duplicate or leave with missing notions, no mathematical assertion deferred to a tag, no reliance on another node's proof, and no clause moved wholesale into a new node. Each cited input has a verbatim quote in citations.json, and proof_deps is exactly the union of uses. All three steps are shorter than 2000 characters. The first step is marked non-elementary because it uses the Hom-bijection theorem; the other two are short substitutions into explicit definitions using already-proved equations.

For small cases, P=0 satisfies the same argument: the zero homotopy-class section is unique even when Y is nonzero acyclic. For an acyclic complex Y not contractible, the proof never claims s is invertible in K; only its section from P exists. For s=1_P uniqueness forces t_s=1_P. For arbitrary parallel denominator arrows, precomposition with t_s gives equality, as needed for cofilteredness. No assumptions on projectives existing in the ambient category enter the proof.

I ran all newly recorded Mathlib searches through msearch.py and read the returned hits. The two semantic phrasings cover both K-projectivity and the general initial-index observation; the Loogle and grep queries found no theorem stating all clauses. The first semantic search process had already completed after a transport interruption, and its successful result is preserved in searches.jsonl; it was not rerun. Existing inherited searches are retained as provenance. No unavailable service was recorded as a negative result.
