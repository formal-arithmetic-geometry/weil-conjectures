# Worker report: det-def-sfb-change-of-scalars

## Files written

- dag/nodes/sec-proetale-coefficients/det-def-sfb-change-of-scalars.json — definition, split in nine assembly steps using existing nodes; not a Mathlib leaf.
- citations.json — nineteen exact statement quotations, one for every step/node citation.
- searches.jsonl — six searches run by NI for this item, with original tool records retained.
- report.md — this report.

Zero new nodes; zero new Mathlib leaves. Nothing written to the shared repository or launcher, no git command there, no Lean written, no compiler invoked, no agents started.

## Attachments

None. The previous attachment rejection was read in the assignment. Unlike the sources available to that attempt, the present read clone contains ExtendScalars.lean and MapMod.lean; MapMod defines the inverse-scalar equivalence and comparison isomorphisms. This delivery does not infer completion of all five clauses from these partial observations and does not propose another ATTACH.

## WANTED

None. The latest blueprint and Stacks categories.tex needed here are present.

## Evidence and reuse

The prescribed abandoned-directory listing returned no matching directories. The active sandbox initially contained no item or report. I read the live item and the current blueprint/latest statement and proof, the chapter record and unit record, and the latest unit _section.md. The stored unit record is the older smooth-purity open–closed triangle, whereas the latest unit at this pro-étale path is open–closed operations on module sheaves. This scalar-change definition serves the foundational coefficient infrastructure; no unit or chapter record is edited.

Whole-DAG/blueprint searches for scalars exposed sk-def-sfb-change-of-scalars, the already reviewed parallel imported node. Its nine-step proof, reviewed for NV on 2026-10-16, is useful existing material. I reused and checked that assembly, retaining attribution in proof_origin and this report, repointed step sources to the current blueprint, and shortened the explicit finite-diagram argument. I did not copy its historical Mathlib searches into the item as searches of my own. My six new query records are exactly those in searches.jsonl. LeanFinder and LeanSearch returned ordinary ModuleCat and Rep special cases; Loogle returned internal restriction only; grep and reading Mod.lean at 350–415 confirm scalarRestriction and comap, with no internal extension/coextension there. Reading ModuleCat/ChangeOfRings.lean signatures at 400, 520, 659 and 885 confirms their narrower ambient category. A second semantic phrasing found representation internal Hom, still not the full item. Thus no whole-item Mathlib match.

## Source error

STATEMENT-DISPUTED: clause 2 calls extension right exact without assuming finite colimits exist. Stacks tag 0034, categories.tex label definition-exact, explicitly assumes all finite colimits exist in the source before using that terminology. The hypotheses here provide coequalizers, not an initial object or finite coproducts. For an explicit test, take the thin category of integers ordered by ≤, tensor addition, and unit 0. Every parallel pair is equal and has its target as coequalizer; translations preserve all existing colimits. The only monoid object is 0 (0 ≤ R and 2R ≤ R force R = 0), and its module category is the integer poset itself. It has no initial object, so it lacks the empty finite colimit, even though the identity scalar extension preserves every existing colimit. This also has closed structure [X,Y] = Y-X and equalizers, so extra closedness does not repair the existence issue. I faithfully clarified the conclusion to preservation of every existing finite colimit, hence right exactness whenever the source has finite colimits. This is exactly the clarification already accepted in sk-def-sfb-change-of-scalars; no new hypothesis is imposed on the preservation assertion.

The item also referenced det-prop-sfb-module-category, absent from the live DAG. I replaced that bracket by the existing lem-sfb-modobj-abelian, whose statement is precisely the abelianity fact used. All five substantive constructions and conclusions remain.

## Not duplicates

No new node is proposed. The parallel existing blueprint node sk-def-sfb-change-of-scalars states the same scalar-change package after the terminology clarification; it is recorded in blueprint.same_as. All smaller construction and comparison nodes are reused. The redundant direct extension/coextension comparison is composed explicitly from the two existing inverse-scalar comparisons, rather than made into another dependency.

## Review by NI

I read sections B–E of delivery-errors in full (including their repeated copy), the stage-1 brief, stage document, worker role, GOAL, and the three fixed blueprint levels in SETUP. For the item I read blueprint/latest/blueprint/sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/det-def-sfb-change-of-scalars.md and its proof file. For each module-object node cited below I read both the live DAG statement and its corresponding current .md at that same latest unit path. The only extra definitions are def-sp-abelian, read from its live statement and latest blueprint file, and def-galois-exact-functor, checked against Stacks categories.tex definition-exact (tag 0034). There are no new nodes whose sources or edge cases could be deferred.

Step 1 uses def-sfb-modobj-restriction, which actually states the action, linearity on arrows and unchanged underlying objects/maps. These give equality after forgetting. No braiding, closedness or existence hypothesis is added.

Step 2 uses def-sfb-modobj-extension. Its statement includes the displayed balanced coequalizer, multiplication on the first factor and the arrow induced by tensoring f. I checked braidedness, coequalizers, both tensor-colimit assumptions and commutativity of R against clause 2. I did not require S commutative.

Step 3 uses def-sfb-modobj-extend-restrict-adjunction for the natural Hom bijection and its unit, lem-sfb-modobj-extension-right-exact for finite-colimit preservation, lem-sfb-modobj-restriction-preserves-limits for limit preservation, and def-galois-exact-functor for the terminology. The precise natural bijection is in the adjunction node's statement; it is not borrowed from a construction node's proof. The finite-colimit-existence qualification was repaired as above.

Step 4 uses def-sfb-modobj-coextension. Its statement explicitly supplies the equalizer arrows, their evaluation transpose, the S-action by precomposition with right multiplication, and postcomposition on morphisms. I checked the order: in (s·f)(t)=f(ts), t is the first multiplication input. Currying S⊗S⊗E in its first S factor yields S⊗E→[S,N], so no exchange of tensor factors or braiding is hidden. The clause-3 hypotheses are independent of clause 2: only closedness and equalizers are needed.

Step 5 uses def-sfb-modobj-restrict-coextend-adjunction, whose statement supplies evaluation at the unit, its linearity and the inverse m↦(s↦f(sm)), and lem-sfb-modobj-restriction-preserves-colimits, whose statement gives the preservation conclusion under precisely that adjunction's hypotheses. This verifies the direction Res ⊣ Coext.

Step 6 cites both adjunction statements for the same restriction functor and lem-sfb-modobj-abelian for abelianity. I verified finite-colimit preservation of R⊗- and S⊗- from the standing tensor assumptions, ambient abelianity and tensor additivity. The lemma applies to each monoid independently and does not require S commutative. Its off-unit use is declared in split_report.tool_uses: it is the general abelianity tool explicitly requested by the source, not a replacement geometric route.

Step 7 cites def-sp-abelian for biproducts, kernels and cokernels; the two preservation nodes for preservation; and def-galois-exact-functor for exactness. I wrote the kernel/cokernel of finite sums formula and its universal-property equations, including empty sums, so existence is not silently extracted from preservation. This is an elementary argument from the stated definitions, not another missing lemma.

Step 8 uses def-sfb-modobj-restriction-equivalence, whose full statement has exactly the combined hypotheses plus invertibility and specifies the inverse restriction functor. Step 9 uses def-sfb-modobj-extension-along-iso and def-sfb-modobj-coextension-along-iso; both statements give the required natural isomorphism to inverse restriction. I inverted the latter explicitly. Their shared hypotheses were checked in step 8; no uniqueness-of-adjoints theorem is silently applied here because the actual comparison isomorphisms are already cited statements.

For all nineteen step citations, citations.json quotes the verbatim live statement, not the cited node's proof or its source metadata. Each fact taken is literally present in that quotation. Every proof dependency is in the union of step uses; no citation points back to this item. No theorem was moved into a new node or relabelled as a new clause. All nine steps are below 2000 characters (maximum 775). I kept existing import flags and other maintainer-owned metadata, set same_as, and added only split-owned fields.

Small cases checked: identity φ makes all three scalar functors identity up to the asserted comparisons; inverse φ reverses module directions correctly; a noncommutative S over a commutative R needs no central-image assumption for the S–R bimodule or induced left module. For ordinary rings, (s1·(s2·f))(t)=f((ts1)s2)=((s1s2)·f)(t), confirming the coextension action order without commutativity. Zero objects and empty finite diagrams are included in the abelian exactness argument. The integer-poset example tests the only statement correction.

## Unfinished work

None in the stage-1 split. Existing unsplit dependencies remain separate items as required. Server dry-run and delivery results follow from the required delivery commands.
