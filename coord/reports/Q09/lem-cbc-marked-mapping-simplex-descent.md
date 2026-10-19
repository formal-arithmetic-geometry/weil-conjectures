# Worker report: lem-cbc-marked-mapping-simplex-descent

## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-marked-mapping-simplex-descent.json: statement, stage-2 Lean record, ancestry and existing proof route retained. Former step 8 is replaced by steps 8–10; former steps 9–10 become 11–12 with their internal references renumbered. All other proof texts remain unchanged.
- dag/nodes/sec-smooth-purity/lem-cbc-marked-homotopy-precomposition.json: one new statement-only lemma, status unsplit, no Mathlib match. It isolates parameterized composition of marked homotopies, including its endpoints and sharp components, for arbitrary marked objects over a simplicial base.
- citations.json: one verbatim statement quotation per step/node citation. Full statements are quoted to retain all hypotheses and avoid misleading extracts.
- searches.jsonl: actual msearch results, retained as emitted; seven searches for the new lemma (two LeanFinder phrasings, Loogle, LeanSearch and three source greps).

## Attachments

None. Searched the project declaration tag and marked/homotopy/precomposition terminology under /home/ubuntu/weil-src-slopmaster2/WeilConjectures. No declaration of this marked relative construction or of the whole item appeared. The item's existing stage-2 record is retained, not treated as a finished proof.

## WANTED

WANTED: project-local archive of Jacob Lurie, Higher Topos Theory, Section 3.1.3 and Proposition 3.2.2.8, for lem-cbc-marked-mapping-simplex-descent and lem-cbc-marked-homotopy-precomposition. I read the IAS PDF over HTTP using an in-memory pdftotext extraction (printed pp. 153–157 and 180–181), without writing to literature. The Harvard mirror was discovered online but a direct request was forbidden; the IAS request with a browser user agent succeeded. Kerodon Theorem 4.4.4.4 (Tag 01DK) was read online for the existing pointwise criterion. No SGA source is used. There is no matching Stacks tag for this marked simplicial construction.

## Return repaired

The human return identifies former step 8 (2033 characters) as non-elementary and asks for every hidden argument to be exposed as a cited lemma, with statement and Lean record unchanged. This is a substantive re-split, not an unchanged re-push:

1. New lem-cbc-marked-homotopy-precomposition states the construction of the whole simplicial transformation, its endpoint precomposition maps and its sharp components. New step 8 applies it separately to the RX and RY inverse paths.
2. New step 9 cites the existing relative marked lifting calculus for sharp = core, the existing pointwise-equivalence lemma for equivalence of transformations, and the existing Joyal exponential lemma for the functor objects to be quasicategories.
3. New step 10 cites the existing infinity-mapping-composition statement for edge representatives, composition, and the characterization of equivalence edges by invertible homotopy classes. Thus joining a path of edges no longer hides an uncited lemma. The coherent-inverse conclusion uses the existing definition of functor equivalence.

The other nine original steps and the route are retained. The largest resulting proof step is 1507 characters; the replacement steps have 766, 638 and 858 characters. No non-elementary step exceeds 2000 characters. Statement and Lean record were compared as JSON values and are identical to the current shared copy. The sandbox initially contained only dispatcher .brief files, with no earlier node/report/search log to preserve; the current shared node was therefore the retained returned proof used as the starting point.

## Not duplicates

lem-cbc-marked-homotopy-precomposition vs lem-cbc-marked-mapping-simplex-descent: the new lemma is only a parameterized composition construction for arbitrary marked objects, without simplexwise weak-equivalence hypotheses, descent, replacement, or an equivalence conclusion. It is strictly smaller than the item and not one of its clauses.

lem-cbc-marked-homotopy-precomposition vs lem-coef-relative-marked-anodyne-calculus: the existing node identifies flat mapping quasicategories and sharp cores and gives lifting results; it does not construct a transformation of whole flat mapping objects from a homotopy of source maps.

lem-cbc-marked-homotopy-precomposition vs lem-coef-infinity-pointwise-equivalences: that node detects when an already specified transformation is an equivalence. The new node constructs the transformation, without claiming it is an equivalence for arbitrary targets.

lem-cbc-marked-homotopy-precomposition vs lem-coef-infinity-mapping-composition: that node constructs homotopy-category composition from right-pinched mapping spaces. It does not give the relative marked exponential composition formula.

lem-cbc-marked-homotopy-precomposition vs lem-cbc-enhanced-relative-exponential: that node builds a relative exponential over cartesian fibrations and characterizes its cocartesian edges, with substantially different hypotheses and conclusion.

lem-cbc-marked-homotopy-precomposition vs lem-cbc-cocartesian-section-currying: that node concerns currying sections with domain S times a quasicategory, not arbitrary marked source homotopies over S.

lem-cbc-marked-homotopy-precomposition vs lem-coef-simplicial-relative-homotopy-invariance: the existing statement compares extension homotopy classes for unmarked simplicial pairs and categorical/weak equivalences, not parameterized marked mapping objects.

lem-cbc-marked-homotopy-precomposition vs lem-coef-joyal-homotopy-exponentials: the existing node supplies unmarked functor quasicategories and homotopy-category exponentials; it does not assert the relative marked construction or its sharp-component condition.

lem-cbc-marked-homotopy-precomposition vs lem-coef-fibrant-pattern-homotopy-inverse: the existing node supplies inverses for weak equivalences of fibrant patterned objects. It does not construct induced transformations on entire flat mapping objects with arbitrary sources and targets.

Searches for duplicates used the whole DAG's statement fields, not only this chapter, and blueprint_refs.py searches for 'homotopy precomposition', 'marked mapping', 'precomposition', 'homotopy', 'marked homotopy', and 'whiskering'. The relevant candidates were opened. The imported matches for general 'precomposition' and 'whiskering' are about sheaves, coefficient constructions or exchange maps, not this marked exponential lemma. No same-statement blueprint node was found. The new ancestry is thm-cbc-finite-level-proetale, via the item followed by the item's pre-existing via chain.

## Review by Q09

I read the current item, its chapter and sk-prop-sf-cbc unit records, its current-blueprint ancestor thm-cbc-finite-level-proetale, and the full statements of every cited node. HTT printed p. 154 defines flat and sharp marked mapping objects by their representing maps; Remark 3.1.3.1 identifies the flat quasicategory and its sharp Kan core. Propositions 3.1.3.3 and 3.1.3.5 (pp. 155–157) give the mapping-equivalence test and strong inverse data. Remark 3.1.3.4 gives the flat-boundary lifting argument. Proposition 3.2.2.8 (p. 181) uses degreewise pullback pushouts and skeletal induction; the retained item correctly labels its marked version as agent-formulated, rather than claiming that proposition verbatim proves marked descent. The ancestor's opening compactification proof uses this only through generic coherent-presentation foundations: the repair changes neither the compact-support route nor coefficients.

The new lemma is an agent expansion of HTT's marked exponential adjunction, not a quoted theorem. All its objects and markings are introduced, and its statement defines Map^epsilon over S explicitly. I checked the formula degreewise: the intermediate map is (u,v) ↦ (H(u,tau(v)),v). It lies over S because H does. A marked edge in U times flat Delta^k has degenerate parameter; tau of that parameter is degenerate, H takes its U-coordinate to a marked V-edge, and a then takes the pair to a marked W-edge. Thus the output really belongs to the flat mapping object. Simplicial operators restrict both appearances of v and commute with H and a. Constant tau gives the two endpoint maps, and at a vertex a the component is exactly aH. When H is sharp-marked, aH is sharp-marked by composition of marking-preserving maps. This argument explains the smaller lemma to its next worker; its node itself carries only the statement and empty proof/proof_deps. No assertion of invertibility is made for a general W. This is the hidden parameterized construction the human requested as a node, not a new name for the item's descent conclusion.

Step 1 uses lem-coef-marked-relative-cartesian-model for the relative model, cofibrancy and its cocartesian opposite, lem-coef-relative-marked-anodyne-calculus for the flat quasicategory/sharp core, and def-cbc-enhanced-diagrams-cones for explicit simplicial conventions. Opposite reversal and flat-product marking are the written coordinate checks. In particular a parameter edge is unrestricted except when checking product markings.

Step 2 uses lem-coef-marked-relative-cartesian-model for sigma_! being left Quillen and lem-coef-model-infinity-derived-adjunction for preservation of weak equivalences between cofibrant objects. All sources are cofibrant by the former statement, and composition is applied rather than an unjustified preservation claim for pullback.

Step 3 uses lem-coef-infinity-monomorphism-boundary-cells for the skeletal pushouts; its case X empty gives the absolute skeletal filtration. def-cbc-enhanced-diagrams-cones supplies degreewise pullbacks/products, and def-coef-infinity-marked-coanodyne states the marked pushout convention. The pullback/pushout and marking identity is written degreewise in the retained step, rather than taken from a node that only defines a notion.

Step 4 uses parts (a),(b) of lem-coef-model-cofibrant-colimit-comparison. I checked all six span objects are cofibrant and the boundary-to-simplex maps are monomorphisms, hence cofibrations by lem-coef-marked-relative-cartesian-model. Only that leg needs be injective. The simultaneous induction covers all maps T to S and includes the empty boundary of Delta^0 and empty cell families.

Step 5 uses part (c) of the same colimit comparison at omega, with cofibrant initial objects and cofibration successor maps. There is no nonzero limit ordinal below omega, so no continuity hypothesis was skipped. T=S gives the desired relative weak equivalence; the simplex indexing category need not be finite.

Step 6 uses lem-coef-relative-marked-anodyne-replacement, in the cocartesian opposite justified in step 1, for a functorial coanodyne replacement. def-coef-infinity-marked-coanodyne names the appropriate opposite class. lem-coef-marked-relative-cartesian-model explicitly supplies two-out-of-three and marked inverse paths between fibrant objects, which now apply to Rf. This uses the node's statement about paths, not an unrecorded construction from its proof.

Step 7 uses lem-coef-marked-anodyne-lifting-calculus for the pushout product, lem-coef-relative-marked-anodyne-calculus for target lifting, and lem-coef-infinity-monomorphism-boundary-cells to extend boundary lifts across monomorphisms. The marked pushout product has the correct flat parameter. The weak factorization-system characterization in lem-coef-joyal-model-structure gives the trivial fibration, and lem-coef-joyal-quasicategory-characterizations gives the coherent functor equivalence. Dimension zero is included.

Step 8 uses precisely the new lemma's formula, endpoints and sharp-component construction, instantiated twice with U=V=RX or RY and W=Z. The sharp homotopies from step 6 imply its weaker flat-H hypothesis. Nothing assumes arbitrary parameter edges of a or b are equivalences.

Step 9 uses the new lemma's sharp-component clause, the cocartesian opposite of lem-coef-relative-marked-anodyne-calculus for sharp=core, and lem-coef-infinity-pointwise-equivalences with K=C=A and K=C=B. A and B are quasicategories by step 1. lem-coef-joyal-homotopy-exponentials says exactly that Fun(K,Q) is a quasicategory for Q a quasicategory, so it justifies applying composition inside these functor objects. None of these existing statements was replaced by a duplicate node.

Step 10 uses lem-coef-infinity-mapping-composition's ordinary homotopy category, representation of each component by an edge, and equivalence iff invertible component class. Consequently a finite zigzag of equivalences gives an equivalence edge after inverting backwards classes and composing. The length-zero case is identity. The two endpoint equalities supplied by the new lemma give exactly the composites in the quasi-inverse definition of def-cbc-enhanced-diagrams-cones. This repairs the second hidden argument in former step 8 without citing the proof of another node.

Step 11 retains the commuting precomposition square and uses lem-coef-joyal-model-structure for two-out-of-three and lem-coef-joyal-quasicategory-characterizations to move between coherent equivalences and Joyal weak equivalences. Its reference to old step 8 was updated to steps 8–10. Step 12 retains the universe argument: lem-coef-relative-marked-anodyne-replacement gives small replacements, lem-coef-marked-anodyne-lifting-calculus gives universe-relative cell presentations, and lem-coef-marked-relative-cartesian-model gives the fibrant inverse criterion. The inverse and homotopy witnesses remain small; the reference to steps 7–9 was updated to steps 7–11.

Small cases checked for the new lemma: U empty gives the unique map to a point; V empty forces U empty whenever H exists; W empty permits only empty-domain vertex maps, so there is no illicit nonempty choice; constant H gives a degenerate transformation. For S a point, U=V=Delta^0 and arbitrary W, the construction acts on every simplex of W. For U=V=Delta^1 with flat marking, an identity homotopy with constant sharp parameter preserves the flat markings, whereas the statement does not claim every flat H is sharp or every component is invertible. For a naturally marked cocartesian target, the sharp-component clause feeds exactly the core criterion used in step 9. All constructions work in a containing universe without finiteness or fibrancy assumptions in the new lemma. The retained descent also covers S empty and noninjective f; no new hypothesis is introduced.

I checked delivery-errors B–E: the new statement is self-contained TeX, its notions cite their actual definition-bearing nodes, proof fields are empty, and its source is identified honestly as a construction from HTT with no invented Stacks tag. The recorded searches are the exact command queries and actual log records. Read Mathlib RelativeMorphism.lean:137–159 (homotopies relative to a subcomplex), SimplicialObject/Homotopy.lean:130–164 (componentwise simplicial-object homotopies), ModelCategory/RightHomotopy.lean:83–88 (precomposition with one map), and HomotopyCat.lean:395–406 (ordinary-category natural transformations). These hits do not state the new marked mapping-object transformation with the sharp condition and are not one-line specializations. The whole DAG and blueprint duplicate checks found no existing equivalent construction. Non-elementary facts in replacement steps are all named citations, including the previously hidden joining of paths. proof_deps is the union of uses. Generic off-unit tools newly cited in steps 9 and 10 are declared in split_report.tool_uses; the maintainer-owned tool_uses field was left as found. No statement dispute or source error was introduced, no Lean was written, and no compiler/Lake/build tool was run.

## What remains

The new lemma is deliberately unsplit and will enter the stage-1 queue for its own split. One attempted grep used a nonexistent InternalHom directory. Although msearch emitted OK with zero hits, I explicitly marked that attempt unavailable and repeated its query on the existing SimplicialSet directory; it produced the RelativeMorphism and closure-property hits discussed above. No absence conclusion rests on the invalid directory. No mathematical part of the requested repair is left unresolved. The required server dry run and push are recorded below when complete.

## Server validation

The separate server review_split command exited 0 and printed PASS. The complete delivery dry run follows; its result, rather than this preliminary check alone, controls the push.
