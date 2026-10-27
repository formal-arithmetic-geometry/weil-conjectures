# Q34: lem-sfb-flat-inertia-algebraic-space-quotient

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-inertia-algebraic-space-quotient.json`: item, statement unchanged, eight-step split, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-free-flat-group-space-quotient.json`: new statement-only node, Stacks 06PH, no Mathlib match.
- `citations.json`: a verbatim statement for every step/node citation, including all its hypotheses.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, flat inertia, gerbes, free actions and algebraic-space quotients. There is no project declaration stating the item. Unrelated torsor/cohomology declarations do not give this geometric statement. No Lean was written or compiled.

## WANTED

None. All sources used are present in the read repository.

## Corrections and route

The item arrived unsplit with no sandbox node or earlier report. Its statement is correct and was preserved verbatim. I added the scheme smoothness definition to its statement dependencies. There is no released repair note for this item.

The main source is `stacks-morphisms.tex`, Proposition `proposition-when-gerbe` (06QJ), converse: divide the smooth arrow space by its flat stabilizer group, identify the resulting monomorphic relation and apply Bootstrap. I also read `lemma-gerbe-over-iso-classes` (06QD), `lemma-presentation-inertia` (06PR), `lemma-smooth-quotient-stack` (0DLS), and `lemma-gerbe-smooth` (0DN8). For smoothness descent I read `spaces-descent.tex`, `lemma-syntomic-smooth-etale-permanence` (0AHD) and `lemma-smooth-permanence` (0AHE). Instead of adding gerbe definitions or moving the conclusion into a gerbe theorem, the split computes the atlas fibres directly. Its scheme-chart descent is the argument of 0DLS. It proves both algebraicity and smoothness of the canonical quotient map.

I read the chapter and unit records, the latest blueprint unit and `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). The current unit proof uses compactification and constructibility; this small algebraic-space input lies below the existing historical alteration/Picard helper chain. No unit or chapter route is replaced. `blueprint_refs.py ancestor` prints None for the inherited chain: the item has a null blueprint ancestor already, which I retain, with its exact existing place and via list. The new node adds the item to via and identifies the precise 06QJ free-action input in place.

## Mathlib searches and duplicate checks

All searches in the new node were run with the required `msearch.py` command and their actual query texts, hits and outcomes are in `searches.jsonl`. I read the returned hits. The first free-action wording returned topological properly discontinuous quotient coverings and the set-theoretic `MulAction.selfEquivOrbitsQuotientProd`; the second wording returned `Scheme.LocalRepresentability.representableBy`/`isRepresentable`, colimits of set actions and representation coinvariants. I read `Topology/Covering/Quotient.lean` (topological covering-map hypotheses), `GroupTheory/GroupAction/Quotient.lean` lines 395--415 (set equivalence only), and `AlgebraicGeometry/Sites/Representability.lean` lines 180--211 (Zariski gluing by open immersions). None states the algebraic-space/fppf quotient theorem. The grep hit was the topology file's heading; the Loogle AlgebraicSpace/Torsor query had no hits. The item semantic search returned scheme flat descent and smoothness facts, not a flat-inertia theorem.

I also searched smooth source descent before contemplating a second node. The scheme version is already `lem-sbc-smooth-flat-surjective-source-descent`, and the alleged need for an algebraic-space version disappears by the explicit scheme-chart argument in step 4. I did not create that redundant node. Loogle's exact IsSmooth query could not recognize the identifier; the alternative substring query returned smooth/flat ring and scheme facts. These are recorded honestly, with the former index failure distinguished from evidence of absence.

Whole-DAG searches used the tag 06PH and the terms free action, free group algebraic space, gerbe, inertia, groupoid quotient and smooth descent. Blueprint searches for gerbe, flat inertia, free action, free quotient, flat equivalence, smooth quotient, neutral gerbe and smooth descent/permanence found no matching imported theorem; the sole equivalence-relation hit was a finite-stage coefficient relation, not this statement. Existing finite constant-group affine quotient results are narrower and cannot handle the variable flat group algebraic spaces here. The existing flat groupoid algebraic quotient produces an algebraic stack, not a space quotient of a free action. Existing fppf-space recognition and descent nodes are reused.

## Not duplicates

`lem-sfb-free-flat-group-space-quotient` vs `lem-sfb-flat-inertia-algebraic-space-quotient`: the new node concerns an arbitrary free action on an algebraic space, producing an algebraic-space orbit quotient and an fppf torsor. It says nothing about algebraic stacks with nontrivial inertia, the sheaf of their isomorphism classes, or smoothness of their quotient map. It is the strictly smaller geometric input used in step 2, not a clause of the item.

`lem-sfb-free-flat-group-space-quotient` vs `lem-sfb-flat-groupoid-algebraic-quotient`: that existing theorem produces an algebraic stack with an fppf presentation from a general flat groupoid, without freeness, space representability of the orbit sheaf or its torsor kernel-pair formula. It does not state the new theorem.

`lem-sfb-free-flat-group-space-quotient` vs `lem-per-free-finite-group-affine-quotient`: the latter is for a finite constant group on an affine scheme; the new result allows any flat locally finitely presented group algebraic space over an arbitrary algebraic-space base and arbitrary algebraic-space acted-on object. Its additional generality is essential for the stabilizer group, with no finiteness, smoothness or affineness assumed.

No preexisting active node had source tag 06PH in the shared read clone at the time of the searches. The new node has only this tag in its source. No new gerbe, inertia-comparison or smoothness-descent node was created.

## Review by Q34

I checked delivery-errors B--E against the actual JSON and the sources, not just their tags. I read all cited statements, and `citations.json` copies the full text so the conditions are independently visible.

Step 1 uses the algebraic-stack definition for the smooth atlas and representable diagonal. The etale-smooth-atlas fppf-descent theorem explicitly upgrades this convention to an fppf stack. The representable calculus explicitly gives smoothness and surjectivity under base change, and the space fibre-product theorem supplies the actual spaces R and G. The stabilizer/inertia identification is written on objects, so it does not cite a definition for an unstated theorem: G(T) is exactly Aut(x_T), and the assumed chart test of inertia gives its flatness and local finite presentation. No smooth stabilizer is assumed.

Step 2 uses precisely the new 06PH theorem: its arbitrary algebraic-space base is B=U, its acted-on object is Z=R, the action is explicitly r composed with g inverse, its laws and freeness are checked by composition and cancellation. Thus all hypotheses hold. Its statement supplies the algebraic space A, the flat locally finitely presented surjection q, and local lifting. The sheafification definition supplies the descent of invariant endpoints, without using any proof hidden in the new node. The new node has an independent self-contained statement, no proof or proof dependencies, and all its notions are defined inline or cite their actual definition.

Step 3 uses the sheafification local-sections theorem for exactly the local equality of the two isomorphism classes. It does not cite full faithfulness or a gerbe theorem as a substitute. The two local lifts r1,r2 have the same source and target; the automorphism g=r2 inverse composed with r1 has the required source, and g acting on r1 is r2. This proves injectivity of the orbit quotient on every test scheme, not only geometric points. Conversely local isomorphisms give local orbit sections, which agree by that calculation and glue in A. The formulas commute with pullback and sheaf uniqueness, yielding the canonical relation isomorphism. This is a routine local quotient comparison, completely written out, not a new theorem moved out of the item.

Step 4 uses the actual *scheme* source-descent statement and checks its objects are schemes: W is an etale scheme chart of A, and Z an etale scheme chart of R times_A W. The map Z to W is surjective flat locally finitely presented by base change of q and etale composition; Z to R is etale because W to A is etale. Hence Z to U is smooth. This meets every hypothesis of the scheme descent node, which does not need quasi-compactness. In particular, the proof never concludes q smooth from its flatness. It repeats the same explicitly specified chart argument for t. The identity arrows provide sections of both projections, giving surjectivity without a point-space theorem. Flatness and local finite presentation of the smooth projections are exactly clauses of the calculus node.

Step 5 uses actual local representatives of sections of Q from the sheafification theorem, then the atlas definition on T_i, then the smooth-space etale-sections theorem for its smooth surjective algebraic-space pullbacks. The latter provides maps into the space, so these are actual atlas lifts, not a lifting claim for a quotient presheaf. The calculus node and the fppf-site definition justify that these etale refinements are fppf covers. All covers and their refinements belong to the bounded site.

Step 6 uses the relation isomorphism already proved in step 3 to identify the restricted atlas fibre with a base change of A. The space fibre-product theorem supplies representability locally, and the smooth/surjective fppf-locality statement supplies both stability and subsequent target descent. The fppf-local algebraic-space node requires a bounded family of charts: the proof explicitly retains at most one covering member per target point, chooses all charts in the containing universe and invokes the scheme-coproduct theorem and the universe convention for their coproduct. Thus it does not apply a small-index theorem to a proper class. These are only tests over a scheme T, exactly the target scope of the locality statement.

Step 7 checks every Bootstrap hypothesis: Q is an fppf sheaf by its construction; U is a scheme, hence an algebraic space; every scheme fibre is an algebraic space smooth surjective, and the calculus gives flatness and local finite presentation. The existing bootstrap theorem assumes no diagonal condition on Q. Its conclusion is algebraic-space representability. Smoothness of pi is then exactly the atlas test in the item, and surjectivity follows from the actual local object lifts, not a representability assumption on pi.

Step 8 chooses the smooth-over-S atlas that the algebraic-stack definition expressly permits. Q is already an algebraic space here, so representability of its diagonal makes U times_Q V a scheme. Its projections have the stated smooth or etale properties by base change. The scheme source-descent theorem now applies to W to V to S with W to V flat, locally finitely presented and surjective. It proves V to S smooth, the required etale-chart test for Q.

I tested the empty stack (empty atlas and empty quotient, vacuous descent), an algebraic space viewed as a discrete stack (trivial stabilizers, quotient is itself), and a neutral classifying stack BG with G flat locally finitely presented but nonsmooth (for example an infinitesimal group in positive characteristic). In the last case the atlas need not be the trivial torsor section; the proof uses a genuine smooth atlas, and descends smoothness through the fppf map q. This is why the conclusion is smoothness of the nonrepresentable stack map, without forcing G smooth. The cancellation and sheafification arguments include nonreduced tests, which rule out the common geometric-point-only error. No hypothesis of separatedness, quasi-compactness, finite inertia or Noetherianity was introduced.

I checked the dependency closures of the existing geometric tools: none reaches the item. There is no SGA source. Every non-elementary step is under 2000 characters (the largest is 1065); the only nontrivial comparison (step 3) is a direct local cancellation/gluing calculation rather than an unnamed black box. The off-unit tools are expressly declared in split_report.tool_uses: generic scheme source descent, space fibre products, local sheafification and scheme coproducts. This keeps the inherited route intact.

## Unfinished work

The new 06PH theorem is deliberately statement-only, for a subsequent stage-1 item. Nothing else in the assigned split is left unproved in natural language. The required dry run and push follow this report.
