# Q65 worker report: lem-coef-infinity-cofinal-coslice-calculus

## Files written

All paths below are relative to the sandbox. Nothing was written to the shared repository, Lean checkout, master checkout, or launcher.

- `dag/nodes/sec-six-functors/lem-coef-infinity-cofinal-coslice-calculus.json`: item, split into eight proof steps; statement unchanged; Mathlib verdict no match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-join-cocone-associativity.json`: new statement, unsplit, no Mathlib match. Sharp cocone model, comparison with the coherent model, vertex isofibrations, and join parameterization/associativity. It has no proof or proof dependencies.
- `dag/nodes/sec-six-functors/lem-coef-infinity-contractible-right-join-restriction.json`: new statement, unsplit, no Mathlib match. A weakly contractible right factor makes the join inclusion right anodyne and gives all boundary lifts on sharp cocone restriction. It has no proof or proof dependencies.
- `citations.json`: 24 step/node entries, with verbatim statement passages. These are checked against the actual statements, not their proofs.
- `report.md`: this report. `searches.jsonl` was produced by the required search command. The sandbox's `write_split.py` is a local reproducibility aid, not a delivery file.

Two new nodes, zero Mathlib leaves.

## Attachments

None. The exact blueprint tag is absent from the project declarations in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`. Searches there for cofinal, coslice and quasicategory returned ordinary geometric neighbourhood/affine approximation uses of cofinality, not the four-clause assertion. The new join/slice and right-anodyne statements likewise have no project declaration; the only apparent join/cocone keyword hit was an ordinary graded-object colimit theorem. No sorried declaration in the master reference was treated as an attachment, and no Lean was written or compiled.

## Sources wanted

WANTED: archival copy of Lurie, Higher Topos Theory, April 9, 2017, Sections 1.2.8-1.2.9, Propositions 2.1.2.1, 4.2.1.5-4.2.1.6, Lemma 4.2.3.6, Proposition 4.3.1.12, Lemmas 5.3.1.21, 5.4.5.11, 5.4.5.14, 5.4.6.4, for this item and its two children. The source was read online at https://www.math.ias.edu/~lurie/papers/HTT.pdf; there is no HTT PDF/text archive under the named literature directory. The worker brief prohibits downloads and edits to literature, so the item's proof is marked agent-written and this wanted request is reported here.

No Stacks tag supplies these quasicategory theorems. Their source places therefore give precise HTT result identifiers, rather than inventing a Stacks attribution. No SGA source is used.

## What was wrong or incomplete

The imported item had no proof. Its statement is valid and is retained, including no ordering between the infinite regular cardinals. In particular, the absolute cocone shape need only be tau-small, not kappa-small; a kappa-cofinality test need not be tau-small. Both facts are respected in steps 6 and 8.

In HTT's printed proof of Lemma 5.4.5.11(1), the inclusion from the union of K join K' and the cone on K' to the cone on K join K' is called a categorical equivalence by Lemma 5.4.5.10, although that lemma requires its middle factor K' to be weakly contractible and this is not assumed of an arbitrary filteredness test. This invocation alone cannot prove the assertion. For example, with K a point and K' empty the union has two disconnected vertices whereas the target is the edge between them, so the inclusion is not a categorical equivalence. This is a gap in that proof, not a counterexample to the item's statement. Step 7 supplies the missing argument: cone the whole union in E, then apply strong cofinality to the singleton v in D. No unit-level route changes and no statement changes are made.

There is also a notational slip in the printed proof of part (2), saying K is now kappa-small and weakly contractible where the test shape is K'. Step 8 uses L for that test shape, so its role cannot be confused with the original cone boundary K.

## Search and reuse

Before writing the children I searched the whole DAG for the item, cofinal/coslice/filtered/join concepts, HTT identifiers 5.4.5.10 and 4.2.3.6, and both proposed child IDs. I ran `tools/blueprint_refs.py ancestor` for the item and whole-blueprint searches for cofinal coslice calculus, filtered, cofinal, right anodyne, weakly contractible, join, iterated cocone, and contractible right join. The blueprint searches are substring searches, so the broad join search also returned unrelated words such as adjoint; I read the relevant existing infinity-category candidates separately. No blueprint node states either child. `blueprint.same_as` is consequently empty, and both children retain the complete inherited ancestry through this item to `prop-coef-integral-exceptional-adjoint`.

The current main-20261015 proof of that ancestor was read, particularly paragraph 2's mapping-complex inverse-limit calculation and derived coefficient adjunction. The chapter and unit records were read. This is a generic coherent-cocone foundation within the already chosen enhancement ancestry, not a replacement of the geometric biduality or six-functor route. This item is not the key statement of its unit, so no unit realized fields were edited.

All Mathlib searches in the new nodes were actually run with `msearch.py Q65 lem-coef-infinity-cofinal-coslice-calculus ...`. I used two semantic phrasings for each child and the item, LeanSearch, Loogle, and source grep. Their stored results contain the actual logged query, hits, digest and timestamp. The services responded; there is no unavailable search being counted as absence. Ordinary `CategoryTheory.isCardinalFiltered_under` (Presentable/IsCardinalFiltered.lean:202-216) and the Under.forget filtered-colimit instance (Limits/Preserves/Over.lean:44-53) were read: both require ordinary Category instances. Simplicial skeleton/coskeleton adjunctions are adjunctions for truncation, not joins and coherent slices. Quasicategory/Basic.lean:35-103 provides horn fillers; SimplicialSet/CategoryWithFibrations.lean:36-86 provides generic Quillen horn/boundary lifting classes, not the right-anodyne join result or its specified restriction map. Focused grep in AlgebraicTopology/Quasicategory returned zero for the relevant join/slice/right-anodyne patterns. Broad initial grep/Loogle hits were not treated as evidence of absence; the focused searches and the source readings supply that evidence.

## Not duplicates

lem-coef-infinity-join-cocone-associativity vs lem-coef-infinity-join-cone-calculus: the existing theorem compares a left cone with a fat cone by ordinary functor categories, with fixed boundary pullbacks and a mapping-space formula. The child constructs the sharp slice with n-simplices K join Delta^n, its vertex projection, and the arbitrary-L join adjunction and iterated sharp-slice identity. These are not assertions of the existing statement. Ordinary Fun(K join point,C) with fixed boundary and a varying prism parameter is not literally the sharp slice K join Delta^n; identifying them is exactly the extra model theorem needed here.

lem-coef-infinity-join-cocone-associativity vs lem-coef-infinity-blunt-sharp-join-equivalence: the existing theorem gives equivalences of functor categories from two joins. It does not state the right-adjoint sharp slice construction, its isofibration projection, or the sharp/fat slice comparison and iterated identity. It is a possible ingredient for splitting the new child later, not a one-line specialization that already states it.

lem-coef-infinity-contractible-right-join-restriction vs lem-coef-infinity-terminal-anodyne: the existing statement concerns inclusion of a terminal vertex in a quasicategory. Here B can be a weakly contractible simplicial set with no terminal object and need not be a quasicategory; the conclusion concerns inclusion of an entire right join factor and lifts of the associated slice restriction.

lem-coef-infinity-contractible-right-join-restriction vs lem-coef-infinity-anodyne-cocones: the existing statement assumes an inclusion already right anodyne, and concludes a pushout-join assertion and a fixed-vertex mapping-space equivalence. It does not prove that B into A join B is right anodyne or give the all-boundary lifting property on sharp slices.

lem-coef-infinity-contractible-right-join-restriction vs lem-coef-infinity-cone-mono-right-anodyne: the existing statement has right join factor a point and varies the left factor by a monomorphism. The child allows any weakly contractible right factor and states the resulting sharp-slice restriction theorem. The existing special case alone cannot be cited for an arbitrary weakly contractible test diagram.

Neither child restates any clause of the item: neither mentions cardinal filteredness, cofinal functors, or preservation/creation of colimits. Those arguments remain in the item's steps.

## Review by Q65

I checked B through E of delivery-errors against the node files and the online sources. In particular I read HTT's actual sharp/fat slice definitions and Proposition 4.2.1.5 for the first child, with the vertex-fibration results 2.1.2.1 and 4.2.1.6. The second child's join hypothesis is exactly Lemma 4.2.3.6 with empty left subobject; I read that lemma and its proof, as well as its explicit slice-restriction uses in 5.4.5.11(2) and 5.4.6.4. The all-boundary formulation means both vertex lifts and lifts of edges with prescribed endpoints; this is stronger than merely saying the slice categories are equivalent, and the proof uses exactly this stronger conclusion. Both children are statements only, self-contained, with all notions defined inline or by genuine definition/model dependencies.

For step 1 I opened both the new join model statement and `lem-coef-infinity-isofibration-pullback-limit`. The former provides the sharp model, naturality and vertex isofibration; the latter really permits an arbitrary other leg D to E, so no fibration assumption on f is smuggled in. The relative sharp-cocone identity is checked degree by degree, rather than attributed to a theorem about ordinary pullbacks of objects. Coherent composition comes from the actual statement of `lem-cbc-simplicial-composition-spine`. The filteredness/cardinal conventions come from `def-coef-presentable-infinity-category`.

Step 2 takes the join adjunction and iterated identity from the new model node, and only existence of a cocone from the filteredness definition. The cardinal bound is written out; it also works for aleph_0 because a join of two finite sets of nondegenerate simplices is finite. No homotopy-category cone is substituted for a coherent one.

For step 3 I read `lem-coef-infinity-coslice-colimit-formula` and use only its standalone assertion that every small kappa-filtered quasicategory is weakly contractible. I do not apply its pushout formula, which assumes an ambient category with all colimits. I read `lem-cbc-simplicial-groupoid-localization`: it gives full mapping spaces between constant diagrams, including noninvertible transformations; this is what yields beta and its compatibility path. `lem-cbc-enhanced-functor-cone-calculus` supplies the needed quasicategories, and the composition-spine statement composes the transformations. Only the hypothesized colimit of the I-vertex diagram is chosen; no K-colimit or cocompleteness is assumed.

For step 4 the actual cone-calculus statement supplies the homotopy-fiber mapping formula and the colimit test, including the dual assertion. I checked the exponent interchange identifying Fun(I,D under p) with the K-cocone category in Fun(I,D); the fixed K-diagram is k sent to the constant I-diagram p(k). This identifies the exact two mapping spaces displayed in the proof. The localization statement supplies the constant-diagram equivalence, and `lem-coef-kan-homotopy-pullback-invariance` supplies invariance of the resulting fibers, with the specified path inserted if a square commutes up to homotopy. The cone-calculus statement's contractibility of initial objects proves reflection by comparison with the already constructed colimit, so reflection is not inferred just from the existence part.

Step 5 uses the precise definition of preservation in `def-coef-presentable-infinity-category`, and the preceding if-and-only-if in each ambient category. Both ambient existence hypotheses remain explicit. This short consequence is marked elementary and is not a new lemma.

In step 6 I checked that the new restriction lemma applies with the right factor L, which is weakly contractible, while K need not be kappa-small. The definition of f's strong cofinality is invoked only for t restricted to L. The arrow-lifting argument specifies both endpoints, so an arbitrary equivalence of categories would not have been enough. The filteredness of both coslices was already proved in step 2.

In step 7 I explicitly checked the source gap described above and replaced only that missing argument. The glued diagram U is tau-small because both K and L are. The cone in E supplies a single coherent naturality homotopy on U, not independent triangles at its vertices. Strong cofinality is applied to the singleton v, which is kappa-small and weakly contractible for every infinite kappa. Composing its specified triangle with the U homotopy yields the needed family of compatibility homotopies on all of K times L. The cited composition-spine and functor-cone statements supply coherent composition in the corresponding functor quasicategories. This verifies the cocone in the relative category without an inequality between the cardinals. Indeed this argument does not need K to be kappa-small, though the item's stated hypothesis is retained.

For step 8 the relative sharp-cocone identity of step 1 identifies the required functor as the indicated pullback projection. The new right-join node supplies boundary lifts since L is weakly contractible. The cofinality definition supplies the lower arrow; lifting that arrow gives the object and arrow required upstairs. I checked that no tau-smallness of this kappa-small L was used. The target's tau-filteredness uses K tau-small, and the source's was established in step 7.

I tested the new model on empty K (the slice is C), empty L (the iterated identity is the original slice), K a point (the usual under category), and C terminal. For the second child, A empty gives an identity restriction, B a point gives the terminal-vertex join case, and a disconnected B is explicitly excluded: taking two unrelated vertices in B shows why that hypothesis cannot be dropped. For the item I checked empty cone boundary, empty filteredness test, singleton strong-cofinality test, and both possible inequalities between kappa and tau. A kappa-filtered indexing category is nonempty, so the colimit proof never silently includes an empty indexing shape. When tau is at most kappa there may be no tau-small kappa-filtered shapes of a given large kind; the colimit assertion is conditional on the actual shapes, and no enumeration argument assumes otherwise.

I opened every cited statement and copied its relevant passage to citations.json; in particular step 5 quotes the preservation definition rather than merely the filteredness definition. I checked no cited proof is used as an interface. The new children point only to definitions and to the new sharp model, so there is no reverse dependency to the item. The old dependencies reused here were checked not to depend on the item. Cross-unit generic tools are declared in split_report.tool_uses; no maintainer-owned tool_uses or unit/chapter fields were edited. The split leaves real generic join foundations for later workers, rather than moving a clause of the item into a child.

## Unfinished work and validation

The two children intentionally remain unsplit for the next stage-1 worker. No part of the item's argument is left as a promise to apply an unstated cofinality or colimit theorem. The server-side `check_dag` completed with no finding introduced by the sandbox or on its nodes. The server-side `review_split` returned PASS. The required `deliver.py Q65 lem-coef-infinity-cofinal-coslice-calculus --no-push` returned `OK (not pushed)` with preflight passed, commit `2407e43089`. The report now records that result; a final no-push packaging check includes this report update. The sandbox is for a fresh second reader; this worker has not delivered or pushed it.

## Second reading by Q65

I reread the item against HTT Lemmas 5.4.5.11, 5.4.5.14, 5.4.6.4, Proposition 4.3.1.12, and the definitions in HTT 5.4.5.8; the stated hypotheses retain both independent regular cardinals, the separate tau-small and kappa-small tests, and the relative homotopy pullback. Verdict: statement agrees hypothesis by hypothesis, including empty and singleton shapes.

Step 1 was checked against the statements of the sharp join model, isofibrant pullback, composition spine, and filteredness definition; the relative pullback identity is degreewise and uses no unspoken fibration hypothesis. Verdict: dependencies say exactly what is used.

Step 2 was checked against the join model and filteredness definition; the cardinality calculation covers finite joins and the empty test. Verdict: complete.

Step 3 was checked against the standalone weak-contractibility clause of the coslice colimit formula, functor/cone calculus, groupoid localization, and coherent composition. Verdict: the constant-diagram mapping-space argument supplies the required extension without assuming a colimit of p.

Step 4 was checked against the dual cone mapping-fiber criterion, homotopy-pullback invariance, and localization mapping-space equivalence. Verdict: both existence and reflection of colimits are addressed; the comparison path is explicit.

Step 5 was checked against the preservation definition and Step 4 in both ambient categories. Verdict: elementary consequence is correctly marked and does not hide a lemma.

Step 6 was checked against the sharp join model, the weakly contractible right-join restriction statement, and the kappa-cofinality definition. Verdict: vertex and edge lifts are specified, and no kappa/tau ordering is used.

Step 7 was checked against HTT Lemma 5.4.5.11(1), with the printed weak-contractibility gap repaired by the common target cocone and singleton strong-cofinality test. Verdict: the glued shape is tau-small, all compatibility homotopies are retained, and the empty case is covered.

Step 8 was checked against HTT Lemma 5.4.5.11(2), 5.4.6.4, the degreewise pullback identity, and the right-join boundary lifting statement. Verdict: the source and target filteredness hypotheses are identified and the kappa-cofinality test is applied to the correct restricted diagram.

The join/cocone-associativity node was checked against HTT Sections 1.2.8–1.2.9, Proposition 4.2.1.5, and the sharp-slice/isofibration results; its statement is self-contained, has only statement content, and was tested on empty factors, a point, and a terminal target. Verdict: retained.

The contractible-right-join node was checked against HTT Lemma 4.2.3.6 and Proposition 4.1.1.8; its right-anodyne generators, boundary lifting meaning, arbitrary simplicial-set factors, and weak-contractibility hypothesis are explicit. Verdict: retained; empty-left, point-right, and disconnected-right edge cases were checked.

No duplicate DAG node or Lean/Mathlib declaration was found for either child after repository, source-checkout, blueprint, and recorded Mathlib searches. Citations were checked for verbatim statement passages and all 24 entries match their cited node statements.

Changes made: added this second-reading audit required by the delivery contract; no mathematical statement or proof step required repair after the source and dependency reread.
