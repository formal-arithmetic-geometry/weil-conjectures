## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-simplex-filtered-vanishing.json`: statement, split; no exact Mathlib match. The original statement is unchanged. The exact-couple definition was added to statement dependencies because the statement already names this notion.
- `citations.json`: seven verbatim statement excerpts for the seven step/citation pairs.
- No new nodes and no new Mathlib leaves. `searches.jsonl` records the searches actually run; the imported search history remains in the item. `write_split.py` is sandbox-only preparation, not part of the delivery.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id and the filtered-vanishing, simplex, augmented-subset and finite-filtration concepts. No project declaration states the item. The existing simplex resolution modules under `lean/Sheaf/TraceFormula/` address a different, chain-level free resolution, not this derived triangle-tower criterion.

## WANTED

None. The argument uses the local Stacks source and an explicit agent-written finite biproduct calculation.

## Findings and changes

The item was unsplit and the sandbox initially contained no node or previous report. There is no repair note for this item. I read its current parent `lem-sfb-root-tower-inner-support`, the chapter and unit records, and paragraph (3) of the current main-20261015 direct-images proof. That paragraph gives the open/proper direct-image route; the simplex criterion is explicitly an agent expansion below this route, not a theorem quoted from the blueprint. The inherited nearest-blueprint-ancestor command returns `None`; the null `from.node`, full via chain and precise from.place were therefore retained. Blueprint searches for simplex, finite filtration and exact couple found no equivalent blueprint statement.

I read Homology Tag 012W, `lemma-biregular-ss-converges` (homology.tex:6361ff), including the finite-tail proof. Its literal hypothesis is a filtered cochain complex; it cannot simply be applied to a tower of distinguished triangles. The repair is an explicit grading conversion and application of the already-existing `lem-sp-finite-cocone-exact-couple`, whose statement takes an abstract exact couple and requires only constant/zero diagonal tails. This avoids assuming a strict filtered-complex model of the tower. I also read Homology's exact-couple definitions and shifted variant (Tags 011Q, 011S, 0AMJ), the complete statements of `def-sp-exact-couple`, `def-sp-convergence` and `def-sp-spectral-sequence`, and Derived Categories Tags 05RU/05RT and 05QR (`lemma-third-object-zero`).

The DAG tag search for 012W exposed the existing exact-couple theorem and several strictly filtered-complex lemmas. The latter cannot be used without an additional realization result. The cone criterion already has the Mathlib leaf `lem-kun-distinguished-cone-zero`; I opened it and Mathlib's `Triangle.isZero₃_iff_isIso₁` at Pretriangulated.lean:388–391. Neither a new convergence node nor a new cone node is justified. The least-vertex contraction is a short coordinate identity, written in full as elementary steps rather than promoted to a node. There is no displaced clause of the item and no proof hidden inside a new statement.

Mathlib searches were made through the required msearch command, with two semantic phrasings and Loogle/LeanSearch/grep. I read the hits: `alternatingConstHomotopyEquiv` concerns a periodic complex with one copy of the object per degree, not the subset row; the spectral-object API constructs general pages but does not give this criterion by one-line specialization. The cone criterion matches an already existing leaf and is cited as such. These searches and their results are retained, including the preexisting item's searches; no unavailable request was recorded as a negative search.

## Not duplicates

No new nodes. The prospective finite convergence lemma was rejected as a duplicate of `lem-sp-finite-cocone-exact-couple`; the prospective zero-cone lemma was rejected as a duplicate of `lem-kun-distinguished-cone-zero`. `lem-sp-degreewise-filtered-acyclic` concerns acyclic graded cochain complexes, not an acyclic first-page differential of a triangle tower.

## Review by Q10

I reviewed sections B–E with the node and all cited statements open. The statement needs no correction: for a nonempty finite ordered set, the augmented row is contractible; finiteness supplies actual constant and zero tails in every cohomological degree. Grothendieck abelianness is stronger than necessary for this finite argument but is kept exactly as imported. No SGA source is used.

Steps 1–2 construct actual morphisms using finite biproduct projection matrices, so they apply in an arbitrary abelian category and do not assume elements or a faithful forgetful functor. I checked the two component cases separately, including augmentation degree -1 and the top subset. `def-sp-spectral-sequence` supplies precisely the next-page homology isomorphisms; the displayed cancellation proves exactness instead of quoting simplex acyclicity. For m=1 the complex is M → M by the identity. For m=2 it is M → M⊕M → M with diagonal augmentation and (x0,x1) ↦ x1−x0. The least-vertex homotopy is projection to vertex 0 in degree 0 and the map c ↦ (0,c) in degree 1. Empty I is excluded and is essential: with no vertices, a nonzero M in degree -1 would have no contraction. Zero M and the top row endpoint cause no exception.

Step 3 uses the statement of `def-sp-exact-couple` for its bidegrees and the supplied exact-couple datum of the item, not a theorem about realizing arbitrary triangle towers by strict filtered complexes. I verified the conversion explicitly: a=-Q, b=P+2Q; the triangle boundary changes (P,Q) by (2,-1), so its composite with the quotient map changes (a,b) by (1,0). The initial page of this convention is called E2, while it is E1 in the item; the vanishing next page therefore corresponds to E3 in that convention. This renumbering is only the first derived-couple stage and does not claim an incorrect uniform renumbering of all cohomological bidegrees. For fixed n, D(P,n−P)=H^n(F^(P−n)D), and the alpha maps point towards decreasing P. The lower constant tail P≤n−1 proves the colimit universal property, while the upper bound P≥n+m gives zero. These are exactly the two hypotheses of `lem-sp-finite-cocone-exact-couple`. Its quoted equal-kernel epimorphisms give the limiting-page/graded-image identification; `def-sp-convergence` defines the precise image filtration being used. I take no cohomology identification or separatedness conclusion from the cited lemma, since it expressly does not assert these: the identification and both finite endpoints are written out here. This is a generic tool use from another unit, declared in split_report.tool_uses, not a change to the geometric route.

Step 4 uses `def-sp-convergence` for the graded quotients and explicitly runs descending induction from G^(n+m)=0 to G^(n−1)=H^n(D). I checked that this uses a finite interval for each arbitrary n, so it needs neither a uniform bound in n nor a completeness theorem. To detect the zero derived object I use only the actual localization definition in `def-weil-abstract-derived-category`: the representative map K→0 is a quasi-isomorphism because all its cohomology maps are isomorphisms. There is no unquoted conservativity theorem hiding here.

Step 5 uses the complete iff statement of `lem-kun-distinguished-cone-zero` on the given distinguished cone triangle, with all its pretriangulated hypotheses furnished by the ordinary derived category. Naturality of the vanishing assertion means the unique maps between zero objects; the equation for inverses of the cone-application morphisms is written explicitly. Thus no natural contraction, vertex choice under arbitrary index maps, chain-level graded identification or infinite-totalization convergence is asserted.

All six distinct cited node statements were opened. Each citations.json excerpt is a literal substring of the respective statement; no citation uses an argument from the cited proof. The dependency union is exactly the union of the step uses. The five proof steps are all below 2000 characters, and none hides a separate standard comparison lemma: the only non-elementary convergence theorem is the cited generic exact-couple node. No new statement-only nodes require small-case or duplicate audits. I corrected the initial temptation to invoke 012W directly by spelling out the exact-couple reindexing, and reused the existing cone leaf rather than adding a duplicate.

## Unfinished work

None in the stage-1 mathematical split. Server dry-run and direct delivery results are recorded below when completed.

## Dry-run repairs

The first dry run exited before preflight because the exact-couple excerpt was shorter than the citation gate’s 40-character minimum. I expanded it to the complete literal displayed formula giving all three bidegrees used in step 3; the proof was unchanged.

The second dry run reached server preflight and rejected the words “the item’s” in step 3 as non-self-contained (B2). I replaced them with “the displayed first-page differential”; all objects and hypotheses remain introduced in the statement and proof.
