# Q30: def-sfb-algebraic-moduli-stack

## Files written

- dag/nodes/sec-six-functors-basics/def-sfb-algebraic-moduli-stack.json: existing definition, dependency audit and signed split_report; statement and five stmt_deps retained; no Mathlib match.
- citations.json: [] because this is a definition with no proof steps or proof citations.
- report.md: this report. searches.jsonl is the search command's unmodified log.

New nodes: 0. New Mathlib leaves: 0. A definition is split by its explicit construction and statement dependencies; it has no theorem proof to subdivide.

## Attachments

None under WeilConjectures. Searched both the exact blueprint tag and the notions there: no matching declaration. The already registered Sheaf.AlgebraicGeometry.AlgebraicModuliStack file was read, including CategoryTheory.SpaceMapIsSmooth, IsSmoothModuliAtlas, IsAlgebraicModuliStack, IsSmoothModuliStack. These agree with the item and contain explicit definitions, but the direct-delivery brief restricts ATTACH to WeilConjectures declarations. The maintainer-owned lean and reviewed_lean fields are retained unchanged.

## WANTED

None for this definition. The cited Stacks source files are locally present. The generic definitions needed from def-sfb-stable-pointed-moduli-groupoids were read in its statement and in its existing Lean interface; this item does not use the unavailable Pikaart--de Jong PDF or any theorem about stable curves.

## Findings and corrections

The live node already has status split and a stage-2 review, but has no stage-1 split_report/reviewed record. No released repair note exists. This delivery supplies the stage-1 audit only. No statement change, new existence claim, Lean edit, compiler invocation or route change is made.

Stacks 026O uses fppf stack descent; the discussion immediately following it explicitly allows the etale convention used here. Read criteria.tex lemma-stacks-etale, which states the equivalence with exactly the etale-stack, algebraic-space-diagonal and smooth-surjective-atlas assumptions. This equivalence is source validation, not an additional theorem asserted by this definition. An existing DAG lemma, lem-sfb-etale-smooth-atlas-fppf-descent, covers that theorem separately, so no duplicate is created.

The source field's additional stacks-properties.tex definition-immersion is extraneous for the present statement (no immersion is defined). Its maintainer-owned source field is preserved. Supplementary source for the chartwise smoothness clause is spaces-morphisms.tex Tag 03ZC, definition-smooth; for structural smoothness it is stacks-morphisms.tex Tag 075U, definition-smooth and lemma-local-source-target.

## Unfinished work

None in the definition audit. All theorem-level existence, atlas independence, descent and change-of-presentation results remain separate existing items; none is smuggled into this definition.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. Whole-DAG searches for 026O, 075U, definition-algebraic-stack and smooth surjective scheme atlas, and blueprint_refs.py searches for algebraic stack, smooth atlas and moduli were inspected. The stable-pointed groupoid definition supplies generic prerequisites and a Deligne--Mumford predicate, whereas this item allows smooth rather than etale atlases. Definitions of open substacks, curve groupoids, moduli-stack properties and adequate moduli spaces use this notion and do not replace it.

## Review by Q30

I read Stacks algebraic.tex definition-algebraic-stack (026O) and its following discussion in full for the three defining clauses. I read spaces-morphisms.tex definition-smooth (03ZC) for the algebraic-space-to-scheme chart predicate, stacks-morphisms.tex definition-smooth (075U) and lemma-local-source-target for smoothness of the structural map, and criteria.tex lemma-stacks-etale to check the etale convention. No SGA source is used. There are no new nodes requiring additional source review.

There are no proof steps, so C1/C4 proof citations are vacuous and citations.json is empty. For statement-dependency checks I opened each of the five cited node statements: def-pc-scheme supplies schemes and their maps; def-weil-size-convention fixes the universes; def-trf-algebraic-space supplies the sheaf, representable etale chart and surjectivity notions; def-sfb-stable-pointed-moduli-groupoids explicitly supplies arbitrary categories fibred in groupoids, functors and 2-isomorphisms over Sch/S, the triples construction of 2-fibre products, effective etale descent, and representability by algebraic spaces; def-sbc-smooth-morphisms supplies smoothness of scheme projections. Although the generic groupoid interface sits in a stable-curve definition, its generic paragraphs introduce an arbitrary F; no genus or characteristic assumption is being borrowed. Each cited statement actually defines the notion taken from it. Nothing is inferred from the proof of a cited node.

I checked that the atlas condition quantifies over every test scheme T and every h_T to F, and that the presentation is over T, so the tested projection is the given base-change map rather than an unrelated map. The atlas and every presentation occur existentially inside a predicate; no global choice or hollow object is defined. The structural U to S is required to be smooth in the last predicate. No finite-type, separated-diagonal, quasi-compactness, genus or field assumption was added.

For edge cases, an empty stack can have the empty atlas: nonempty T has no map into it, and the empty test has the empty base change. For the discrete groupoid of a scheme X, the identity atlas gives the intended algebraic-stack test; adding structural smoothness requires X to S smooth. Nontrivial stabilizers are retained in the 2-fibre products, so this does not replace a moduli stack by its set of isomorphism classes. An empty chart alone cannot establish surjectivity onto a nonempty test scheme. These checks find no statement dispute.

Against delivery-errors B--E: the statement is self-contained relative to its five actual definition dependencies, uses proper TeX and explicit predicates, and has no new node or Mathlib-leaf metadata to validate. There is no relabelling of a theorem clause, hidden lemma, induction, or long proof step. The only correction needed was missing stage-1 audit metadata; I preserved the previous statement, searches, provenance and Lean registration. Fresh logged LeanSearch, Loogle, LeanFinder and grep queries, including a second Artin-stack phrasing, returned scheme notions, Artinian schemes or manifold atlases; I read the returned pinned Mathlib Smooth definition and the manifold hit and found no matching algebraic-stack definition. Prior searches remain in the item and are not represented as newly executed searches.
