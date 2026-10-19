# Worker report: prop-sf-pf-coherence

## Files written

- `dag/nodes/sec-six-functors/prop-sf-pf-coherence.json`: repaired item; three former long arguments are now short cited steps.
- `dag/nodes/sec-six-functors/lem-sf-pf-open-factor-coherence.json`: new statement node, no Mathlib match.
- `dag/nodes/sec-six-functors/lem-sf-pf-compactification-pasting.json`: new statement node, no Mathlib match.
- `dag/nodes/sec-six-functors/lem-sf-pf-coefficient-realization-transport.json`: new statement node, no Mathlib match.
- `citations.json`: verbatim statement excerpts for every cited node at every item step.

## Attachments

None. I searched the project declarations in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; the tagged identity and compactification declarations have `sorry`, and the composition declaration is only an objectwise invertibility result. The module explicitly says it does not state the associativity pentagon as an equality of canonical transformations (lines 340–357). None supplies every clause of this item.

## WANTED

None.

## Source error

None found. The imported item statement and its six-functor coefficient categories were retained. The source record still contains its inherited bibliographic SGA 4 external field, but no proof step cites SGA 4 or SGA 4½; the repaired proof follows the current main-20261015 blueprint route and the supplied open/proper/coefficient comparison nodes.

## Not duplicates

The three new nodes carry no Stacks tags. Searches of the whole DAG and blueprint for their key phrases found no node stating the same open-factor coherence, compactification pasting, or coefficient-realization transport claim.

## Review by Q75

I read the retained item, the current `sk-prop-sf-pf-coherence` unit, the chapter record, the current main-20261015 proof text, the source declarations in `WeilConjectures/SixFunctors/Etale/Derived/ProjectionFormula.lean`, and the full statement of every node cited by the six item steps. Steps 1, 2 and 4 retain the previous explicit route: `fix-prop-projection-formula` supplies naturality, identity, pentagon, compactification and proper compatibilities; `fix-prop-adjunctions` supplies the adjunction units, counits and triangle identities; `lem-pur-derived-pullback-tensor-iso` supplies monoidal pullback composition; and the proper step expands both adjunction transposes and uses the same counit expression on each side. I checked each cited statement contains the precise map or hypothesis used.

The returned step 3 was replaced by `lem-sf-pf-open-factor-coherence`. Its statement is applied with the finite open maps from `lem-sf-open-tensor-normalization`, the completed open comparison and strict tower normalization from `lem-cbc-completed-extension-zero-comparison` and `lem-sf-integral-compactification-system-realization`, the invertible open unit from `det-sf-open-closed-sequence-ring-sheaf` and derived exactness from `lem-sf-exact-functor-derived-triangulated`, and the constructible-domain checks from `det-cor-int-compactness-ii-extension-zero` and `sk-lem-sf-open-ctf`. The pullback-tensor comparison is exactly the statement of `lem-pur-derived-pullback-tensor-iso`. Thus the new node states the hidden restriction/full-faithfulness argument, while the item step only verifies its hypotheses and applies it.

The returned step 5 was replaced by `lem-sf-pf-compactification-pasting`. I checked that `def-exchange-projection` defines the compactification projection as the proper projection mate followed by the open tensor map and defines compact-support exchange as proper exchange followed by the open base-change map. The new lemma takes exactly the open equality from step 3, the proper equality from step 4, and the refinement intertwining statements of `lem-fix-projection-compactification-comparison`, `fix-lem-exchanges`, and `fix-prop-projection-formula`; the item step is now only the concrete substitution.

The returned step 6 was replaced by `lem-sf-pf-coefficient-realization-transport`. I checked its hypotheses against `prop-sf-pf-reduction`, `lem-pur-system-level-projection-formula-coherence`, `thm-sf-pf-field`, `lem-cbc-rational-compact-support-coefficient-coherence`, `lem-pur-compact-support-condensed-realization`, and `thm-sf-pf-proetale`, together with the comparison data in `def-sf-datum` and `def-exchange-projection`. These statements explicitly preserve units, counits, tensor/pullback maps, compactification maps and transitions, so transport is by functoriality of specified composites and does not assume faithfulness of reduction. All three new nodes were searched with LeanSearch, Loogle and Mathlib grep; the recorded queries and results are in their `mathlib_searches` fields and in `searches.jsonl`. I tested edge cases in the review: identity base change, proper (f), empty open, (U=X), one coefficient quotient, and a constructible integral input without a finite-Tor hypothesis. No new definition or Lean file was written.

## Retained repair audit, 2026-10-17

I compared all four sandbox node files with the current shared repository. Only the item exists there, still unsplit, and its six returned steps have lengths 1573, 1902, 6182, 1566, 2010, and 2076 characters. The retained repair keeps the exact statement, Lean record, and steps 1, 2 and 4; its steps 3, 5 and 6 are 1087, 1003 and 1233 characters. Thus this is the requested extraction of the returned arguments, not a rebase-only submission. The Q75 dedicated handoff has exactly those three repair points; its preceding entries concern other items. The older Q79 transport note supplies no further mathematical repair point.

For the open-factor node I read both the original 6182-character argument and the statements of `lem-sf-open-tensor-normalization`, `lem-cbc-completed-extension-zero-comparison`, `lem-fix-constructible-tensor-completion`, and `lem-pur-site-restriction-module-adjunction-exact`. I made the invertibility of the two completed open maps explicit in clause (3), because the item uses these maps to identify its source with an object in the image of the fully faithful open extension. This asserts the consequence of the original completion comparison and strict-tower construction, without adding finite Tor amplitude to K. Finite type over the field supplies the quasi-compactness required by the completed extension theorem. The empty open gives only zero extensions and zero-to-zero isomorphisms; the identity open gives the original object and identity maps. At a point the tensor-completion comparison is the usual comparison for bounded finite R-modules; neither clause (2) nor clause (3) requires flatness of their cohomology.

For the pasting node I checked the types of z, d and v. Both open routes end in j'_!(AK tensor J'HFL); v then uses J'(theta_L inverse), giving j'_!(AK tensor J'F'GL). Substitution of the open identity into R'(v)e G(R(gamma)pi), naturality of e at gamma, and the proper identity give the asserted right hand side; naturality of the proper projection at beta_K gives its final form. Hence this node is the conditional diagram-pasting argument, not the unconditional base-change clause of the item. No invertibility of proper exchange is needed. For identity g all comparisons reduce to the identity normalization, and for j=id this is just the proper-factor equation.

For the transport node I read its entire comparison-data hypothesis and checked each factor of the four composites against `def-exchange-projection`. Applying a functor preserves composition; the hypothesized intertwining equations successively replace the unit, square comparison, counit and open tensor/base-change maps by their counterparts. Their adjacent comparison isomorphisms cancel, leaving exactly b_t T(m)=m b_s. Composition cocycles identify successive coefficient transports, so equality is pushed forward without claiming that finite evaluations detect equality. Identity comparison functors give the original equation, and no reduction functor on a rational object is introduced.

The Not duplicates audit includes the closest existing statements: `lem-sf-open-tensor-normalization` concerns ambient and diagram-site maps, rather than completed constructible restriction and strict-tower normalization; `lem-pur-system-level-projection-formula-coherence` gives the composition law in semilinear systems, rather than the conditional open/proper base-change pasting equation; `lem-cbc-rational-compact-support-coefficient-coherence` intertwines compact-support exchange under scalar extension, rather than all four composites under general supplied comparison data. I reran whole-blueprint and DAG keyword searches and read these nearby statements. The new lemmas are smaller components of the retained proof route.

I checked delivery-errors B–E: new nodes are statement-only and introduce their objects and coefficient domains; all use the existing definitions; no Stacks tag is claimed by these formal lemmas; the search records agree with the retained command log and their actual hits. Every item-step citation has a verbatim quote in citations.json, checked against current statements, and every non-elementary step names its used results. No new node restates the whole item or asserts its unconditional base-change conclusion. The proof uses the current blueprint and its formal open/proper route, never an SGA source.

The first required dry run reached citation validation and rejected the stale quote for the open-factor lemma after I made its isomorphism assertions explicit. I replaced it with the verbatim final clauses (1)–(3), then reran delivery checks.
