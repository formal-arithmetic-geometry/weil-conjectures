# Q02: lem-cbc-derived-extension-zero-base-change-open-pasting

## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-derived-extension-zero-base-change-open-pasting.json: existing statement split in six steps, unchanged conclusion and hypotheses. No new nodes and no new Mathlib leaves.
- citations.json: verbatim statements for every node cited by each proof step.
- report.md: this author's review. searches.jsonl records the actual search calls.

## Attachments

None. The exact blueprint-tag search under WeilConjectures returned no declaration. I read the nearby BaseChangeSquare.lean definitions, unit formula, isomorphism theorem and comparison-to-star theorem; they do not state open-composition pasting. BaseChange.lean:487, AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChange_comp, concerns a fixed source X and successive ambient maps q₁,q₂ with j ≫ q₁ = k and k ≫ q₂ = l, rather than the two arbitrary cartesian squares with composable open verticals required here. Comp.lean:51 defines the composition comparison only. Thus none supplies an exact attachment.

## WANTED

None. The required blueprint, Stacks sources and pinned Mathlib source are available locally.

## Corrections and source comparison

The item was an unsplit statement-only child of the reviewed derived-base-change corollary, with no earlier sandbox split or report. No delivery invocation was interrupted or repeated. The imported statement is well-typed and true, including its orientation b = inverse exchange. Its id contains “derived” for historical reasons, but its title and statement explicitly concern the underived comparison; I preserve these fields.

The current blueprint main-20261015 sec-six-functors-basics/sk-prop-sf-cbc/cor-cbc-derived-extension-zero-base-change.proof.md ends with the pasting assertion. The item makes its open-immersion direction explicit. I retain its historical chapter, unit and ancestor binding and fill its from.place with that clause. I read dag/chapters/sec-smooth-purity.json and dag/units/sk-prop-sf-cbc.json; this is below the same finite-coefficient compact-support-base-change route, without changing a unit or chapter.

I read Stacks etale-cohomology.tex Tag 03S3 (definition-extension-zero), including the module adjunction and restriction description, and Tag 03S6 (lemma-shriek-base-change), whose proof uses uniqueness of adjoints. I read categories.tex Tag 0B65 (lemma-transformation-between-functors-and-adjoints) and Tag 0DV0 (lemma-compose-counits). I also read sites-cohomology.tex remarks-compose-base-change and -horizontal (Tags 0E46 and 0E47); these illustrate pasting for direct-image base change, so I do not apply their geometric statement to shriek. The actual categorical tool is the existing Mathlib leaf lem-weil-pbc-mate-pasting. I read pinned Mathlib CategoryTheory/Adjunction/Mates.lean at mateEquiv_hcomp:209 and the two conjugation formulas:486,505, including their exact orientations. The expanded argument is therefore marked agent-written, rather than claiming that Stacks writes this precise six-step proof.

No statement dispute, missing hypothesis or change of coefficient category was found. All inverse images are for constant Λ-module sheaves on small étale sites, not pro-étale or adic coefficients. Arbitrary g is allowed. Finiteness of Λ remains as requested, although the categorical argument needs only a commutative ring.

## Searches and reuse

I searched the full DAG by tag 03S6 and keywords, and tools/blueprint_refs.py by “pasting” and the longer statement phrase. The blueprint ancestor command returned cor-cbc-derived-extension-zero-base-change. Existing nodes provide every tool, so no child is created. The parent corollary's derived pasting assertion is not used to prove its own underived prerequisite.

Seven new Mathlib search calls are in searches.jsonl: two LeanFinder phrasings, LeanSearch, two Loogle attempts, and two grep calls. The first new Loogle pattern was invalid; its record says unavailable rather than claiming absence. The valid quoted mateEquiv_hcomp search finds the generic mate-pasting theorem already represented by lem-weil-pbc-mate-pasting. I preserve the inherited search queries and correct the inherited unknown-identifier Loogle verdict for the same reason. The source grep locates the relevant generic tools at lines 209,486,505. Semantic hits include Scheme.Modules.restrictFunctorComp; I read Modules/Sheaf.lean:478–489 and verified that this is restriction of structural modules, not extension by zero on the small étale site. No exact Mathlib leaf for the item was found; applying the generic theorem requires the unit and coefficient identifications supplied in the proof.

## Not duplicates

No new nodes. The existing lem-weil-pbc-mate-pasting is deliberately cited for its general clauses (2) and (3), not copied into a new geometric clause node. The underived-compatibility sibling identifies the project's alternate implementation of b; the vertical-pasting sibling concerns successive horizontal base maps. Neither is needed here.

## Review by Q02

I opened every cited node and read its statement. Step 1 uses extension-by-zero-adjunction for L_a ⊣ R_a, the open-square definition for the commuting schemes, sheaf-level clause (1) of derived-inverse-image-composition for associativity, and inverse-image-composition-module-linear for the lifts to modules. I explicitly write the s-comparisons as composites of inverse-image comparisons, so their pasting equation is the associativity equation with the two commuting-square equalities inserted. Equality on underlying abelian sheaves implies equality of module morphisms, since a module-sheaf morphism has the same underlying map with a linearity condition. No derived coherence is assumed on modules.

Step 2 uses extension-zero-base-change for the precise transpose of t = b⁻¹, adjunction-mate for the unit/counit formula and bijection, and extension-by-zero-adjunction for the module adjunctions. The displayed calculation applies naturality at ε and the triangle identity Rε ∘ ηR = id, verifying that t's mate is s. This avoids treating the raw b-map as a mate of the same orientation.

Step 3 uses the composite-adjunction statement for its explicit unit and the conjugate-iso-unit-equation statement for the unique unit-compatible left-adjoint comparison associated to r⁻¹. The composition node identifies the canonical comparison appearing in the item. The conjugate definition states the mate bijection and its inverse law; it gives cᶜ = r⁻¹ and ((c′)⁻¹)ᶜ = r′. I checked their types: c goes from the composite left adjoint to the single one; its conjugate goes from the single right adjoint to the composite. This is not a use of the composition node's proof in place of its statement: the extra unit equation is supplied by the separate uniqueness theorem cited here.

Step 4 substitutes all eight functors into clause (2) of the existing mate-pasting node. It gives T = (t_j L_k) ∘ (L_j′ t_k) and T-flat = (R_k′ s_j) ∘ (s_k R_j). All four left/right adjunctions are those established in Step 1, and the composite adjunctions are those fixed in Step 3. Step 5 uses clauses (3a),(3b) of that same leaf, including conjugate direction, to compute the mate of D = (P_X c) T ((c′)⁻¹ P_V) as (r′ P_X) T-flat (P_V r⁻¹). Substitution of the Step 1 equation makes this s_l. The mate-definition node explicitly states injectivity through a bijection, so D = t_l follows, without any claim about equality on stalks detecting equality of maps.

Step 6 only inverts that equation and cancels g⁻¹(c⁻¹) against g⁻¹(c). Its citations supply invertibility of the base-change and composition maps; the remainder is elementary functoriality and inverse cancellation. I checked that its source is g⁻¹j_!k_!F and its target is (j′k′)_!g_V⁻¹F on both sides.

Small cases checked directly in these formulas: F=0 and the zero coefficient ring give the unique map; V empty, U empty when possible, and X′ empty also give the unique zero comparison. If k or j is the identity, the unit-compatible composition comparison and the corresponding identity exchange cancel, leaving the other exchange. If g is the identity, s_k,s_j,s_l are identity comparisons after the standard identifications, so the equation is naturality of c. For a nonempty nested pair of proper opens, the same mate formulas still apply without supposing g itself open. No stalk-conservativity shortcut is needed. No point or nonempty object is chosen.

I checked delivery-errors B–E: no new node hides a clause, no unproved auxiliary statement is introduced, all non-elementary inputs are cited by their statements, every dependency exists, and no proof uses the parent corollary. All six steps are below 2000 characters; their categorical subarguments use existing nodes rather than hiding additional lemmas. Off-unit non-leaf tools are declared in split_report.tool_uses; mate-pasting and the adjunction definitions are already generic tools. No SGA source is used. No Lean file was written and no compiler or build was run.

## Unfinished work

None in the split. Server validation and direct delivery are performed with the required deliver.py commands.
