# Q123: lem-trf-finite-ring-bundle-section-orientation

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-ring-bundle-section-orientation.json: statement node, now split into ten proof steps. The statement and imported metadata are preserved. No Mathlib match.
- citations.json: a verbatim statement quotation for every step/node citation.
- report.md: this report.

No new nodes; no new Mathlib leaves. The local write_split.py is a reproducible sandbox-only writer; searches.jsonl contains the actual search-command log. Neither is a library source or an additional DAG delivery.

## Attachments

None. Searched the project under lean/WeilConjectures for the blueprint tag and for vector-bundle, section-orientation, affine-purity and affine-adjunction terminology. The apparent affine-space base-change theorem in SixFunctors/Etale/Derived/SmoothDuality/SmoothBaseChange.lean, lines 80--89, contains sorry and uses pro-etale categories. OrientationDatum.lean defines compatibility structures; it does not prove this finite-ring ordinary-etale assertion. Neither is an attachment.

## WANTED

None. All documents used are present in the read-only literature tree.

## Findings and corrections

The imported item was unsplit. Its mathematical statement is unchanged. The proof distinguishes the ordinary finite-ring local argument from the final valuation-quotient identification. It never replaces the former by a pro-etale purity statement with narrower coefficients or bases.

An isomorphism of compact-support traces alone would not show that its adjunct is invertible. Step 2 instead compares the actual explicit affine-space adjunction with the ambient adjunction, using the unbounded compact-support compositor and conjugation of adjunctions. Likewise, source-locality alone does not identify dualizing objects after changing the base to an open: Step 3 writes the additional base-open adjunction into the Hom calculation. These were potential gaps in a short version of the imported argument, not errors in the statement.

The overlap need not be affine. Every overlap is Noetherian, and the trace and linear-invariance nodes apply to any such base. Step 1 explicitly cites that opens are etale and that quasi-compact open immersions are finite type, and checks separatedness using their diagonal. The source and base isomorphisms are open immersions onto the whole target.

The proof does not invoke descent for arbitrary derived morphisms. Both objects are shifted by -2d and are locally concentrated in degree zero; the existing degree-zero gluing theorem applies. Forward maps and inverse maps are glued separately, and uniqueness makes the composites identities. The final comparison checks the canonical projection formula at the coefficient unit, so equality of normalizations is equality of actual morphisms.

## Not duplicates

No new nodes. The whole-DAG searches and blueprint_refs.py searches for vector bundle orientation, section orientation, linear trace and coordinate terminology found the existing affine-trace, linear-invariance, vector-integration and degree-zero-gluing inputs, which are reused. det-sp-orientation-vector-bundle and cor-pur-vector-bundle-purity concern narrower purity conventions and a different orientation/compatibility assertion; they are not substituted for this finite-ring zero-section statement. blueprint.same_as remains empty because no imported blueprint node states this whole assertion.

## Mathlib searches

Preserved all inherited searches. Ran Q123 searches through the required msearch.py command: two distinct semantic phrasings with LeanFinder, one LeanSearch phrasing, Loogle for CategoryTheory.Adjunction, CategoryTheory.Functor, and two Mathlib/AlgebraicGeometry greps. Read the returned hits. Semantic hits concern ordered-module orientations or topological/manifold vector bundles. Loogle gives ordinary adjunction definitions and constructors. The geometry greps find no etale orientation theorem. None gives this statement or a one-line specialization. Exact query text and actual log results are appended to mathlib_searches. No unavailable service was recorded as a negative result.

## Route and sources

Read GOAL.md, the fixed chapter record sec-trace-formula, unit sk-i-curve-zero, the three blueprint levels in SETUP.md, the worker contract, and delivery-errors B--E in both occurrences. The item is a tool in the normal-cone specialization portion of lem-trf-local-term-locality proof (2), not the unit's key node. No unit/chapter record is changed. Its current source is main-20261015 sec-smooth-purity/sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md Step 4, read in full. Also read the current affine-space trace proof, vector-integration proof, vector-bundle-purity statement/proof, and affine-local adjoint-locality proof. The expanded proof is marked agent-written because these blueprint texts are agent-written.

Read Stacks more-etale.tex: Tag 0F7H (section-derived-lower-shriek-compactification, explicitly allowing the unbounded category for a torsion ring), Tag 0F7I (lemma-shriek-well-defined), Tag 0F7J (lemma-shriek-composition), Tag 0F7K (lemma-pseudo-functor), and Tag 0F7L (lemma-base-change-shriek). Read derived.tex Tag 06XS (lemma-negative-exts), sites-modules.tex Tag 03EM (lemma-internal-hom), and sites.tex Tag 04TQ (lemma-glue-maps). These support the existing comparison and degree-zero-gluing tools; no new node cites a section number as a lemma. No SGA source is used.

Off-unit uses in split_report.tool_uses are existing generic tools for the specified ordinary-etale section-orientation argument: geometry of bundle compactifications and opens, normalized affine trace, coherent compact supports, open adjunctions, ordinary Tate pullback, degree-zero gluing, and mate and tensor-unit calculus. They do not replace the normal-cone/contracting-correspondence route. The maintainer can judge these declarations on review; no top-level tool_uses has been set.

## Review by Q123

I read the item and every cited node's statement with its source, and checked that each proof use is a statement-level consequence. citations.json copies those statements verbatim, including the exact finite-ring and category hypotheses. There are no new-node sources to audit.

1. The projective-completion node expressly supplies Noetherian E and its compactification. The open-subscheme node supplies Noetherian overlaps and the inverse images of affine opens. The two open-immersion nodes give etaleness and finite type; separatedness follows because the diagonal of an open immersion is its identity. The Tate node supplies the actual inverse-image identification of the line. This verifies all locality/compositor hypotheses, without supposing affine intersections or separatedness of S over any field.
2. The affine-trace statement supplies the explicit adjunction with right functor p^*(-)(d)[2d] and the normalized counit. Its comparison is stated on bounded-below objects there, so the separate unbounded comparison theorem is necessary and cited. The conjugation node explicitly says a left-functor isomorphism gives an invertible right-functor conjugate; the ambient-adjoint node supplies that other adjunction. This makes alpha invertible with its specified counit, not an arbitrary isomorphism.
3. The etale-locality node gives the exact extension/restriction adjunction for both source and base opens. The compact-support theorem gives Rpi!v! = u!Rb!; the composite-adjunction node specifies the corresponding Hom bijection. The conjugation and mate-pasting nodes ensure it is the counit-preserving comparison and that the comparison composes. I checked the Hom domains: M is on E_T; the two intermediate targets are respectively on S and T, so no coefficient category or base is confused.
4. The affine-trace base-change equality applies to the bounded-below line L and to every Noetherian W. Together with Step 3 and the Tate identifications its adjoint is precisely the claimed restriction equality of alpha maps. This is an equality of the actual maps, not of isomorphism classes.
5. The linear-trace node uses exactly the pullback action rho_g. The isomorphism adjunction moves the pulled-back source across its inverse compact-support identification, producing rho_g inverse in the transpose; invariance under rho_g implies invariance under its inverse as well. The conjugation and mate-pasting statements supply this change of adjunction. The vector-bundle definition states that the frame transition is a matrix in GL_d of the global functions on W and that all linear maps preserve zero. I use no determinant/sign character. Pulling the equality back to zero and inverting proves overlap equality.
6. Exact inverse image and Tate pullback identify the shifted local objects with degree-zero sheaves. The gluing node explicitly requires just this local concentration, gives both existence and injectivity of restriction on Hom, and includes the empty cover. Applying it to inverses proves invertibility rather than merely a globally defined map. This also proves independence of the chosen cover and restrictions to any other frame.
7. The comparison for h followed by a frame is the composite comparison by the cited conjugation and mate-pasting laws. The source-locality lemma applies since h is an isomorphism of Noetherian bundles, hence an etale separated finite-type map. In the pulled-back frame both maps are literally the same local orientation; the gluing injection proves equality globally.
8. I checked d=0 using the explicit identity adjunction and rank-zero symmetric algebra, the empty base using empty-cover gluing, and A=0 using the zero module category. N=1 reduces to A=0. These cases use neither a nonzero section nor a nontrivial coefficient ring.
9. The projection-map definition explicitly defines the proper map as the adjoint of a counit tensor identity. At the tensor unit the triangle identity makes it identity; the unit constraints and open tensor-comparison statement specify the remaining maps. Thus no unproved projection formula for arbitrary coefficients is being invoked here. This is an elementary normalization calculation from these definitions.
10. The bundle-purity statement covers the precise valuation quotient, any Noetherian S with ell invertible, and the unbounded ordinary category. Its gamma is defined by the canonical projection and the actual integration map. The vector-integration statement explicitly specifies its local restrictions as the same affine traces. Steps 3 and 9 identify the local adjunct, and Step 6 identifies inverse section maps globally. The Tate node includes the divisible-annihilator power-map comparisons, so a common multiple identifies an arbitrary allowed N with the ell-power convention. No finite-type-over-a-field restriction or coefficient flatness has been inserted.

I checked delivery-errors B--E point by point: complete statement and existing definitions, no new unsplit proof sketches, actual searches and sources, verbatim citation coverage, no movement of an item clause into a new node, no unsupported isomorphism-to-adjunct inference, no general derived-morphism descent, no affine-overlap assumption, and no source or target weakening. Every proof step is below 2000 characters; the formal comparisons are written explicitly rather than hidden in a long step. The dependency graph is checked by the required server preflight below.

## Unfinished work

None in the authorized stage-1 split. The pre-existing dependency nodes retain their independent proof/formalization status. This delivery writes no Lean and runs no compiler.

## Validation

The required server dry run returned OK (not pushed): tools/preflight_delivery.py passed, including the DAG and split checks. No Lean compilation was run. The final dry run and push use this completed report.
