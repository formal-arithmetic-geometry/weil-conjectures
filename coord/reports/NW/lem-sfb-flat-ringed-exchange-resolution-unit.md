## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-flat-ringed-exchange-resolution-unit.json: item split, statement unchanged, five proof steps; no new nodes or Mathlib leaves.
- citations.json: one verbatim statement quotation for each of the seven cited node occurrences.
- searches.jsonl: five actual Mathlib searches made through msearch.py; inherited search records remain in the item.

## Attachments

None. I searched WeilConjectures by the exact blueprint tag and by resolution-unit, derived-mate and exchange terminology. The general theorem CategoryTheory.Adjunction.derived_mateEquiv_app_fac in WeilConjectures/Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:107 is a useful formal comparison but assumes a separate compatibility equation hθ; it does not itself state the geometric item. The existing module/abelian termwise-exchange nodes only concern constant coefficients or require exact vertical inverse images. They cannot be attached to this item for arbitrary structural ring maps.

## WANTED

None. All sources used are available locally.

## What needed correction

No statement correction or statement dispute. The unsplit item had no proof. The main pitfall is that only the horizontal pullbacks are exact: a generic derived-mate theorem requiring exact vertical pullbacks cannot be applied. Another pitfall is proving the equation only on injectives and then cancelling a noninvertible resolution unit at an arbitrary P. The proof avoids both by rotating the specified square to the horizontal adjunctions. It invokes existing every-complex normalization statements for composition and 2-isomorphisms, then gives the entire naturality calculation.

The inherited blueprint reference has from.node = null, confirmed by blueprint_refs.py ancestor. I preserved that field and its existing precise place/via chain. I read the current latest blueprint direct-images proof and the unit record. This is a generic normalization prerequisite below its direct-image step, and changes neither the unit statement nor its route. The item is not the unit key node, so no unit realization file was changed.

## Unfinished work

None for this one-level split. The proof uses existing dependency nodes; those nodes retain their own status and proofs. There are no new obligations hidden as statement-only copies of the desired equality.

## Not duplicates

No new nodes. Existing lem-weil-pbc-derived-exchange-module-termwise and lem-weil-pbc-derived-exchange-termwise concern constant-coefficient scheme sites and resolution representatives. Existing lem-pur-exact-derived-mate requires exact vertical left adjoints, which this item does not assume. Existing lem-sfb-ringed-derived-composition-comparison and lem-sfb-ringed-derived-two-iso-comparison supply the strictly smaller path normalization inputs and are reused. Whole-blueprint searches for derived adjunction, resolution unit and ringed exchange found no equivalent item statement.

## Review by NW

I read sites-cohomology.tex Tag 0736 (lemma-base-change-map-flat-case), including the actual injective-resolution construction, and Tag 07A7 (remark-base-change), which defines the unbounded geometric mate by its transpose. Neither source passage alone explicitly states the requested arbitrary-representative equation. I therefore mark the explicit normalization calculation as agent-written, rather than claiming it is a quotation from Stacks. I also read Tags 0D6D (lemma-derived-pullback-composition), 0D6E (lemma-derived-pushforward-composition), the adjunction passage Tag 07A6 (lemma-adjoint), and Tag 0FPI (lemma-adjoints-push-pull-compatibility). The recorded DAG comparison nodes make the universal units and the specified 2-isomorphism more explicit than those source passages.

For step 1 I opened all three cited statements. The exact-functor node says every complex computes both derived functors, so only the stated exact horizontal pullbacks are identified termwise. The adjoint-lift node supplies the geometric functors, not arbitrary substitute adjoints. The resolving-derived-adjunction-normalization node explicitly supplies its transpose formula for every chain map; it does not impose K-injectivity on its target in that conclusion. Applied to the identity on BP and the ordinary horizontal counit, this gives the two displayed identities. In the latter case the ordinary transpose is the identity of aT. This checks the crucial non-injective case, and the comparison is for the canonical universal derived pair used in the item. Universal-pair uniqueness preserves these equations for any choice of that canonical pair.

For step 2 I opened both cited comparison statements and their recorded Comparison/TwoIso normalization fields in lean/Sheaf/SixFunctors/RingedDerivedComparisonData.lean:236 and :315 (read only). Composition.kappa_model is expressly quantified over every complex; TwoIso.pushforward_model has the same quantifier. Composing the two path equations and the 2-isomorphism equation yields (*), with the ordinary right path comparison t in the indicated direction. These are the actual statements being used, not an inference from bare existence of derived composition. All corners are small ringed sites as required, all four morphisms are ring-compatible ringed-topos morphisms, and the square includes the specified compatible 2-isomorphism. No cartesian scheme-square assumption or coefficient-constancy hypothesis is introduced.

For step 3 I checked the specified mate in def-trf-topos-derived-base-change-map and the adjunction-direction/pasting clauses of lem-weil-pbc-mate-pasting. The latter is an existing Mathlib leaf. The full right conjugate of the inverse-image square has direction Rb to aS, so its horizontal mate is the displayed map A Rbar to Sbar B. The same rotation applies underived. Canonical adjunction compatibility of the step-2 comparisons fixes which mate is computed. It is a formal application of existing mate identities and triangle identities, not a new comparison lemma.

Steps 4 and 5 use only those displayed equations, naturality, and functoriality. I checked their domains explicitly: W = BP is on X', SW is on Y', and η^S_W has domain Q(SW) and target Sbar(QW). First naturality of η^R moves the genuine complex map u_P through its resolution transformation; (*) applies at W. Then naturality of the horizontal derived counit moves η^S_W to the left, and the second step-1 normalization applies at SW. The final parenthesized chain map is exactly the ordinary mate e_P by (***). These elementary steps require no further non-elementary fact or source node. Neither resolution transformation is inverted, and neither pullback is asserted to preserve injectives or K-injectives.

I tested zero complexes, identity horizontal morphisms, and identity vertical morphisms. The zero case gives zero morphisms; identity horizontal maps give the ordinary naturality normalization; identity vertical maps reduce to the canonical identity-derived-unit comparison. General nonflat vertical maps are permitted throughout because the rotation uses only horizontal exactness. Noninvertible resolution transformations remain in the formulas, including for a nonacyclic module concentrated in degree zero. I checked the two other exact-derived-mate candidates precisely to avoid their additional exactness hypotheses. No new statement was introduced, so there are no new small-case assertions to test.

Against delivery-errors B through E: the item remains self-contained and retains every statement notion/dependency; no new node, proof-sketch statement, duplicate, clause copy, or Mathlib leaf was manufactured. All newly recorded searches actually ran and their hits were read; the single-adjunction normalization hits do not state the geometric square theorem. Every proof citation has a literal quotation from its statement in citations.json. Every invoked non-elementary normalization is a cited existing node, with off-unit use declared as a generic tool. A read-only dependency traversal found no cited node reaching the item. All five steps are below 2000 characters; their arguments are written out and hide no new geometric lemma. No SGA source is used, no Lean was written or compiled, and all writes are confined to this sandbox.
