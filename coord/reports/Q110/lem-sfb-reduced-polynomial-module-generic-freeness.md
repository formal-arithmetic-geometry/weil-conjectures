# Q110 stage-1 delivery

Item: lem-sfb-reduced-polynomial-module-generic-freeness. Stage 1 only; no Lean writing, compilation, Lake, or repository mutations.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-reduced-polynomial-module-generic-freeness.json: item, statement unchanged, complete nine-step split following the polynomial case of Stacks 051Z.
- dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-good-locus-localization.json: statement, unsplit; no Mathlib match. Polynomial specialization of Stacks 051X.
- dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-good-locus-extension.json: statement, unsplit; no Mathlib match. Polynomial specialization of Stacks 051W.
- citations.json: verbatim statement quotes for every cited node in every item step.
- searches.jsonl and research/: genuine msearch log, exact queries, and full search outputs. Some additional exploratory searches concern prospective nodes that were not created because existing nodes were found.

## Attachments

None. I searched lean/WeilConjectures both for the item tag and for generic freeness and the reduced/polynomial/module notions. RingHom.exists_nonzero_flat_localizationAway, in RingTheory/GenericFlatness.lean, assumes a domain and concludes algebra flatness, not the item's clauses for finite polynomial modules over reduced rings. The project FreeLocus file covers Noetherian-domain generic freeness, also with stronger hypotheses. No exact project declaration was found.

## WANTED

None. All mathematical sources used are in literature/stacks-project/algebra.tex.

## Corrections and route

The imported statement is correct and unchanged. No STATEMENT-DISPUTED issue was found. The original proof was empty. I read the full polynomial-algebra argument in Tag 051Z, from its induction on n through both cases of its induction on m, as well as the preceding good-locus definitions and Tags 051W, 051X and 051Y. The source's text says R/J_i once where its filtration actually has P/J_i; this split uses the polynomial ring P throughout.

The source omits details for the claim that every element of the coefficient ideal is a coefficient of a relation. Rather than depend on that claim, Step 4 uses the principal opens of the actual coefficients, which cover exactly the complement of the coefficient ideal's vanishing locus. On each such chart a specific relation already has a unit coefficient. This implements the same localization reduction and the same two inductions without a hidden coefficient lemma. It changes no unit or chapter route.

The source asserts equality of the two good loci after reducing the number of variables. Only one inclusion is needed. Step 7 explicitly derives that inclusion using the existing Tag 0561 node: finite presentation over the smaller polynomial ring transfers to the larger finite type polynomial algebra. Freeness is over the same localized base on both sides. I did not cite the finite-extension equivalence (0564), whose hypotheses would be inappropriate for the polynomial ring extension.

The inherited blueprint ancestor is null: blueprint_refs.py ancestor reports None. The existing via chain and from.place are retained, and the two new nodes prepend this item to that chain. I read the current latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). The new nodes support the already recorded 051Z/052B/06QS/06RC input below that proof. Unit and chapter records were not edited.

## Not duplicates

lem-sfb-polynomial-good-locus-localization vs lem-sfb-reduced-polynomial-module-generic-freeness: localization compatibility holds for arbitrary modules and bases and makes no density assertion; the item proves density over reduced bases by two inductions.
lem-sfb-polynomial-good-locus-extension vs lem-sfb-reduced-polynomial-module-generic-freeness: the new statement is an extension inclusion for three arbitrary modules and makes no density assertion; the item proves density for one finite module over a reduced base.
lem-sfb-polynomial-good-locus-localization vs lem-sfb-polynomial-good-locus-extension: one compares a module with its base localization, the other compares three modules in an exact sequence; neither implies the other.

I searched the whole DAG by the tags 051W/051X and their source labels and by good-locus/localization/extension concepts, and searched all blueprint nodes with blueprint_refs.py. Neither good-locus statement exists. The existing lem-trf-polynomial-shear-leading-coefficient (051N), lem-trf-finitely-presented-over-subring (0561), and lem-weil-pbc-zero-locus-eq-iff-radical-eq (00E0) are used directly. I created neither a shear lemma nor a scalar-transfer lemma nor a reduced-basic-open lemma. A prospective polynomial-action lemma was discarded after locating 0561. The prime-stalk free locus is a different set from the union of principal charts with globally free module and polynomial finite presentation. The scheme-level maps-extension node lem-weil-pbc-module-finite-presentation-extension concerns extending maps over a qc open, not extensions in a module short exact sequence.

## Review by Q110

I checked the statement against the polynomial case of 051Z, including arbitrary reduced and possibly zero bases, finite generation over P rather than R, arbitrary free bases, and the finite-presentation clause over P_f. I read 051W and 051X in full for the two new statements; since a polynomial algebra is free on monomials and finitely presented over its base, the algebra conditions in the general good-locus definitions are automatic. Neither helper assumes finiteness or reducedness. The new files have statements and statement dependencies only, with no proof sketch or proof dependency. Their searches were run with msearch and both phrasings were examined. The extension search finds free_shortExact and finitePresentation_of_ker but no good-locus inclusion; the localization search finds freeLocus_localization, which concerns prime stalks, and free-localization spreading lemmas requiring finite presentation over the base. I read those declarations at Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean:103 and :171, RingTheory/Localization/Free.lean:78, Algebra/Module/FinitePresentation.lean:219 and :338, and Algebra/Category/ModuleCat/Free.lean:167. Combining their distinct inputs and localization comparisons is not a one-line specialization, so neither helper is a Mathlib leaf.

Step 1 uses the definitions already introduced in the item. I verified the fraction calculation showing reducedness survives localization, without assuming that R is a domain or that f is regular. Step 2 uses exactly the equality stated in the new localization node, then gives the topological density argument explicitly; no separate density-assembly node is needed. Principal opens form a basis directly from the definition of the Zariski closed sets V(I). Step 3 uses exactly the inclusion stated in the extension node. The filtration is constructed from a finite list of generators, so it needs neither Noetherianity nor a prime filtration, and no cyclic-filtration node was created for this elementary construction.

Step 4 uses the radical node's actual statement that the radical is the intersection of the prime ideals containing an ideal. Empty D(a) means a belongs to every prime, hence is nilpotent; Step 1 supplies reducedness of the localized ring. It also uses exactly the localization node's equality to justify chartwise density assembly. The principal cover is by actual coefficients, so a specified relation acquires a unit coefficient on each chart. The J=0 branch gives a polynomial module free on its possibly infinite monomial basis, with the identity presentation over itself. Step 5 explicitly sets the inner induction invariant and establishes the constant-unit case, which settles n=0.

Step 6 uses exactly the existing shear node's positive degree and leading coefficient drawn from the original nonzero coefficients. Its ring is arbitrary commutative, matching this application. All those coefficients are units in the m=0 case, so dividing by the leading coefficient is justified. The triangular substitution has the stated polynomial inverse. Reduction of powers by the monic relation gives the displayed finite generating list over n-1 variables; no assumption that J is finitely generated is used. The outer induction is invoked only when n>0. Step 7 uses exactly 0561's implication from finite presentation over a smaller ring to finite presentation over a finite type algebra. Here the larger ring is generated by y_n over the smaller one, and M carries its given compatible action. I checked the coordinate transport fixes R, so base freeness is preserved as well.

Step 8 reuses the localization equality and radical formula. On D(a), the selected coefficient becomes a unit; on a principal open disjoint from the closure of D(a), it becomes zero, not just a zero divisor. Unit coefficients remain units. Thus the number of nonzero nonunit coefficients decreases in either branch. The inner induction quantifies over all reduced bases, so it applies to each localization. The empty-spectrum exception handles localization to the zero ring. Step 9 merely assembles the two completed inductions and the finite generator filtration. The item has no step exceeding 2000 characters and no inline sub-claim hiding an unproved non-elementary lemma. Every cited statement was read in full and copied verbatim to citations.json.

I tested R=0, M=0, n=0, J=0 and J=P; R=Z with M=Z/2; products k times k with different ranks (which require separate principal charts); and reduced bases with zero divisors. The inner step can be seen concretely for g=x+2 over Z: D(2) makes 2 a unit, while the other branch is empty because D(2) is dense. For R=k times k the outside-closure branch can be nonempty and the chosen coefficient vanishes there. Nonreduced bases are deliberately excluded only in the item: over k[epsilon]/epsilon^2 the module k would disprove its density conclusion. Both helper statements remain valid there, since they assert only compatibility of good loci, not their density. Infinite base rank is necessary already for M=P with n>0. No hidden domain, Noetherian, nontrivial-ring, finite basis or finite-presentation hypothesis was added.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the files and sources: complete self-contained statement-only new nodes, definitions supplied, exact Stacks tags, genuine recorded searches, no Lean attachment, no duplicate or circular dependency, no new clause restating density, explicit induction and fraction comparisons, and all source hypotheses matched. The only off-unit uses are generic polynomial shear, scalar finite presentation transfer and the radical calculation, declared in split_report.tool_uses. No SGA is used.

## Unfinished work

Nothing remains for this one-level split. The two new unsplit lemmas are intentionally left statement-only for subsequent stage-1 items. The required dry run and delivery results are reported by the delivery command.
