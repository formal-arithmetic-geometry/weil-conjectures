# Stage-1 delivery: lem-trf-affine-fan-canonical-section-rigidity

## Files written

- dag/nodes/sec-trace-formula/lem-trf-affine-fan-canonical-section-rigidity.json: statement, split into four steps using existing nodes. No Mathlib match.
- citations.json: six verbatim quotations, one for each step/dependency pair.
- report.md: this report.

There are **0 new nodes and 0 Mathlib leaves**. Existing source metadata, statement, earlier searches, ancestry and creation record are retained.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint id, MonoidalSpace, MonoidSpectrum, sharp monoids, monoid spectra and fine fans found no project declaration giving this item. Ring-spectrum results do not apply to arbitrary sharp monoidal spaces.

## Literature wanted

None. Read the local ILO Travaux de Gabber PDF, Expose VIII, printed pp.98--99 (PDF pages 104--105): 3.1.1 sharpening, 3.1.2 localization, 3.1.3 spectrum and basic opens, 3.1.4 local structure, 3.1.5 locality, 3.1.6 morphisms, and Lemma 3.1.8(ii) with its proof via (i). No SGA source is used. There is no Stacks tag for this monoidal-spectrum assertion; the sheaf separation used below is the equalizer definition already in the DAG, not an uncited comparison theorem.

## Findings and scope

The item is correct as stated. Its earlier empty proof is replaced by the explicit uniqueness calculation omitted in the source's short universal-property proof. No statement correction or dispute is needed. The parent universal-property node depends on this item, so citing that parent would be circular; it is not cited. The nearby germ-rigidity item is a different, stronger neighborhood assertion requiring finite generation and is not needed here.

Read GOAL.md, SETUP's three blueprint levels, the chapter and unit records, and literature/blueprint/latest (main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345). Read the current chapter, unit, and lem-trf-local-term-locality statement and proof. This fan item belongs to the recorded historical alteration/nearby-duality support branch; the current ancestor uses contracting correspondences instead. This delivery changes only the assigned supporting item and does not replace a unit or chapter step. The recorded historical provenance is retained and explained in split_report.blueprint.

## Searches and reuse

The sandbox initially contained only dispatcher brief markers, with no item, report or earlier search log. The item was read from the shared repository. Before writing, searched the whole DAG for canonical-section fan assertions and basis/sheaf uniqueness; opened the existing localization-sections, fine-fan-blowup, hom-universal and germ-rigidity nodes. tools/blueprint_refs.py ancestor gave lem-trf-local-term-locality. Whole-blueprint searches for affine fan and sharp monoid gave zero matches; the broader monoid search found general monoidal category facts but no affine sharp-monoid spectrum statement. A textual search of the current latest blueprint likewise found no replacement for this supporting item. No duplicate was created.

Ran the required msearch wrapper for this item with LeanFinder (two different phrasings), Loogle, grep, and LeanSearch; exact tool/query texts and actual log summaries are appended to mathlib_searches, preserving the older entries. Read every returned signature. Checked Mathlib/AlgebraicGeometry/Spec.lean:167--181 (Spec.basicOpen_hom_ext), GammaSpecAdjunction.lean:258--267 (comp_ring_hom_ext), and AffineScheme.lean:154 (ext_of_isAffine). These concern commutative rings and ringed spaces/schemes, not fine-monoid spectra and monoid sheaves. LeanSearch also returned localization-map extensionality, whose input is equality of underlying homomorphisms, not the monoidal-space recovery asserted here. None is an exact match or a one-line specialization. Loogle and the monoidal-spectrum grep returned zero hits. The successful new LeanSearch is recorded as successful; the inherited unavailable 2026-10-22 search is preserved as historical evidence, not used for an absence verdict.

## Not duplicates

No new nodes. The existing localization-sections lemma gives stalks and canonical zero germs, but does not give point recovery after a local morphism or uniqueness of that morphism. Its statement is used directly. No source-tag duplicate pair is introduced.

## Review by NC

I read the source's uniqueness claim together with its definitions, rather than applying the whole universal-property lemma to itself. I opened the statements of all three cited DAG nodes and checked the six quotations against their exact decoded statement strings before writing citations.json.

Step 1 uses def-trf-fine-fan-blowup for locality as inverse image of units and for the stalk-map convention. It uses lem-trf-affine-fan-localization-sections for the precise sharpened stalk and the equivalence between a canonical zero germ and avoidance of the prime. The target stalk is sharp by the item's hypothesis; the source stalk is sharp because an invertible class in a quotient by units has a representative which is a unit. The proof writes that elementary inverse calculation explicitly. Thus localness detects zero in both directions, with no injectivity assumption on the stalk homomorphism. The formula for the point is complement in P, including the empty prime.

Step 2 uses def-trf-fine-fan-blowup for P_a and the quotient by units and the localization-sections statement for the canonical restriction maps. Both na and -na belong to P_a, so their classes vanish; no saturation, torsion-freeness or freeness of P is used. This gives cl(p-na)=cl(p). Naturality of the given sheaf map then gives precisely the requested restricted canonical pullback. Every element is such a numerator/denominator class, so no denominator-generating assertion is hidden in the step.

Step 3 uses the basic opens in def-trf-fine-fan-blowup and the equalizer definition of a sheaf of sets in def-weil-pbc-sites-and-cohomology, clause (1). The former definition makes a monoid sheaf a sheaf on underlying sets. For any U, the D(a) contained in U cover U, and their inverse images cover g^{-1}U by continuity. Restrictions of the two images of a section agree by naturality and the prescribed basic components. The equalizer map is injective, which proves equality. This is an explicit application of the sheaf definition in a few lines, not an uncited theorem extending a functor from a basis. Existence is already supplied by the given morphism g. The empty-open case follows from the empty-cover equalizer.

Step 4 uses only Steps 1--3 and extensional equality of the two pieces of the morphism data. It first identifies point maps, then basic components, then all open components; it does not compare sheaf maps before identifying their inverse-image domains.

For the B--E checklist: no new statement-only child, elementary child, duplicate, clause restatement or false Mathlib leaf was introduced. All objects are quantified in the existing statement. TeX uses single backslashes after JSON decoding. Cited statements contain exactly the facts used; every non-elementary step cites the needed definition and localization theorem. There is no self-reference or dependency on the parent. Step lengths are 708, 589, 644 and 409 characters, all below 2000. Tested P={0}, p=0, a=0, n=0, empty T and empty inverse-image opens. For P=N the generic prime has zero stalk and the closed prime has nonzero positive germs, which agrees with the formula. Nonsaturated P=<2,3> causes no issue because only localization and units are used; T need not be finite or a fan. Omitting locality really would invalidate point recovery (the zero homomorphism at the closed point of S(N) illustrates the failure), so it is explicitly retained and used. I found no remaining mathematical gap.

## Unfinished work

None in this one-level split. No Lean was written, and no compiler, Lake, build, local check_dag, local review_split, or local preflight command was run. The required server dry run and direct delivery follow this report.
