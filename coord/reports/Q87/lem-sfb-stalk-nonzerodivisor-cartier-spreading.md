# Stage-1 report: lem-sfb-stalk-nonzerodivisor-cartier-spreading

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-stalk-nonzerodivisor-cartier-spreading.json`: statement, now split into eight steps; no Mathlib match for the complete statement.
- `citations.json`: every step/node citation with a verbatim quotation from its statement.
- `searches.jsonl`: the required search command's actual log; five new searches, in addition to the inherited item searches, retained intact in the item.
- `report.md`: this report.

No new nodes, hence zero new Mathlib leaves. `prepare.py` is a sandbox-only preparation script, not a DAG delivery file.

## Attachments

No attachment for this item. Searched the live `lean/WeilConjectures/` for the exact blueprint id and for Cartier/nonzerodivisor terminology. Its ideal-sheaf Invertible and EffectiveCartier modules define the local equation condition and prove flat-pullback/locality properties, but do not prove this stalk criterion or the algebraic spreading assertion. The already attached affine module-germ theorem belongs to the existing `lem-sbc-affine-module-germ-localization` and is reused without modifying that node.

## Wanted literature

None. Read Stacks `divisors.tex`, Tag 0AG8, label `lemma-effective-Cartier-in-points`, statement and proof; `algebra.tex`, Tag 061L, label `lemma-regular-sequence-in-neighbourhood`, finite-kernel proof; and `schemes.tex`, Tags 01IN (`lemma-closed-subspace-scheme`), 01I3 (`lemma-standard-open-affine`) and 01IA (`lemma-quasi-coherent-affine`), including the standard-open restriction description immediately preceding 01IA. The ring and module localization formulas in the cited existing nodes make the affine identifications precise.

## Problems found and changes

The statement is correct and unchanged. Its source handoff records an argument, rather than a completed proof. All of that argument is now implemented in steps, including a numerator actually in the ideal, all finite denominator products, the finite annihilator, and the explicit kernel calculation in the final localization. It is unnecessary, and would be false in this generality, to assume that the localization maps from the ambient ring are injective. No such assumption was used.

The inherited `blueprint.from.node` is null, and `tools/blueprint_refs.py ancestor` reports None. Retained that existing provenance and its explicit place/via chain rather than inventing an ancestor. Searched the whole DAG by Cartier, nonzerodivisor, localization, affine ideal-sheaf and annihilator concepts and Tag 0AG8, and searched blueprint references for localization, Cartier, nonzerodivisor, non-zero-divisor, principal ideal and 01IB. No blueprint node gives this statement. The regular-prime-divisor local-equations node uses regularity/integrality and is not this general criterion. This is not a unit key node, so no unit realization fields are changed.

The generic off-unit module basic-open localization tool is declared in `split_report.tool_uses`. It supplies standard quasi-coherent affine localization, not a replacement of the alteration/unit route. All other cited statement tools are Mathlib leaves or already Lean-closed.

## Unfinished work

None at stage 1. No Lean was written, and no compiler, Lake, build, local check_dag, local review_split or local preflight was run. Server dry run and direct push are performed with the prescribed delivery tool.

## Not duplicates

No new nodes. Existing nodes were reused for localized ideal membership, closed-immersion ideal sheaves, affine ring stalks, affine module germs, basic-open rings and basic-open module sections. In particular, no node merely restates the ring clause or scheme clause of this item.

## Review by Q87

I read the sources above and checked the split against B--E of delivery-errors in both copies of those sections. The statement of 0AG8 uses points on the closed subscheme; the item assumes the condition at every point, and outside the closed subscheme its ideal is the unit ideal. These formulations agree. The ring assertion is the affine argument in that proof, with its one-element finite-kernel argument expanded in the form retained in this item's handoff. No new hypothesis or weakened conclusion was introduced.

Step 1 uses the fraction definition in `def-weil-pbc-localization-at-prime`: an element of the extended ideal is a finite sum of fractional multiples of ideal elements. The written common numerator belongs to the original ideal. Multiplication by a unit times the given nonzerodivisor is injective. Step 2 uses exactly the finite-generation clause of `def-weil-pbc-noetherian-ring` and the statement of `lem-exc-localization-ideal-membership-clearing`, applied to the ideal `(a)`, not to `I`. I read its Mathlib declaration in Localization/Ideal.lean at lines 76--79. The explicit inverse of each denominator in the product localization is supplied, so the generator equality is proved rather than asserted.

Step 3 uses only finite generation of the explicitly defined annihilator ideal and the defining fraction zero criterion. It writes out how one product kills its whole ideal. Step 4 uses the away-localization equality definition: from a fraction killed by a, it produces an actual numerator in the annihilator, then multiplies by v. This works with zero divisors and nilpotents and never cancels g in B. These are short finite-generator and fraction calculations; no unproved regular-sequence or kernel-localization theorem is hidden in them.

For step 5 I opened all four cited statements. `pqf-def-locnoeth` supplies a cover by spectra of Noetherian rings, so I select a member of that cover rather than silently needing the theorem that every affine open is Noetherian. `def-sbc-closed-immersion-ideal-sheaf` explicitly gives quasi-coherence, the section ideal and its tilde description. `lem-weil-pbc-affine-open-stalk-localization` clause (c) supplies the ring localization respecting germs; `lem-sbc-affine-module-germ-localization` supplies the module germ as localization without a finiteness assumption. Applying the latter to the quasi-coherent ideal makes its image in the localized ring exactly the extended ideal. All their hypotheses hold for this closed subscheme and selected affine open.

For step 6, `lem-weil-pbc-affine-ideals-closed-subscheme` clause (0), not its converse construction clause, supplies an affine principal open and the ring restriction localization. `lem-weil-pbc-affine-module-basic-open-localization` supplies both fractions of sections and their zero criterion. Because the ideal inclusion is the sectionwise inclusion, these fractions identify its sections with the extended ideal inside B_g. Step 7 uses the affine ideal-sheaf description from the cited closed-immersion definition and compares the resulting open cover with the exact definition of effective Cartier ideal. It does not need a claim that arbitrary global equations exist. Step 8 computes the kernel on the open complement directly; the target sheaf of the defining map is zero there. Its cited Cartier definition allows the unit equation and a vacuous cover on the empty scheme.

For the edge cases I checked I=B (choose a=g=1), the empty closed subscheme, empty X, empty generating lists for a zero annihilator, and B with nilpotents. For example B=k[e]/(e^2) and I=B fits the unit case, so the argument does not smuggle in reducedness. The zero ring has no prime, so the ring hypothesis has no instance there. All steps have fewer than 2000 characters. Every non-elementary fact is supplied by the node statements just described; the citation file checks the quoted substrings literally. Searches returned associated-prime, regularity, principal-ideal, finite-localization and ideal-sheaf construction results, but none states the complete item or is a one-line specialization of it. No new unsplit node, duplicate, clause relabelling or cycle was introduced.
