# Worker report — Q103

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-perfect-residue-coefficient-dvr.json`: item, statement, split into six steps; no complete Mathlib match.
- `citations.json`: verbatim statement quotations for all twelve step/node citations.
- No new nodes and no Mathlib leaves. The item statement and inherited provenance are unchanged.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and `Comparator/` for the exact blueprint tag and for perfect residue fields, coefficient DVRs, Cohen, and formally smooth coefficient extensions. No project declaration states this item. The existing generic source declarations do not supply the full coefficient-DVR construction.

## WANTED

None. I read ILO, *Travaux de Gabber*, Expose IV, printed pp. 56–59, especially 4.1.2–4.1.6 and the first two paragraphs of 4.2.5, in the repository PDF. Stacks sources for each of the actual support statements are present.

## Problems found and changes

The item was an unsplit supporting statement, not an imported blueprint theorem, and had no proof. Its formulation agrees with the coefficient-ring argument of IV 4.2.5. In particular, W need not have p itself as uniformizer, the extension k'/k_0 may be infinitely generated or imperfect, and C need not be a domain or flat over W. I retained all those cases.

The closest Mathlib result `Algebra.FormallySmooth.of_perfectField` has an `Algebra.EssFiniteType` hypothesis in the pinned `Mathlib/RingTheory/Smooth/Field.lean:53–59`. The field step cannot be dismissed as this instance in the arbitrary-extension case. Instead, I reused the DAG's arbitrary characteristic-p field nilpotent-lifting theorem and proved that its ring lift is k_0-linear by the pth-power calculation in step 1. This avoids creating a separate perfect-field formal-smoothness node. The m-adic versus discrete formal-smoothness distinction is explicit: step 1 uses the zero maximal ideal of a field, and steps 2 and 6 use the existing adic notion.

I reused the existing 07NR complete local model and 07NP flatness nodes. The assertion that its model is a DVR is proved in the item: flatness makes pi a nonzerodivisor, the quotient field makes (pi) maximal, separatedness gives finite orders for nonzero elements, and least orders generate ideals. Thus no new node merely restates the first clause. I also wrote out why pi C is closed, using completeness of C/pi C, before applying 07NJ. This matters when pi is a zerodivisor in C.

I searched all DAG statements/titles and the blueprint with `tools/blueprint_refs.py search` for perfect fields, separable fields, formally smooth, and coefficient DVRs; read the existing 0322/0320 users; and checked the actual statements of the selected nodes. No new node is needed. The nearest blueprint ancestor is `lem-per-artin-gabber-affine-curve`; its current duality chain reaches this construction through `lem-per-cohen-gabber-finite-presentations` step 7. I read the unit and chapter records. I did not change the unit's realization, since this supporting item is not its key statement. The six generic off-unit algebra theorem citations are explicitly declared in `split_report.tool_uses`.

The earlier NG searches in the item are preserved. My additional actual msearch queries and returned hit names are recorded in `mathlib_searches` and in the tool-written `searches.jsonl`, including second phrasings. They find lifting tools and the finite-type field instance, not the item's full construction. No searches are invented and no unavailable service is called a negative result.

## Not duplicates

No new nodes. Existing nodes supply every non-elementary input, and elementary perfect-base linearity, DVR division, injectivity, and ideal-closure deductions remain steps of the item.

## Review by Q103

I checked the item against the actual French statements of ILO IV 4.1.3 (complete metrizable target, closed ideal with powers tending to zero), IV 4.1.5 (flatness and formally smooth closed fibre), IV 4.1.6 (lifting the complete formally smooth quotient algebra), and IV 4.2.5. The source constructs V exactly by lifting k'/k_0 and then lifts V into A' by formal smoothness. The split follows these operations, with Stacks 07NR and 07NJ stating the required general tools, rather than silently assuming a Cohen ring for the possibly ramified W.

For step 1 I opened `lem-weil-pbc-field-char-p-nilpotent-lifting`: it really asserts a ring lift from ANY characteristic-p field into ANY characteristic-p ring through a nilpotent ideal. Here D is a k_0-algebra, so p vanishes; J squared is zero, so N=2 is valid. It does not assert k_0-linearity, so the step proves that separately: write every base scalar as a pth power, and use the characteristic-p binomial identity to kill the difference in J. I also opened the adic-formal-smoothness definition and checked that the field's zero ideal makes its continuity condition automatic. No separable-algebraic hypothesis is imposed on k'.

For step 2 I opened `lem-weil-pbc-fs-adic-lift-from-residue-field` and read Stacks `more-algebra.tex`, Tag 07NR, label `lemma-lift-fs`. Its statement includes the compatible A_0-algebra quotient isomorphism, which is essential: it gives the specified, not merely an abstract, map of residue fields. W is Noetherian since all its ideals are principal; k' is Noetherian and complete for zero. These verify all hypotheses. This use does not claim that V is already a domain.

For step 3 I opened `lem-weil-pbc-fs-adic-local-flat` (07NP, `lemma-formally-smooth-flat`), `def-weil-pbc-flat-ring-map`, and `lem-weil-pbc-dvr-unit-times-uniformizer-power` (00PD, `lemma-characterize-dvr`). The first applies to Noetherian LOCAL rings and the local h from step 2; the definition explicitly preserves injections on tensoring, exactly what is used on multiplication by pi in W. The tensor identification is given with its inverse. The DVR factorization theorem is applied to W, which is already a Noetherian local domain with nonzero uniformizer, not prematurely to V. The field quotient V/(pi) is nonzero and identifies (pi) with the unique maximal ideal; the nonzerodivisor calculation then proves injectivity of W to V.

For step 4 I opened the completeness and DVR definitions. Completeness explicitly includes intersection of ideal powers equal to zero. The finite-order argument is written out and supplies both the domain property and principality of every ideal. It is an elementary deduction from the established nonzerodivisor and principal maximal ideal, not an uncited invocation of a regular-local characterization. The zero ideal and the requirement that V not be a field are included.

For step 5 I opened `lem-weil-pbc-complete-local-quotient` and read Stacks 0325, `lemma-quotient-complete-local`. C is Noetherian and complete and pi C is proper because the structure map is local. The theorem gives completeness, hence separatedness, of C/pi C for n/pi C. The equation for the intersection of (pi C+n^m)/pi C is therefore zero, giving exactly the closed-ideal equality demanded by the next node, not a different topology.

For step 6 I opened `lem-weil-pbc-fs-adic-lift-into-complete` and read 07NJ, `lemma-lift-continuous`, as well as ILO IV 4.1.3. Its statement explicitly gives an R-algebra lift with the source ideal mapped into the target ideal of definition. I matched all arguments: source W to V, source ideal m_V=(pi); complete target C with I=n; J=pi C closed by step 5; t=r=1 since J is contained in n and g kills m_V. The compatibility of the W-action is proved from e and s. Locality is checked by the image of m_V and preservation of units; the given residue isomorphism from s is retained. No C-flatness, C-domain, or pi-regularity assumption is used.

I checked the B–E faults: no new statement-only node carries a hidden proof; no duplicated node or restated item clause is introduced; all citations quote the opened statements verbatim in citations.json; all uses are in proof_deps; no definition is cited for a theorem it does not state; no SGA route is used. Every proof step has fewer than 900 characters, so none hides a long comparison lemma. Small cases checked were k'=k_0 (V=W is possible), ramified W with p a unit times pi^e, k'=k_0(t) and arbitrary infinitely generated extensions, C of characteristic p with pi=0, and C=W/pi^a with nilpotent pi. The lifting argument still works in the latter cases; it intentionally does not assert that V to C is injective. Perfectness is used only for automatic base linearity in step 1. There is no statement dispute and no source correction.

## Unfinished work

None in the one-level split. The delivery remains subject to the maintainer's independent mathematical review.
