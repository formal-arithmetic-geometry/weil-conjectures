# Stage-1 report

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-affine-koszul-hom-alternating-cech.json`: repaired split item.
- `dag/nodes/sec-picard-framework/lem-sc-module-localization-filtered-colimit.json`: new unsplit statement node; Mathlib no exact match.

## Attachments

None. No sorry-free declaration states the item.

## WANTED

No WANTED items. I read `perfect.tex` lines 1911-2052 (Tags 0911 and 08D1) in the local Stacks source packet.

## What was repaired

The returned split had not defined $I$ from the chain Koszul complex, omitted the transition map, used the wrong combined sign, and cited the full ordered Cech definition for alternating rows. I now define $I^i=K_{1-i}$ with $d_I=-d_K$, state the transition on basis wedges, cite the existing alternating-Cech node, and use the unsigned fraction map with the corrected total twist `(-1)^(pq+p(p-1)/2)`. The source is available locally, so the proof origin is now document-based.

## Review by H1

I read `perfect.tex` lines 1911-2052, the item’s Koszul, Hom, and site-Cech definition nodes, and the existing `lem-pc-alternating-cech-computes` statement. Step 1 checks the wedge basis and transition against Tag 0911. Step 2 checks the one-element localization colimit and uses the alternating node’s strictly increasing rows and face differential; the full site-Cech definition supplies the restriction convention. Step 3 checks $d_I=-d_K$, the Hom differential, and both total differential formulas against Tag 08D1; I corrected the sign by using the unsigned fraction map and $(-1)^{pq+p(p-1)/2}$, and verified the two sign equations. I checked $r=0$ and $M^\\bullet=0$. Every citation quote is copied from its node statement.

## Not duplicates

lem-sc-module-localization-filtered-colimit vs lem-sc-affine-koszul-hom-alternating-cech: the new node concerns one module and one element's multiplication colimit, while the item concerns a finite Koszul Hom complex and all Cech rows.
lem-sc-module-localization-filtered-colimit vs def-weil-pbc-module-localization-away: the existing node defines fractions and the universal property, while the new node identifies the filtered multiplication colimit with that localization.
lem-sc-module-localization-filtered-colimit vs def-weil-pbc-module-localization: the existing node constructs localization at an arbitrary multiplicative subset, while the new node proves the colimit presentation for powers of one element.
lem-sc-module-localization-filtered-colimit vs lem-weil-pbc-localization-of-localization: the existing node proves transitivity of ring localizations, while the new node concerns module localization as a filtered colimit.
lem-sc-module-localization-filtered-colimit vs def-weil-ring-localization-away: the existing node defines ring localization, while the new node identifies module localization colimit.
lem-sc-module-localization-filtered-colimit vs lem-sc-local-domain-dim-one-principal-localization-fraction-field: the existing node concerns a domain's fraction field, while the new node applies to every module over every commutative ring.
lem-sc-module-localization-filtered-colimit vs def-weil-ring-localization-away: the existing node is a ring construction, while the new node is a module colimit theorem.
lem-sc-module-localization-filtered-colimit vs lem-weil-pbc-generic-fibre-localization-domain-irreducible: the existing node identifies a generic fibre localization for a domain, while the new node gives the filtered colimit presentation for arbitrary modules and elements.

## What remains

The localization node is statement-only and awaits a later proof stage.

## Second reading by H1

- Item statement: compared hypothesis by hypothesis with Stacks 0911/08D1 lines 1911-2052; it now introduces the shifted complex, differential, transition, alternating rows, and signed fraction map explicitly.
- Step 1: checked against `def-weil-pbc-koszul-complex` and `def-pur-hom-complex`; the wedge fraction and transition are exactly those in Tag 0911.
- Step 2: checked against `lem-sc-module-localization-filtered-colimit`, `lem-pc-alternating-cech-computes`, and `def-weil-pbc-site-cech-complex`; the product $f_{i_0}\cdots f_{i_p}$ gives each displayed localization row.
- Step 3: checked the explicit $d_K$ and $d_I$ signs against the Koszul node, the face differential against the alternating-Cech node, and the Hom differential against `def-pur-hom-complex`; the corrected twist is written with both total differential checks.
- Step 4: checked that an isomorphism of complexes induces a quasi-isomorphism and tested the empty-index case $r=0$ and zero complex $M^\bullet=0$; this is elementary.
- New node `lem-sc-module-localization-filtered-colimit`: self-contained statement with the commutative-ring, element, module, directed system, transition, localization, and fraction map all explicit; source Tag 00CM/label recorded; tested on $M=0$, a field, and $f=0$ (the colimit and localization both have the expected zero-divisor behavior); no existing node states the filtered-colimit identification and Mathlib searches are recorded.

Changes made: added `lem-pc-alternating-cech-computes` to Step 3's dependencies and citations, and expanded the sign paragraph to state the two bidegree equations explicitly. This closes the previously compressed C4/C3 check that the face differential and total-sign compatibility are supplied by cited statements. The dry-run delivery preflight passed before and after these repairs.
