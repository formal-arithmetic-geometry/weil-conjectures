1. Files written: item `lem-sc-strict-henselization-noetherian` (split); new unsplit nodes `lem-sc-strict-henselization-faithfully-flat` and `lem-sc-strict-henselization-completion-noetherian` (Mathlib no match).
2. Attachments: none.
3. WANTED: none.
4. The imported item had no proof. The Stacks proof of Tag 06LJ uses faithful flatness of the strict henselization map, Noetherianity and faithful flatness of the strict henselization completion, and descent of Noetherianity. The DAG already had the descent lemma `lem-weil-pbc-faithfully-flat-descent-noetherian`; the two strict-henselization facts were absent, so they were added as statement-only prerequisites rather than restating the item.
5. I could not close the two prerequisite facts in Lean because the source project contains no strict-henselization declarations; they remain unsplit literature leaves as required by stage 1.

## Review by K1
I read the item source, Stacks Tag 06LJ, and the existing DAG statements for `lem-weil-pbc-faithfully-flat-descent-noetherian` and `lem-weil-pbc-strict-henselization-triples`. Tag 06LJ explicitly says that faithful flatness of `R -> R^sh` gives the reverse implication, while its forward implication proceeds by proving the strict henselization completion Noetherian and the completion map faithfully flat, then applying faithful-flat descent. Step 1 cites the new faithful-flatness statement exactly. Step 2 uses that same statement and the existing descent statement, whose hypotheses are precisely a faithfully flat map and Noetherian target. Step 3 uses the new completion statement, which supplies those two hypotheses for `R^sh -> completion`, and applies the same descent statement. I checked that all local-ring, Noetherian, and strict-henselization hypotheses occur in the item or cited statements. The Mathlib searches for both new nodes used LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. I tested the direction on the identity case (a separably closed field, whose strict henselization and completion are itself) and on a complete Noetherian DVR; no hypothesis is silently added.

## Second reading by K1

- Item statement: checked against Stacks Tag 06LJ (lemma-henselization-noetherian), conditions (1) and (3); the equivalence and local-ring hypotheses agree after explicitly citing the strict-henselization construction.
- Step 1: checked against Tags 04GP and 04GN and the faithful-flatness node; the cited statement supplies exactly the map used.
- Step 2: checked against Tag 06LJ and `lem-weil-pbc-faithfully-flat-descent-noetherian`; its hypotheses match the map and Noetherian target, with no elementary step hidden.
- Step 3: checked against Tag 06LJ parts (a), (c), and final descent; the completion node supplies Noetherianity and faithful flatness, and the descent node supplies the conclusion.
- `lem-sc-strict-henselization-faithfully-flat`: checked against Tags 04GP and 04GN; self-contained definitions and recorded Mathlib searches are present; identity and DVR cases are valid.
- `lem-sc-strict-henselization-completion-noetherian`: checked against Tag 06LJ (a), (c); the maximal ideals and completion ideal are now explicitly introduced, and the recorded searches found no Mathlib theorem.

Changes made: corrected the item node's `created.item` provenance; added the strict-henselization definition dependency to the item statement; introduced the maximal ideal and its extension in the completion statement; and replaced the non-tag source reference `15.46.1` with Tags 04GP/04GN.

## Not duplicates

- `lem-sc-strict-henselization-faithfully-flat` vs `lem-weil-pbc-strict-henselization-triples`: the existing node constructs the strict henselization as a filtered colimit and proves it is strictly henselian; it does not state faithful flatness of the canonical map from the local ring.
- `lem-sc-strict-henselization-faithfully-flat` vs `lem-weil-pbc-etale-prime-generates-maximal`: the existing node concerns the maximal ideal in an etale algebra localized at a prime, not faithful flatness of strict henselization.
- `lem-sc-strict-henselization-faithfully-flat` vs `lem-weil-pbc-standard-etale-monic-derivative`: the existing node concerns standard-etale presentations and derivatives, not faithful flatness.
