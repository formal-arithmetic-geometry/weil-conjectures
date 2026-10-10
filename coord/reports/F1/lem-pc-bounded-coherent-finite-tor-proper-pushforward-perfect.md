Files written:

- `dag/nodes/sec-picard-framework/lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect.json`: statement split into three theorem-level steps.
- `dag/nodes/sec-picard-framework/lem-pc-direct-image-bounded-coherent.json`: statement-only child; Mathlib no match.
- `dag/nodes/sec-picard-framework/lem-pc-noetherian-bounded-coherent-pseudo-coherent.json`: statement-only child; Mathlib no match.
- `dag/nodes/sec-picard-framework/lem-pc-pseudo-coherent-finite-tor-perfect.json`: statement-only child; Mathlib no match.

Attachments: none.

WANTED: none.

The source read for the item and all three children was `literature/stacks-project/perfect.tex`, the proof of Derived Categories of Schemes, Lemma 36.27.1 (Tag 08EV), together with the displayed proof in the local Stacks checkout `/home/ubuntu/c1-stacks-review/perfect.tex`. I also checked the related Tag 0B6G proof in `more-morphisms.tex`; it applies this criterion and does not provide a duplicate declaration.

## Review by F1

I checked that the item hypotheses are exactly the hypotheses used by the Tag 08EV direct-image criterion: the base is Noetherian, the morphism is locally of finite type, the complex has bounded coherent cohomology, each cohomology support is proper over the base, and the complex has finite Tor dimension over the inverse-image structure sheaf. Step 1 cites the new direct-image statement, whose conclusion is precisely bounded coherent cohomology of `Rf_*E`; it is not merely quasi-coherence or a sheaf-level finiteness claim. Step 2 cites the new Noetherian criterion and uses its exact bounded-coherent conclusion to obtain pseudo-coherence. Step 3 cites the new finite-Tor criterion and applies it to the same object `Rf_*E`; the finite Tor hypothesis is the item's hypothesis and is not silently strengthened. I read each cited node statement and copied the exact sentence used into `citations.json`. I searched the whole DAG and blueprint for the three Stacks tags and key phrases; no existing node states any of these theorem-level inputs. I tested the statement on the identity morphism and on a bounded complex of coherent sheaves with empty support; both reduce to the usual perfectness criterion and the zero complex. Mathlib searches for the item and each new node used LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable, and all other searches found only generic derived-category or Noetherian infrastructure.

What was wrong or incomplete in the imported node: it had no proof, no proof dependencies, and stale search dates/queries. These were repaired by recording the Tag 08EV route and adding the three required statement-only children. No source or hypothesis was changed.

What remains unfinished: the three child statements are intentionally unsplit queue leaves; they are not claimed to be Mathlib results.

## Not duplicates

lem-pc-direct-image-bounded-coherent vs lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect: the child states only bounded coherent cohomology of Rf_*E and omits the finite-Tor hypothesis and perfectness conclusion; the item is the full Tag 08EV criterion.
lem-pc-noetherian-bounded-coherent-pseudo-coherent vs lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect: the child is the general Noetherian implication from bounded coherent cohomology to pseudo-coherence and does not mention f, support, or direct image; the item includes all geometric hypotheses and concludes perfectness.
lem-pc-pseudo-coherent-finite-tor-perfect vs lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect: the child is the abstract pseudo-coherent plus finite-Tor criterion for an arbitrary scheme object, while the item derives pseudo-coherence from a proper direct image and includes the Noetherian and proper-support hypotheses.
lem-pc-noetherian-bounded-coherent-pseudo-coherent vs lem-sc-coherent-pseudo-coherent: the new node handles arbitrary bounded complexes with coherent cohomology, whereas the existing node handles only a single coherent sheaf in degree zero.
lem-pc-noetherian-bounded-coherent-pseudo-coherent vs lem-sc-derived-internal-hom-stalk-localization: the existing node is a localization statement used in an internal-Hom proof, not the bounded-coherent-to-pseudo-coherent criterion.
lem-pc-noetherian-bounded-coherent-pseudo-coherent vs lem-sc-ext-stalk-localization: the existing node concerns Ext stalk localization and does not state any pseudo-coherence implication.

## Second reading by F1

- Item statement: checked against Derived Categories of Schemes, Lemma 36.27.1, Tag 08EV (`lemma-perfect-direct-image`) in `perfect.tex`; hypotheses and conclusion agree, including finite Tor dimension over `f^{-1}\mathcal O_S`.
- Step 1: checked that [lem-pc-direct-image-bounded-coherent] states exactly the bounded coherent direct-image conclusion supplied by Tag 08E2; no unstated hypothesis is used.
- Step 2: checked that [lem-pc-noetherian-bounded-coherent-pseudo-coherent] is the Noetherian bounded-coherent implication in Tag 08E8; its conclusion is the required pseudo-coherence.
- Step 3: checked that [lem-pc-pseudo-coherent-finite-tor-perfect] is the pseudo-coherent plus finite Tor criterion in Cohomology Tag 08CQ; it applies to the same object `Rf_*E`.
- New node `lem-pc-direct-image-bounded-coherent`: statement-only, self-contained definitions cited, TeX valid, source corrected to Tag 08E2; searches and duplicate check reviewed.
- New node `lem-pc-noetherian-bounded-coherent-pseudo-coherent`: statement-only and self-contained, source corrected to Tag 08E8; searches and duplicate check reviewed.
- New node `lem-pc-pseudo-coherent-finite-tor-perfect`: statement-only and self-contained, source corrected to Tag 08CQ; searches and duplicate check reviewed.
- Edge cases checked: identity morphism, zero complex and empty support, and a field base reduce to the stated criteria without changing hypotheses.

Changes made: corrected the item source file from `more-morphisms.tex` to `perfect.tex`, and corrected each child source to its actual Stacks tag and label (08E2, 08E8, 08CQ). No proof step or statement was weakened.
