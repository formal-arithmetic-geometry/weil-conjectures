1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-etale-local-ring-faithfully-flat-descent.json` — statement split into four proof steps.
- `dag/nodes/sec-abelian-varieties/lem-sc-etale-local-ring-stalk-faithfully-flat.json` — statement-only Stacks interface; no Mathlib match.
- `dag/nodes/sec-abelian-varieties/lem-sc-etale-local-ring-flat-descent.json` — statement-only local flatness descent interface; no Mathlib match.
- `dag/nodes/sec-abelian-varieties/lem-sc-faithfully-flat-tensor-zero.json` — Mathlib leaf `Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality`.

2. Attachments: none.

3. WANTED: none.

4. The item had no proof. I checked the existing scheme-level child `lem-sc-etale-faithfully-flat-local`, which invokes this affine statement, and kept the affine hypotheses explicit. The proof now first obtains faithful flatness of the localized field-extension map from Tag 0C4Y, then invokes a separate local flatness descent statement, then uses Tag 00RV for base change of relative Kähler differentials and faithful-flat tensor reflection to descend their vanishing, and finally applies the affine pointwise characterization of etaleness. The local flatness step was made its own child because the generic module flatness lemma does not state the localized ring-map situation used here.

## Review by K1

I read the item, its blueprint ancestor `lem-sc-mult-n-etale-kernel`, and the source places Tag 0C4Y, Descent Tags 02L2/02KY/02VM, and Algebra Tag 00RV. I also read the statements of every cited DAG node. Step 1 uses exactly the new stalk faithful-flatness statement, with `q_K` contracting to `q`. Step 2 uses the new local flatness descent statement, whose conclusion is precisely flatness of `B_q` over `A_{q\\cap A}`. Step 3 uses the existing Kähler base-change statement and the new Mathlib leaf stating that faithfully flat tensoring reflects a zero module. Step 4 is the elementary affine `IsEtaleAt` criterion from the item’s stated hypotheses. The field, finite-presentation, prime-contraction, and localization hypotheses were checked against each statement. I tested the interfaces on the identity extension `K=k` and on a finite separable extension; both reduce to the expected identity/localization cases. Mathlib searches were run for the item and all three new nodes with LeanFinder, Loogle, grep, and LeanSearch; unavailable services are recorded as unavailable.

## Not duplicates

lem-sc-etale-local-ring-stalk-faithfully-flat vs lem-sc-etale-local-ring-faithfully-flat-descent: the new node states only faithful flatness of the localized stalk map, while the item concludes etaleness by also descending flatness and differentials.
lem-sc-etale-local-ring-stalk-faithfully-flat vs lem-sc-etale-faithfully-flat-local: the existing node is the scheme-level pointwise etale descent statement; the new node is its affine ring-level faithful-flat input.
lem-sc-etale-local-ring-stalk-faithfully-flat vs lem-sc-etale-base-change-geometric: the existing node proves both directions of scheme etale base-change; the new node isolates only the stalk faithful-flatness assertion.
lem-sc-etale-local-ring-stalk-faithfully-flat vs lem-sc-lfp-field-extension-pointwise-descent: the existing node descends local finite presentation; the new node descends faithful flatness of local rings.
lem-sc-etale-local-ring-flat-descent vs lem-sc-etale-local-ring-faithfully-flat-descent: the new node states only the flatness clause, while the item also descends vanishing differentials and concludes etaleness.
lem-sc-etale-local-ring-flat-descent vs lem-weil-pbc-fpqc-descend-locally-finite-presentation: the existing node is global fpqc descent of local finite presentation, not pointwise flatness after field base change.
lem-sc-etale-local-ring-flat-descent vs lem-weil-pbc-fpqc-descend-flat: the existing node is scheme-level fpqc flatness descent; the new node is the localized affine pointwise specialization with explicit primes.
lem-sc-etale-local-ring-flat-descent vs lem-galois-fpqc-descend-etale: the existing node descends global etaleness of a morphism; the new node supplies only local flatness.
lem-sc-faithfully-flat-tensor-zero vs lem-weil-pbc-criterion-flatness-fibre-noetherian: the existing node is a fibre criterion for flatness over a Noetherian ring; the new leaf reflects zero modules under faithful tensor.
lem-sc-faithfully-flat-tensor-zero vs lem-weil-pbc-flat-module-faithfully-flat-maximal-ideals: the existing node constructs faithful flatness from nonzero maximal fibres; the new leaf uses faithful flatness to reflect module vanishing.
lem-sc-faithfully-flat-tensor-zero vs lem-weil-pbc-local-completion-faithfully-flat: the existing node concerns completion maps; the new leaf is the general tensor reflection property.
lem-sc-faithfully-flat-tensor-zero vs lem-weil-pbc-flat-faithfully-flat-maximal-ideals: the existing node gives a maximal-ideal criterion for ring maps; the new leaf gives tensor-zero reflection.
lem-sc-faithfully-flat-tensor-zero vs lem-weil-pbc-field-extension-base-change-faithfully-flat: the existing node proves faithful flatness of field scalar extension; the new leaf is the independent consequence that faithful tensoring reflects zero modules.

## Second reading by K1

- Item statement: checked against Varieties Tag 0C4Y and Descent Tags 02L2, 02KY, 02VM; corrected the pointwise flatness formulation to use `(A_K)_{p_K}` and defined `p_K=q_K∩A_K`.
- Step 1: checked the localized faithful-flatness conclusion against the stalk node and Tag 0C4Y; verdict correct under the stated contraction hypothesis.
- Step 2: checked the local flatness descent interface against Descent Tags 02L2 and 02KY; verdict correct and its localized base/target rings are explicit.
- Step 3: checked differential base change against Algebra Tag 00RV and tensor-zero reflection against Tag 00HP/Mathlib; verdict correct, with faithful flatness supplied by Step 1.
- Step 4: checked the affine etale criterion against the etale definition node; verdict correct after adding the missing citation to `def-weil-etale-morphism`.
- `lem-sc-etale-local-ring-stalk-faithfully-flat`: statement-only form, self-contained hypotheses and Tag 0C4Y source checked; verdict retained.
- `lem-sc-etale-local-ring-flat-descent`: statement-only form, explicit primes/localizations and Descent source checked; verdict retained.
- `lem-sc-faithfully-flat-tensor-zero`: Mathlib declaration and source checked; verdict retained as the exact tensor-triviality reflection leaf.

Changes made: repaired the item’s incorrect unlocalized base ring in the etale criterion, added the missing etale-definition citation and verbatim citation entry, and corrected the stale `created.item` ownership metadata. Small cases (identity field extension, field algebras, and zero differential module) are consistent with the repaired statements; no duplicate node or cycle was found.
