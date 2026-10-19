# Delivery report: lem-trf-completed-local-base-change

1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-finite-type-base-change-adic-quotients.json`: new unsplit statement node; Mathlib searches found only supporting completion APIs, no exact theorem.
- `dag/nodes/sec-trace-formula/lem-trf-adic-inverse-limit-iso.json`: new unsplit statement node; Mathlib searches found completion lift APIs, no exact general inverse-limit theorem.
- `dag/nodes/sec-trace-formula/lem-trf-completed-local-base-change.json`: repaired item split.
- `citations.json`: verbatim statement quotes for every cited node at every proof step.
- `report.md`: this report.

2. Attachments: none. I searched the read-only source for the item tag and relevant completed-local declarations; no finished declaration states this item.

3. WANTED: none.

4. What was wrong and what changed:

The returned version treated the substantial finite-type localization, quotient, inverse-limit, and canonicality argument as elementary in Steps 3 and 4. It also relied on Tag 0GDX as though it proved the completed-local identification. This is a source-use error: the displayed Tag 0GDX (the label `more-morphisms-lemma-relative-map-approximation-pre`) assumes an isomorphism of completed local rings as part of its hypotheses and therefore cannot establish the present conclusion. Algebra Tag 00MA(3) supplies the finite-module completion mechanism, but not the geometric localization comparison by itself.

I repaired the split by creating two strictly smaller statement-only nodes. `lem-trf-finite-type-base-change-adic-quotients` isolates the finite-type affine localization and quotient comparison at every adic level. `lem-trf-adic-inverse-limit-iso` isolates the passage from compatible quotient isomorphisms to the inverse-limit completion isomorphism. The item now cites the existing fibre-product point and residue-field nodes for uniqueness of `x_B`, the existing completion nodes for Noetherianity/locality/flatness, and the two new helpers for the formerly hidden argument. Steps 3 and 4 are no longer marked elementary except for the final naturality observation. The proof dependency union and statement dependencies were recomputed.

I checked duplicate searches across the whole DAG and blueprint. The existing completion finite-module nodes concern module completion or different finite-algebra product decompositions; none states the finite-type local geometric comparison used here. The existing fibre-product point node gives the prime correspondence, while its residue-field companion gives the residue-field identification; neither states the completed-local conclusion. The new nodes therefore do not duplicate an existing statement or restate the item.

5. What I could not finish, and why: the two new helper nodes are intentionally unsplit stage-1 statements. Their statements are complete and their Mathlib searches are recorded; a later worker must prove or attach them.

## Review by NB

I read the current item, unit `sk-i-curve-zero`, ancestor blueprint proof for `lem-trf-local-term-locality`, Stacks Schemes Tag 01JT, More on Morphisms Tag 0GDX, and Algebra Tag 00MA(3). I also opened every node cited by each item step and copied its statement verbatim into `citations.json`.

Step 1 uses the scheme, locally finite-type, fibre-product, and locally Noetherian definitions, then takes the prime correspondence from `lem-weil-pbc-fibre-product-points` and the residue-field identification from `lem-weil-pbc-fibre-product-point-residue-field`. The completion-local node supplies that the completed base has the same residue field. These statements together justify that the relevant tensor product is the residue field and hence has one prime, giving the unique point `x_B`; no unproved uniqueness was left as an elementary assertion.

Step 2 uses the existing completion Noetherianity, local-completion-local-ring, and Noetherian-completion-flat statements. I checked that the hypotheses are met: `A=O_{S,s}` is Noetherian because `S` is locally Noetherian, and the finite-type affine chart gives `C` over `R`. The tensor-product chart and localization are exactly the canonical base-change map.

Step 3 cites the new `lem-trf-finite-type-base-change-adic-quotients` statement and the new `lem-trf-adic-inverse-limit-iso` statement. The first states the finite-level quotient isomorphism and transition compatibility; the second states precisely that these compatible isomorphisms induce the completion isomorphism. This is the localization, quotient, inverse-limit, and canonicality material that the returned version incorrectly marked elementary.

Step 4 uses only the adic-completion definition for the identification of the inverse-limit map with the canonical local base-change map; the chart-independence sentence is marked elementary because it is just naturality of localization and quotient projections after Step 3's explicit construction. The resulting map is an `A^`-algebra map by construction.

I tested edge cases in the underlying argument: `X=S` gives the identity completion map; `X=A^1_S` gives the expected formal power-series local ring; and the residue-field tensor at a closed point is a field, so the claimed uniqueness of `x_B` holds. The source error concerning Tag 0GDX is explicitly recorded above, and the repaired proof no longer treats that approximation lemma as evidence for its own conclusion.

## Not duplicates

lem-trf-adic-inverse-limit-iso vs lem-trf-completed-local-base-change: the helper is an abstract inverse-limit isomorphism from compatible quotient maps, while the item is the geometric completed-local base-change theorem.
lem-trf-finite-type-base-change-adic-quotients vs lem-trf-completed-local-base-change: the helper is only the finite-level quotient comparison for a finite-type localization; the item also asserts point uniqueness and the completed isomorphism.
lem-trf-adic-inverse-limit-iso vs lem-pod-adic-limit-finite-modules: the existing node concerns finite modules over a complete DVR and their module reductions; this helper concerns arbitrary adic rings and ring inverse limits.
lem-trf-finite-type-base-change-adic-quotients vs lem-pod-adic-limit-finite-modules: the existing node is a DVR module theorem; this helper is a geometric finite-type algebra localization theorem.
lem-trf-adic-inverse-limit-iso vs def-weil-pbc-coherent-formal-modules-affine-quotient-cone: the existing node defines a formal-module cone; this helper states an isomorphism of arbitrary adic ring limits.
lem-trf-finite-type-base-change-adic-quotients vs def-weil-pbc-coherent-formal-modules-affine-quotient-cone: the existing node concerns coherent formal modules; this helper concerns local rings of finite-type affine schemes.
lem-trf-adic-inverse-limit-iso vs lem-weil-pbc-affine-formal-map-limit-dictionary: the existing node is a sheaf/formal-module dictionary with extra coherence data; this helper is the elementary ring inverse-limit comparison.
lem-trf-finite-type-base-change-adic-quotients vs lem-weil-pbc-affine-formal-map-limit-dictionary: the existing node concerns coherent formal maps and section limits; this helper compares finite-type local algebra quotients.
lem-trf-adic-inverse-limit-iso vs lem-weil-pbc-affine-global-formal-comparison: the existing node compares global formal sections; this helper compares arbitrary adic ring quotients.
lem-trf-finite-type-base-change-adic-quotients vs lem-weil-pbc-affine-global-formal-comparison: the existing node is an affine formal-sheaf comparison; this helper is the finite-type local geometric quotient statement.
lem-trf-adic-inverse-limit-iso vs lem-weil-pbc-coefficient-subring-principal-source: the existing node concerns coefficient rings and principal ideals; this helper is a general inverse-limit ring statement.
lem-trf-finite-type-base-change-adic-quotients vs lem-weil-pbc-coefficient-subring-principal-source: the existing node concerns coefficient subrings; this helper concerns finite-type scheme localizations.
lem-trf-adic-inverse-limit-iso vs lem-weil-pbc-coherent-formal-modules-affine-complete: the existing node concerns completion of coherent formal modules; this helper concerns arbitrary compatible ring quotient isomorphisms.
lem-trf-finite-type-base-change-adic-quotients vs lem-weil-pbc-coherent-formal-modules-affine-complete: the existing node is a coherent formal-module completion result; this helper is a finite-type local ring quotient comparison.
lem-trf-adic-inverse-limit-iso vs lem-weil-pbc-complete-local-quotient: the existing node proves completeness of a quotient of one complete local ring; this helper compares two inverse-limit systems.
lem-trf-finite-type-base-change-adic-quotients vs lem-weil-pbc-complete-local-quotient: the existing node concerns one quotient ring's completeness; this helper compares two finite-type localizations after base change.
lem-trf-adic-inverse-limit-iso vs lem-weil-pbc-completed-affine-coherent-iso-lift: the existing node lifts coherent sheaf section isomorphisms; this helper is a ring inverse-limit construction.
lem-trf-finite-type-base-change-adic-quotients vs lem-weil-pbc-completed-affine-coherent-iso-lift: the existing node concerns coherent module sheaf lifting; this helper concerns finite-type affine local rings.
lem-trf-adic-inverse-limit-iso vs lem-weil-pbc-completion-exact-finite-modules: the existing node is exactness of completion on finite modules; this helper is an isomorphism of inverse-limit rings.
lem-trf-finite-type-base-change-adic-quotients vs lem-weil-pbc-completion-exact-finite-modules: the existing node concerns exact finite-module completion; this helper includes localization and finite-type algebra base change.
lem-trf-adic-inverse-limit-iso vs lem-weil-pbc-completion-finite-extension: the existing node decomposes completion of a finite algebra into local factors; this helper is the abstract inverse-limit step and does not assume finite algebra/module structure.
lem-trf-finite-type-base-change-adic-quotients vs lem-weil-pbc-completion-finite-extension: the existing node assumes S finite as an R-module and gives a product decomposition; this helper treats a finite-type (possibly nonfinite) algebra and one localized point.
lem-trf-adic-inverse-limit-iso vs lem-weil-pbc-coherent-formal-modules-affine-quotient-cone: that existing node is a coherent formal-module quotient-cone construction with sheaf hypotheses; this helper is a general ring inverse-limit isomorphism.
lem-trf-finite-type-base-change-adic-quotients vs lem-weil-pbc-coherent-formal-modules-affine-quotient-cone: that existing node concerns affine coherent formal modules; this helper compares local quotients of a finite-type algebra after base change.
