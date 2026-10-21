# Worker report: lem-pur-unrestricted-frobenius-factorization

Group Q61; stage 1; 2026-10-21. Direct delivery under the dispatcher's brief.

## Files written

- `dag/nodes/sec-six-functors/lem-pur-unrestricted-frobenius-factorization.json`: existing statement, now split into eight steps; no statement change; existing statement dependencies preserved.
- `citations.json`: one verified verbatim statement quotation for every step/node citation (21 entries).
- `report.md`: this report.
- `searches.jsonl`: five actual Mathlib searches recorded by msearch.py. Their results were read and appended to the item's inherited search records without deleting those records.

New nodes: 0. New Mathlib leaves: 0. The item is not a Mathlib leaf.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and the notion did not find a declaration or collection of declarations proving every clause. I read `AlgebraicGeometry/AbsoluteFrobenius.lean`, the relevant definitions and naturality lemma in `AbsoluteFrobeniusNatural.lean`, `AlgebraicGeometry/Frobenius.lean`, the naturality statement in `Morphisms/Frobenius.lean`, and the definitions, projection statements and implementation notes of `GeometricFrobenius.lean`. In particular, `AlgebraicGeometry.Scheme.comp_iterateFrobenius` proves absolute naturality, and the Galois construction supplies projection statements, but these do not prove the item's model/absolute/Galois factorization. The geometric-Frobenius module describes that comparison as further work. Partial coverage is not an ATTACH claim.

## WANTED

None. Every source used is present in the read clone.

## What was wrong or missing

The existing item had a complete statement and no proof. The existing finite-type-only `prop-trf-frobenius-factorization` and `def-weil-relative-frobenius-geometric-fiber` cannot be applied to arbitrary models. The split therefore constructs the model map from its projections after proving it is over k_0; it does not apply either restricted statement. No statement dispute or unit-route departure was found. No definitions or target signatures were changed.

The item's inherited chapter/unit is the six-operations package. I read its chapter and unit records; the item is not that unit's key statement, so I did not change its realization fields. Its nearest blueprint ancestor is `def-pur-scheme-geometric-frobenius`, confirmed by `tools/blueprint_refs.py ancestor`. The split realizes that ancestor's factorization paragraph and second commuting square, as required by the current parent's step 2. Its blueprint metadata remains intact.

## Mathlib and duplicate searches

I used only msearch.py for Mathlib searching. The exact logged queries are in searches.jsonl and the item. LeanFinder's first wording returned ring/field Frobenius and Witt-vector results; its second wording returned scheme-pullback projection results. LeanSearch returned field and algebra Frobenius results; Loogle returned perfect-ring inverse identities and unrelated categorical Frobenius terminology. The grep in Mathlib/AlgebraicGeometry returned no Frobenius declaration. None states the whole item, nor makes it a one-line specialization. The existing fibre-product and finite-field identity nodes already supply the relevant general Mathlib results, so no new leaf is warranted.

Whole-DAG searches included the item id, Frobenius filenames and key words, and Tag 0CC7. Whole-blueprint searches were `Frobenius`, `Frobenius natural`, `Frobenius factorization`, `0CC7`, and `unrestricted Frobenius`. I opened the statements of the relevant existing Frobenius nodes rather than relying on hits or source tags. No blueprint node states this unrestricted collection of clauses, so same_as stays empty.

## Not duplicates

- `lem-pur-unrestricted-frobenius-factorization` vs `prop-trf-frobenius-factorization`: the existing proposition assumes a finite-type model and asserts iterated arithmetic factorization. This assigned item covers arbitrary models and also states the projection, inverse, geometric cancellation, and naturality identities. No new node duplicates that proposition.
- `lem-pur-unrestricted-frobenius-factorization` vs `lem-trf-frobenius-open-square`: that node concerns Cartesian squares for open immersions and their iterates; it does not state the unrestricted absolute/model factorization.
- `lem-pur-unrestricted-frobenius-factorization` vs `lem-weil-absolute-frobenius-well-defined`: that node constructs Frobenius, identifies its sections and affine restrictions, and proves localness. It does not state the scalar-extension factorization.

## Unfinished work

None for this stage-1 split. No Lean was written and no compiler, Lake, or build tool was invoked. The repository and launcher were read only. All writes are in the assigned sandbox. The required delivery command supplies remote validation and publication.

## Review by Q61

I read the full source of the item: main-20261015 `sec-smooth-purity/sk-def-sf-weil-complexes/def-pur-scheme-geometric-frobenius.md`, especially its absolute-Frobenius display, arithmetic/geometric convention and second commuting square. I compared it with the item's arbitrary-model statement and with the current parent split. I also read Stacks `varieties.tex`, Definition `definition-absolute-frobenius` (03SM) and Lemma `lemma-frobenius-endomorphism-identity` (0CC7), including the ring-homomorphism proof; `schemes.tex`, Definition `definition-fibre-product` (01JP), including its universal property; and `fields.tex`, Section `section-finite` (09HY), with the finite-field identity supplied by the existing Mathlib leaf. Tag/label correspondence was checked in the Stacks tag table. There are no new nodes needing additional source review.

For step 1 I opened `def-weil-scheme-over-base`, `def-weil-affine-spectrum`, `def-weil-locally-ringed-space-morphism`, and `def-weil-scheme-characteristic-p`. They give respectively the structure morphism, the spectrum's global ring, the ring maps on sections, and the precise characteristic condition (including the empty scheme). Sending p=0 through the structure morphism and restrictions proves that condition. No characteristic instance requiring a nonzero ring is smuggled in.

For step 2 I opened `def-weil-absolute-frobenius-scheme` and `def-weil-locally-ringed-space-morphism`. The former says the space map is the identity and sections go to q-th powers; the latter specifies ring-homomorphism components and composition. The displayed equality h-sharp(s^q)=h-sharp(s)^q checks both components of the two composites. This is the actual two-line proof of naturality; no separate naturality lemma is hidden behind a citation to a definition. It works with exponent q directly and needs no affine-cover or gluing theorem.

For step 3 I opened all five cited statements. `lem-weil-finite-field-pow-card` explicitly states c^q=c; the absolute-Frobenius node explicitly supplies its affine description; affine spectrum is contravariantly functorial; `def-weil-frobenius-substitution` identifies sigma with the q-power field map; and scheme-over-base defines what it means for F_0 to be over k_0. Thus naturality from step 2 gives t_0 F_0=t_0, and applying it separately to both projections proves exactly the two stated absolute-Frobenius projection equations. This step is marked non-elementary because it invokes the existing finite-field theorem.

For step 4 I reread `def-pc-base-change`, `def-pc-fibre-product`, the field substitution definition and affine-spectrum functoriality. The fibre-product statement includes the existence and exact projection formulas of induced maps, not merely their names. The substitution node states that sigma fixes k_0 and gamma is its inverse in Gal(k/k_0), so both coefficient maps really are over the base. This checks the compatibility hypotheses needed before constructing Phi and g_epsilon. The proof uses only those unrestricted fibre-product constructions, not the finite-type-only relative-Frobenius definition.

For step 5 the sole cited statement is `def-pc-fibre-product`. It explicitly asserts uniqueness for a map with the two specified projections. I computed both projections of both composites and compared them with the projections of F from step 3. There is no claim that matching points suffices, and no assumption that either factor is a k-morphism.

For step 6 I again read the fibre-product, affine-spectrum and substitution statements. Both inverse products in the field are the identity. Contravariance gives Spec(sigma) Spec(gamma)=Spec(gamma sigma), with the reverse order for the other composite. Each composite has both projections equal to those of id_T, which is precisely the uniqueness clause cited. For step 7 no external result is needed: the two explicit associative cancellations use only steps 5 and 6 and prove both geometric identities separately.

For step 8 I reread the base-change statement's induced map h_T and the fibre-product statement's projection formulas and uniqueness. Their hypotheses are met by the assumed k_0-morphism f_0. The proof writes both projections of f Phi_X and Phi_Y f and uses step 2 on f_0 for the first; equality for absolute Frobenius is step 2 on f. This gives both final assertions, without importing a commuting square whose hypotheses might require finite type.

I checked B--E of delivery-errors against these files. There are no new unsplit statements, clauses relabelled as nodes, missing new-node searches, or off-route theorem citations. Every external fact used is in a cited statement; the sectionwise power identity, induced-map calculations and cancellations are explicitly elementary. Citations.json was checked against the actual statements, and I enlarged the coefficient-automorphism quotations to include the inverse convention as well as the automorphism property. All proof steps are below 700 characters; none triggers the 2000-character hidden-lemma review.

For edge cases, T_0 empty makes all endomorphism equations valid by the same universal property and uses the zero ring harmlessly. For T_0=Spec k_0, Phi=id and F=g_sigma, confirming which of sigma and gamma appears in the factorization. On F_q[epsilon]/(epsilon^2), q>=2 kills epsilon and the factorization still works without asserting that Phi is invertible. On F_q[x_i : i in an infinite set], the q-power map exists with the same section calculation, so finite type was not implicitly used. A nonseparated model needs no affine-intersection assertion: the proof works directly on sheaf morphisms and universal properties. The original statement passes these tests and was retained verbatim.
