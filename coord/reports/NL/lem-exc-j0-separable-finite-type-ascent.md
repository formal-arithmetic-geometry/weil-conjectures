# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-exc-j0-separable-finite-type-ascent.json`: statement, split into six proof steps; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-exc-generic-smooth-domain.json`: one new statement-only unsplit node, Stacks 07ND; no Mathlib match.
- `citations.json`: eleven step/node entries, each copying the cited statement verbatim.

One new node, zero Mathlib leaves. The item statement and its statement dependencies are unchanged. No unit record is changed.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the item tag, J-0/J0, smooth/generic, and separable/fraction-field combinations. The extension-of-residue-field and finite-separable-extension models found there do not state the item or the new general domain-base lemma. The upstream master checkout is only reference material. No claim of attachment relies on a master sorry.

## Literature wanted

None. The shared repository lacks the untracked literature checkout on this machine; the already obtained copies are available read-only under `/home/ubuntu/weil-launcher-nt/literature/`. I read `more-algebra.tex`, Tags 07PB (`lemma-J-0-goes-up`) and 07P7 (`definition-J`), and `algebra.tex`, Tags 07ND (`lemma-smooth-at-generic-point`) and 07NF (`lemma-regular-goes-up`), there. No download was needed.

## Audit of the imported item and route

No statement dispute or source error was found. The item states 07PB with J-0 expanded, including injectivity, both nonzero domain assumptions, finite type, Noetherianity of the base and separability of the induced fraction-field extension. The source proof first makes the base regular on a principal open, then uses generic smoothness, then regularity ascent. The split follows precisely that argument and explains the final open in the original spectrum.

The item already had extensive Mathlib searches but no proof. I retained those inherited records unchanged and added this run's recorded searches. The new lemma is strictly an input, not the J-0 conclusion renamed: it does not assume any regular open and only asserts smoothness after localization, so applying it still requires the regular-base construction, the separate regularity-ascent theorem, and the final localization argument. It holds even for the identity map on a singular domain.

The blueprint ancestor was checked with `tools/blueprint_refs.py ancestor`; it is `thm-exc-curve-open-dimension-general`. Searches of the whole blueprint for `J-0`, `separable smooth`, `smooth generic`, `07ND`, `fraction fields smooth`, `nonempty regular`, `generic smoothness`, and `separable fraction` found no duplicate blueprint statement. Both nodes retain the field-excellence/J-2 ancestry. The new node adds the item in front of its `via` chain. This is below the unit's proof; it does not replace the unit's cohomological route.

`lem-weil-pbc-regular-ring-smooth-ascent` is declared in `split_report.tool_uses`: its general commutative-algebra statement is the exact black box 07PB cites as 07NF. It is filed under `sk-thm-p1`; this item’s unit has no replacement for it. No maintainer-owned `tool_uses` field was set.

## Not duplicates

lem-exc-generic-smooth-domain vs lem-weil-pbc-smooth-at-generic-point-over-field: the existing 07ND node assumes that the base is a field; the new lemma allows an arbitrary domain base. Applying the field statement to the fraction field does not itself descend smoothness to an open over the original domain, so it does not specialize in the direction needed here.

lem-exc-generic-smooth-domain vs lem-weil-pbc-smooth-at-generic-point-over-field-residue-separable-fg: the existing node concerns finitely generated intermediate fields of a generic residue field over a field base, not existence of a smooth localization over a domain base.

lem-exc-generic-smooth-domain vs lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra: the existing node constructs some smooth algebra inside a specified extension of fields; the new lemma makes a principal localization of a given finite type algebra smooth over a given domain. Neither the prescribed algebra nor the nonfield base occurs in that construction theorem.

lem-exc-generic-smooth-domain vs lem-weil-pbc-smooth-at-generic-point-over-field-residue-separable: the existing node transfers separability to the zero-prime residue field for a field-base algebra. It does not give a smooth localization over a domain base.

## Mathlib research

All new searches were run with the mandated `msearch.py NL lem-exc-j0-separable-finite-type-ascent ...`; the log is `searches.jsonl`. The new node has two semantic phrasings, a Loogle query `Algebra.IsSmoothAt, IsFractionRing`, a grep of `RingTheory/Smooth` for `generic|IsFractionRing|fraction|separable`, and a LeanSearch attempt. The item has two semantic phrasings, `IsRegularRing, IsOpen`, a grep for J-0/regular-locus names, and its own LeanSearch attempt. LeanSearch returned HTTP 500 and is recorded as unavailable, not absence.

I read the types of the returned hits: localization maps being smooth, local descriptions of morphisms already known smooth, normalization dominance, and finite fraction-field extensions do not state either claim. I also read `Mathlib/RingTheory/Smooth/Field.lean:44-51` and `Smooth/Locus.lean:150-157`. `Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable` and `Algebra.IsSmoothAt.exists_notMem_smooth` supply ingredients but not generic smoothness over an arbitrary domain in one line. The latter already assumes smoothness at the chosen prime. The grep for J-0 hits `GradedRing.projZeroRingHom`, an unrelated projection. No new Mathlib leaf is claimed.

## Unfinished work

Only the new 07ND input remains unsplit, as required for a one-level split. Its statement is complete and has no proof sketch or proof dependencies. No mathematical gap in the item's proof was left as an uncited fact. Delivery is reserved for the fresh second reader.

## Review by NL

I checked delivery-errors B through E against the actual node files and the source statements. For the item I read all of 07PB and its J-0 definition in 07P7, rather than treating the imported dependency list as a proof. For the new node I read both directions and the proof of 07ND, while retaining only its separability-implies-smoothness direction. Its general domain-base hypotheses agree with that source; Noetherianity is not required in 07ND. It is a statement only, with finite type, separability and smoothness linked to their actual definition nodes and domains, fraction fields and principal localizations explained inline. TeX uses single mathematical backslashes after JSON decoding.

In step 1, the affine-spectrum definition supplies the Zariski topology. I wrote the elementary complement-of-V(I) argument choosing a nonzero f, so a principal-open basis theorem is not hidden behind a citation. Injectivity ensures that the image of f in S remains nonzero.

In step 2, I opened `lem-weil-pbc-localization-noetherian`, which really states Noetherianity for a localization at any multiplicative subset, and checked its conditions for powers of f. I opened `lem-weil-pbc-principal-localization-open-immersion`, whose statement gives exactly the principal open as the image. These are not being cited merely as definitions. The localization-at-prime definition gives the fraction equivalence used to write both local-ring maps; the regular-ring definition requires precisely Noetherianity and regular localizations. Consequently the hypothesis on U applies to each contracted prime, with no assumption of regularity of R outside U.

In step 3, I opened the finite-type-algebra definition: its finite-generator formulation is exactly what the displayed polynomial-over-fractions argument uses. The fraction fields remain K and F because R and S lie inside their localizations and the localizations already lie inside those same fields. Thus the original separability assumption is used for the correct field embedding. No generic-flatness theorem or unproved base-change smoothness is silently applied here.

In step 4, the new generic-smoothness statement gives exactly a nonzero h with A to B_h smooth; it does not merely give pointwise formal smoothness or a field-base statement. I checked each of its hypotheses against step 3. Step 5 uses the statement, not the proof, of `lem-weil-pbc-regular-ring-smooth-ascent`, which I read alongside 07NF. Its two hypotheses are regularity of A from step 2 and smoothness from step 4, and its conclusion makes T Noetherian as part of being a regular ring.

In step 6, I checked the product a=image(f)s is nonzero, the two unit calculations identifying the iterated localization with S_a, and the displayed inverse maps on local rings. The open-immersion node supplies openness and the image D(a); the zero prime witnesses nonemptiness. The regular-ring definition then supplies the local conclusion. These are elementary calculations from the cited statements, not additional lemmas or a new node for a clause of the item. I corrected my draft's search grouping to assign the concurrently completed search records to the intended node by query rather than by completion order.

For small cases, R=S a field permits f=h=1 and gives its single regular point. A polynomial algebra over a regular domain is compatible with the assertion; no positive transcendence degree is required. The identity map on an arbitrary singular domain verifies that the new generic-smoothness statement does not assert regularity or smuggle in the item's conclusion. A finite purely inseparable extension of an imperfect field, for example adjoining a p-th root of a non-p-th-power in characteristic p, is excluded by the separability hypothesis, as it must be. Zero rings and vanishing localization denominators are excluded explicitly. The proof never assumes the base field perfect, finite, or algebraically closed, and never uses excellence to prove an input to excellence.

Every citation has a verbatim statement quotation in `citations.json`. I compared all same-tag 07ND nodes listed above and found no general domain-base duplicate. There is no new definition, no relocation of the entire conclusion into a child, and no change to the item statement. The dry run below is the required remaining mechanical check.

## Second reading by NL

- Item statement: checked every hypothesis and conclusion against more-algebra.tex, Tag 07PB, `lemma-J-0-goes-up`, and Tag 07P7, `definition-J`; PASS. Injectivity, finite type, the nonzero domains, Noetherian base and separable induced fraction-field extension all match; J-0 is correctly expanded.
- Step 1: checked against the first sentence of 07PB and the actual statement of `def-weil-affine-spectrum`; PASS. The complement-of-V(I) calculation supplies the principal open, and injectivity prevents its denominator from vanishing in S; no basis lemma is silently assumed.
- Step 2: opened `lem-weil-pbc-localization-noetherian`, `lem-weil-pbc-principal-localization-open-immersion`, `def-weil-pbc-localization-at-prime`, and `def-weil-regular-scheme`; PASS after spelling out the denominator condition, cross multiplication in K, and inverse identities. The localization is Noetherian and only primes in U are used.
- Step 3: checked the finite-generator clause of `def-weil-pbc-finite-type-algebra` and the fraction definitions in the statement; PASS. Dividing each polynomial coefficient by the same power of f proves finite type, including zero generators; both fraction fields and their embedding remain the original ones. This is elementary.
- Step 4: opened `lem-exc-generic-smooth-domain` and algebra.tex Tag 07ND, `lemma-smooth-at-generic-point`; PASS. Step 3 supplies every hypothesis, and the conclusion is an actually smooth principal localization over A, not merely a field-base result.
- Step 5: opened `lem-weil-pbc-regular-ring-smooth-ascent` and algebra.tex Tag 07NF, `lemma-regular-goes-up`; PASS. Regularity of A and smoothness of A to T are exactly its hypotheses. This generic tool from another unit is disclosed in the existing split_report, without setting a maintainer-owned tool_uses field.
- Step 6: checked against the principal-open immersion statement, the localization fraction definition, and the regular-ring definition; PASS after replacing the reference to the verification in step 2 by the actual denominator, cross-multiplication and inverse checks. Both unit calculations are correct even for n=0; the zero prime witnesses D(a) nonempty. This is elementary from the cited statements and step 5.
- New node `lem-exc-generic-smooth-domain`: checked all hypotheses against algebra.tex Tag 07ND, `lemma-smooth-at-generic-point`, including its proof's explicit nonzero smooth localization; PASS. This is a non-elementary input strictly smaller than J-0 ascent, with no regular-base assumption. B1-B7 pass: statement only, all objects introduced, domains/fraction fields/localizations defined inline, finite type/separability/smoothness linked to the correct definition nodes, proper TeX and tag/label source. Same-tag search across all dag/nodes found the four field-base or field-construction nodes already distinguished above; I read each statement and none supplies the arbitrary-domain assertion. Whole-blueprint searches for generic smoothness and separable fractions found no duplicate, and the ancestor tool confirms thm-exc-curve-open-dimension-general. My independently phrased LeanFinder and grep searches are in searches.jsonl and the node; the returned declarations require smoothness already, concern localization maps, or supply several ingredients rather than a one-line specialization. No Mathlib leaf or slopmaster2 attachment was found.

Small cases checked independently: for R=S a field the identity is smooth and the unique prime is regular; for an arbitrary singular domain the identity still satisfies the new node with g=1, so it does not smuggle in regularity. R=k and S=k[x] allow positive transcendence degree, and zero finite-type generators cause no exception in step 3. Zero rings and empty spectra are excluded by the nonzero domain assumptions. A nontrivial purely inseparable field extension is excluded precisely by separability; no perfectness or excellence is assumed.

Changes: expanded the local-ring fraction verifications in steps 2 and 6 to remove the remaining backward reference to an argument; added and assessed two independently phrased Mathlib searches on the new node. Kept the item statement, the one necessary new node, the six-step route and all citation uses. Verified citations.json still quotes each used node's current statement verbatim; no citation entry changed because no cited statement or uses list changed. No statement dispute or source error found. No Lean, compiler, build, shared-repository edit, or direct git command was used.
