## Worker report

Files written:
- dag/nodes/sec-proper-base-change/lem-weil-pbc-module-derived-complete-products-triangles.json: item, split; no Mathlib match for the entire arbitrary-ideal assertion.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-module-localization-tower-vanishing.json: statement, unsplit; no Mathlib match for the localization/multiplication-tower comparison.
- citations.json: a verbatim statement quote for every citation in the four steps.

Attachments: none. Searched WeilConjectures for the exact blueprint tag and derived-completeness terminology. Read CategoryTheory/DerivedCategory/Complete/Principal.lean, especially derivedComplete_iff_rightOrthogonal and isTriangulated_derivedComplete at lines 294 and 308. They require I to be principal with a nonzerodivisor generator and use the reduction-tower sheaf definition, so they do not give this arbitrary-ideal module assertion. The upstream master is reference material, not a finished-proof certificate.

WANTED: none.

The imported statement is correct and unchanged. It previously had no proof. Its existing ancestry points to the original finite-extension lattice sentence; that ancestor has subsequently been reviewed with rational-category corrections. This item remains the general module tool needed by the nilpotent-torsion-limit descendant, not a change to the fixed proper-base-change unit. Read the chapter and unit records and the original finite-extension blueprint proof. No unit realization fields need changing for this auxiliary item.

No unfinished part of the item's proof remains. The new comparison lemma is deliberately statement-only for the next splitting level. Searches ran through msearch.py; LeanSearch returned Internal Server Error and is recorded unavailable. Read the returned ordinary categorical localization, Ext-dimension and derived t-structure signatures: none is the scalar localization/tower comparison. Read ObjectProperty/Orthogonal.lean lines 35–43 and Triangulated/Orthogonal.lean lines 40–70; their general closure results do not identify the Stacks multiplication-tower condition. They therefore do not make the item a Mathlib leaf.

## Not duplicates

lem-weil-pbc-module-localization-tower-vanishing vs lem-weil-pbc-module-derived-complete-products-triangles: the new lemma compares a single scalar's multiplication tower with shifted-source Hom from A_f, without any ideal, family or triangle; the item proves two closure results by universal-property and factorization arguments.
lem-weil-pbc-module-localization-tower-vanishing vs lem-weil-pbc-nilpotent-torsion-derived-limit-complete: the existing node asserts completeness of a homotopy limit of nilpotent torsion complexes; the new node makes no nilpotence or limit-of-varying-objects assertion and only compares the two vanishing tests for one scalar and one complex.

Also opened lem-weil-pbc-local-hom-tower-criterion (0997): it states vanishing of derived INTERNAL sheaf Hom on a slice ringed site, not ordinary derived-category morphisms in all degrees. It does not itself state the module shifted-Hom criterion. Its localization-free-resolution helper is an exact sequence of module sheaves, not the needed Hom/tower equivalence. Neither is cited as if it supplied that missing clause. Searched all dag/nodes by 091P, 091S, A_f, multiplication-tower and derived-completeness concepts; blueprint_refs searches for derived complete, localization, multiplication tower, localization Hom, hom from and Hom exact found no blueprint statement of the new criterion. The plain module definition already exists and is reused.

## Review by NC

I read more-algebra.tex, lemma-hom-from-Af (091P), including its proof of (1) iff (3), and definition-derived-complete (091S) with the entire following closure paragraph. The new statement is exactly the (1)/(3) comparison with Ext degree n written as Hom(A_f[0][-n],K). It makes the localization and every object explicit and retains arbitrary commutative A, arbitrary f including zero divisors, and arbitrary unbounded K. It is a genuinely smaller input than either closure clause, with no proof or proof sketch in its statement. Read the tag-to-label table to check both citations.

Step 1 uses clause (2) of lem-weil-derived-limit-existence for exact countable products in D(A), and clause (1) for existence and isomorphism-independence of multiplication-tower limits. Its hypotheses hold: products of modules have coordinatewise kernels and any tuple in a product of surjections lifts by choice, as explicitly written. The module completeness definition quantifies over every choice of derived limit, so the isomorphism-independence clause really is needed and supplied. This establishes existence rather than relying on a potentially vacuous vanishing condition.

Step 2 uses only the new single-scalar criterion and the existing module completeness definition. I checked that the latter uses T(K,f), not the distinct adic reduction-tower coefficient definition. Every integer degree is retained; replacing n by -q does not lose negative degrees. No principal-ideal or finite-generation hypothesis enters.

Step 3 is an elementary argument from the product definition: all projection composites of the candidate map are zero, and uniqueness forces the map itself to be zero. Step 2 then supplies completeness. This needs no compactness, tensor/product interchange or exactness of sheaf products. The product definition's statement explicitly contains precisely this uniqueness clause.

Step 4 uses clause (ii) of lem-weil-pbc-hom-into-triangle-exact: a map W to Y whose composite into Z is zero factors through X. I read its full statement, checked the direction of Hom, and read derived.tex lemma-representable-homological (0149) for this factorization. Both endpoints having no maps from W imply the middle has none. Shift stability is explicitly derived by applying the inverse shift, and TR2 from def-weil-triangulated-category supplies Y → Z → X[1] and Z[-1] → X → Y for the other two cases. During self-review I corrected an unnecessarily complicated rotation sentence to these exact rotations; signs do not affect the vanishing argument. I did not cite the contravariant Hom-out-of-triangle node in place of the required covariant assertion.

Small cases checked: I=(0) imposes only f=0; A[1/0] is the zero ring/module and its Hom groups vanish, consistently with the zero-transition homotopy limit. If I=A, f=1 forces K=0 since Hom(A[q],K) detects its cohomology; closure then reduces to zero products and two-out-of-three for zero objects. For any nilpotent f, A_f=0, again consistent with the criterion. The zero ring has only zero modules and poses no exception. All products and rotations are in the same D(A), never in the condensed or pro-etale coefficient category. The new node was checked against B1–B9: self-contained, statement-only, TeX, explicit localization meaning, correct tag/label, actual logged searches, no duplicate or item clause. C1/C4 are backed by citations.json; D1/D2 are avoided because the closure arguments stay in the item. No hypothesis is added to either statement, and no statement dispute was found.

Dry-run repair: the preflight citation scanner interpreted the shift [q-r] as a hyphenated node id. Rendered those shift brackets with TeX bracket commands, preserving the formula.

## Second reading by NC

- Item statement: checked against more-algebra.tex Tags 091S and 091P, including arbitrary rings/ideals, all integer degrees, unbounded complexes, and both closure clauses; verdict correct and unchanged.
- Step 1: checked the cited derived-limit existence clauses and exact countable products in the module category; verdict dependencies match and the existence/isomorphism-independence argument is explicit.
- Step 2: checked the new 091P comparison node and the point-derived-completeness definition; verdict all shifts and all elements of the ideal are retained.
- Step 3: checked the product universal property; verdict elementary projection and uniqueness argument is sufficient.
- Step 4: checked the covariant Hom exactness node, shifts, and TR2 rotations; verdict factorization and all three two-out-of-three cases are stated with the correct morphism direction.
- New node `lem-weil-pbc-module-localization-tower-vanishing`: checked against Tag 091P (1) and (3), self-contained localization and derived-category hypotheses, statement-only form, TeX, source label, searches, and edge cases; verdict valid and needed.
- No other new nodes: the item node is the existing target and all cited dependency nodes predate this split.
- Changes: retained the worker's corrected TeX shift brackets and added this second-reading section; no mathematical statement or proof step required further repair.
