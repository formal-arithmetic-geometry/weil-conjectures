## Worker report

Files written:

- `dag/nodes/sec-smooth-base-change/sk-lem-universal-datum.json`: seven proof steps, unchanged statement, completed definition dependencies and blueprint metadata, exact coefficient scopes throughout.
- `dag/nodes/sec-smooth-base-change/lem-sbc-module-bc-integral-surjective.json`: statement; absent from Mathlib; genuinely unsplit arbitrary-coefficient tool.
- `dag/units/sk-lem-universal-datum.json`: only `realized` and `realized_by` changed. The existing older cyclic-coefficient realization is retained and the current item and its two tools are added.
- `citations.json`: all 21 step citations, each quoting the actual statement read. `searches.jsonl` records the real searches. No Lean was written or compiled.

## Attachments

The existing DAG node `lem-sbc-module-bc-injectivity` already contains the needed arbitrary-Lambda injectivity clause (1), with its source theorem and closed project declaration recorded on the base. I initially copied a narrower variant into this sandbox; the second reading removed that duplicate so the delivery does not modify an existing node.

The item itself cannot be attached as finished: `AlgebraicGeometry.Etale.exists_curveTestDatum` states the item exactly, but its dependency traversal reaches sorry declarations. The current source declarations in CurveTestDatum.lean:298-313 and its referenced construction at 219-284 were read. In particular the constantModSheaf nonvanishing theorem at 192-201 is sorry. The own proof being sorry-free does not close the item.

The four entries in the inherited open audit have existing mathematical homes:

- `AlgebraicGeometry.Etale.higherDirectImage_limit` belongs to `sbc-lem-higher-image-pulledback-stalk-continuity`: its statement explicitly gives the arbitrary-ring pulled-back-sheaf, small cofiltered, two stalk assertions of the source theorem. No new continuity node is needed.
- `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isIntegralHom` belongs to `lem-sbc-integral-underived-exchange`: arbitrary commutative ring, Cartesian square, integral vertical map, canonical underived exchange isomorphism.
- `AlgebraicGeometry.Etale.isZero_of_isZero_lowerStar_obj` belongs to `lem-sbc-integral-direct-image-detects-zero`: integral direct image detects zero for module sheaves. The present split only needs the converse pushforward implication and avoids this conservativity fact.
- `AlgebraicGeometry.Etale.exists_not_isZero_higherDirectImage_constantModSheaf` is covered jointly by the existing stronger prime-output `lem-sbc-prime-cyclic-detection` and `lem-sbc-prime-quotient-detection`. Neither alone is claimed as an exact attachment: the two cited statements give the source theorem by contraposition and choosing the supplied prime. A fresh node restating this composite consequence is unnecessary.

The source theorem `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective` belongs to the new module integral-surjective node, but is not finished: its reachable sorry is the integral underived exchange already represented above. Its signature, docstring, and proof at IntegralBaseChange.lean:125-169 were read.

## WANTED

None. The item statement, the Stacks proof route, and all required source declarations are available read-only.

## Faults found and corrected

The imported item left elementary flags null, had only the field-failure proof dependency, and omitted all integral, normalization, injectivity and coefficient dependencies. The new proof supplies these facts as statements of cited nodes.

The existing cyclic-coefficient tools are phrased for abelian sheaves killed by n and hypotheses about all Z/n-module sheaves. BC for all Lambda-module sheaves does not say BC for all Z/n-module sheaves. The item reuses the existing arbitrary-Lambda injectivity node and adds only the genuinely new integral-surjective statement. In the normalization step, the already-existing abelian pushforward theorem is valid after forgetting the particular sheaf and its canonical comparison arrow; it needs no lower-degree BC assumption. This is the specific safe use of forgetting coefficients.

Imported Step 5 said h was affine because it was a base change of affine f. In the displayed square, e is the base change of f and h is the base change of g. Step 4 now derives qcqs of h from the established qcqs of g. No unsupported orientation switch remains.

The current blueprint statement is for general Lambda; the inherited unit record is still the older Z/n statement. Its single proof paragraph has the same field/algebraic-closure/normalization route. I preserved that record and its existing sbc realization, adding the current realization only in the authorized binding fields. The two statements are not silently identified, and `blueprint.same_as` is empty for the item. The old `sbc-lem-bc-universal-test` is not cited as if it supplied arbitrary-Lambda coefficients.

The imported statement allows an integer n. The proof handles negative n by N = |n|, and proves n is nonzero by its image in the field furnished by Step 1. Neither a positivity hypothesis nor a nonempty-base hypothesis was added to the statement.

## Unfinished work

The new integral-surjective theorem remains statement-only, as required for a one-level split. Its source proof explains its later route: the surjective inverse-image unit embeds F in pi_*pi^*F, critical-map cokernel monotonicity controls failure, and integral exactness and exchange identify the comparison arrow. This argument is in the report, not hidden in its statement. The required full validation command is `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q114 sk-lem-universal-datum --no-push .`; READY is issued only after it prints OK. A separate second reader performs the eventual delivery.

## New nodes

There is one new statement-only node file and zero new Mathlib leaves. Searches for the new integral-surjective statement included LeanFinder, LeanSearch, Loogle and source grep, and a second semantic phrasing. The existing injectivity node was searched and reused rather than copied. Every recorded query was actually run with msearch.py. The exact replies, hit counts, top names and digests are preserved in the results fields from searches.jsonl. General tensor-product injectivity, scheme-morphism stability, and free-sheaf cokernel presentations do not state the cohomological comparison results.

The smooth-relative-dimension search found Mathlib's permanence result, but I then found and reused `lem-sbc-smooth-relative-dimension-permanence`, whose statement already covers all the required geometry. No smooth-permanence node was created. The geometric coefficient-reduction and normalization tools were likewise reused.

## Not duplicates

The existing `lem-sbc-module-bc-injectivity` was compared with the proof use and retained: its clause (1) applies after instantiating the base change parameter (a:S'\to S), and the item's universal BC hypothesis supplies its stronger universal premise. No duplicate node is delivered.

lem-sbc-module-bc-integral-surjective vs sbc-lem-bc-integral-surjective: the new statement works for all sheaves of modules over a specified arbitrary ring Lambda, assuming only fixed-base BC(p,Lambda,q-1), and imposes no torsion or invertibility. The existing statement is the n-annihilated abelian theorem under a universal BC(f,n,q-1) hypothesis. The latter cannot be instantiated from this item's coefficient hypothesis.

Neither new node is a clause of the item's existence conclusion: injectivity applies to a preexisting arbitrary square, and integral-surjective detection compares two preexisting arbitrary squares. Neither constructs a normal test base or asserts nonzero cyclic higher image. Before creation I searched all DAG statements by coefficient, injectivity, integral-surjective, and Lean declaration names, and ran blueprint_refs searches for 0F03, 0F04, integral surjective, cokernel, injectivity critical, and base change critical map. The only same-tag blueprint statements are the two distinguished here.

## Review by Q114

I compared the original statement with `literature/blueprint/main-20261015/blueprint/sec-smooth-base-change/sk-lem-universal-datum/_section.md` and read the complete proof of Stacks Tag 0F08, label `lemma-base-change-does-not-hold`, in etale-cohomology.tex:17296-17339. The chapter requires the smooth-base-change Stacks route. The proof retains the prescribed field reduction, integral algebraic closure, integral normalization, and constant-coefficient detection. Stacks states the cyclic-ring version, so the general-Lambda extensions are attributed to the agent and the actual module-coefficient Lean statements, not passed off as the literal Stacks theorem.

For the reused injectivity node I read Tag 0F03, `lemma-base-change-q-injective`, including its short-exact-sequence argument, and checked the existing arbitrary-ring theorem in Injectivity/CriticalMap.lean against clause (1). For the new integral-surjective statement I read all of Tag 0F04, `lemma-base-change-q-integral-top`, and the arbitrary-ring theorem in IntegralBaseChange.lean. Its g is required qcqs, pi integral and surjective, and its lower-degree property remains in Lambda-module sheaves. I checked those conditions appear explicitly in the new statement. These are real comparison tools, not an existence clause re-labelled as a node.

Step 1 uses the exact general-Lambda statement of `sk-lem-failure-field`: it supplies all five objects and the failing arrow. The two qcqs statements give the missing morphism hypothesis, while `sk-def-bc` explains the inherited fixed degree. Step 2 invokes the new module integral-surjective statement with exactly this f_1 and g_0; algebraicity makes the closure map integral, and the spectra of the two fields each have one point. The argument uses no assertion that an arbitrary transcendental extension is integral.

In Step 3 I opened `lem-sbc-normalization-algclosed-field`, which supplies the affine integral normal base, algebraically closed function field, integral pi and the factorization through the generic point. I also opened `lem-sbc-integral-pushforward-base-change-arrow`: its last implication is in the needed direction, from the square over the normalization to the pasted square, and it has no BC hypothesis. Its coefficient category is abelian, so I read all three clauses of `lem-weil-pbc-exchange-forget-coefficients` before using it. Their exactness and canonical-arrow comparison identify degree-q arrows after forgetting; a module-linear bijection has a module-linear inverse. Thus failure in the given Lambda category survives without asserting BC for arbitrary abelian coefficients. Both domain and target of g are affine, so its qcqs condition is actually available. Cartesian pasting here is the defining universal property of the fibre product, with the identifications retained.

Step 4 uses clause (1) of the existing arbitrary-Lambda injectivity statement after instantiating its base-change parameter and expanding universality, and uses qcqs stability under base change with h as the base change of g. A mono to the zero sheaf would have zero source and be invertible; this small argument gives target nonvanishing. Step 5 invokes exactly the nonzero base-change-target premise of `lem-sbc-prime-cyclic-detection`. I read its statement: it requires an algebraically closed K, qcqs h, a nonzero natural annihilator, and gives a prime not a unit in Lambda, with nonzero P_r/(r) higher image. Those are precisely the conclusions used in Step 6. The latter step is the contrapositive of the statement of `lem-sbc-prime-quotient-detection`; it does not assume Lambda/(r) is the prime field. Factorization n = dt and the explicit inverse t/n prove invertibility of d.

For Step 7 I read clause (1) of `lem-sbc-smooth-relative-dimension-permanence` and clauses (1)-(3) of `lem-weil-pbc-affine-morphism-permanence`. They give the two geometric properties for arbitrary base changes, and the affine total space over an affine base. This is a generic geometric tool from the vanishing unit, declared in split_report.tool_uses; it does not replace the universal-datum route. The other declared tools are the explicitly prescribed field-failure statement omitted by the old unit's uses list, and the coefficient-forgetting comparison required by the category boundary in Step 3.

I tested the reused injectivity statement and the new integral-surjective statement with q=1, the zero coefficient ring, empty test schemes, and the identity integral map. At q=1, only BC in degree zero is used. For Lambda=0 all arrows are zero-object isomorphisms, so the conclusion and implication hold. If T' is empty and pi surjective then T is empty too; the statements assert no nonexistent field or point in these cases. Identity pi reduces the second theorem to a tautology. Neither requires a nonempty fibre, finite-type base, Noetherian hypothesis, or an injectivity claim after a nonsurjective target replacement. In the item, the failure provides the nonempty field point that rules out n=0; n=1 or Lambda=0 has no possible failure. Negative n is handled without changing the statement. I corrected coefficient scope, the orientation of h, all formerly missing dependencies, and the unit's realization binding. No source SGA route or compiler operation was used.


### Continuation audit, 2026-10-17

I re-read the sandbox after the earlier interruption, together with the current source and the complete B–E return checklist. The original statement agrees verbatim with the current blueprint; no statement repair is needed. The helper statements introduce every square and coefficient sheaf themselves, contain no proof text, and have empty proof lists. The only adjacent same-tag statements are the two cyclic-coefficient results distinguished in “Not duplicates”. The blueprint search also found `sbc-lem-bc-universal-test`; it is the older cyclic-coefficient universal-failure result and does not give the present arbitrary-Lambda statement under its fixed-base failure hypothesis. No third helper was created.

I independently traversed the committed sorry-map dependency edges. The injectivity theorem reaches 2022 names and no direct or transitive sorry flag. The integral-surjective theorem reaches 2557 names and the unfinished integral underived exchange. The item reaches 2990 names and six unfinished declarations, so it cannot be treated as a closed attachment. This agrees with the visible sorry in the coefficient-reduction theorem. I read the four inherited frontier declarations at their current source locations and compared the existing continuity, integral exchange, and integral zero-detection statements; the mathematical homes above are sufficient, and no extra copy is needed.

I checked every cited statement again, rather than relying on the earlier review: normalization supplies exactly the integral factorization and the algebraically closed function field; integral pushforward supplies the implication from the normalized square to the pasted square; the forgetting-coefficients theorem identifies those canonical arrows after cohomology; and the two prime-coefficient nodes give precisely the nonunit prime and the contrapositive vanishing implication. In Step 3, the lower-degree hypothesis is never enlarged to all abelian sheaves. In Steps 5–6, the positive annihilator is absolute value of the given integer and the output prime divides the original signed integer as well. The qcqs condition used for h comes from base change of g. These checks cover C1/C4 and E1/E4/E5. All 21 citation entries are verbatim parts of the current statements and are in bijection with the step uses.

I reran semantic, Loogle and grep searches for the integral-surjective helper and the existing injectivity declaration through msearch.py and appended the exact replies from its log, also recording the new item searches. The abstract four lemma returned by LeanSearch requires the two long exact sequences and their comparison; it is not a one-line specialization proving the injectivity helper. Likewise a geometric normalization isomorphism and stability of integral or surjective morphisms do not compare higher-direct-image arrows. Thus there are still zero Mathlib leaves. For B/D/E, the new statements remain smaller general-purpose tools, not clauses of the existence conclusion; q=1, zero coefficients, empty schemes and identity replacement remain valid. No compiler, Lean-file write, live-project write, or push was performed. The required dry run is the final validation and its outcome is recorded below when available.

### Final worker audit and validation, 2026-10-17

I reopened every statement in the 21 citation entries and the source passages of Tags 0F03, 0F04 and 0F08, with their label-to-tag mappings. I also reread the exact module-coefficient signatures in CriticalMap.lean:82-104 and IntegralBaseChange.lean:141-169, and the item in CurveTestDatum.lean:298-313. The reused injectivity node and the new integral-surjective node preserve the arbitrary-module coefficient scope; neither uses the stronger cyclic-coefficient hypothesis of the older blueprint nodes. The full-DAG name and tag searches and whole-blueprint searches found no additional duplicate. All 21 citations still supply the stated implications, including the direction of integral pushforward and the comparison of the canonical arrows after forgetting coefficients. The previously repaired orientation of h and the signed integer annihilator remain correct.

I independently checked the committed 7d675a26 audit for the existing injectivity declaration (closed on the base), the integral-surjective declaration (2557 names and the integral-exchange sorry), and the item (2990 names with six reachable sorries). Thus the item is a split, not a finished attachment. Refreshed LeanFinder, Loogle, grep and LeanSearch results for all three nodes are recorded exactly from this sandbox's search log; none gives a Mathlib leaf. The first required dry run printed `OK (not pushed) deliver/Q114/sk-lem-universal-datum at 0b1677b19c: preflight passed`. After recording the refreshed searches and this audit, the same dry run is repeated on the final sandbox. No delivery push is authorized or performed by this worker.

## Earlier second reading (a previous round; superseded)

I checked the item statement against blueprint `sk-lem-universal-datum` and Stacks Tag 0F08 (`lemma-base-change-does-not-hold`), hypothesis by hypothesis; verdict: faithful, with the arbitrary-\(\Lambda\) and signed-\(n\) clauses explicit.

Step 1 was checked against `sk-lem-failure-field`, the affine qcqs and qcqs-morphism statements, and `sk-def-bc`; verdict: each cited statement supplies the named object or hypothesis and no cyclic-coefficient assumption is smuggled in.

Step 2 was checked against the algebraic-closure and finite-integral definitions and `lem-sbc-module-bc-integral-surjective`; verdict: the algebraic closure map is integral and surjective, and the contrapositive preserves the stated failure.

Step 3 was checked against normalization, coefficient-forgetting, integral pushforward, Cartesian-square, affine qcqs, and qcqs-permanence statements; verdict: the direction of the pushforward implication and the coefficient category are correct, and the pasted square is identified explicitly.

Step 4 was checked against `sk-def-bc`, module-coefficient injectivity, and qcqs permanence; verdict: the map is mono in the required degree, (h) is obtained from (g) by base change, and nonzero target follows by the stated elementary zero-object argument.

Step 5 was checked against `sbc-def-base-change-map` and prime cyclic detection; verdict: (N=|n|>0), the annihilator and algebraically closed-field hypotheses are established, and the output prime has exactly the asserted divisibility and nonunit properties.

Step 6 was checked against prime quotient detection; verdict: the contrapositive is used in the correct direction, and the displayed inverse proves invertibility on (S'), including negative (n).

Step 7 was checked against affine-morphism and smooth-relative-dimension permanence; verdict: the inherited geometry and all clauses of the item are assembled without restating the item as a helper node.

The existing node `lem-sbc-module-bc-injectivity` was checked against Stacks Tag 0F03 and its exact arbitrary-ring Lean declaration; verdict: clause (1) supplies the needed monomorphism, all notions have definition dependencies, and no duplicate is delivered.

The new node `lem-sbc-module-bc-integral-surjective` was checked against Stacks Tag 0F04 and its exact arbitrary-ring Lean declaration; verdict: self-contained statement, all notions have definition dependencies, no proof text, no Mathlib match, and no duplicate of the cyclic-coefficient node.

I changed only this second-reader report section. No statement, proof step, citation, node, or search record required repair after the independent B1–B7, C1–C5, and E1–E5 checks; the required dry run below is the final mechanical validation.

## Second reading by Q114

- Item statement: checked hypothesis by hypothesis against blueprint `sk-lem-universal-datum` and Stacks Tag 0F08 (`lemma-base-change-does-not-hold`); verdict faithful, including arbitrary `\Lambda`, signed `n`, and the geometric-generic datum.
- Step 1: checked against `sk-lem-failure-field`, affine qcqs, qcqs-morphism permanence, and `sk-def-bc`; verdict all objects and the universal lower-degree hypothesis are supplied.
- Step 2: checked against algebraic closure, integral morphism, and `lem-sbc-module-bc-integral-surjective`; verdict the field extension is integral and surjective and the failure implication has the correct direction.
- Step 3: checked against normalization, affine/qcqs permanence, coefficient-forgetting exchange, integral pushforward, and Cartesian-square statements; verdict the pasted square and comparison-arrow direction are justified without enlarging the coefficient hypothesis.
- Step 4: checked against `sk-def-bc`, arbitrary-`\Lambda` injectivity, and qcqs base-change permanence; verdict the base-change arrow is mono, its target is nonzero, and `h` is the base change of `g`.
- Step 5: checked against the base-change-map definition and prime cyclic detection; verdict `N=|n|` supplies the positive annihilator and the nonunit prime with the stated nonvanishing.
- Step 6: checked against prime quotient detection; verdict the contrapositive and the explicit inverse for `d` are valid, including negative `n`.
- Step 7: checked against affine-morphism and smooth-relative-dimension permanence; verdict the assembled datum has every conclusion of the item.
- Existing node `lem-sbc-module-bc-injectivity`: checked its statement, source Tag 0F03, and duplicate searches; verdict retained and cited, with no new duplicate.
- New node `lem-sbc-module-bc-integral-surjective`: checked B1–B7 against Tag 0F04 and the arbitrary-coefficient source declaration; verdict self-contained statement-only helper with complete definition dependencies and recorded searches, and no Mathlib match.

Changes made: none after the independent second reading; the prior repairs already removed the duplicate injectivity helper, corrected the `h` orientation, restored all coefficient and geometry dependencies, and recorded the required blueprint and search metadata. The final dry run was rerun after this section was added and passed preflight, DAG, and split review.
