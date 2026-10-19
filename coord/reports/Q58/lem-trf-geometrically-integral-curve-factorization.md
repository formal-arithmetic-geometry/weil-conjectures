# Q58: lem-trf-geometrically-integral-curve-factorization

## 1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-geometrically-integral-curve-factorization.json`: statement, now split into 13 steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-geometric-reducedness-separable-scalar-restriction.json`: one new statement-only node, Stacks Tag 0C2Y; no Mathlib match.
- `citations.json`: all 78 step/node citations, with verbatim statements (including their hypotheses).

There are one new node and zero Mathlib leaves. The item is not its unit's key node, so no unit file was changed. No Lean source was written or compiled.

## 2. Attachments

None. I searched both read-only project source trees for the item's blueprint tag and for curve factorization, Stein factorization and geometrically integral generic fibres, and inspected the related declarations. No sorry-free project declaration gives this complete statement. In particular a field/trait relative-curve result does not establish the present arbitrary excellent Noetherian base case. The upstream master is reference material, not evidence of a completed proof.

## 3. Literature wanted

WANTED: de Jong, Families of curves and alterations (1997), Lemma 5.2, printed pp. 612–613, for lem-trf-geometrically-integral-curve-factorization. The node's local document `literature/de-jong-families-curves-alterations-1997.pdf` is missing. I read the Numdam PDF online, including the proof on printed p. 613, but downloaded nothing into the project. Accordingly proof_origin.by is agent. The separating-functions, normal modification and Stein-factor construction follow that proof; the local Stacks texts justify the expanded arguments.

## 4. Corrections and audit findings

The imported item had no proof. Its statement is faithful to the trivial-group, properness-only consequence of de Jong's lemma, so I did not change it or any maintainer-owned field. I did not claim projectivity of the modification over S. Taking the graph closure and its finite normalization suffices for the properness asserted here.

The finite-type assumption needed for normalization is supplied by properness, and excellence is used to obtain Nagata/N-2 coordinate domains and hence a finite normalization. I did not treat finiteness as part of the definition of normalization. The generic fibre need not be smooth: I used normality, geometric reducedness of its function field and the generic-point irreducibility criterion instead of the existing smooth-generic-curve Stein lemma.

An initially contemplated new generic geometric-integrality criterion was unnecessary: the existing generic-stalk reducedness and generic-point irreducibility nodes give it. The one genuinely missing tool is change of geometric reducedness when restricting scalars along a separable algebraic extension. I stated exactly Stacks 0C2Y, including its non-finite and zero-algebra cases. It is neither a factorization theorem nor one of the item's geometric-fibre conclusions.

I preserved the item's inherited blueprint ancestry and filled the new node's ancestry through this item. I read the current main-20261015 locality statement and proof, and the intermediate Orgogozo/de Jong preparation nodes: this is the geometric preparation inside that inherited branch, not a substitute for the normal-cone argument. No SGA 4 or SGA 4½ route is used. Off-unit tools are declared individually in split_report.tool_uses; they supply generic scheme/field facts, not an alternative trace-formula route.

## 5. Unfinished work

No missing step of the item's argument remains. The new node is intentionally statement-only, as required for a one-level split; its later split follows Stacks 0C2Y. All automated checks and delivery are run after writing this report.

## Not duplicates

There is no existing DAG node stating Tag 0C2Y. I searched the whole DAG by tag and concept and the whole blueprint with blueprint_refs.py before creating the node; same_as is empty. The first delivery duplicate check additionally found the following two nodes citing the auxiliary diagonal tag 0C2X; I opened both complete statements and sources and verified the differences below.

lem-trf-geometric-reducedness-separable-scalar-restriction vs lem-weil-pbc-finite-separable-multiplication-etale: the existing node asserts that multiplication k′ tensor_k k′ to k′ is etale for a finite separable field extension; it does not state geometric reducedness of an arbitrary algebra over either ground field. The new equivalence allows infinite separable algebraic extensions and uses that diagonal result only in its source proof.

lem-trf-geometric-reducedness-separable-scalar-restriction vs lem-pur-finite-field-derived-tensor-summand: the existing node constructs an idempotent and a derived tensor summand for finite fields and sheaves on a site; it does not compare reducedness of algebra tensors after arbitrary field extensions. Its coefficient fields are finite, unlike the new lemma.

lem-trf-geometric-reducedness-separable-scalar-restriction vs lem-weil-pbc-separably-generated-tensor-reduced: the existing node proves reducedness of tensor products of a separably generated field extension; the new node compares two base fields for an arbitrary algebra over a separable algebraic intermediate field.

lem-trf-geometric-reducedness-separable-scalar-restriction vs lem-pur-geometric-reducedness-from-generic-stalks: the existing node passes geometric reducedness from the generic stalks of a reduced scheme to the scheme over a fixed field; it does not change the ground field.

lem-trf-geometrically-integral-curve-factorization vs lem-trf-relative-curve-factorization: the existing field/trait-base statement is not the arbitrary-base theorem here; I neither recreated it nor used its conclusion to supply the present theorem.

## Review by Q58

I read de Jong Lemma 5.2 and its proof online, the local Stacks algebra proof of Tag 0C2Y (both directions and its use of the separable diagonal, 0C2X), and the relevant local varieties, morphisms, more-morphisms, coherent and more-algebra passages. I opened every cited DAG node and collected its complete statement in cited-statements.txt before generating citations.json. The citations quote the actual statements, not paraphrases. The checks below concern the arguments and hypotheses, not just the existence of dependency ids.

1. The proper-stability node permits generic base change. The affine fraction-field node identifies the fraction field on a nonempty affine of the integral generic fibre. The dimension/trdeg theorem applies because that fibre is an integral finite-type K-scheme. The affine function-field transfer node compares two affine integral K-schemes with the same field, so I apply it to an affine open and Spec M, not to a nonaffine scheme. The affine fibre-product node then interprets the field tensor products as domains.

2. I checked the characteristic hypotheses separately. In characteristic zero K is perfect and the cited perfect-field basis node applies. In positive characteristic 030W requires reducedness after every extension of K, which step 1 supplies. Its separability definition, applied to the finitely generated extension M itself, gives a separating basis. Dropping its last member gives F, and the cited separably-generated tensor theorem supplies geometric reducedness over F. I did not infer this merely from algebraic separability of M/K.

3. The projective-space chart node supplies precisely polynomial charts and their affine coordinate maps; its properness node supplies properness over S. Clearing the finitely many denominators on a nonempty affine is explicit. Algebraic independence supplies injectivity and dominance, without assuming that S is a field.

4. The two scheme-image nodes give the quasi-coherent kernel construction and topological closure. The partial-section node gives the isomorphism above U. Quasi-compactness holds since U is Noetherian. Injectivity of sections into M comes from the integral-scheme stalk node. The kernel is prime on each nonempty affine chart, proving reducedness as well as irreducibility; I did not conflate topological closure with an integral scheme.

5. Proper base change/composition and the closed-immersion properness node apply to the graph product. The finite-type-over-Noetherian node provides Noetherianity. The locally-finite-type affine-pairs node supplies finite-type coordinate algebras, the excellence-ascent node supplies their excellence, and the affine-cover node extends this to all affine charts. All hypotheses are supplied by the proper finite-type constructions over S.

6. The residue-field normalization node applies to the generic point of the quasi-separated integral Z with the degree-one extension M/M. It supplies normality and the function field, but does not supply finiteness. The quasi-excellent/Nagata theorem and the Nagata and N-2 definitions supply finite integral closure separately. The localization theorem identifies the affine pieces. Writing finite module generators as fractions proves the dense-open isomorphism explicitly and within the graph open U.

7. The finite-proper and proper-stability nodes give properness of the normalization and r. The finite-type/excellence tools apply again. The generic-fibre definition and affine localization identify the local rings of T with local rings of X', which proves normality directly, without a smoothness claim or a perfect-base assumption.

8. The proper coherent-pushforward node applies because X' and P are Noetherian and O_X' is coherent; the finite-module/kernel criterion on Noetherian affine rings verifies that input. The relative-spectrum node gives the stated affine charts and compatibility under restriction. The finite-morphism criterion applies to the coherent algebra. The morphism-into-affine statement supplies evaluation maps and their uniqueness, so they glue to the required g.

9. The sections-in-function-field node shows the chart algebras of Y are domains. The principal-open argument proves that the evaluation map has dense image: a nonzero section on a reduced scheme cannot vanish at every point. Thus Y is nonempty irreducible and reduced. The finite-proper node gives h proper. The proper-over-separated node has exactly the hypotheses g over S, X'/S proper and Y/S separated, and gives g proper. The finite-type and excellence statements apply just as in step 5. Dominance of q follows from dominance of qg.

10. The proper-variety H0 theorem applies to the proper integral F-variety T and gives a finite field L. The fraction-field section-base-change statement applies to the quasi-compact separated inverse image of an affine chart of P and its quasi-coherent structure sheaf. Its canonical linear isomorphism is a ring isomorphism by the explicit pure-tensor formula added to the step; no unproved algebra identification is taken from the node. Relative spectrum then gives Y_F=Spec L and the actual generic fibre of g. For the constants claim, a monic polynomial over global sections makes an algebraic z integral in each normal local ring; representatives agree inside M and glue. This is a direct local-ring argument, not an appeal to an uncited Stein connectedness theorem. Finally the separably-generated-implies-separable node and the definition of separability applied to F(a) prove that the finite extension L/F is separable.

11. I read both directions of the new 0C2Y statement and checked its application with k=F, k1=L, A=M. It gives exactly the missing reducedness after every L-field extension. The generic-stalk criterion requires a reduced scheme; T is integral, with sole generic stalk M. The finite-separable-closure node applies because M/L is finitely generated. The algebraic-closure-in-M result of step 10 makes its separable constants equal L. The generic-point criterion transfers the resulting geometric irreducibility from Spec M to T. Together these prove the first geometrically integral generic fibre.

12. The module-over-field flatness theorem and flat-ring-map definition give the injection after tensoring L into M; this exactness assertion is not inferred merely from a bare tensor definition. Step 1 makes the target tensor a domain, hence its unital subring is a domain. The same generic-stalk and generic-point statements now apply to the integral K-generic fibre of Y, proving the second geometric-integrality assertion. The transcendence-degree tower formula and the dimension theorem have exactly finitely generated field/variety inputs and give dimensions d−1 and 1.

13. The square commutes by the graph projections and r=qg. The closed-dominant dimension node applies to the proper dominant maps π and h: the schemes are integral, the targets locally Noetherian and the maps locally of finite type, as its statement requires; properness supplies closedness. Its generic field degrees give dim X'=dim X and dim Y=dim S+d−1. Thus the finite-total-dimension clause is proved, not dropped.

For small cases I checked d=2 (one chosen rational coordinate, a curve T, one-dimensional Y_eta), S=Spec K, imperfect positive-characteristic K, already-normal X, and the degree-one constant extension L=F. The new scalar-restriction statement allows A=0 and infinite separable algebraic k1/k, exactly as Stacks does; without separability it would be false (a nontrivial purely inseparable field extension is reduced over itself but not geometrically reduced over k). All 13 proof steps are shorter than 2000 characters. The short affine-kernel, local-ring and fraction-denominator arguments are written out rather than hidden in new nodes that would merely restate pieces of this item.

The logged Mathlib queries include LeanSearch, LeanFinder, Loogle and grep, with a second formulation. I read the returned signatures and the geometric-reducedness source, including its TODO about comparison with the all-extension-field formulation. The results do not state the new arbitrary-algebra scalar-restriction equivalence. Searches that failed service access are recorded unavailable; no query was fabricated. The new statement's five query strings and the item's added query strings are copied exactly from searches.jsonl.

## Repair after NOT MERGED

The prior delivery was approved by review but rejected at landing because `lem-trf-closed-dominant-dimension` had changed on the current DAG. I rebased the retained split conceptually against the current node, reopened its complete statement, and replaced the step-13 citation quote in `citations.json` with the current verbatim statement, including its explicit generic-point stalk notation and updated dependency names. The proof step still uses exactly the current conclusion: for the proper dominant maps \(\pi:X'\to X\) and \(h:Y\to S\), finite function-field extensions give equality of dimensions. No statement, proof step, dependency, or new node was otherwise changed.
