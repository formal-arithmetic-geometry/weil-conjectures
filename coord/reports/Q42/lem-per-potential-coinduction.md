# lem-per-potential-coinduction — Q42

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-potential-coinduction.json`: statement, split into five explicit steps; not a Mathlib leaf. Six fresh logged searches cover the corrected internal derived comparison in two phrasings. Retained the imported searches and all ancestry fields.
- `citations.json`: one verbatim statement quotation per use per step (15 entries).
- `report.md`: this report. No new DAG nodes or unit changes.

## Attachments

None. Searched the entire `WeilConjectures/` checkout by the item tag and by coinduction/coextension, restriction/scalars/Hom and potential terminology. The tag and potential-coinduction names are absent. Read `WeilConjectures/Algebra/Category/ModuleCat/Sheaf/RestrictScalars.lean:36-65` and `SixFunctors/Etale/Derived/CoextendScalars.lean`, including its K-injective instance and derived-direct-image comparison. `CategoryTheory.Sheaf.restrictCoextendScalarsAdj` gives the ordinary external adjunction only. `AlgebraicGeometry.Etale.rightDerivedLowerStarCompCoextendScalarsIso` concerns direct image, not internal Hom with an arbitrary first variable. Neither proves every clause of this item. The exact upstream master is reference material only and supplies no attachment evidence.

## WANTED

None. The Gabber PDF and all Stacks sources used below are present locally.

## Statement corrected

STATEMENT-DISPUTED: the claim that this internal Hom comparison always belongs to D+ is false. Take X = Spec of an algebraically closed field of characteristic different from ell, r = s = 1, and K = F_ell[0]. Take the zero-differential complex M having F_ell in every degree n >= 0 and zero in negative degrees. Both inputs are bounded below. On this punctual etale topos vector spaces are injective, so RHom(M,K) is computed directly by the Hom complex. In degree -n it is F_ell for every n >= 0, with zero differential. It therefore has nonzero cohomology in arbitrarily negative degrees. This example even has the standard potential dualizing K on a point.

Changed only the comparison's ambient category from D+ to D and explicitly stated that the two Hom objects need not lie in D+. K_s is still in D+, and every original input hypothesis is retained. Gabber XVII Proposition 6.2.1.1, printed p. 294, also prints D+ for this comparison with M in D+; that displayed label fails on the same example. The coefficient-adjunction identity itself is valid in D, and the resolution proof below supplies it without potentiality, Noetherianity or constructibility. This corrects the source's boundedness annotation, not its coefficient comparison.

The only external citer found by searching the entire DAG is `lem-per-gabber-local-duality-general`: its step 4 applies the comparison to ordinary constructible sheaf filtration quotients Q_a. That step obtains boundedness from field-coefficient duality, rather than from membership of the general comparison in D+. Thus the citer's use remains valid with the corrected statement. It was read and left unmodified. The unit is not changed; the perverse local-duality coefficient route remains the one prescribed by the ancestor.

## DAG and blueprint searches; Not duplicates

No new nodes were created. Searched the whole DAG by title and statement concepts (coinduction, coextension, K-injective resolutions, derived Hom/scalar adjunction), by the Stacks tags 013K, 070J, 08BJ, 0A6F and 0A95, and used `tools/blueprint_refs.py search coinduction`, `search coextension`, `search 'internal Hom'`, and `ancestor lem-per-potential-coinduction`. No blueprint node states this comparison. Retained `same_as: []` and the precise existing ancestor place and via chain.

In particular the existing `lem-sfb-dc-hom-scalar-adjunction` compares scalar EXTENSION in the first Hom variable with restriction in the second. It does not state coinduction in the second variable. The existing scheme-structure-sheaf coinduction lemmas in the Picard chapter are limited to the Zariski structure sheaf and are not cited as if they applied on the small etale site. The proof instead writes out the elementary sheaf formulas on every localized site. The Mathlib module adjunction and its evaluation functions were read at ChangeOfRings.lean:554-667; they are ordinary module facts, not an exact or one-line specialization proving this derived sheaf theorem.

## Review by Q42

I read the item's source in Gabber, Expose XVII Proposition 6.2.1.1, printed p. 294, with the preceding local-duality theorem and following constructibility arguments. Its brief coefficient comparison does not give the general lower bound claimed by the imported item. The point example above forced the correction before splitting. I also read the chapter and unit records and the ancestor's local-duality route. This auxiliary coefficient calculation replaces no chapter or unit step.

For Step 1 I read `def-pc-sheaf-restrict-scalars` and `def-pur-sheaf-hom`. They give precisely the same underlying abelian sheaf and the localized morphism interpretation used there. The scalar action, its laws, exactness and evaluation linearity are written directly from these definitions. No result about flat coefficient quotients is assumed (these quotients generally are not flat). The relevant Stacks material is sites-modules.tex Section 04TT and Lemma 03EM. I read Modules Tag 0A6F as an analogy only: it is stated for topological spaces, so the step proves its needed site formulas rather than citing that tag as a general-site theorem.

Step 2 uses the same two definitions. The forward and inverse formulas are checked on a local section, with both inverse identities, S-linearity and restriction compatibility displayed. This is a short explicit evaluation argument, not a new unsplit adjunction lemma nor an invocation of the proof of a different DAG node. It establishes the adjunction needed in the next step as well as its internal sheaf form.

For Step 3 I opened `lem-weil-pbc-module-sheaves-enough-injectives`: it applies to every commutative constant coefficient ring on the small etale site of any scheme. I opened `lem-weil-pbc-dplus-injective-representative`: its statement gives exactly the bounded-below injective K-injective representative of K used here, since the preceding node supplies enough injectives. I read their Stacks sources, Injectives 01DU and Derived Categories 013K, 070J. I opened `lem-weil-pbc-right-adjoint-preserves-kinjective` and read Derived Categories 08BJ: the adjunction has the right orientation, U is exact by Step 1, and C is its right adjoint by Step 2, so C(I) is K-injective over S. I checked `def-pur-hom-complex` and `def-pur-derived-internal-hom`: with S in degree zero their formulas identify U C(I) with RHom_R(S,K), without asserting that forgetting the S-action preserves K-injectivity. Termwise vanishing of I gives the lower bound on C(I). Small etale sites are taken in the module universe, as in the existing definitions; no large-category colimit is involved.

Step 4 uses `def-pur-hom-complex` for its product and signed differential, and `def-pur-sheaf-hom` and scalar restriction for its local maps and underlying R-module complex. I read sites-cohomology.tex Section 0A8X. Each degree comparison is exactly the map already verified in Step 2. I wrote the differential identity with its sign, and the sectionwise product/restriction argument explicitly. No claim of exactness of products of sheaves is used. The first variable can be unbounded above; products, not finite sums, are used.

Step 5 uses `def-pur-derived-internal-hom` only for the actual model with a K-injective second variable, and `lem-pur-rhom-well-defined` for independence under quasi-isomorphisms of representatives and K-injective targets. I opened that node and read the full statement and proof of Stacks sites-cohomology.tex Lemma 0A95, with Section 08J7. Its hypotheses hold over R for I and over S for J, established separately in Step 3. Restriction is exact, and the formula is compatible with precomposition and postcomposition before localization, which gives naturality in both derived variables. No constructible six-functor comparison, flatness, projectivity, or additional finiteness is used. All statements quoted in citations.json are verbatim from the actual cited nodes, and each says what its step takes from it. Generic homological tools outside the unit are declared in split_report.tool_uses.

I checked delivery-errors B--E individually: no new unsplit nodes with proofs, no duplicate or clause restatements, no invented search records, every non-elementary resolution or invariance input cited, and no use of a definition as a theorem about it. The elementary steps consist of the displayed scalar identities and product differential calculation. Every step is under 2000 characters. Checked s=r (identity coefficient map), r=s=1, M=0, K=0 and X empty; the formulas reduce to the unit/evaluation identity or zero maps as appropriate. Also checked the nonflat r>s case: the proof uses right-adjoint coinduction and injective targets, not underived coefficient tensor. No forbidden SGA source is used. No Lean file was changed and no compiler or Lake command was run.

## What remains unfinished

No mathematical subclaim is left unproved inside this split. The existing foundational dependency nodes retain their own independent project status. The required server dry run and direct delivery are performed after this report is written.
