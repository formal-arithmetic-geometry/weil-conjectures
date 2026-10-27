# Worker report: lem-trf-affine-local-dimension-term-comparison

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-affine-local-dimension-term-comparison.json`: statement node, now split into eight proof steps. No Mathlib declaration covers the full conjunction; the existing domain tower Mathlib leaf supplies the generic-degree argument.
- `citations.json`: seventeen exact statement quotations, one per step/dependency pair.
- `report.md`: this report.

New DAG nodes: **0**. New Mathlib leaves: **0**. The initial sandbox contained no item, split, report or search log. I copied the live unsplit item, retained its statement, source, blueprint lineage and six inherited search records, and appended the four searches actually run here. The command-created `searches.jsonl` records these searches.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and for affine dimension, stalk/fraction-field and transcendence-degree comparisons did not find a project declaration proving the full item. `Scheme.Hom.functionFieldMap` in `WeilConjectures/AlgebraicGeometry/Curve/DivisorPullback.lean:64` constructs the generic stalk map under a specified equality of generic points; it does not prove the item's other clauses. `Spec.residueFieldMap_residueFieldIso_hom` in `WeilConjectures/AlgebraicGeometry/Sites/EtaleTopologicalInvariance/PropertyC.lean:43` proves the affine residue-field square only. Neither is an attachment for the whole item. The landed `Sheaf/TraceFormula/LocalDimensionFormula.lean` was also read: its definition `dominantFunctionFieldAlgebra` uses the actual generic stalk map, and its later local-dimension theorem has additional hypotheses and does not state this comparison conjunction.

## Literature wanted

None. Every source needed is available in the read repository. No SGA source was used.

## Audit of the imported node and route

The imported statement is correct, including its assertion that the comparisons require neither finite type nor Noetherian hypotheses. No STATEMENT-DISPUTED correction is needed. Its proof was empty. I added the definition dependency `def-weil-locally-ringed-space-morphism`, since the statement uses the stalk map of a scheme morphism, and supplied the proof. No mathematical clause was changed.

The chapter record is `sec-trace-formula`, the unit is `sk-i-curve-zero`, and the blueprint ancestor is `lem-trf-local-term-locality`. I read the chapter and unit records and the current main-20261015 ancestor proof, especially the (1)--(2) normal-cone route. This item is a lower-level affine comparison on the existing route through `lem-trf-local-dimension-formula`; it does not replace a unit step or change the chapter. It is not the unit's key node, so no unit file is delivered.

The proof is marked agent-written because it expands the terse affine reduction of Stacks 02JU with explicit germ, quotient and tower calculations. The sources read were:

- `schemes.tex`, Tag 01HV, label `lemma-spec-sheaves`, especially (6), and Tag 01HY, label `lemma-morphism-into-affine-where-point-goes`, including its germ square and localness argument.
- `algebra.tex`, Tag 00E3, label `lemma-spec-localization`; Tag 00KF, label `definition-height`; and the Local rings paragraphs describing the residue field of a localization as the fraction field of the quotient and the map on fractions. The quotient-localization source is Tag 00CT, label `proposition-localize-quotient`.
- `morphisms.tex`, Tag 01RV, label `lemma-integral-scheme-rational-functions`, integral case, and Tag 02JU, label `lemma-dimension-formula`, whose proof reduces to algebra.
- `fields.tex`, Tags 030G and 030H, labels `definition-transcendence-degree` and `lemma-transcendence-degree-tower`. For the essential non-field intermediate-ring version, I read the existing node `lem-exc-domain-transcendence-degree-tower` and Mathlib `RingTheory/AlgebraicIndependent/TranscendenceBasis.lean:537` (`lift_trdeg_add_eq`) and `:546` (`trdeg_add_eq`). This domain version, rather than only the field tower theorem in Stacks, is what step 8 cites.

No new node needs a source audit. At the original delivery the generic affine-stalk, localization-height and integral function-field lemmas were declared as generic tools in `split_report.tool_uses`. In the current DAG all five reused theorem nodes are Mathlib leaves, so the repair removes the obsolete off-unit tool requests. Their full current statements were reread, not inferred from their leaf status. I did not write the maintainer-owned `tool_uses` field.

## Not duplicates

No new nodes were created. Whole-DAG searches located and reused `lem-weil-pbc-affine-open-stalk-localization`, `lem-weil-pbc-localization-dimension-chains-below-prime`, `lem-weil-pbc-prime-residue-field-algebra`, `lem-sc-integral-function-field-affine-fraction` and `lem-exc-domain-transcendence-degree-tower`. I also opened the existing Spec stalk-map and residue-field naturality nodes; the needed naturality follows directly by the written fraction and quotient calculations, so it does not need another node. Whole-blueprint searches for `affine local dimension`, `transcendence fraction`, `stalk localization` and `transcendence degree` found no blueprint node stating the full item. `blueprint.same_as` is therefore empty.

## Review by Q15

I checked the split against delivery-errors B--E with the cited node statements and the source passages open. There are no statement-only new nodes, copied clauses, missing searches for new nodes, or new-node same-tag pairs. Every non-elementary input is the statement of an existing cited node, and the elementary parts spell out the needed calculations.

Step 1 uses clause (c) of `lem-weil-pbc-affine-open-stalk-localization` separately for the given affine opens U and V. That statement supplies the canonical germ isomorphisms and their fraction formula; it assumes only an affine open in a scheme. The localization definition supplies the maximal ideals. The locally-ringed-space morphism definition supplies a sheaf map commuting with restrictions and local stalk maps. I wrote the inverse-image-of-maximal-ideal argument using units, and then used the germ square to prove contraction. No dominancy, Noetherian or finite-type hypothesis is inserted here.

Step 2 uses only the fraction description of localization and the germ compatibility of the locally ringed morphism, both already cited. The equation is checked on an arbitrary a/t with t outside p; contraction makes phi(t) a permitted denominator. The calculation proves compatibility for the canonical isomorphisms of step 1, not merely for some abstract isomorphisms.

Step 3 uses exactly the chain-supremum statement of `lem-weil-pbc-localization-dimension-chains-below-prime`, which has no finiteness hypothesis. I checked the distinction between its chains ending at a prime contained in p and the item's chains ending at p: appending p proves equality of the two suprema. A ring isomorphism gives an inclusion-preserving bijection of prime ideals, so dimension is unchanged. The argument covers infinite height as well.

Step 4 uses the residue-field and localization definitions and clause (b) of `lem-weil-pbc-prime-residue-field-algebra`. That clause actually states that the residue field is a fraction field of R/p; I did not substitute a node that only names residue fields. Local ring isomorphisms identify maximal ideals and induce quotient isomorphisms. The quotient map sends the class of a/t to the class of phi(a)/phi(t); this is the residue-field map of f by its definition and the stalk square of step 2. Contraction proves the quotient-ring map is injective, so the induced fraction-field map is well-defined. This checks the field algebra structures, not just field isomorphism types.

Step 5 is elementary from the transcendence-degree definition: transport polynomial coefficients and family members along the commuting field isomorphisms, and reverse the operation with their inverses. Both independence and cardinality are preserved. This supplies the residue transcendence-degree equality without invoking an uncited comparison lemma.

Step 6 uses the full statement of `lem-sc-integral-function-field-affine-fraction`: the affine opens are nonempty, and X and S are integral, as required. It gives the domains, injective generic germs, and fraction representatives. The image of the generic point is generic by the explicit continuity/closure/density inclusion, so the extension is the actual generic stalk map. The morphism definition makes the generic germ square commute. As the two generic stalks are fields, the generic map is injective; the square then proves that A -> B is injective. Thus both domain towers used later really exist and have identical composites.

Step 7 is a direct two-line consequence of fraction representatives and the definition of independence: a fraction a/t satisfies the nonzero polynomial tT-a, so an independent subset must be empty. The empty family is independent because the ring maps are injective. I checked that the coefficient t is nonzero, which is essential here. This avoids creating an elementary zero-degree node or hiding a general localization lemma.

Step 8 cites the domain tower node, whose actual statement permits intermediate domains rather than requiring fields. Step 6 verifies its injectivity and compatibility hypotheses for A -> B -> L and A -> F -> L. Substitution of the two zero terms gives the two displayed equalities with the same middle quantity trdeg_A L. No cancellation of an infinite cardinal is used, and there is no finite-type premise.

Small cases checked: identity morphisms (both degree terms vanish); a generic point on either affine chart (height zero and residue field the generic fraction field); A and B already fields; A a non-field domain with its fraction field as B; a transcendental field extension; and extensions with infinitely many independent variables or unbounded prime-chain lengths. Zero rings cannot occur because nonempty affine opens of integral schemes have nonzero domain coordinate rings. These checks expose no statement error. No proof step exceeds 2000 characters; the germ/contraction step and generic-map step have been expanded in this repair as described below.

The citation file was checked by literal substring membership against every cited statement. The proof-dependency list is exactly the union of step uses. No Lean was written, no compiler or Lake tool was run, and all writes are inside the assigned sandbox.

## Unfinished work

None in the one-level split. All current reused proof inputs are Mathlib leaves. The initial repair dry run completed successfully: `OK (not pushed)` at `f576e3015a9`. The expanded repair below is subject to a fresh final dry run before delivery.


## Repair of the landing return (2026-10-22)

The return names delivered head `570367a7af8` and says that the reader approved it, but the side-project completion had never been promoted to the live DAG. I retained the delivered sandbox proof, citations, report and search log. The first required dry run rebuilt it against the current server DAG and passed at `f576e3015a9`; this established that the retained delivery can be rebased without changing its statement. I then made the following substantive adjustments before the final dry run, rather than merely repushing that head.

The current repository item is still `unsplit` with no proof. Its statement, source, blueprint lineage, chapter, unit, creator and other non-split fields agree with the retained sandbox version. The permitted split fields contain the eight-step argument, its dependencies and the original searches. There is no released repair note for this item. I preserved the current statement and route, and the delivery tool constructs the new commit on the current DAG; I ran no git command in the shared repository.

I opened all fourteen current dependency statements, regardless of whether they might have changed since the returned head. The nine definition nodes still define exactly integral schemes, affine spectra, localizations, module stalks, Krull dimension, residue fields, transcendence degree, generic points and locally ringed morphisms. The five theorem nodes still supply precisely the affine germ localization (step 1), localization chain supremum (step 3), quotient fraction field (step 4), integral generic fraction field (steps 6--7), and injective domain tower equality (step 8). All fourteen now have status `mathlib`. Thus the report's former reference to reused unsplit nodes and the three off-unit tool requests were stale; both are corrected. All seventeen existing quotation pairs remain verbatim substrings of the current statements, so no citation is bent to accommodate a changed hypothesis.

For step 1 I expanded the inverse-image calculation for the extended prime ideal: a denominator equation $u(ta-b)=0$, with $u,t$ outside the prime and $b$ inside, forces $a$ into the prime. This explains the exact inference used for contraction. For step 6 I added the formula for the actual generic stalk map on $a/t$, showing directly that it is the fraction-field map induced by the given affine ring homomorphism. These are elementary calculations inside the existing argument, not new lemma nodes or new clauses. Their cited definitions and affine fraction theorem cover every object and denominator used. Steps 2--5 and 7--8 retain the previously reviewed arguments; I reread each against the current cited statements, including the field-isomorphism coefficient square and the domain version of the cardinal tower formula.

I reread Stacks 01HV (lemma-spec-sheaves), 01HY (lemma-morphism-into-affine-where-point-goes), 00E3 (lemma-spec-localization), 00KF (definition-height), 00CT (proposition-localize-quotient), 01RV (lemma-integral-scheme-rational-functions), 02JU (lemma-dimension-formula), 030G (definition-transcendence-degree) and 030H (lemma-transcendence-degree-tower), along with the main-20261015 ancestor proof. The domain tower input is verified in the existing Mathlib leaf and its `lift_trdeg_add_eq` / `trdeg_add_eq` declarations at lines 537 and 546; Stacks 030H itself only states the field tower version. The proof does not import the Noetherian and finite-type hypotheses of the dimension inequality 02JU: it proves only the affine comparisons that precede that inequality, and those hypotheses are unnecessary here.

The fresh library search still finds no project declaration for the whole conjunction. The generic map construction and affine residue-field square noted above cover only parts of it. Rechecking the identity, field, fraction-field and infinite-cardinal cases confirms that no finite-degree cancellation or Noetherian hypothesis has entered the repair. The item has no new nodes, no altered statement, no unrecorded searches, and no new same-tag pairs. All writes remain in this sandbox, and no Lean, compiler or Lake tool was used.


## Final continuation check (2026-10-22)

The retained repair, including the expanded ideal-membership and generic-map calculations, survived the provider interruption. The required initial dry run exited successfully at `0e8eb0061a2` (`OK (not pushed)`); no delivery invocation remained active. I compared the sandbox item with the current shared item: the live node remains unsplit, and the differences are confined to the proof, its dependency lists and origin, the split status/report and recorded searches. The statement, source, blueprint lineage and other inherited fields agree.

I reread all fourteen current dependency statements and rechecked every step against them. All seventeen step/dependency pairs have exact current-statement quotes in `citations.json`, and the proof dependencies equal the union of the step uses. The eight proof steps have lengths 1313, 504, 803, 830, 599, 1175, 539 and 738 characters, so none triggers the long-step review threshold. The existing four search-log entries were retained and their results reread; the statement and search questions have not changed, so no search was repeated or invented.

I also reread the current chapter and unit records, the main-20261015 ancestor proof, and the cited Stacks passages. In particular the domain tower formula was checked in Mathlib `TranscendenceBasis.lean:537` and `:546`, rather than attributed to the field-only Stacks tower statement. The project-source attachment check found no exact blueprint tag or declaration for this full conjunction; the two partial declarations and the additional-hypothesis local-dimension statement documented above were reread. The field, identity, generic-point and infinite-cardinal cases still satisfy the argument without cancellation or added finiteness assumptions. The substantive retained repair is ready for the final dry run and direct delivery.
