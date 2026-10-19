## Files written

- dag/nodes/sec-trace-formula/lem-trf-integers-excellent.json: statement item, split in seven steps; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-regular-ring-universally-catenary.json: one new statement-only unsplit generic tool; no Mathlib match.
- citations.json: the complete verbatim statements for all twelve step/node citations.
- searches.jsonl: actual msearch.py results; old item searches retained and fresh queries appended.

## Attachments

None. Searches in /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint id, excellent/Excellent, catenary, and CohenMacaulay found no project declaration asserting the item or the new general theorem. The excellence hit is only a comment in Etale/Derived/Stability.lean. No compiler or Lean writing was used.

## WANTED

None. All mathematical sources used here are present in literature/stacks-project/.

## Findings and corrections

The item is true as imported, and its statement is retained verbatim. It had no proof and no Lean-audit declaration to attach. Its source 07QW explicitly distinguishes the integer seed from preservation of excellence under finite type extension; the latter is insufficient to prove the seed. No unit/chapter record or maintainer metadata is changed. The original existing searches are retained. This sandbox contained only dispatch markers, with no earlier split or search log.

I read chapter sec-trace-formula, unit sk-i-curve-zero, its current main-20261015 ancestor proof and the item's arithmetic-model ancestry. The split supplies the excellence input for spreading out before the Orgogozo/nearby-cycle part of the existing normal-cone argument. It changes none of that route and uses no SGA source. The three off-unit non-leaf tools (integer localizations, integer G-ring, and the J-2 residue-field criterion) are declared in split_report.tool_uses with their purposes. The new general catenarity theorem inherits the item's unit.

## Not duplicates

The whole DAG was searched for excellent, J-2, universally catenary, Dedekind/catenary, 07QW, 07PJ, 00NM and 00NQ; blueprint_refs.py searched excellent, regular ring, catenary, J-2 and perfect field across all chapters. No blueprint node states integer excellence or the general regular-ring catenarity theorem. Existing lem-exc-fields-excellent applies only to fields, and the polynomial-chain theorem is over a field, so neither proves catenarity for finite type integer algebras. All DAG nodes containing either source tag 00NM/00NQ were opened; the following lines distinguish their statements, including occurrences only in proofs/searches.

lem-trf-regular-ring-universally-catenary vs lem-zl-bertini-finite-cover-curve: the existing statement concerns Curves through prescribed points preserving a finite cover; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-complete-local-flat-presentation: the existing statement concerns A local map of complete Noetherian local rings has a flat Cohen presentation; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-complete-local-map-regular-presentation: the existing statement concerns Compatible regular presentations of a map of complete local rings; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-flat-over-regular: the existing statement concerns A local map from a regular local ring sending a regular system of parameters to a regular sequence is flat; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-flat-polynomial-append-fibre-regular-sequence: the existing statement concerns Appending closed-fibre regular coordinates preserves flatness; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-flat-polynomial-append-tensor-fibre: the existing statement concerns Flatness of the polynomial-append tensor fibre; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-flat-regular-fibre-parameter-selection: the existing statement concerns Select flat polynomial parameters in a regular closed fibre; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-fs-adic-lift-from-residue-field: the existing statement concerns A formally smooth complete local algebra over the residue field lifts to a formally smooth complete local algebra; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-geometrically-regular-over-field-flat: the existing statement concerns Flatness over a localized polynomial ring whose variables give a basis of the differentials of a residue subfield; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-global-complete-intersection-local-regular-sequence: the existing statement concerns The equations of a global complete intersection form a regular sequence at every prime; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-hypersurface-derivation-regular: the existing statement concerns Quotient of a regular ring by an element with a unit derivative is regular; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-miracle-flatness: the existing statement concerns Miracle flatness; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-polynomial-ring-maximal-chain-height-difference: the existing statement concerns Maximal chains of primes in a polynomial ring over a field have length the difference of the heights; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-popescu-find-sequence: the existing statement concerns Choosing generators of a regular prime with controlled annihilators (Ogoma); it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-popescu-resolve-char-p: the existing statement concerns Popescu's local problem is resolvable in characteristic p for geometrically regular Lambda; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-popescu-resolve-separable: the existing statement concerns Popescu's local problem is resolvable at a regular prime with separable residue field; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-regular-fiber-kernel-parameter-lift: the existing statement concerns Lift regular closed-fibre kernel parameters preserving the base regular sequence; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-regular-local-finite-gl-dim: the existing statement concerns A regular local ring has finite global dimension; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-regular-local-finite-module-resolution: the existing statement concerns Finite modules over a regular local ring have bounded projective resolutions; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-regular-local-generators-regular-sequence: the existing statement concerns A regular system of parameters is a regular sequence; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-regular-local-hypersurface-criterion: the existing statement concerns A non-square element cuts a regular local hypersurface; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-regular-local-mcm-free: the existing statement concerns A maximal Cohen–Macaulay module over a regular local ring is free; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-regular-ring-normal: the existing statement concerns A regular ring is normal; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-smooth-at-maximal-ideal-alg-closed-differentials-bound: the existing statement concerns Over an algebraically closed field, few differentials at a closed point imply smoothness there; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-weil-pbc-smooth-over-field-local-complete-intersection: the existing statement concerns A smooth algebra over a field is a local complete intersection; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs thm-trf-frobenius-fixed-points: the existing statement concerns Scheme-theoretic Frobenius fixed points; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-sbc-regular-codimension-two-etale-extension: the existing statement concerns Finite etale extension across a regular codimension-two boundary; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-exc-fields-excellent: the existing statement concerns Fields are excellent; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-exc-regular-locus-open-from-prime-quotients: the existing statement concerns Regular locus is open when every prime quotient has a regular open; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-pur-smooth-pair-local-coordinates: the existing statement concerns Local coordinates for a closed immersion of smooth schemes; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-pur-smooth-pair-regular-immersion: the existing statement concerns Local regular equations for a closed immersion of smooth schemes; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

lem-trf-regular-ring-universally-catenary vs lem-trf-snc-divisorial-log-chart: the existing statement concerns Divisorial charts of a smooth strict normal crossings pair; it does not assert universal catenarity for every commutative Noetherian ring whose prime localizations are regular.

The existing excellent-ring definition is a predicate, not a theorem giving catenarity. The J-2 criterion already states exactly the general openness implication needed here and was reused; no integer-J-2 or perfect-prime-field node was created. The binomial/prime-field calculation belongs to Step 4. The new theorem is a genuinely general dimension-theoretic tool, with neither the integer ring nor any G-ring or J-2 conclusion in its statement; it is not a renamed clause of this item.

## Review by NP

I read the local Stacks TeX of 07QW (more-algebra.tex, proposition-ubiquity-excellent), including the complete proof. Its integer case asks for the G-ring and J-2 theorems and universal catenarity; that is the seven-step proof here. I also read 07PX (proposition-ubiquity-G-ring), 07PJ (proposition-ubiquity-J-2), 07PC (lemma-J-2, especially condition (4) and its implication to (1)), 07QT (definition-excellent), 00NM (algebra.tex, lemma-CM-ring-catenary, whole proof), and 00NQ (lemma-regular-ring-CM, statement and proof), checking labels against tags/tags. The new theorem is their regular-ring corollary: every prime localization is Cohen--Macaulay by 00NQ, so the Noetherian ring is Cohen--Macaulay, and 00NM gives universal catenarity. This is only an explanation of its source in the report; the new JSON carries a statement and no proof.

Step 1 uses the complete statement of lem-weil-pbc-z-localizations-dvr: Noetherianity, the exhaustive zero/nonzero prime classification, Q at zero, and dimension-one DVRs with principal maximal ideals elsewhere. The statement of lem-weil-pbc-field-regular-ring gives regularity at the zero prime. The definition def-weil-regular-scheme supplies exactly the comparison between dimension and the number of maximal-ideal generators. Thus the DVR case needs no extra theorem: one generator and dimension one are already the definition. All these cited statements were opened; no property was taken from a cited node's proof. Regularity was established here rather than hidden in the new node.

Step 2 uses only the actual conclusion of lem-weil-pbc-z-g-ring. It gives the integer G-ring condition, so there is no inappropriate appeal to the definition as if it proved formal-fibre regularity. This is an existing theorem, not an assertion that integer excellence follows from being a G-ring alone.

Step 3 uses the residue-field description furnished by the integer localization node and the explicit characteristic-zero clause of def-weil-pbc-finite-purely-inseparable-extension. That clause already makes L/Q trivial, so there is no unproved perfectness assertion. The subalgebra B is the actual image of Z in L, finite as a Z-module on the generator 1, with fractions all of L. Step 1 makes its whole spectrum regular; its zero prime witnesses nonemptiness. Identifications use the injective field structure map and preserve the given Z action, as the criterion requires.

Step 4 again uses the exhaustive prime classification and the stated definition of purely inseparable extension. For kappa((p)), Bezout explicitly supplies inverses to nonzero residues, so the residue field is Z/pZ. The elementary power calculation is written out: binomial coefficients in the interior are divisible by p, Frobenius and its iterates fix the prime subfield, and (x-a)^(p^n)=0 forces x=a in the field L. No general perfect-field or separability theorem is cited or silently needed. The image B of F_p in L is generated by 1 as a Z-module, its fraction field is L, and lem-weil-pbc-field-regular-ring states its regularity. A field has its zero prime, so the chosen regular open is nonempty.

Step 5 applies the complete statement of lem-exc-j2-residue-field-criterion, which was read and compared with 07PC (4). Its Noetherian hypothesis is Step 1, and both kinds of required finite subalgebra witnesses are Steps 3 and 4. In particular one needs a model finite as a MODULE, not merely finite type: the explicit single module generator checks that distinction. The result is openness in EVERY finite type algebra, exactly the J-2 predicate used by excellence.

Step 6 takes precisely the conclusion of the new generic theorem. Its hypothesis is regularity at every prime plus Noetherianity, already proved in Step 1. The new theorem's statement introduces R, A, the comparable primes and chains; its notion dependencies are existing definition nodes, and no hidden Cohen--Macaulay notion is required to read the statement. The conclusion is universal catenarity, not just catenarity of Z. Step 7 reads the full statement of def-exc-excellent-ring and combines the four established conditions without adding a hypothesis.

I checked B1--B10: the new node is statement-only and self-contained, uses single TeX escaping and correct Stacks labels, cites its notion definitions, has complete blueprint ancestry and same_as=[], and has real recorded searches. The fresh leanfinder searches used two meanings of the catenarity statement (regular rings and saturated chains), Loogle found no catenary declaration, and RingTheory grep found no catenary/CohenMacaulay occurrence. LeanSearch returned finite-type Noetherianity, not catenarity. The second semantic query returned ringKrullDim_add_length_eq_ringKrullDim_of_isRegular; I read Mathlib/RingTheory/KrullDimension/Regular.lean: this concerns quotient dimensions for a regular sequence and does not imply the universal saturated-chain assertion by one specialization. Item searches in two phrasings likewise returned ordinary rings, domains, Dedekind and Zariski-main facts, not excellence. The existing item's prior search results were retained and considered too. No unavailable result was represented as absence.

For C1/C4 and D, every non-elementary input has a cited statement, the new node is genuinely more general than the integer application and supplies only one dimension-theoretic input, and the two J-2 witness cases are proved directly in the item. citations.json copies complete statements, so it includes every clause used, not a fragment selected from a proof. The dependency graph has no intended return edge: all existing cited nodes' direct dependencies were inspected, and the new node depends only on definitions. Server checks test the actual overlay for cycles.

For E, I tested both residue characteristics and the boundary n=0 in the purely inseparable calculation (then x=a directly). For p=2 the binomial identity and the same argument still hold. The new theorem includes fields, DVRs, finite products of fields and the zero ring: the last has only the zero algebra, so its chain conditions are vacuous. Taking equal endpoints gives length zero. There is no assumption of globally finite dimension: only each fixed prime interval has a finite bound, as required by universal catenarity. Nonregular rings are outside its hypothesis, and no excellence assumption was inserted. No statement dispute arose. Each step is below 2000 characters (the longest is Step 4, 1147 characters); the longest step is one explicit elementary prime-field argument and hides no separate general lemma.

No earlier return entry was supplied. During self-review I avoided creating an integer J-2 clause or a prime-field perfectness lemma, and explicitly checked module finiteness and nonemptiness in both residue-field cases. Required dry-run diagnostics and the final delivery result are recorded below after the commands complete.

## Unfinished work

No part of the one-level split remains unfinished. The one new unsplit theorem is deliberately left as a future stage-1 item, with its complete statement, sources and genuine Mathlib searches. It is not asserted proved in Lean.

## Validation

The required deliver.py NP lem-trf-integers-excellent --no-push completed with exit 0 and printed OK (not pushed), preflight passed, commit c19061f96e. This includes the server overlay DAG and split checks. The process exited before delivery was invoked; only one invocation was active. No node repair was required by this dry run.
