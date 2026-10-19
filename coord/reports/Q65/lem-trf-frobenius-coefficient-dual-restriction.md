# Stage-1 report: lem-trf-frobenius-coefficient-dual-restriction

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-frobenius-coefficient-dual-restriction.json`: statement, now split into nine proof steps; no exact Mathlib match.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `searches.jsonl`: preserved command-generated search records; `write_split.py` is sandbox-only preparation code.
- `report.md`: this report.

No new DAG nodes, definitions or Mathlib leaves. No unit record changed: this item is a subsidiary coefficient lemma, not the key statement of its unit.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the item id and for coextension, restriction/dual and dual/restriction notions. `AlgebraicGeometry.Etale.coextendScalars` and `rightDerivedLowerStarCompCoextendScalarsIso` in `SixFunctors/Etale/Derived/CoextendScalars.lean:55-95` construct derived coextension and compare ordinary direct image. They do not state either exceptional-dualizing/internal-Hom clause of this item. They are reference implementations, not attachments. Upstream master is not used as evidence of a finished proof.

## Literature wanted

WANTED: Lu–Zheng, Duality and nearby cycles over general bases, Remark 3.3 / Theorem 5.1, inherited contextual source for the geometric-duality parent. The PDF named by the item's inherited source is absent. The coefficient lemma itself is proved here by an agent argument from the explicit cited ringed-site/categorical results; it is not attributed to Lu–Zheng or to the Lean coextension file. No download was attempted.

## What needed repair

The item had an empty proof and no proof dependencies. Its statement is mathematically correct, including the unbounded/no-finite-Tor clause, and was retained verbatim. There is no STATEMENT-DISPUTED correction.

The key coefficient distinction is restriction, not derived tensor reduction. At n > 1 the residue field is not a perfect A-module, so finite-Tor scalar-extension results do not prove this item. The correct right-adjoint functor is derived coextension, represented by the annihilator of the uniformizer in a K-injective target. Likewise the existing `lem-sf-compact-support-restriction-of-scalars` is pro-etale; I did not apply it to ordinary etale categories. Steps 5-6 write the etale comparison directly using a single compactification and the generic ringed-topos composition theorem.

The source blueprint ancestor is `lem-trf-local-term-locality`, proof (1)-(2); the subsidiary route runs through trace specialization, cohomological comparison, nearby-cycle Verdier duality and geometric-duality bounds. I read the current main-20261015 ancestor proof and `dag/units/sk-i-curve-zero.json` and the trace-formula chapter. This item supplies the coefficient-devissage input already requested by `lem-trf-geometric-duality-uniform-range`, rather than replacing the contracting-correspondence route or the lecture-notes purity route. All off-unit statement tools are declared in `split_report.tool_uses`; no maintainer-owned `tool_uses` field was set.

## Searches and reuse

Read the inherited item searches, ran the prescribed search command with two semantic phrasings, Loogle and two source grep queries, and recorded the exact command-generated records. LeanSearch and both other services were available. The substantive hits were `ModuleCat.restrictCoextendScalarsAdj` and its evaluation/inverse formulas; I read Mathlib `Algebra/Category/ModuleCat/ChangeOfRings.lean:585-679`. Those are ordinary module adjunctions, not a derived etale exceptional-dualizing comparison. Representation coinduction, Shapiro and vector-space duality hits also do not state the item.

Searched the whole DAG statements, the whole slopmaster2 `WeilConjectures/` source, and `tools/blueprint_refs.py search` for coextension, coefficient dual restriction, and compact-support restriction, and used `ancestor` for provenance. Reused twenty existing dependencies. I considered but did not introduce a general coextension-adjunction node, a residue-socle node, or an etale compact-support restriction node: their needed special cases are explicit short calculations from the cited statements and definitions. There are no new-node searches or unlogged claims to audit.

## Not duplicates

No new nodes. The potentially tempting duplicate `lem-sf-compact-support-restriction-of-scalars` is a pro-etale theorem; the needed etale calculation is Steps 5-6 of the item, using `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, which explicitly covers arbitrary small ringed sites. The algebraic self-injectivity input is exactly the A_(E,n) clause of the existing `lem-weil-coefficient-frobenius`, not a new lemma.

## Review by Q65

I checked this split against delivery-errors B-E with the node statements open, and read the relevant local sources: Stacks `sites-modules.tex` for module sheafification and the abelian forgetful functor (03CY, 03DA), extension by zero (03DI), internal sheaf Hom (04TT); `sites-cohomology.tex` for derived pushforward composition (0D6E), Hom complexes (0A8X), internal Hom into K-injectives and well-definedness (0A94, 0A95, 08J7); `derived.tex` for the exact-left-adjoint K-injective lemma (08BJ); `etale-cohomology.tex` for the separably closed point case of 0EZP; and the existing coefficient-Frobenius blueprint statement and its Baer-criterion proof. I read the current trace-formula ancestor and the source Lean coextension implementation only as context. There is no new node whose independent source or hypotheses remain to check.

Step 1 uses `def-pc-sheaf-restrict-scalars` for the unchanged abelian sheaf and `lem-weil-pbc-module-sheaves-colimits-forgetful` for actual kernel/cokernel exactness; it does not assume restriction preserves injectives. `def-pur-sheaf-hom` defines Hom on slice sites, so the evaluation-at-1/annihilator formula gives a sheaf map and its inverse. Independence of a lift and factorization through the annihilator prove the ordinary adjunction explicitly; no black-box coinduction theorem is hidden there.

Step 2 uses `prop-pur-kinjective-resolutions-exist` on small ringed sites for target resolutions, `lem-weil-pbc-right-adjoint-preserves-kinjective` with the exact functor of Step 1 for their coextensions, and `lem-weil-pbc-kinjective-hom-derived` for independence via homotopy equivalences. Each statement has precisely the unbounded scope required. `def-pur-derived-internal-hom` supplies the K-injective computation and independence of the internal-Hom model. In Step 3 the same Hom-derived lemma applies separately over A and k; the displayed chain-map and homotopy factorization supplies the derived adjunction, including its naturality. No bounded-below derived comparison is substituted for it.

Step 4 uses only `def-pur-sheaf-hom`, `def-pur-hom-complex` and `def-pur-derived-internal-hom` after Step 2. I checked the full product over all source degrees and the differential sign, not just degree zero or individual module Hom. Factorization through the annihilator commutes with restrictions, products, the two differential summands and composition. Thus the step is elementary relative to the previously established K-injective representatives; arbitrary unbounded source complexes cause no totalization or finite-Tor assumption.

In Step 5 `thm-nagata-compactification` supplies the compactification since Spec F is qcqs; `lem-weil-pbc-finite-type-over-noetherian` verifies Noetherianity of Z and its proper compactification over the field. `def-amb-etale-compact-support` says exactly Rr_* j_! on ordinary unbounded etale categories. `def-weil-pbc-extension-by-zero` and `def-weil-presheaf-modules-sheafification` identify both the presheaf and sheafified coefficient actions; these definitions actually include the construction used. Step 6 uses the general small-ringed-topos theorem `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, not the pro-etale specialization. I checked both structural ring maps are A -> k, that the two composites coincide, and that the exact identity-topos direct image is derived by the termwise restriction functor. The compact-support definition then gives exactly the required natural functor comparison.

Step 7 uses the first clause of `lem-kun-0ezp`, which really states that every etale object over the separably closed field is a disjoint union of copies of the point. The sheaf axiom therefore proves the exact module-equivalence needed, even when F is not algebraically closed. `lem-weil-coefficient-frobenius` explicitly states injectivity over itself for A_(E,n); it is the finite quotient A, not the non-self-injective integral DVR, that is used. With the equivalence, `lem-weil-pbc-bounded-below-injectives-kinjective` applies to A_s[0]. `lem-weil-l-adic-extension-integers-dvr` states the domain/DVR property used in cancellation. The socle identification and multiplication map are written out, rather than called a standard Frobenius-ring fact.

Step 8 uses `thm-amb-etale-exceptional-adjoint` with precisely the finite-ring and Noetherian-compactification hypotheses checked in Step 5. Every intermediate Hom category is specified, so the residue action is not forgotten before representability. `lem-galois-yoneda-fully-faithful` states full faithfulness for representable presheaves on an arbitrary category, which is exactly what is needed to turn the displayed natural Hom bijections into inverse arrows; no general evaluation form of Yoneda is being taken from a merely fully-faithful citation. Step 9 uses functoriality in `def-pur-derived-internal-hom` to compose the established isomorphisms and obtain contravariant naturality in M.

For small cases I checked n=1 (all coefficient functors and the socle isomorphism reduce to identities), n=2 (the socle is pi A, and the residue module need not be A-flat), Z=Spec F (the conclusion is the direct module Hom/coextension formula), the empty scheme, zero M, shifts, and unbounded M. These tests agree with both clauses. No hypothesis on the geometric field beyond separable closedness is used. The uniformizer is already fixed, so its socle identification is allowed; no claim of uniformizer-independent normalization is added.

Every non-elementary fact is an existing cited statement; every citation has a verbatim statement quotation in `citations.json`. No new node restates a clause or an elementary consequence, no source tag serves in place of a node, and no dependency reaches back to this item (checked on the available DAG). Every step is under 2000 characters. No SGA source is used. No Lean file, compiler, Lake process, live project file, or launcher file was written or run.

## Unfinished work

No mathematical step of the item remains unfinished. The inherited unavailable contextual Lu–Zheng PDF is recorded above; the submitted proof is explicitly agent-origin and does not rely on an unavailable assertion from it.
