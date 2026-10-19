## Worker report

Files written:

- `dag/nodes/sec-smooth-purity/def-weil-constructible-intervals.json`: definition, split; no whole-item Mathlib match. The original two dependencies remain, and three existing nodes explicitly supply the coefficient quotient, general cohomological interval condition, and full-subcategory construction.
- `citations.json`: `[]`, since this is a definition with no proof steps.

New nodes: none. New Mathlib leaves: none.

Attachments: none. I read the two tagged project candidates in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/CategoryTheory/DerivedCategory/Constructible.lean:133` (`AlgebraicGeometry.Etale.DerivedCategory.constructibleIn`, with full subcategory at :150) and `WeilConjectures/SixFunctors/ProEtale/Derived/Constructible.lean:168` (`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleIn`, with full subcategory at :184). The former is on the etale site. The latter uses `ProEtale.DerivedCategory.boundedConstructible` defined at :86 as the essential image of etale-origin complexes. Its own implementation notes explicitly distinguish that definition from the intrinsic pro-etale constructibility used by this item's cited definition. No equivalence under exactly this item's arbitrary-scheme hypotheses was established; the tagged declarations therefore do not justify an exact attachment. Their local bodies are sorry-free, but that alone does not remedy the mismatch of definitions.

WANTED: none. The shared checkout has no populated `literature/blueprint` directory, and the supplied master checkout has an empty blueprint directory. I located and read the existing local archive at `/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-constructible-intervals.md` and the adjacent `def-weil-finite-torsion-constructibility.md`. The imported item's displayed formula and hypotheses agree verbatim with that source. No files were downloaded or written into any reference checkout.

The imported definition had not named the coefficient-ring convention and the generic interval/full-subcategory constructions as direct statement dependencies. I added the existing nodes, spelled out the quotient and inherited morphisms, and left the prime, finite extension, positive level, invertibility hypothesis, integers and inclusive endpoints unchanged. There is no statement dispute. The constructibility dependency mentions a global finite-field datum, but the actual finite quotient and intrinsic stratification predicate do not use it; the item's existing downstream interface already records this in `lean.note`. I have not added a finite-field hypothesis to this item or replaced its intrinsic constructibility with etale origin.

Nothing remains unfinished in this one-level definition split. Its status is split, its proof and proof dependencies remain empty, and no unit record is changed: it is not the key statement of `sk-def-sf-operations`.

## Existing-node and Mathlib searches

I searched the complete DAG and blueprint with `tools/blueprint_refs.py search` for `constructible intervals`, `cohomological`, `D_c`, `constructible cohomological`, `cohomological amplitude`, and `induced category`, and ran the ancestor query. The only blueprint definition of this same interval category is the item itself; the other matches use rather than define it. I opened the existing `def-weil-derived-category-cohomological-support` and `def-sf-induced-category`, so no duplicate interval or full-subcategory node was created. The ancestor is the item and its `blueprint.from` remains null; `same_as` is now the searched empty list.

All Mathlib searches used `msearch.py ND def-weil-constructible-intervals`, and the node records the exact queries. Two semantic phrasings return the general `DerivedCategory.IsGE` / `IsLE` bounds and their cohomological characterizations, with no constructibility condition. Loogle on `"constructible"` returns constructible subsets of spaces; Loogle on the two derived-category bounds returns bounded-representative results. The broad grep finds constructible sets in ChevalleyComplexity, with no constructible complexes; the narrower grep confirms `isGE_iff` and `isLE_iff`, whose source I read at `Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean:74-118`. One overly restrictive grep has no hits and is recorded as such. LeanSearch returned Internal Server Error and is recorded as unavailable. These generic bounds are already covered by the existing amplitude node and are not a Mathlib match for intrinsic constructibility.

## Review by ND

I read the item, its chapter and unit records, and the original definition in the local blueprint archive named above. The source defines exactly the objects of bounded intrinsic finite-torsion constructibility whose cohomology vanishes at every integer outside the closed interval. It asserts no stability under shifts, tensor products or triangulated structure for a fixed interval, and I have introduced no such assertion. The general six-operations unit has no proof paragraphs to realize for this auxiliary definition; the fixed chapter and unit route are unchanged.

I opened every statement dependency. `def-weil-derived-cohomology-sheaves` defines the cohomology functor on the derived category of modules over a sheaf of rings, explicitly including the constant ring on the small pro-etale site; this is the precise cohomology in the displayed formula. `def-weil-finite-torsion-constructibility` supplies the bounded full subcategory and its intrinsic finite locally closed stratification condition. `def-weil-l-adic-coefficient-extension`, clause 4, defines the very quotient `A_{E,n}` for a prime, finite extension and positive integer level. `def-weil-derived-category-cohomological-support` defines amplitude by vanishing below a and above b, which is exactly vanishing outside the inclusive integer interval. `def-sf-induced-category` supplies the full-subcategory construction with ambient Hom sets, identities and composition. Thus none of these citations is being used for a theorem absent from its statement. There are no numbered proof steps, so C1/C4 require no proof-step citations; `citations.json` is correctly empty.

I checked the domain of every definition: the coefficient level is positive; the cohomology indices and endpoints are integers; a is at most b; Y is an arbitrary scheme with ell invertible, and no Noetherian, finite-type, quasi-compactness, or finite-field condition is silently used. In particular I did not use an etale/pro-etale comparison theorem to identify the two constructibility notions in the Lean candidates. At a=b, only the one permitted cohomology degree can be nonzero; at the two endpoints the formula allows nonzero cohomology, so the interval was not accidentally made open. Negative endpoints cause no problem. A zero complex meets the vanishing condition in every interval; the empty scheme is not excluded. An object with a nonzero cohomology sheaf just below a or just above b is excluded regardless of constructibility. These checks also confirm that the statement imposes conditions on cohomology, not on the terms of a representative complex.

Against delivery-errors B-E: there are no new nodes requiring independent hypotheses, tag labels or new-node searches; the only added prose makes existing data explicit. Stacks Categories Tag 001D, `definition-subcategory`, was read at `/home/ubuntu/work-bp/sheaf/literature/stacks-project/categories.tex:207-228` and agrees with the inherited-Hom interpretation already stated in `def-sf-induced-category`. The statement remains self-contained through its named definitions and uses single TeX backslashes. No theorem or clause was shifted into a new node, no proof from a cited node was borrowed, and no new false lemma or circular proof was introduced. I corrected the missing direct definition dependencies; there were no other mathematical corrections.


## Earlier second reading (a previous round; superseded)

- Item statement: compared every hypothesis and the displayed formula with the archived `sec-smooth-purity/sk-def-sf-operations/def-weil-constructible-intervals.md` (order 1466), and its constructibility clause with the adjacent definition (order 1454); PASS. The prime, finite extension, positive level, invertibility on an arbitrary scheme, integer endpoints and inclusive interval are preserved.
- Proof steps: none; checked `proof = []` and `proof_deps = []` against the source, which defines an object predicate rather than asserting a theorem; PASS. `citations.json = []` is correct, since there are no proof-step citations.
- New nodes: none; checked all sandbox node files and the existing DAG search for interval/constructibility vocabulary; PASS. No elementary claim, duplicate, restatement or Mathlib result was made a new node.
- Dependency `def-weil-l-adic-coefficient-extension`: read clause 4 and the chosen uniformizer in clause 3; PASS. It supplies exactly the quotient used here, for every positive integer level, without any finite-field datum.
- Dependency `def-weil-derived-cohomology-sheaves`: read its arbitrary-site definition and its explicit constant-ring small-pro-etale specialization; PASS. It supplies cohomology of derived objects, not vanishing of terms of a chosen representative.
- Dependency `def-weil-finite-torsion-constructibility`: read the full statement and its recorded intrinsic interface; PASS for the intrinsic finite-stratification predicate. Its introductory finite-field parameters are unused by that predicate, as the existing `lean.note` records. No finite-field hypothesis is introduced here. The stratification is global and finite; it has not been replaced by the affine-local Stacks convention.
- Dependency `def-weil-derived-category-cohomological-support`: read its support-set definition and amplitude clause; PASS. Outside the inclusive interval means exactly degrees strictly below a or strictly above b. Independently read Mathlib `DerivedCategory.isGE_iff` and `isLE_iff` at `TStructure.lean:90,107`.
- Dependency `def-sf-induced-category`: read its Hom formula, identities, composition and injective-object-map specialization; PASS. Apply it to the inclusion of the objects satisfying the displayed predicate. Independently read Categories Tag 001D, label `definition-subcategory`, at the local Stacks archive `categories.tex:207-228`, and Mathlib `CategoryTheory.ObjectProperty.FullSubcategory` at `FullSubcategory.lean:24-95`; both give the inherited morphisms used here.
- Existing Lean candidates: independently read the etale definitions at `CategoryTheory/DerivedCategory/Constructible.lean:86-159` and the pro-etale implementation notes and definitions at `SixFunctors/ProEtale/Derived/Constructible.lean:38-50,78-95,165-193`; PASS on leaving them unattached. The former uses another site and the latter uses an essential-image predicate. A tagged, locally sorry-free body does not identify that predicate with the intrinsic global finite-stratification definition under the item's hypotheses.
- Small cases: the zero complex is admitted; on the empty scheme the vanishing condition is vacuous; for a field of characteristic different from ell and n=1 the coefficient ring is the residue field and the same predicate applies; at a=b=0 only degree zero can survive; negative endpoints remain meaningful; cohomology in degrees a and b is allowed, while degrees a-1 and b+1 are forbidden; PASS. Level n=0 lies outside the source's domain and was not added. No fixed-interval triangulatedness or stability theorem is asserted.
- Blueprint and route: read `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-def-sf-operations.json`, and independently ran whole-blueprint searches for `constructible intervals` and `cohomological amplitude` plus the ancestor query; PASS. The former returned `thm-sf-preservation-class`, a preservation theorem rather than this definition, and the latter returned no node. This auxiliary definition realizes no missing proof step of the unit and changes no chapter or unit route.

Changes in this second reading: appended three independently executed Mathlib search records to the item, preserving the raw `searches.jsonl` output. The semantic search returned general derived-category bounds. The broad grep was capped at 25 hits and is recorded only as evidence about its returned candidates; a second grep scoped to `Algebra/Homology/DerivedCategory` returned no constructibility hits. Added this independent review. No mathematical statement, dependency, source, proof or citation was changed: the first worker's split withstands the checks above, and no statement dispute was found. The first worker's report and `## Review by ND` remain in place.

## H1 repair: stage-2 declaration and compilation evidence

The returned packet was missing the item declaration and its node `lean` record. I added
`lean/Sheaf/Paper/ConstructibleCohomologicalIntervals.lean`, whose documented primary
declaration is
`AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructibleIn`. It combines the
landed `intrinsicFiniteTorsionConstructible` predicate with the landed
`proEtaleCohomologicalSupport` predicate, requiring support only in the inclusive interval
`[a,b]`; the module also records the inherited full-subcategory category
`intrinsicFiniteTorsionConstructibleInCategory`. The node now records the primary module,
declaration, verbatim signature, branch, author, date, and the category declaration.
The upstream étale-origin and pro-étale-origin declarations remain unattached because
their constructibility predicates differ from this item's intrinsic finite-torsion
predicate.

Validation used the prescribed `scompile.py` wrapper on the item module:

```text
sandbox Sheaf/Stage2/Sandbox0.lean
(with the modules compiled into /tmp/nt-local-compile-vzia4yxl/.lbuild) [2.2 s]
library Sheaf/Paper/ConstructibleCohomologicalIntervals.lean
[2.4 s]
```

The first probe had an unused `hab` warning; I repaired it by naming the hypothesis
`_hab` in the primary declaration and updated the node's verbatim signature. The final
run exited 0 with no errors or warnings.

The stage-1 delivery dry run was then rerun with
`python3 /home/ubuntu/weil-launcher-nt/deliver.py ND def-weil-constructible-intervals --no-push`.
It printed:

```text
OK (not pushed) deliver/ND/def-weil-constructible-intervals at c63e054ca7: preflight passed
```

After normalizing the recorded signature to the exact output of
`tools/stage2_delivery.py signature` and recording both declarations in `lean.declarations`,
I reran the dry run. It printed:

```text
OK (not pushed) deliver/ND/def-weil-constructible-intervals at 3fbb39b81c: preflight passed
```

A final source-convention repair made the Lean declaration explicitly carry the source's
hypothesis that the coefficient exponent is invertible on `Y`:
`[HasInvertibleExponent (Padic.coefficientExtensionRing l E n) Y]`. This is the recorded
project convention for “the prime `ell` is invertible on `Y`” for `A_{E,n}`; it adds no
finite-type, Noetherian, or finite-field hypothesis. The node's recorded signature was
updated to match the declaration exactly, and the module was rechecked by `scompile.py`:

```text
sandbox Sheaf/Stage2/Sandbox0.lean
(with the modules compiled into /tmp/nt-local-compile-2mhd81n4/.lbuild) [2.6 s]
library Sheaf/Paper/ConstructibleCohomologicalIntervals.lean
[2.5 s]
```

The final repair dry run printed:

```text
OK (not pushed) deliver/ND/def-weil-constructible-intervals at b5e21d6f70: preflight passed
```

A final dry run after the report update also passed:

```text
OK (not pushed) deliver/ND/def-weil-constructible-intervals at edcce45b8b: preflight passed
```

## Second reading by ND

This is an independent stage-1 reading on 2026-10-16. I read delivery-errors B–E, GOAL.md, coord/dag-sync.md, the worker contract, the stage-1 contract, and the sandbox packet. The earlier second reading and H1 stage-2 repair section above are historical records, not validation performed by this reader. The present brief authorizes only stage 1: no Lean was written and no compiler, Lake, build or compilation wrapper was run. The stage-1 delivery wrapper packages node JSON and the report only.

- Item statement: PASS against the archived blueprint `master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-constructible-intervals.md`, order 1466, read at `/home/ubuntu/work-bp/sheaf/literature/blueprint/`. Matched prime ell, finite extension E/Q_ell, n >= 1, arbitrary scheme Y with ell invertible, integer a <= b, membership in D^b_c, and vanishing in every integer outside [a,b], separately. The added quotient and inherited-Hom description unpack existing conventions without changing objects or hypotheses.
- Proof steps: PASS; there are zero, as appropriate for the source's definition. Checked `proof = []`, `proof_deps = []`, `proof_origin = null` and `citations.json = []`; no theorem is concealed in an elementary step and no proof-step quotation is missing.
- New nodes: PASS; the sandbox has only the item JSON, hence zero new nodes and zero new Mathlib leaves. B1–B7, C5 and D1–D2 introduce no new-node obligations. The three reusable added dependencies already exist in the shared DAG.
- Coefficient dependency `def-weil-l-adic-coefficient-extension`: PASS against its statement, clauses 3 and 4. The chosen uniformizer and quotient O_E/(varpi_E^n O_E) have exactly the source's coefficient domain; no characteristic p or finite-field datum is needed here.
- Cohomology dependency `def-weil-derived-cohomology-sheaves`: PASS against its full arbitrary-site statement and explicit specialization to the constant coefficient ring on Y_proet. The vanishing condition concerns cohomology objects in the derived category, not terms of a representative complex.
- Constructibility dependency `def-weil-finite-torsion-constructibility`: PASS against its statement and adjacent archived blueprint file, order 1454. It requires finitely many nonzero cohomology sheaves and, for each, a global finite locally closed constructible stratification with locally constant finite stalks. The unused introductory finite-field datum is not used to define that predicate; the existing dependency `def-weil-proetale-constructible-sheaf` states the same stratification predicate for every scheme and finite coefficient ring. I read that statement too, and did not add a finite-field or finite-type hypothesis to this item.
- Amplitude dependency `def-weil-derived-category-cohomological-support`: PASS against its statement and Mathlib `DerivedCategory.isGE_iff` / `isLE_iff`, `TStructure.lean:90-118`. Below a means r<a and above b means b<r; the endpoints themselves are admitted. Both are exactly the complement of the displayed inclusive integer interval.
- Full-subcategory dependency `def-sf-induced-category`: PASS against its induced Hom sets, identities, composition and injective-object-map clause; independently read Stacks Categories Tag 001D, label `definition-subcategory`, `/home/ubuntu/work-bp/sheaf/literature/stacks-project/categories.tex:207-228`. Read Mathlib `CategoryTheory.ObjectProperty.FullSubcategory`, `FullSubcategory.lean:24-105`, including the category instance and inherited identity/composition. Inclusion of the objects satisfying the interval predicate is the specialization needed here.
- Source conventions: PASS after reading Stacks Pro-etale Cohomology Tag 09AJ, label `definition-constructible`, archived `proetale.tex:5224-5233`. Stacks uses a finite stratification on each affine open and Noetherian coefficients; this item's blueprint uses a global finite stratification with finite coefficients. I retained the blueprint convention and did not silently equate the two on arbitrary schemes. The item's source is the blueprint, not Tag 09AJ.
- Existing declarations: PASS on leaving the slopmaster2 candidates unattached, after independently reading `CategoryTheory/DerivedCategory/Constructible.lean:86-159` and `SixFunctors/ProEtale/Derived/Constructible.lean:38-50,78-95,165-193`. The former is on the etale site; the latter defines constructibility by an etale essential image. A comparison with the intrinsic predicate is not a definition and was not proved here. No sorry-bearing declaration in the read-only master was treated as a finished proof.
- Independent searches: PASS; ran a new finite-stratification/Set.Icc LeanFinder query, Loogle on `"FullSubcategory"`, and a scoped Mathlib grep for `constructib|stratif|locallyConstant`, all through the prescribed msearch.py. Read the returned general bounded-representative theorem at `TStructure.lean:180-188` and the full-subcategory declarations. Neither supplies intrinsic constructibility. Exact queries and actual verdicts are appended to the node, with raw wrapper records preserved in searches.jsonl; no unavailable service is called a no-match.
- Duplication and route: PASS against a whole-DAG interval/constructibility text search, a whole-blueprint `constructible intervals` query, the ancestor query, and the item's chapter/unit records. The sole blueprint search hit `thm-sf-preservation-class` is a preservation theorem using intervals, not this definition (its statement was opened). The item is its own blueprint ancestor and is an auxiliary definition, not the unit's key statement. No chapter or unit record changes.
- Small cases: PASS. The zero complex has zero cohomology in every degree. The empty scheme is permitted, with the zero sheaf satisfying the conditions. For Y the spectrum of a field of characteristic different from ell and n=1, A is the residue field and the same condition applies. For a=b=0, exactly degree zero is allowed; for a=b=-1, exactly degree -1 is allowed. Degrees a and b may be nonzero, whereas a-1 and b+1 must vanish. Level n=0 is outside the source's domain. No triangulatedness or shift stability of a fixed interval subcategory is asserted.

Changes made: removed the stale stage-2 `lean` record from the sandbox item JSON, since it is not owned by a stage-1 split and referred to a module outside this delivery. The historical Lean file is left untouched and is not packaged by deliver.py; the wrapper preserves any maintainer-owned record on its fetched base. Appended three independently executed search records and this review. Preserved the first worker's sections, including `## Review by ND`, and its mathematical statement, dependencies, proof, citations and source. No statement dispute or mathematical repair was necessary. New nodes: 0; new Mathlib leaves: 0.
