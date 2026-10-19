# Stage-1 report: def-trf-coefficient-conventions

## Files written

- `dag/nodes/sec-smooth-purity/def-trf-coefficient-conventions.json`: definition; split by explicit references to its nine existing defining notions; no exact Mathlib match.
- `citations.json`: `[]`, because the item is a definition with no proof steps.
- `searches.jsonl`: actual search log produced by msearch.py; seven queries, including a second semantic phrasing and an unavailable LeanSearch request.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit file is changed: this recorded-in-advance coefficient node does not state the containing unit's admissibility datum.

## Attachments

None. I searched both read-only source trees by the node id, the exact blueprint tag, coefficient conventions, finite coefficient categories, finite-Tor categories, and compact-support cohomology. The relevant project definitions include `AlgebraicGeometry.ProEtale.DerivedCategoryFiniteTor` in `SixFunctors/ProEtale/Derived/TorAmplitude.lean:183`, `AlgebraicGeometry.ProEtale.Ctf` in `SixFunctors/ProEtale/TraceFormula/Defs.lean:196`, and `AlgebraicGeometry.ProEtale.compactlySupportedGlobalSections` / `compactlySupportedCohomology` in `SixFunctors/ProEtale/Derived/LowerShriek.lean:238,246`. These cover component notions, not the full finite-field/finite-extension/category/fibre/cohomology convention bundle. In particular the latter uses derived global sections and general coefficient categories; it does not itself give this item's full finite-stage setup or identify its codomain with the finite-module point category. I therefore make no exact attachment claim and do not treat a sorry declaration of master as a completed proof.

## Wanted sources

None for the item. Although the source path is absent under the shared checkout's literature directory, I found and read the exact master blueprint file at `/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-admissible/def-trf-coefficient-conventions.md`. The node's source path remains its canonical literature-relative path.

## Corrections and source comparison

The original was already a definition bundle, not a theorem needing proof steps. All nine seeded statement dependencies are genuinely used. I made each a citation in the statement, bound the implicitly used symbol `s` as `Spec k`, and named the domain of `K` and the integer index `i` in the displayed definition. The source already uses these objects in this sense: this is an explicit reading of the source, not a mathematical change. The finite-stage categories, all field/ring/scheme hypotheses, and both displayed formulas are preserved. No STATEMENT-DISPUTED issue was found.

The complete source statement is realized by the item's definition dependencies. There is no relocation of a clause into a new node and no proof route is replaced. I read the containing chapter and unit records and the three-level rules in SETUP.md. The unit is the distinct admissibility datum, has no proof steps, and this node is explicitly marked recorded in advance from the trace-formula chapter.

## Blueprint and duplicate search

I ran `tools/blueprint_refs.py ancestor def-trf-coefficient-conventions`, and searched the whole blueprint for `trace formula coefficient conventions`, `coefficient`, `coefficient conventions`, and `finite-coefficient categories`, together with DAG searches for `Fib_s`, the title and the finite-torsion coefficient-category phrase. The existing component nodes are reused. `def-pur-conventions` additionally includes twists, exceptional inverse image and all four stages; `def-weil-ordinary-compact-cohomology` includes ordinary and compact cohomology at all stages but does not state this whole geometric-fibre/site/finite-Tor convention bundle. Neither is an alternate statement of this item, so `same_as` is `[]`. Since the item is itself a blueprint node, `from` correctly remains null.

## Not duplicates

No new nodes are proposed, so there are no new/existing tag pairs requiring a distinction.

## Review by Q28

I read the exact master blueprint statement named above and compared it clause by clause with the sandbox item. I opened and read the complete statement of every cited node, rather than relying on its title or proof. There are no numbered proof steps: for this definition the following clause-by-clause review is the substantive citation check, and the empty proof and citations.json are intentional.

The datum clause uses `def-weil-finite-field-fiber`, whose statement explicitly fixes p prime, a at least 1, q = p^a, the field k_0 of q elements, its algebraic closure k, the coefficient fields and the quotient A_{E,n}. It also defines geometric base change and a_X as the projection to Spec k. `def-weil-scheme-morphism-properties` explicitly collects the finite-type and separated predicates, with their underlying defining nodes named. Thus the scheme and coefficient hypotheses are those of the source; smoothness, properness and admissibility have not entered.

The site clause uses `def-weil-pbc-proetale-site`, whose statement specifies the small site, its universe convention, the constant coefficient sheaf A_X, the module-sheaf category and its derived category. `def-weil-finite-torsion-constructibility` defines D^b_c using bounded constructible cohomology, including finite stalks on a finite stratification. `def-weil-finite-tor-amplitude` defines D^b_ctf as the full subcategory with one finite interval bounding cohomology of tensor products with every degree-zero A-module sheaf. I checked that these remain separate conditions at A = O_E/(varpi_E^n); in particular no claim says all bounded constructible objects have finite Tor amplitude.

The operations clause uses the finite-level paragraph of `def-weil-derived-pullback-tensor-hom`, which defines precisely the derived pullback, derived tensor and internal Hom on the ambient constant-coefficient pro-etale categories. It does not supply arbitrary preservation assertions on D^b_c, and the sandbox adds none. The schemes here have characteristic p and ell differs from p, as required by that paragraph. `def-weil-derived-cohomology-sheaves` gives H^r as the kernel/image quotient for a representing complex, on this same site. I checked that its sheaf-valued cohomology is not confused with the module-valued H^i after taking compact-support cohomology.

For the displayed formulas I read `def-weil-ordinary-compact-cohomology`: its statement explicitly contains both `RGammac(Y,K)=Fib_s(Ra_{Y!}K)` and `H_c^i(Y,K)=H^i(RGammac(Y,K))`, at the finite stage and the very same geometric-point category. This directly provides the convention, without inferring a theorem from a bare definition of Rf_!. `def-weil-finite-coefficient-point` constructs the exact functor Fib_s from D^b_c(s,A) to D^b_fin(A), using evaluation at the algebraically closed point, and explicitly reserves its equivalence assertion for a separate lemma. The sandbox uses its construction only, and asserts no equivalence or new finiteness/preservation theorem. I also read the existing `def-weil-coefficient-cohomology-modules` statement to check the distinction; no new node for this notion is needed because the cited ordinary/compact cohomology statement already gives the exact formula and its module-valued interpretation.

I tested the conventions on the empty geometric fibre, the point X = Spec k, the zero complex, shifts and n = 1. The expressions remain defined, and none of these tests forces properness or smoothness. For n > 1 over a nonfield quotient A, the distinction between bounded constructibility and finite Tor amplitude remains essential and is preserved. I did not introduce an assertion that tensor or internal Hom of arbitrary bounded constructible objects stays bounded.

Against delivery-errors B1-B10: there are no new statements or sketches to review, all objects and citations are explicit, the TeX is singly escaped mathematically in the JSON strings, no artificial Stacks source is assigned to an original blueprint convention, and no Mathlib leaf is claimed without an exact declaration. All seven recorded Mathlib queries really ran with msearch.py. I read the relevant returned t-structure, sheaf-cohomology, pro-etale and ell-adic definitions: generic ambient boundedness and ordinary Ext-valued cohomology are not this bundle, and completed integral ell-adic coefficients are not the finite constant coefficients A. LeanSearch's HTTP 500 is recorded as unavailable. The blueprint and source-declaration checks are described above.

Against C1-C8: no non-elementary theorem is smuggled into a proof step, and every statement citation has the content described above. There is no use of a cited node's hidden proof, no new edge that could close a cycle, and no cross-unit proof tool or replacement unit route. Against D1-D5: nothing is relabelled into a child node, and the definition has no omitted mathematical proof to move elsewhere. Against E1-E7: the finite coefficient ring, site, geometric base and domains match across the cited statements; no Frobenius or coefficient-category identification is silently made; the edge cases above reveal no false assertion, and no source error required a correction.

## Unfinished work

None in this one-level definition split. Its existing dependencies retain their own states. No Lean file, compiler, Lake command, live repository file or launcher tool was modified.

## Earlier second reading (a previous round; superseded)

I reread the source blueprint node `def-trf-coefficient-conventions` in `literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-admissible/def-trf-coefficient-conventions.md`: every finite-field, coefficient-ring, scheme, site, category, operation, and compact-support clause agrees with the sandbox statement; the explicit bindings of `s`, `K`, and `i` only make the displayed formulas self-contained. There are no proof steps to audit because this node is a definition.

The definition dependencies were opened and checked by their statements: `def-weil-finite-field-fiber` supplies the global fields and geometric base change; `def-weil-scheme-morphism-properties` supplies separated finite type; `def-weil-pbc-proetale-site` supplies the site and module derived category; `def-weil-finite-torsion-constructibility` and `def-weil-finite-tor-amplitude` supply the two distinct finite-level subcategories; `def-weil-derived-pullback-tensor-hom` supplies the ambient derived operations; `def-weil-derived-cohomology-sheaves` supplies cohomology sheaves; `def-weil-ordinary-compact-cohomology` supplies `Fib_s(Ra_{X!}K)` and `H^i`; and `def-weil-finite-coefficient-point` supplies the point fibre functor and finite coefficient target. Each cited statement says the notion used, with no hidden proof dependence or extra hypothesis.

I tested the conventions on the empty scheme, `X = Spec k`, the zero complex, shifts, and `n = 1`; all expressions remain defined. For `n > 1`, bounded constructibility and finite Tor amplitude remain separate as required by the cited definitions. No new node was proposed, so B1–B7, duplicate-node checks, and Mathlib-leaf checks apply vacuously; the recorded searches remain the worker's actual LeanFinder, Loogle, grep, and unavailable LeanSearch runs.

Changes made in this second reading: appended this source-and-dependency audit and made no mathematical or node-file changes, since no discrepancy was found.

## Return repair: rebase after landing refusal

The return entry reported only `NOT MERGED` because `coord/.merge.lock` was held by another delivery; it identified no mathematical or preflight defect. I nevertheless treated this as a repair rather than an unchanged resend. Before rerunning delivery I re-read the current shared-DAG records for all nine statement dependencies and compared their statements with the definition above: `def-weil-derived-cohomology-sheaves` (Mathlib), `def-weil-derived-pullback-tensor-hom`, `def-weil-finite-coefficient-point`, `def-weil-finite-field-fiber`, `def-weil-finite-tor-amplitude`, `def-weil-finite-torsion-constructibility`, `def-weil-ordinary-compact-cohomology`, `def-weil-pbc-proetale-site`, and `def-weil-scheme-morphism-properties`. Their current records still state exactly the operations, coefficient categories, finite-field datum, geometric fibre, and scheme hypotheses used by this definition; no citation or statement adjustment is required. The delivery command is being rerun so its temporary worktree overlays the split onto the current DAG before preflight. No live repository or merge lock was touched.


## Second reading by Q28

I independently read delivery-errors B–E, GOAL.md, coord/dag-sync.md, the stage-1 definition rule, the containing chapter/unit source, and the exact blueprint source `literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-admissible/def-trf-coefficient-conventions.md` (node/order 1511). This source is an original convention, not a Stacks-tagged theorem; assigning it a Stacks tag would be inaccurate.

- Item datum clause: checked against the source's first paragraph and the complete current statements of `def-weil-finite-field-fiber` and `def-weil-scheme-morphism-properties`; PASS. The former fixes prime p, a >= 1, the finite field and algebraic closure, geometric base change and the coefficient quotient; the latter supplies separated finite type. The explicit s = Spec k preserves the source's meaning.
- Item site/category clause: checked against the source's second paragraph and `def-weil-pbc-proetale-site`, `def-weil-finite-torsion-constructibility`, `def-weil-finite-tor-amplitude`; PASS. These respectively supply the constant-ring module derived category, bounded constructible objects, and the additional uniform finite interval for tensoring with every degree-zero module sheaf. No finite-Tor property is inferred from constructibility.
- Item operations clause: checked against `def-weil-derived-pullback-tensor-hom` (finite-level paragraph) and `def-weil-derived-cohomology-sheaves`; PASS. The operations are ambient derived operations; no closure assertion on arbitrary bounded constructible tensor products or internal Homs is added. Their invertibility hypothesis holds because the geometric schemes have characteristic p and ell != p.
- Item compact-support formula: checked against the source's two displayed equalities and `def-weil-ordinary-compact-cohomology`; PASS. That cited statement gives the formulas for every K in the same bounded constructible finite-coefficient category and includes the module-valued interpretation of H^i. There is no appeal to an unstated identification of a sheaf with a coefficient complex.
- Item point-category clause: checked against item 1 of `def-weil-finite-coefficient-point`; PASS. Its stated functor has precisely domain D^b_c(s,A) and codomain D^b_fin(A). The item uses the functor, without asserting its separately stated equivalence theorem.
- Proof steps: none; PASS under stages/1-dag.md section 3(2). This definition is split by naming its existing defining notions. Both proof-dependency lists are empty, and citations.json = [] correctly records that there are no proof-step citations.
- New nodes: none; PASS. There is no elementary lemma, duplicate, source clause relabelled as a child, or unsearched proposed leaf to remove. No new Mathlib leaves are claimed.

Small cases checked: the empty X and zero K give well-defined zero coefficient complexes; X_0 = Spec k_0 gives s as its geometric fibre; n = 1 gives residue-field coefficients, while n > 1 retains the separate finite-Tor condition. The source excludes n = 0, so no zero-level coefficient convention has been added. Shifts and negative i remain covered by integer-indexed derived cohomology. These checks found no statement dispute or missing properness/smoothness hypothesis.

I independently searched the two read-only source trees for this node id and the component declarations, and read slopmaster2 TorAmplitude.lean:168–197, TraceFormula/Defs.lean:185–206 and Derived/LowerShriek.lean:224–248. The finite-Tor full subcategory and the generic composite Rf_! followed by derived global sections are component constructions, not an exact declaration of this entire convention bundle with its finite-module point codomain. No exact closed attachment is warranted, and no master sorry is treated as a finished proof.

Changes in this reading: appended the required exact second-reading section, replacing neither the worker's Review by Q28 nor its earlier history. Kept the node statement, its nine dependencies, its empty proof and citations.json unchanged because the independent source-and-domain check found them correct. The first attempted delivery command included a sandbox argument unsupported by deliver.py; corrected to its documented two-positional-argument invocation. The final dry run and push use that invocation and the tool's temporary worktree only.
