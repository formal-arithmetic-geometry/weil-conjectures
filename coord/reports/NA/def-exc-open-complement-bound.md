## Files written

- `dag/nodes/sec-smooth-purity/def-exc-open-complement-bound.json`: definition, status `split`, seven existing defining dependencies; no Mathlib match. Rechecked and completed the earlier sandbox version.
- `citations.json`: `[]`. A definition has no proof steps.
- `searches.jsonl`: retained the earlier actual search log and appended the fresh prescribed msearch queries. The node records the seven fresh searches exactly, including the unavailable service.

There are zero new nodes and zero Mathlib leaves. No unit record changes: this definition is not the key statement of `sk-prop-a1-kummer`.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and `Comparator/` for the exact id/tag and for open-complement/cohomological-dimension terminology, and read the candidate declarations. `AlgebraicGeometry.ProEtale.HasUniformCohomologicalDimensionLE` (`SixFunctors/ProEtale/ExceptionalAdjoint.lean:125`) is a pro-etale, base-change-uniform dimension bound and contains no constructibility clause. `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion_of_lowerStar` (`SixFunctors/Etale/Derived/Stability/ClosedImmersion.lean:115`) is a conditional exceptional-inverse-image theorem assuming a bound on a particular object. `AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt` (`AlgebraicGeometry/Sites/CohomologicalDimension.lean:43`) is a different torsion-cohomology theorem and contains `sorry`. None is this combined predicate. No upstream master sorry declaration is treated as a finished proof.

## WANTED

None. The actual blueprint source is available read-only at `/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/def-exc-open-complement-bound.md`, order 1914. I read it in full. The node retains its canonical relative literature path. Nothing was downloaded.

## What was wrong and what changed

The imported node is a definition of a condition, not an assertion that it holds for every open immersion. Its dependencies mixed defining notions with downstream applications. The split now names schemes, open immersions, quasi-compactness, small etale sites, module sheaves, higher direct images, and constructible sheaves. `def-weil-finite-type-morphism` is used only for its explicit quasi-compactness clause; no finite-type hypothesis is imposed.

Both defining clauses retain their full quantifiers. Vanishing is for EVERY module sheaf and every degree strictly above the specified nonnegative bound. Constructibility is for every constructible input sheaf in every degree. The coefficient ring and immersion are explicit parameters of the predicate. The current direct-image dependency defines integer-indexed higher images, so the all-integer formulation includes negative degrees legitimately.

The source's final paragraph explains that `lem-exc-closed-amplitude` and `prop-exc-closed-tor` use these conditions and mentions independently known curve/chart cases. I read both statements: they assume the two properties for their closed-support computations, rather than supply any notion required to define the properties. That application commentary is recorded here and these downstream nodes are removed from `stmt_deps`. No unconditional finiteness assertion is proved or introduced.

The chapter and unit records are unchanged. The defining paragraph supports the open-complement hypotheses used within the unit; no step of the unit's affine-line/Kummer route is replaced.

## Statement corrected

STATEMENT-DISPUTED: the source says only “finite ring”, but its cited coefficient interfaces require a commutative ring. `def-weil-pbc-etale-sheaves` and the module-sheaf paragraph of `def-weil-pbc-direct-image` assume a commutative ring; `def-weil-pbc-constructible-complexes` starts with a finite commutative ring. A finite ring alone does not meet these hypotheses: in M_2(F_2), E_12 E_21=E_11 whereas E_21 E_12=E_22. This is an explicit domain/type mismatch with the cited definitions, not a claim that higher direct images cannot be studied over noncommutative rings.

The faithful repair makes “commutative” explicit. The intended finite coefficient stages A=O_E/varpi_E^n in the purity conventions and the unit are commutative. The directly related theorem `thm-pur-open-complement-unconditional` already assumes commutativity. The chart applications `thm-pur-general-admissibility` and `thm-sf-preservation-class` use those commutative stages. `lem-exc-open-complement-known` retains the source's abbreviated “finite ring” wording and has the same convention issue to clarify in its own split; it is not edited here. This correction adds no geometric assumption and changes neither defining property. No target statement is edited.

## Mathlib and blueprint searches

All fresh Mathlib searches were run through `/home/ubuntu/weil-launcher-nt/msearch.py NA def-exc-open-complement-bound`. The node copies the actual tool/query strings from the log. Two LeanFinder phrasings were read: their hits concern vanishing on injective objects, derived-category t-structures, condensed/sheaf category axioms, exact sheafification, or Ext. These do not define this predicate. I additionally opened `Mathlib/CategoryTheory/Abelian/RightDerived.lean:153`: its higher-derived vanishing is restricted to an INJECTIVE input, not all sheaves above a fixed bound. `CategoryTheory/Abelian/GrothendieckAxioms/Sheaf.lean:77` concerns the ambient category, not constructible preservation. Loogle with “cohomologicalDimension” returned no hits; the broader “cohomological” query returned twelve spectral-sequence results. Both prescribed grep queries returned no hits. LeanSearch returned Internal Server Error and is recorded as `unavailable`, never as evidence of absence.

Whole-DAG and blueprint searches used `tools/blueprint_refs.py search open-complement`, `tools/blueprint_refs.py search 'cohomological-dimension condition'`, and DAG text searches. The other matches either assert that the present predicate holds under additional hypotheses, concern ideals defining open complements, or define a pro-etale full-dimension/admissibility condition. I opened the candidate definition statements: the pro-etale conditions use a different site, additional base-change/proper-map data, and do not define the present constructibility conjunction. Thus `same_as=[]`. This item is itself imported, so `blueprint.from=null` is correct.

## Not duplicates

No new nodes. Both conjuncts stay within this definition. No elementary observation, restatement of a clause, or duplicate Mathlib fact becomes a child node.

## What could not be finished

Nothing remains in this one-level definition split. This is stage 1: no Lean file, compiler, Lake command, or global build is involved. The required `deliver.py --no-push` preflight is run after this report. The independent second reader is responsible for delivery.

## Review by NA

I read the complete blueprint definition (order 1914), the chapter `sec-smooth-purity`, the full unit `sk-prop-a1-kummer`, and the statements of all seven defining dependencies. For the item the source is the blueprint's defining paragraph; it makes no theorem-level assertion requiring an external finiteness proof. There are no new nodes needing separate sources. I also checked the Stacks tag mappings and source text for schemes (01IJ, `definition-scheme`), open immersions (01HE/01IO, `definition-immersion-locally-ringed-spaces`/`definition-immersion`) and quasi-compact morphisms (01K3, `definition-quasi-compact` and the following affine-open criterion) in the launcher's read-only literature.

For the reference audit underlying C4/B3: `def-pc-scheme` provides the schemes and morphisms; `def-weil-open-immersion` provides identification with an open subscheme; `def-weil-finite-type-morphism` explicitly supplies the inverse-image-of-affine-opens quasi-compactness criterion. `def-weil-pbc-etale-site` supplies SMALL etale sites; `def-weil-pbc-etale-sheaves` supplies constant-ring module categories. The MODULE-SHEAF paragraph of `def-weil-pbc-direct-image` supplies precisely R^q j_* for those coefficients, with integer degrees. The SHEAF clause of `def-weil-pbc-constructible-complexes` supplies finite stratifications with lisse restrictions; the complex clause is not imposed on the quantified input sheaves. Its underlying constructible-sheaf definition was also read. No equivalence with a different affine-local constructibility convention is asserted on arbitrary schemes.

For C1-C4/D1-D5 there is no proof step to hide a fact or carry an unsupported citation: this is the definition case of stages/1-dag.md section 3(2), so `proof=[]`, `proof_deps=[]`, and `citations.json=[]` are appropriate. The two quantified conditions are the predicate's actual data, not unproved claims moved into new children. No tag is substituted for an argument establishing those conditions. No off-unit theorem tool or replacement unit route is used (C7-C8).

I checked B1-B10 and C5-C6 against the files: no new node, no unsupported attachment or Mathlib leaf, valid single-escaped TeX, complete parameter introduction, exact source/provenance, and genuine logged searches. The dependencies are existing definition nodes. Downstream application edges were removed rather than retained as circular defining dependencies; the delivery preflight checks the resulting graph. No chapter, unit, import flag, or maintainer audit metadata is changed.

For E1-E7 I checked hypotheses and objects clause by clause against the source and actual cited statements. I repaired the finite-ring/commutative-ring mismatch explicitly above; no Noetherian, finite-type, finite-dimensional, invertibility, or base-field assumption is added. The vanishing clause is not narrowed to constructible inputs, and the preservation clause is not broadened to arbitrary inputs. The sites remain etale throughout. Small cases: for j=id the exact identity functor gives zero positive higher images and preserves constructible sheaves; for empty V all images are zero. With the zero coefficient ring all module sheaves are zero. Bounds c=0 and c=1 begin the vanishing obligations at q=1 and q=2 respectively, with constructibility still in every degree. A general pair may fail the predicate; its definition asserts no universal validity. These checks reveal no further correction.

I replaced the earlier repetitive handoff report, including historical second-reading sections, with this current worker audit. The earlier stage-2 fix-loader return was a stage mismatch: this remains a stage-1 node/report delivery, explicitly marked `delivery_stage: 1`, with no stage-2 report alias or Lean records. A fresh independent second reading is still required. All worker changes are confined to this sandbox.

## Second reading by NA

Independent reading on 2026-10-16, against delivery-errors B–E, the actual blueprint definition (order 1914), its chapter and unit, and the current dependency statements. The item is a definition under stage 1 section 3(2); it has no theorem to prove.

- Parameter paragraph: checked against the blueprint's finite coefficient ring, quasi-compact open immersion and nonnegative bound; PASS. The existing STATEMENT-DISPUTED repair is justified: the module-sheaf and constructibility interfaces explicitly require commutativity, and the matrix-ring example demonstrates the omitted hypothesis. The intended coefficient stages are commutative.
- Clause 1: checked against the displayed blueprint vanishing and its following quantifier; PASS. It ranges over all module sheaves, not just constructible ones, and only degrees strictly greater than c.
- Clause 2: checked against the blueprint's second conjunct and the sheaf clause of def-weil-pbc-constructible-complexes; PASS. Every constructible input and every degree remain quantified, with the coefficient ring fixed.
- Proof steps: none; PASS. Empty proof, proof_deps and citations.json are correct for this definition. Neither conjunct asserts unconditional vanishing or finiteness, so no theorem is concealed here.
- New nodes: none; PASS. No restatement, elementary lemma, duplicate or unsupported Mathlib leaf has been introduced.
- def-pc-scheme: read its statement and Stacks 01IJ, schemes.tex, definition-scheme; PASS for schemes V and T.
- def-weil-open-immersion: read its statement and Stacks 01HE/01IO, schemes.tex, definition-immersion-locally-ringed-spaces/definition-immersion; PASS for the specified j.
- def-weil-finite-type-morphism: read its explicit quasi-compactness clause and Stacks 01K3, schemes.tex, definition-quasi-compact, with lemma-quasi-compact-affine; PASS. Only this clause is used; finite type is not imposed.
- def-weil-pbc-etale-site: read its statement; PASS for both small etale sites.
- def-weil-pbc-etale-sheaves: read its constant commutative-ring module-category clause; PASS for the categories quantified over.
- def-weil-pbc-direct-image: read its full statement, especially the module-sheaf paragraph and R^q definition for q in Z; PASS for all higher images used here.
- def-weil-pbc-constructible-complexes: read its statement, underlying constructible-sheaf node and actual blueprint source; PASS. The source uses a global finite partition. Stacks 03RU/03RW (etale-cohomology.tex, definition-finite-locally-constant/definition-constructible) was also opened: its affine-local convention is not substituted for this global definition on arbitrary schemes.
- Source application paragraph: read lem-exc-closed-amplitude and prop-exc-closed-tor; PASS for retaining their commentary only in the report, without downstream defining edges.
- Small cases: zero module sheaf, zero coefficient ring, empty V, empty T, and j=id on Spec(k) or any scheme give zero positive higher images and preserve constructible inputs; PASS. At c=0 the first obligation starts at q=1, and at c=1 at q=2. Negative degrees are legitimate under the cited definition and add no positive-degree vanishing assertion.
- Duplicate and attachment check: independently searched the whole blueprint for open-complement, read def-kun-cd, def-weil-full-cohomological-dimension, def-weil-exceptional-adjoint-admissibility and the open-complement theorem statements, and searched both source checkouts by id and dimension terminology; PASS. Cohomological dimension alone omits constructible preservation, the ambient predicates use different data/sites, and the theorem nodes assert instances of this condition. The pro-etale HasUniformCohomologicalDimensionLE and conditional etale closed-immersion theorem were opened and are not exact attachments. No upstream sorry is counted as a proof.

Changes: appended this independent audit, preserving all worker sections including Review by NA; ran a fresh LeanFinder query using finite stratifications and sheaf pushforward, and a fresh Mathlib/CategoryTheory grep, and added their actual results to mathlib_searches. The eight semantic hits concern coherent sheaf composition or condensed locally constant functors, not this predicate; the grep returned no hits. Both searches are in searches.jsonl. No further statement, dependency, source, proof or citation repair was needed. No Lean, compiler, Lake or build tool was used. Delivery verification follows below.

Verification: the required `deliver.py NA def-exc-open-complement-bound --no-push` printed `OK (not pushed)` and `preflight passed` on 2026-10-16. Zero new nodes and zero Mathlib leaves. The final delivery command runs the preflight again before pushing.
