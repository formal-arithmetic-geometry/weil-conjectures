# Stage-1 worker report: def-sf-uniform-direct-image-vanishing

## Files written

- `dag/nodes/sec-smooth-purity/def-sf-uniform-direct-image-vanishing.json`: definition, split with existing statement dependencies; no exact Mathlib match.
- `citations.json`: `[]`, since the item is a definition and has no proof steps.
- `report.md` and the search tool's `searches.jsonl` are the sandbox evidence.

New nodes: 0. New Mathlib leaves: 0. No unit file is changed: this definition is not the key statement of `sk-prop-sf-fullcd-etale-origin`.

## Attachments

None. Searched both read-only source trees under `WeilConjectures/` by the blueprint id, UDV, uniform direct-image vanishing, and cohomological-dimension predicate names. `AlgebraicGeometry.ProEtale.HasUniformCohomologicalDimensionLE` in `WeilConjectures/SixFunctors/ProEtale/ExceptionalAdjoint.lean:125` is a genuinely different predicate: it quantifies over every pro-étale sheaf and all base changes along pro-étale objects. It is not an attachment for an étale predicate without base changes. The nearby quasi-coherent uniform-vanishing theorem in `AlgebraicGeometry/Cohomology/Projective.lean:67` concerns Zariski quasi-coherent modules, not étale constant-coefficient module sheaves. The curve cohomological-dimension results concern global cohomology, not this predicate. No exact project declaration was found, so there is no attachment candidate whose sorry map needs testing.

## Wanted source

WANTED: `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-fullcd-etale-origin/def-sf-uniform-direct-image-vanishing.md`, complete definition (order 1788), for def-sf-uniform-direct-image-vanishing.

The referenced blueprint directory is absent in the shared checkout. I read its imported statement in the item and its verbatim unit/chapter records, rather than claiming to have opened the absent original. The split is a definition dependency audit, with no proof reconstructed from unavailable literature. No download or write outside the sandbox was made.

## Changes and source issues

The imported predicate is sound. It left E implicit while writing A_{E,n}, did not put the existing definition citations at most of the notions, and cited finite-torsion *pro-étale constructibility* only to obtain its coefficient setup. I explicitly introduced the finite extension E, valuation ring and chosen uniformizer; replaced that dependency by `def-weil-l-adic-coefficient-extension` and `def-weil-finite-field-fiber`; replaced the general scheme-properties collection by `def-weil-finite-type-morphism` and `def-weil-proper-morphism` (only its separatedness definition). The other three dependencies remain the small étale site, the module version of derived direct image, and FIN for the final comparison. These edits expand the intended setup and do not add a hypothesis to the vanishing predicate. The finite ring's torsion consequence is written out via its positive characteristic c and cM=0; no separate lemma node is needed.

The cohomology index is now r, avoiding collision with the finite-field cardinality q. The same fixed N still bounds every module sheaf, with no constructibility restriction. The displayed definition explicitly uses the small-étale constant-ring module category and R^r f_* M = H^r(Rf_*(M[0])). The final paragraph distinguishes FIN's pro-étale constructible scope; it does not identify these coefficient categories or import FIN's constructibility clause. The original did not state existence of a bound, and neither does this version. There is no statement dispute.

## Searches and duplicates

The `msearch.py` log records every search, including two initially invalid grep scopes; their node entries explicitly say they are inconclusive and are not evidence of absence. I corrected them with an unscoped Mathlib grep and scoped reads/searches of the actual candidate files. The first two Loogle patterns included unknown identifiers and are likewise reported exactly. The valid `DerivedCategory.isLE_iff` Loogle query produced the generic lemma; I read `Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean:107` through its proof, and `CategoryTheory.Sheaf.H` at `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean:59`. The former bounds one derived object, and the latter defines global/sheaf cohomology by Ext. Neither defines the project predicate over all sheaves and the direct image of f. LeanFinder was tried with two phrasings; LeanSearch was unavailable (Internal Server Error), recorded as unavailable. No Mathlib leaf is asserted.

Whole-DAG/blueprint searches used `blueprint_refs.py search UDV`, `search vanishing`, `search uniform direct image vanishing`, and an `rg` search for UDV/uniform vanishing. The other two UDV blueprint hits are `lem-sf-etale-direct-image-vanishing` (a theorem giving the bound 2d, and citing this definition) and `thm-sf-direct-image-tor-amplitude` (a theorem assuming this predicate); neither is a duplicate definition. I read both statements. `def-finrepair-property-c` defines preservation of constructibility and explicitly omits a uniform bound; it is not a duplicate. Thus `blueprint.same_as` is `[]`. The item is itself imported, so `blueprint.from` must remain null, not an invented self-parent/place.

## Not duplicates

No new nodes. No duplicate-pair review is required.

## Review by Q23

I read the standing brief, all of delivery-errors B through E, the three-level route rules in SETUP, the stage-1 contract, GOAL and dag-sync. For the item, I read the imported definition, `dag/units/sk-prop-sf-fullcd-etale-origin.json`, `dag/chapters/sec-smooth-purity.json`, and every original and final statement dependency. The original external blueprint file is not locally available, as recorded above. There are no new nodes with separate source obligations and no proof steps: the content here is the definition of a predicate, not a theorem that higher direct images vanish. Consequently C1/C4 are checked at the level of the statement's ingredients, not replaced by fictitious proof steps; citations.json is empty for precisely that reason.

The seven final dependency statements supply exactly these ingredients:

1. `def-weil-finite-field-fiber` specifies p, a, q=p^a, k0 and its chosen algebraic closure k, and introduces the finite coefficient notation. I use no geometric-fibre or finite-subfield theorem from its later paragraphs.
2. `def-weil-l-adic-coefficient-extension` specifies E/Q_l, its valuation ring, uniformizer and quotient A_{E,n}; clause 4 explicitly states that the quotient is a finite local ring. Thus n>=1 and finiteness are in force before the elementary finite-characteristic argument. No constructibility notion is taken from this definition.
3. `def-weil-finite-type-morphism` defines both finite-type scheme morphisms and finite-type schemes over a field. It supplies exactly those hypotheses, not any quasi-separatedness theorem.
4. `def-weil-proper-morphism` begins by defining separatedness through the diagonal closed immersion. I take only that definition and impose no properness/universal-closedness assumption.
5. `def-weil-pbc-etale-site` defines the small étale sites X_Et and Y_Et. This is not the small pro-étale site.
6. `def-weil-pbc-direct-image` explicitly includes the constant-ring module-sheaf version, its bounded-below derived direct image and cohomology sheaves. A module sheaf in degree zero is bounded below, so that construction suffices for every M in this predicate. No module/underlying-abelian derived comparison is being claimed: the torsion sentence concerns M itself.
7. `def-weil-pbc-constructible-direct-image-finiteness` clause (2) supplies the final *analogy*: a specified fixed c for all constructible pro-étale sheaves. I do not apply FIN or infer its truth; the new text explicitly records the different sites and quantifiers.

For B1--B10, there are no new statement-only nodes, malformed TeX or unsupported Mathlib leaves; every datum is explicit and every search is in the log. For C1--C8, no uncited non-elementary inference is hidden in a proof, no proof of a dependency is used as its statement, and no off-unit proof tool or new cycle is introduced. For D1--D5, no clause is moved into a child node; the definition is simply the predicate formed from existing definitions. For E1--E7, I checked that the relevant finiteness, n>=1, l!=p, finite-type and separatedness hypotheses are introduced before use; the zero object is a sheaf on Y_Et and not on X_Et; and the two sites remain distinct. The finite-characteristic torsion observation uses no finiteness assumption on M.

Edge cases: N=0 asks for vanishing in every positive degree, and the boundary degree r=N is intentionally unconstrained. The zero module gives zero higher direct images; the empty source also gives zero, consistently with the universal predicate. For an identity morphism the positive-degree direct images vanish, so N=0 has its expected interpretation. No claim that these examples prove the general predicate is made. Modules are allowed to have infinite stalks: a common positive annihilator c still kills them because c*1_A=0. No assertion after arbitrary/pro-étale base change, no assertion of constructibility, and no assertion of existence of N has entered the definition.

## Unfinished work

None within this one-level definition split. The absent original blueprint is listed WANTED for the second reader; no new proof or node depends on it. Delivery is reserved for the second reader. The worker runs only `deliver.py ... --no-push` after this report is written.

## Second reading by Q23

- Item `def-sf-uniform-direct-image-vanishing`: checked the sandbox statement against the complete imported statement (blueprint order 1788), `sk-prop-sf-fullcd-etale-origin` and `sec-smooth-purity`; PASS. The finite-field datum, prime restriction, coefficient level, separated finite-type hypotheses, small étale sites, quantifier over all module sheaves and fixed nonnegative bound agree. Explicitly naming E and changing the degree letter to r preserve the predicate. The original blueprint file is absent, as are the Stacks .tex files advertised in the brief; this is verification against the imported source text, not a claim to have read unavailable files. No new source theorem or proof depends on them.
- Proof steps: none; checked `kind: definition`, `proof: []`, `proof_deps: []` against stage-1 §3(2); PASS. This defines a predicate, so no proof of existence of a bound is due. `citations.json` correctly remains `[]`.
- New nodes: none; checked the sandbox file inventory and original DAG; PASS. B1--B7 and the node-removal audit have no new-node instances.
- Ingredient `def-weil-finite-field-fiber`: read its statement, including the fixed p,a,q,k0,k and coefficient notation; PASS, only its global datum is used, without assuming descent of X or Y to a finite field.
- Ingredient `def-weil-l-adic-coefficient-extension`: read clauses 1--4, particularly the definition of the chosen uniformizer and finite quotient; PASS for every n>=1. Its stated finiteness is sufficient for the elementary torsion observation, even for infinitely generated M.
- Ingredient `def-weil-finite-type-morphism`: read its affine-cover definition and final structure-morphism convention; PASS for both the schemes and f.
- Ingredient `def-weil-proper-morphism`: read the separatedness clause; PASS, it supplies the diagonal definition actually used without adding properness.
- Ingredient `def-weil-pbc-etale-site`: read its objects, morphisms and covering families; PASS, both sites in the predicate are small étale sites.
- Ingredient `def-weil-pbc-direct-image`: read its entire statement, especially the final module-sheaf paragraph; PASS, the constant-ring module version and bounded-below derived image define the displayed R^r on M[0]. No comparison with derived images in abelian sheaves is assumed.
- Ingredient `def-weil-pbc-constructible-direct-image-finiteness`: read its hypotheses and clauses (1)--(2); PASS, the final paragraph is explicitly an analogy with its fixed-bound vanishing clause, not an application of FIN or an identification of the sites or sheaf quantifiers.
- Duplicate and attachment audit: independently searched the whole blueprint for `uniform` and `UDV`, the DAG for uniform vanishing/cohomological bounds, and both read-only Lean trees by the item id and cohomological-dimension vocabulary; PASS. The other two UDV blueprint hits are a theorem concluding it and a theorem assuming it. `def-finrepair-property-c` imposes constructibility alone. Read `ProEtale/ExceptionalAdjoint.lean:105-131`: `HasUniformCohomologicalDimensionLE` quantifies over all pro-étale sheaves and pro-étale base changes, so it is not this definition. The étale direct-image stability declarations are theorems about bounded constructible complexes, not UDV, and their displayed sorry bodies were not treated as proofs.
- Independent Mathlib audit: ran msearch.py LeanFinder with a left-exact-functor phrasing, Loogle with `"cohomological"` and `"rightDerived", "isZero"`, and grep for cohomological dimension/bounds and right-derived zero results; PASS, no exact match. Read `Functor.isZero_rightDerived_obj_injective_succ` at `Mathlib/CategoryTheory/Abelian/RightDerived.lean:153-158`: vanishing only on injectives cannot replace UDV. Also independently read `DerivedCategory.isLE_iff` at `Algebra/Homology/DerivedCategory/TStructure.lean:107-122` and `Sheaf.H` at `CategoryTheory/Sites/SheafCohomology/Basic.lean:59-60`; neither defines UDV. Searches are preserved as produced in searches.jsonl and recorded in the item's mathlib_searches.
- Small cases and scope: PASS for M=0, empty X, and the identity of Spec k (the identity direct image is exact). N=0 constrains every positive degree, N=1 constrains r>=2, and r=N is not constrained. n=1 gives the finite residue-field coefficient ring; n=0 is outside the source's domain and remains excluded. For torsion, two equal elements in the finite list of multiples of 1_A yield a positive c with c1_A=0, hence cm=(c1_A)m=0 locally for every section m. No finite-generation condition on M, base-change condition, or assertion of existence of N was introduced.

Changes: corrected the two invalid Loogle-query verdicts from `no match` to `inconclusive: invalid query`; their unknown-identifier errors cannot support absence. Added the four independently executed search records and this second-reading evidence. The mathematical statement, dependencies, empty proof and citations were left as reviewed. No new nodes or Mathlib leaves were introduced.
