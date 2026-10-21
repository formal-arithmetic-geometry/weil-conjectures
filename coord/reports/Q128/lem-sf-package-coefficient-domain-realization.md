# Stage-1 report: lem-sf-package-coefficient-domain-realization

## Files written

- `dag/nodes/sec-six-functors/lem-sf-package-coefficient-domain-realization.json`: statement, now split into ten short proof steps. Statement unchanged. Mathlib verdict: no match for the complete coefficient-domain and common-stage package.
- `citations.json`: sixteen step/node entries with verbatim quotations from the current cited statements.
- `report.md`: this report. `searches.jsonl` records the five real search-command invocations. `write_split.py` is a sandbox-only authoring helper, not a DAG delivery file.

There are zero new nodes and zero new Mathlib leaves. The sandbox had no previous item, report, split, or searches to recover. Existing non-worker fields, including the source, blueprint ancestry, and creation record, were retained. The statement dependencies now explicitly name completion, rationalization, common-stage coefficients, Tor amplitude, and dimension in addition to the operation datum and site-perfectness. Proof dependencies are exactly the union of step uses.

## Attachments

None. I searched the project `lean/WeilConjectures/` for the exact blueprint tag, coefficient-domain terminology, six-operation package names, and common-stage/exactness terminology. The finite-coefficient `AlgebraicGeometry.Etale.sixOperationsPackage` is only part of this item's assertion; its finite-coefficient statement does not supply this integral/rational/common-stage package. The pro-etale bounded-constructible module-object source explicitly lists sorried preservation inputs, and the common-stage triangulation instances alone do not prove the other clauses. None is an exact attachment of the whole item. No compiler, Lake command, or Lean-writing operation was run.

## WANTED

None. The sources used are present locally.

## Problems found and corrections

The unsplit item itself has a correct statement against the current blueprint. Its proof and proof dependencies were empty. I supplied the assembly, using existing nodes rather than making a new node for each clause. In particular, the finite comparison for arbitrary constructible finite-Tor first arguments comes from `thm-coef-finite-hom`, not from the site-perfect-only elementary comparison in `lem-fix-operation-reduction`.

The latter's coefficient-passage clauses are sufficient for field identification, but its mere mention of operations is not integral preservation. Step 5 therefore separately cites the three existing completed-operation preservation results. Its compact-support citation applies to the actual inverse system, including its quotient and restriction-of-scalars transitions. The proof never claims that an arbitrary bounded tower is effective just because its terms are constructible.

No statement dispute or change of the unit/chapter route was needed. The item is not the unit key theorem; no unit realization fields were changed.

## What remains unfinished

Nothing in this one-level split. The existing dependencies retain their own proof obligations. This delivery is stage 1 only.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs to distinguish. I searched the entire DAG by the source-named ids and coefficient/Hom/common-stage concepts, and used the existing results. `tools/blueprint_refs.py ancestor` gives `prop-functor-package`. Blueprint searches for `coefficient-domain` and `common-stage realization` found no imported node stating the entire item; the `descent-functors` search located the existing descent proposition and its applications. The parent `prop-functor-package` is strictly broader, with seven clauses; it cannot be cited to prove its own realization child. The existing stability theorem supplies finite preservation and the site-perfect qualification, but does not subsume the general exact-functor descent assertion of this item.

## Mathlib searches

All searches were run through the required `batch2/msearch.py Q128 lem-sf-package-coefficient-domain-realization` command; exact query strings and actual results are in the node and `searches.jsonl`. I ran LeanFinder with two distinct phrasings, Loogle for `CategoryTheory.Functor.IsTriangulated`, grep for constructible/rational/Tor and adic scalar terminology, and LeanSearch for the whole coefficient-passage package. All five services/commands returned successfully; none is described as unavailable or recorded without an invocation.

I read every returned hit's signature/output. LeanSearch found underived sheaf pullback/pushforward adjunctions and condensed locally constant functors. Loogle found the triangulated-functor interface and transport lemmas, which assume the categories and exactness data. LeanFinder found condensed categorical structures, internal projectivity, ordinary finite-dimensional internal Hom, and unrelated exact sequences. The grep hits concern adic algebra, constructible subsets, and faithfully-flat module descent. I opened the Mathlib triangulated-functor source, condensed AB source, and ModuleCat descent source; none supplies constructible derived preservation, these evaluation-defined coefficient comparisons, or the full common-stage package. Thus the item is not a Mathlib leaf, although its generic categorical ingredients may have their own leaves lower in the existing DAG.

## Review by Q128

I read the standing stage-1 brief, the complete B–E delivery-error checklists (including the merged checklist), the worker and stage documents, GOAL, the three blueprint levels in SETUP, and the item's chapter/unit records. I read the current `main-20261015` parent statement and proof, not only the historical master source path in the node. The parent proof expressly names the finite Hom, coefficient-change, integral Hom, rational operation, exact scalar-extension, descent, and idempotent-complete triangulation results used here. I also read their current blueprint statement files, the current stability proof, and the rational-operations proof. For the integral operation background I read Bhatt–Scholze, local PDF pp. 49–57: 6.5.5, 6.5.9, 6.5.11, 6.7.2, 6.7.6–6.7.7, and 6.7.13. These supply background; every non-elementary assertion in the item is still cited as a DAG statement. No prohibited SGA source is used. There are no new-node sources to certify.

I opened and read the statement of every cited node. In detail:

1. `thm-sf-ctf-stability` (i)–(iv) really states the four finite-stage restrictions, including nonproper ordinary direct image. The field is the fixed algebraic closure of the finite field, the coefficient exponent is prime to its characteristic, and both scheme and morphism separated/finite-type hypotheses are supplied by the item.
2. `cor-weil-finite-constructible-hom` says preservation for both general finite-Tor inputs and gives exactly `[c-b-2d,e-a+2d]`. It is a theorem on either finite site, so its pro-etale version is available without a change of category. The nonnegative integer bound also permits the empty scheme.
3. `thm-coef-finite-hom` says the comparison is an isomorphism and identifies it as the unique transpose of changed evaluation. Its quotient ring map and inequalities match `n >= m >= 1`. This is stronger than merely knowing the two Hom objects are isomorphic.
4. The stability theorem's clause (ii) separately says the sharper bound and tensor-dual formula for a site-perfect first input. It does not identify arbitrary constructible finite-Tor inputs with site-perfect ones. The item retains exactly this extra hypothesis.
5. `lem-pur-integral-operations-preserve-constructible` gives completed pullback/tensor membership and their reductions. `lem-sf-integral-direct-image-constructible` gives ordinary pushforward membership with a reduction interval independent of n. `lem-sf-integral-compact-support-constructible` gives membership of the actual compact-support tower's derived limit, including completeness and uniformly bounded constructible reductions. The latter requires a compactification of a separated finite-type morphism, already used by the operation datum. These statements allow our field and all the stated morphisms. I do not take their proofs as extra interfaces or infer a preservation theorem from a definition node.
6. `lem-coef-integral-residue-tor` gives uniform Tor intervals from residue cohomology and explicitly warns that this does not mean site-perfectness. `cor-coef-integral-internal-hom` states membership of the ambient integral Hom for arbitrary integral constructible inputs and the canonical evaluation-defined reduction isomorphism for every n. This covers the item's specified integral category with its single cohomological interval.
7. The two coefficient definition nodes identify rational objects and common-stage representatives with exactly the item's categories. `lem-fix-operation-reduction` expressly says the same operations/comparisons commute with rationalization and common-stage scalar extension and preserve evaluation. `lem-coef-rational-operations` expressly identifies rational internal Hom and preserves evaluation, also under finite scalar extension. Therefore the already-preserved integral outputs yield field outputs with the specified operation, including the Hom identification. This step does not appeal to its source proof's completion-adjunction argument as if that argument were another theorem statement.
8. `lem-weil-scalar-extension-exact-triangulated` has precisely the finite field-extension functor in question, including shift and distinguished-triangle preservation. The scheme may be arbitrary, so our finite-type schemes meet its hypotheses.
9. `prop-weil-pbc-descent-functors` has exactly the supplied coherent scalar comparisons and exact-functor hypotheses. I wrote out its representative formula, with beta inverse at the target, and used its explicit final assertion for compatible transformations and their equations. This does not claim descent for incoherent or merely objectwise functors.
10. `thm-weil-pbc-idempotent-complete-triangulation` states the required ordinary triangulation, idempotent completeness, and exactness of every finite-stage embedding on the common-stage category itself. No new Karoubi completion is inserted.

I checked the zero objects, identity morphisms, n=m, and identity field extension E=F: the cited comparisons specialize with their stated unit equations and do not need strict inequalities. At a point (d=0) the general Hom bound reduces to the expected difference interval. On a positive-dimensional scheme the closed point in the affine line is the stability statement's example showing why the dimension-free bound needs site-perfectness; the split does not accidentally assert that stronger bound for it. Empty schemes and zero complexes do not require a negative dimension bound. I checked the order of the three factors in the descended morphism formula against the proposition's displayed arrow. Equations of transformations are taken from the proposition's statement, not deduced by an unproved faithfulness assertion about stage embeddings.

Against B–E: no new nodes, hollow data, relabelled clauses, or hidden statement-only proof sketches were introduced; the item is a complete assembly of independently existing results. Each of the sixteen step citations has its verbatim evidence in `citations.json`. Every step is marked non-elementary because it invokes a theorem, and every substantive claim is in one of the cited statements. The longest step is 964 characters, so none exceeds the long-step threshold or conceals an extracted lemma. Generic uses from other units are declared with individual reasons in `split_report.tool_uses`; they follow the existing package route. I traversed dependencies before writing to ensure none of the major cited results reaches the item or its package parent. The required server dry run below is the authoritative global cycle and preflight check. I did not edit the repository or any launcher script.

## Validation and delivery

The required server preflight is run with `deliver.py --no-push`; its result and the subsequent delivery commit are reported by the command output. No local DAG/preflight checker, Lean compiler, or build tool is used.
