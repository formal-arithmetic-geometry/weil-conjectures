## Files written

- `dag/nodes/sec-six-functors/lem-coef-compact-support-reduction-adjoint.json`: item, statement; split into four steps, no Mathlib match for the whole geometric assertion. Statement and statement dependencies retained verbatim.
- `citations.json`: six verbatim statement quotations, covering every node cited by every proof step.
- `report.md`: this report. `searches.jsonl` was written by the required search command.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint id, compact-support reduction/adjoint terminology, and coefficient comparison names. No declaration there states every clause of this item. The ordinary-etale `compactSupportCoefficientChangeIso` only concerns the scalar-restricted projection map, and does not state the specified B-linear pro-etale adjoint equation for beta. It is not an attachment. The existing Sheaf theorem `AlgebraicGeometry.Scheme.finiteCompactSupportScalarComparison` is used through its existing node, not reported as a newly discovered finished upstream declaration.

## WANTED

None.

## Corrections and source comparison

No statement dispute or correction. The input statement has an empty proof; the missing work is the explicit calculation identifying the adjoint of the actual transition. Its invertibility clause already has an existing owner: `lem-finite-compact-support-scalar-comparison`. I found that node by a whole-DAG statement search and by `tools/blueprint_refs.py search 'coefficient comparison'`. The blueprint search also returned the more restrictive `lem-fix-compact-support-coefficient-change`; that theorem assumes finite Tor amplitude and the global finite-field setting, so I did not apply it to this item.

The item's source is `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-coef-integral-compact-support.proof.md`, paragraph 2. I read it and the live ancestor's statement and proof. The source says the coefficient maps make the compact-support outputs a normalized tower and that the comparisons are the specified ones. Here the four steps realize precisely the finite-level identification used in that paragraph. They introduce neither an effectivity argument nor a new tower construction. I also read the chapter and unit records, SETUP's three levels and tool-lemma rule, GOAL, the worker/stage-1 instructions, and delivery-errors B through E (including the merged copy).

The proof source for the geometric invertibility tool is the existing node and its stated bounded-domain interface; I read that node in full and the public statement and proof explanation in `lean/Sheaf/Paper/FiniteCompactSupportScalarComparison.lean`. I checked the underlying literature in `literature/stacks-project/more-etale.tex`: Tag 0GL5 is `lemma-projection-formula-Rf-lower-shriek`, and Tag 0GL6 is `remark-Rf-lower-shriek-change-of-rings`. These are ordinary derived coefficient changes, not completed coefficient systems. Their pro-etale bounded-constructible transport is precisely what the already existing scalar-comparison node supplies. No uncited comparison between module objects, module-valued sheaves, and intrinsic constant-ring modules is needed in this split.

## Not duplicates

No new nodes. In particular, I reuse `lem-finite-compact-support-scalar-comparison` rather than create a new invertibility lemma, and keep the adjoint/naturality argument inside the item rather than make a node restating its main clause. The exact-id project search has no completed attachment. `blueprint_refs.py search 'reduction adjoint'` found no equivalent blueprint statement. The inherited blueprint ancestor and its precise paragraph-2 place are retained, and `same_as` is empty.

## Mathlib searches

Ran the required `msearch.py` command for LeanFinder, Loogle, grep and LeanSearch, then a second LeanFinder phrasing and a focused grep for the adjunction formulas. Every query and returned summary was copied from the resulting `searches.jsonl` to the item's `mathlib_searches`; inherited records were retained. All services responded. LeanFinder returned ordinary module scalar-adjunction formulas and unrelated finite-support results; the second phrasing returned ordinary module change of rings, scheme module restriction adjunctions, and condensed Hom formulas. LeanSearch returned analytic compact-support results and generic derived-category interfaces. The geometric grep found no match. Loogle found `CategoryTheory.Adjunction.homEquiv` and its unit/naturality formulas. I read `Mathlib/CategoryTheory/Adjunction/Basic.lean`, especially the unit formula and lines 238--246: these justify generic formal manipulations, but do not establish invertibility of the compact-support coefficient comparison. Hence the item is not a Mathlib leaf.

## Review by Q124

I checked every proof citation against the cited node's statement, rather than its proof, and wrote exact quotations in `citations.json`.

Step 1 uses only `def-weil-finite-torsion-constructibility`: boundedness means finitely many nonzero cohomology sheaves, and constructibility is a finite stratification with locally constant finite stalks. Applying cohomology to beta identifies each cohomology sheaf of the actual reduction with that of W; the same support and stratifications witness the needed property. This is an elementary invariance argument, not an extra theorem about the existence of etale origin. The finite-stratification definition is used as a property of the coefficient complex on X; no global finite-field hypothesis is inferred from that definition's introductory conventions.

Step 2 uses `lem-finite-compact-support-scalar-comparison` exactly as stated, with its upper level renamed m and lower level renamed n. Its ground field K0 is our arbitrary k, so there is no algebraic-closure or positive-characteristic hypothesis to add. Both levels are positive; the quotient direction is m to n; the given f is separated and finite type, X and Y are finite type over k, and c is the very same fixed compactification. V satisfies the intrinsic bounded-constructibility assumption, and Step 1 supplies the assumption for its actual ordinary derived reduction. The theorem explicitly specifies the scalar-adjunction transpose of compact support of the scalar unit followed by sfCompactSupportRestriction. `def-coef-compact-support-tensor-comparison` explicitly defines gamma by that same universal-arrow formula, with the same proper/open restriction comparison. Uniqueness in that definition identifies the arrows, so the cited invertibility applies to the named gamma itself. I did not substitute an arbitrary isomorphism or assume quotient flatness, finite projective dimension, or finite Tor amplitude.

Step 3 uses the definition node only for its displayed unit characterization and `lem-sf-compact-support-restriction-of-scalars` only for its naturality in the B-linear argument. I checked the naturality square at beta: its two paths are Res_Y(F_n beta) after sigma_(L_X V) and sigma_W after F_m(Res_X beta). Substituting that equality and the gamma unit equation gives the full chain of four equalities written in the item, ending in sigma_W F_m(rho), which is the actual tau from the statement. All arrows have source F_m V and target Res_Y F_n W after adjoining the scalar unit. This is a short functoriality calculation, not a hidden geometric normalization theorem.

Step 4 uses `lem-pur-sheaf-ring-derived-coefficient-adjunction`, whose statement supplies the natural Hom bijection for unbounded ring-sheaf derived categories, with the representative-normalized unit. The Hom map is a to Res(a) after eta; injectivity identifies the adjoint uniquely from Step 3. Functoriality directly gives the inverse F_n(beta^{-1}) to F_n(beta); no additional result about preservation of constructibility is used here. Combining with Step 2 proves the two invertibilities without claiming that rho or tau themselves are invertible.

I checked delivery-errors B1--B10: no new statement-only obligations, duplicate notions, unintroduced objects, spurious Mathlib leaf or missing blueprint provenance. For C1--C8, the sole geometric theorem is explicitly cited, all other arguments are written out from named definitions and naturality; the off-unit scalar-comparison and scalar-adjunction tools are declared in `split_report.tool_uses`. I checked the dependency closure of the reused comparison and found no path back to this item. For D1--D5, the argument remains in the item and no new node relabels a clause. For E1--E7, the field, coefficient category, quotient direction, actual reduction and specific comparison map match the cited hypotheses; no source error was found. Each step is under 2000 characters.

Edge cases: m=n gives the identity coefficient change and the same naturality calculation for any automorphism beta. For V=W=0 all maps are the unique zero-object arrows and hence the asserted isomorphisms. Empty schemes likewise cause no issue. For m>n the quotient can have infinite Tor dimension (e.g. Z/ell^2 to Z/ell); the argument uses only boundedness of this particular actual reduction, which follows from the supplied beta, and never deduces it for arbitrary complexes. An arbitrary field of characteristic zero with ell invertible is allowed by the reused theorem. Nothing requires X or Y to be separated over k beyond the stated separatedness of f.

## Unfinished work

None in this one-level split. Its cited existing statements keep their existing ownership and status. No Lean was written and no compiler, Lake, build or local DAG/preflight checker was run.
