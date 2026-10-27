## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-etale-shriek-transfer-retract.json`: statement, split into six steps; Mathlib verdict no match. The statement and its eight statement dependencies are unchanged. No new nodes and no new Mathlib leaves.
- `citations.json`: ten verbatim statement quotations, one for each step-node citation.
- `report.md`: this report. `searches.jsonl` is the search command's own log.

## Attachments

None for this item. Searching its exact id/docstring tag in `lean/WeilConjectures/` found no declaration. Searching finite-etale trace and compact-support composition found the existing coefficient-linear trace, the abstract compact-support composition interfaces and the curve-assertions retraction. The latter assumes a retraction and imposes curve and finite locally constant prime-coefficient hypotheses, so it does not state this item. `AlgebraicGeometry.Etale.exists_finiteEtaleModuleTrace_degree` already belongs to `lem-weil-pbc-finite-etale-module-trace-degree`; I cite that existing node rather than duplicating it. The bounded-below compact-support composition node covers the needed comparison but not the trace retraction.

## WANTED

None. All mathematical sources used are present under `literature/stacks-project/`.

## Problems found and corrected

The item was unsplit and supplied no proof. No statement dispute was found. The important distinction is between invertibility of the integer degree on the primary sheaf and invertibility in the coefficient ring: the latter is unnecessary. Step 2 supplies integers a,b with ad+b ell^n=1 and uses only ell^n F=0. I also made the coefficient lift of finite direct-image exactness explicit, instead of applying an abelian-sheaf theorem directly to module sheaves. I initially expressed that lift using the module-category kernel/cokernel definition, then replaced it with the existing stronger node explicitly stating faithful exact coefficient forgetting. Thus the proof cites a theorem for the precise fact it uses.

The existing abelian trace-degree node assumes connectedness and has abelian coefficients. It is not the right input. The coefficient-linear trace-degree node states exactly the constant geometric-fibre version needed here, with arbitrary coefficient ring and arbitrary module sheaf. The comparison uses the identity compactification of the proper finite map, rather than assuming an unspecified equality between underived and derived compact-support functors. The existing composition theorem explicitly permits three independently chosen compactifications, so it gives the comparison for the choices in the item.

## Unfinished work

None for this one-level stage-1 split. No Lean has been written or compiled. Existing cited nodes retain their own proof and audit states; this delivery makes no claim to have completed their remaining Lean proofs.

## Not duplicates

No new nodes were created. Whole-DAG searches by ids, finite-etale trace, finite direct-image exactness, compact-support composition, and tags 03QP and 0GKY found the reusable inputs. Blueprint searches using `tools/blueprint_refs.py` for finite etale trace, trace splitting, finite direct image exact, and shriek composition found no blueprint node stating the whole item. The locally-constant-reduction blueprint node gives an ordinary sheaf splitting in a narrower setting and no derived compact-support comparison. `blueprint.same_as` remains empty. The ancestor command returns `thm-weil-pbc-direct-image-finiteness-proper`, as already recorded by the item. I read the current main-20261015 ancestor: this subordinate trace argument serves its classical constructibility input and leaves the proper-base-change unit route intact.

## Review by Q153

I read Stacks `more-etale.tex`, Tag 0GKY (`lemma-loc-constant-shriek-rel-dim-1`), including its trace-splitting paragraph and the displayed compact-support comparison; `etale-cohomology.tex`, Section 03SH (`section-trace-method`), Definition 03SE (`definition-trace-map`) and the multiplication-by-degree formula; Proposition 03QP (`proposition-finite-higher-direct-image-zero`); `more-etale.tex`, Tag 0F7J (`lemma-shriek-composition`); `derived.tex`, Tag 015F (`lemma-right-derived-exact-functor`); and `sites-modules.tex`, Tag 03DA (`lemma-abelian`). These are the sources for the item and all its inputs; there are no new-node sources to audit. The proof uses Stacks directly throughout.

Step 1 uses the opened statement of `lem-weil-pbc-finite-etale-module-trace-degree`: its conclusion supplies a coefficient-linear t with t eta = d id, and its hypothesis is constant geometric-fibre cardinality. Our finite-etale g and arbitrary Lambda-module F satisfy exactly those hypotheses. In particular I do not take connectedness from the older abelian node. Step 2 is the explicit elementary Bezout calculation and introduces no hidden lemma: all its integer scalars act on the sheaf, and ell^n annihilates its identity.

Step 3 uses the opened statements of `lemma-weil-pbc-finite-direct-image-exact` (abelian exactness), `lem-weil-pbc-module-sheaves-colimits-forgetful` (faithful exact forgetting), and `lem-weil-pbc-module-direct-image-left-exact` (commutation of module pushforward with forgetting). The short-complex homology argument explains reflection of exactness and hence proves the module version in a few lines from those inputs. It never claims the abelian exactness node itself states the module theorem. These facts apply on the small etale sites with their usual size convention and do not require a Noetherian scheme or finite-rank sheaf.

Step 4 uses the opened finite-proper statement, the properness definition in the scheme conventions, the identity compactification explicitly allowed in the compactification definition, the presheaf/sheafification definition of open extension by zero for the identity, and the exact-derived theorem's final clause saying every complex computes RF. All functors are on the same constant-Lambda module-sheaf categories; E[0] is bounded below and step 3 supplies the exactness hypothesis. The identity extension-by-zero identification is written out. The result beta is an isomorphism of derived objects, not just a collection of cohomology isomorphisms.

Step 5 uses the opened statement of `lem-weil-pbc-etale-shriek-qcqs-composition`. T,X,Y are qcqs by assumption; h is separated of finite type by assumption; g has those properties by step 4; Lambda is finite by assumption; and the three compactifications are exactly the choices that theorem permits. The displayed formula alpha = C_E composed with Rh_!(beta) checks its direction and its source H[0]. Step 6 uses only functoriality, the inverse of alpha, and step 2. I wrote both u and v and cancelled alpha^{-1} alpha explicitly, so the specified unit formula and the exact identity v u = id are both established.

I checked the small cases F=0, the zero coefficient ring, d=1, n=1, empty base, and a disconnected base/cover. They cause no problem. For a concrete nonunit degree take Lambda=Z/6, ell=2, n=1, F the constant module with additive group Z/2 and a split three-sheet cover: d=3 is not a unit in Lambda, but ad=1 modulo 2 and the trace normalization works. If the excluded condition ell does divide d is allowed, the normalized equation fails already for a nonzero constant Z/ell sheaf, which confirms the role of that hypothesis.

Against delivery-errors B--E: there are no new nodes to be elementary, duplicate, a restated item clause, ill-sourced, or misclassified as Mathlib. The six steps carry the actual proof and reuse existing nodes. Every non-elementary input has a node citation, and `citations.json` copies the relevant statement text verbatim rather than borrowing a node's proof. The two elementary calculations and the short exactness transfer are written out. No step exceeds 2000 characters (the maximum is below 1000). No target statement or definition is weakened, no extra invertibility or local constancy hypothesis is introduced, and no unit step is replaced. The generic off-unit finite-direct-image and module-forgetting tools are used solely for their stated interfaces; requested tool uses are declared in `split_report` where needed.

The item was searched with the prescribed msearch command using LeanFinder (two phrasings), Loogle, source grep and LeanSearch. Hits concerned ring traces, free module-sheaf pullback or ordinary pushforward composition; none gives the compact-support trace retraction. Existing searches were retained, and this attempt's actual logged searches were added without inventing a search or treating an unavailable service as an empty result.
