## Worker report

Item: lem-sf-locally-free-sheaf-evaluation-biduality. Group Q61. Stage 1 only.

### Files written

- `dag/nodes/sec-six-functors/lem-sf-locally-free-sheaf-evaluation-biduality.json`: unchanged statement; five proof steps; status split; recorded current searches in addition to the inherited searches.
- `citations.json`: one entry for every node cited by every proof step, with verbatim statement excerpts.
- `report.md`: this report and the author's source review.

### New nodes

None. No new Mathlib leaves. The elementary coordinate calculations stay in the item's proof. The only non-elementary globalization input already exists as the Mathlib leaf `lem-sfb-sheaf-cover-local-isomorphism`.

### Attachments

No complete attachment. I searched `lean/WeilConjectures/` by the exact blueprint id, bidual/reflexive terminology, and the adjacent internal-Hom files. The exact tag has no hit. `SheafOfModules.bidual`, `SheafOfModules.bidual_naturality`, `SheafOfModules.bidual_app_bijective_of_iso_free`, and `SheafOfModules.isIso_bidual` in `WeilConjectures/Algebra/Category/ModuleCat/Sheaf/Bidual.lean:77,83,101,140` give evaluation, naturality, and the isomorphism assertion. `SheafOfModules.IsFiniteLocallyFree.homObj_unit` in `Sheaf/InternalHomFree.lean:80` gives locally finite-free duals. Their statements do not give the specified dual-basis coordinate map and inverse formula on every slice. The explicit sum occurs inside the proof of `PresheafOfModules.bidual_app_bijective` rather than as a declaration stating the inverse formula. These are useful partial coverage, not an ATTACH claim. No Lean audit closure is asserted.

### WANTED

None. The sources used are in the read clone.

### Findings and changes

The original node was statement-only and unsplit, with no prior sandbox item or report to resume. The statement is correct and is preserved verbatim. The proof now expands the ordinary finite-free computation instead of introducing a node for a clause of the conclusion. It identifies successive restrictions explicitly, constructs evaluation on local functionals, proves naturality, writes the dual-coordinate inverse, verifies both compositions, and then invokes the existing covering-sieve isomorphism criterion on abelian sheaves. Linearity of the resulting global inverse is checked by injectivity of the forward linear map.

The statement assumes a family of objects covering the terminal sheaf by sieves, not fibre products or a single global final object. I therefore did not use `lem-pur-sheaf-hom-cover-gluing` or `lem-pe-set-sheaf-cover-descent`: their statements assume fibre products. Nor did I use `lem-weil-pbc-ringed-internal-hom-exact-restriction`, which concerns derived Hom. The ordinary restriction identity is a direct substitution in the two existing definitions, just as Stacks 0E8H says it is immediate from the definition.

The computed blueprint ancestor is null, as it already was in the live node, because the created-item chain ends at a maintainer-created parent with `created.item=null`. The existing via chain and this explanation are preserved; `from.place` and `split_report.blueprint` now identify the exact first/last sentences of `lem-sf-hom-finite-projective.proof.md` being expanded. Blueprint searches for `bidual`, `internal hom`, `finite free`, and `cover local isomorphism` found no imported node stating this full ordinary, arbitrary-ringed-site, formula-level assertion. No chapter or unit route was changed.

### Mathlib searches

All current Mathlib queries were run through the mandated `msearch.py Q61 lem-sf-locally-free-sheaf-evaluation-biduality ...` command, with their original results retained in `searches.jsonl`. The node appends those exact tool/query records without changing the inherited Q54 records. Two LeanFinder phrasings returned free-sheaf mapping formulas and local generators, not internal-Hom biduality. LeanSearch returned ordinary module reflexivity and evaluation results. I read `Mathlib/LinearAlgebra/Dual/Lemmas.lean:255-267` and `Dual/Defs.lean:230-248`: these concern duals of modules over one ring, not sheaves of slice morphisms with cover descent. I also read the free-sheaf and generator contexts of the returned sheaf hits. Grep in `Algebra/Category/ModuleCat` found no bidual/reflexivity/internal-Hom-over declarations; a second grep in its `Sheaf` directory returned evaluation-functor documentation and preservation of limits. The two Loogle requests rejected unindexed identifiers; the verdicts explicitly record that failure as unavailable and do not count it as evidence of absence.

### Unfinished work

None in this stage-1 split. No Lean was written or compiled. Formalizing the five steps belongs to later stages.

## Not duplicates

No new-node pairs: no nodes were created. The existing ordinary sheaf-Hom definition, localized-ringed-site definition, module-sheaf definition, and covering-sieve criterion are reused directly. The broader derived-Hom node is not cited for an ordinary-Hom theorem. The fibre-product gluing nodes are not cited under missing fibre-product hypotheses.

## Review by Q61

I read the full statement and the proof of `lem-sf-hom-finite-projective` in the current `main-20261015` blueprint: its first sentence identifies finite-free evaluation with the identity and its last sentence invokes locality and restriction. I checked the item's source against Stacks `sites-modules.tex`, Section 04TT, the displayed slice-Hom rule and scalar action, Tag 03EM (`lemma-internal-hom`), and Tag 0E8H (`lemma-internal-hom-restriction`). I read Stacks `sites.tex`, Tag 04TQ (`lemma-glue-maps`), and the statement and proof of the exact covering-sieve generalization in `Mathlib/CategoryTheory/Sites/LocalProperties.lean:27-70`. There are no new-node sources to review. I read the item's chapter and unit records, the three levels of SETUP, and delivery-errors B through E. Only the local finite-free branch below the unit is being expanded; no SGA source is used.

For step 1 I opened `def-pur-sheaf-hom` and `def-pur-localized-ringed-site`. The former defines Hom sections as morphisms on slices and restriction as restriction of morphisms; the latter explicitly states relocalization and sectionwise identity of successive restrictions. These statements, rather than their proofs, identify the two Hom modules over every object and their maps. Applying the same identity twice gives the bidual restriction identity. This step is elementary, with its identifications written out; no arbitrary inverse-image/internal-Hom interchange is claimed.

For step 2 I checked those Hom sections really are maps on the entire localized category: evaluation at x is described on every V over U, not only on a single section module. The equation for W over V is precisely the naturality condition required for an element of the slice Hom. `def-pur-sheaf-hom` already states that this presheaf is a module sheaf, and `def-weil-sheaf-of-modules-category` states exactly that morphisms are natural abelian-sheaf maps with linear components. Both cited statements supply what is used. Evaluating both naturality composites at an arbitrary local functional gives the same expression, including when N is not locally free. Nothing in this step uses the cover assumption.

For step 3 I checked the chosen sheaf trivialization gives an actual basis at every V over U_i: finite tuples of R-sections give the finite direct sum, with coordinatewise gluing and the finite injections/projections. Both the forward coordinate map and its inverse on every further W over V are stated. Naturality of a local functional forces the coefficients to be restrictions of its values at the chosen basis; linearity forces the displayed finite sum. Conversely that sum defines a natural linear functional. These are elementary consequences of the three cited definitions and the given trivialization, not an uncited theorem that arbitrary sections of a locally free sheaf are globally free.

For step 4 I verified both compositions. The equality with eta is checked against every functional on every W over V, which is necessary for equality in the internal Hom. Interchanging the two scalar factors uses exactly the given commutativity of R(W). The other composition is the coordinate expansion of x. The sum is compatible with restriction because the coefficient maps of eta, R, and M are natural. The cited Hom and module-sheaf definitions supply these properties. No tensor-Hom comparison or derived argument is hidden here.

For step 5 I read the whole statement of `lem-sfb-sheaf-cover-local-isomorphism`. Its condition on arrows W to V whose domain maps to some covering object is word for word the item's covering condition. It permits arbitrary coefficient category, so applying it to the underlying abelian sheaves is legitimate. The cited module-sheaf definition supplies the underlying abelian sheaf and linear forward map. The separate one-line injectivity argument proves the inverse is R(V)-linear, so no unproved claim that forgetting modules reflects all isomorphisms is needed. Uniqueness of a two-sided inverse proves the global inverse restricts to the already constructed formula and that all choices of basis give the same inverse. This is the only non-elementary step; its non-elementary input is the existing Mathlib leaf, not a new clause-shaped node. Since it is already a Mathlib leaf it is available as a tool without a route exception.

I checked the edge cases: rank zero has only zero linear functionals and the inverse is the empty sum; rank one is scalar evaluation; the zero coefficient ring causes no exception; different ranks on different slices do not enter the same finite sum; an empty covering family can satisfy the hypothesis only when every object has an empty covering sieve, in which case the underlying sheaves have singleton section sets and the existing covering criterion still applies; the empty site is also harmless. No site points, fibre products, quasi-compactness, field hypothesis, uniform bound on ranks, or global free retract was added. Each proof step is shorter than 2000 characters. The citation excerpts were checked against the actual statements, and every cited node was opened. The statement was not weakened or otherwise corrected, and no statement dispute is necessary.

Corrections during this reading: I rejected the tempting fibre-product gluing citation because its hypotheses exceed the item, and used the already existing sieve criterion instead. I also rejected a module-reflexivity Mathlib leaf for the item because the comparison with slice Hom and descent would still need proof. No other content correction was needed.
