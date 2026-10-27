# Stage-1 report: lem-sf-open-general-field-uniform-bound

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-open-general-field-uniform-bound.json`: existing statement, now split in seven steps; no Mathlib match for the entire statement.
- `citations.json`: verbatim statement quotations for every node citation in every step.
- `searches.jsonl`: actual msearch records, retained with the results incorporated in the node.
- `report.md`: this report.

There are 0 new nodes and 0 new Mathlib leaves. The original statement, source, blueprint ancestry, creation record and previous Mathlib searches are retained. Additional actual searches are appended. No repository files, Lean files, launcher files, or unit/chapter records were written.

## Attachments

None. I searched the live WeilConjectures source for the item tag, open direct-image vanishing, the field cohomological bound, and the related coefficient comparison. The stronger module higher-image bound in `WeilConjectures/SixFunctors/Etale/Derived/DirectImageAmplitude.lean`, `AlgebraicGeometry.Etale.isZero_rightDerived_lowerStar_of_two_mul_lt`, covers the module vanishing clause alone. It does not state the item's neighbourhood cohomology assertion for every torsion coefficient sheaf and its canonical coefficient-forgetting comparison, so it is not an attachment of this whole item. Related declarations were not treated as finished proofs merely because their bodies assemble other results.

## WANTED

None. All sources used are available in the read-only repository.

## Findings and changes

The item was unsplit and had no earlier sandbox attempt, report or search log. The blueprint's general-field paragraph says that the algebraically closed argument applies verbatim. This needed expansion: establish finite type and the dimension bound on the actual test scheme W=V times_X U, apply the stated general-field bound to W, sheafify on the affine etale tests, and then use the genuine module/abelian derived comparison. A coefficient-forgetting functor need not preserve injective objects; the proof never uses that assertion.

The statement is unchanged and is not disputed. In particular, no algebraic-closedness, constructibility, properness, flatness of the coefficient ring over Z, or bounded exponent beyond the given ring annihilator was added. The ring may be zero, and the open may be empty. The current blueprint's localization unit and its detailed finite-stage general-field paragraph remain the route. Generic statements from other units are declared individually in `split_report.tool_uses`; no unit proof is replaced.

The DAG and blueprint already contain every needed ingredient. Searches included the whole DAG by local dimension, etale base change, cohomological dimension, sheafification and module/abelian comparison, and `blueprint_refs.py` queries for cohomological dimension, affine etale, dimension etale, module abelian, general-field and this exact id. There is no equal blueprint statement for the entire item; its `same_as` remains empty. Reusing the existing nodes avoids creating elementary, duplicate or clause-restatement nodes.

Mathlib was searched through msearch with LeanFinder (two different phrasings), Loogle, LeanSearch and grep. The hits concerned etale loci, formally unramified maps, scheme section restriction, the small etale topology and generic derived-category vanishing. They do not state this item. Each appended query is exactly the corresponding logged query, with the actual returned names and a no-match verdict. Earlier search records remain intact as required.

## What remains unfinished

Nothing in this stage-1 split. Proofs or Lean statements of existing dependency nodes are outside this item's scope. The maintainer independently reviews the delivered split.

## Not duplicates

No new nodes were created. Existing nodes are cited rather than restated.

## Review by NH

I read the full current source `prop-sf-localization-all-stages.proof.md`, especially “(1') at the finite stage,” and the current finite-type torsion-cd proof under `sec-six-functors-basics/sk-prop-pe-unbounded-classical`. These explicitly use the ordinary 2d+c bound on the etale site. I also read the chapter/unit records, the three blueprint levels in SETUP, and delivery-errors B through E. No SGA source is used in this split.

Step 1 uses the exact small-etale covering definition and the abelian sheaf equalizer definition, not a general statement about stalks. On the empty scheme the empty covering gives zero sections, so the whole coefficient category and its derived functors are zero. The scalar identity ell^r m=(ell^r 1)m=0 verifies the local-section torsion definition of `def-weil-pbc-etale-sheaves`. The zero ring and r=0 cause no exception.

For step 2 I read Morphisms 01T1, 01T6, and the etale and finite-presentation definitions, together with Properties 01OW/01OZ. `lem-weil-pbc-finite-type-over-noetherian` really supplies Noetherianity for a finite-type morphism to Spec k; a field is Noetherian by its two ideals. `lem-weil-pbc-noetherian-open-subscheme-noetherian` really supplies quasi-compactness of every open of that Noetherian scheme. The remaining finite-type arguments are written as finite affine covers and explicit finite algebra generators, including f inverse for a principal open. They do not assume that an arbitrary open of an arbitrary quasi-compact scheme is quasi-compact. I checked the open/fibre-product identification from `def-weil-open-immersion` and the universal property of `def-pc-fibre-product`.

For step 3 I read Stacks Morphisms 02GO, More Algebra 07QP and Properties 04MU, and opened all three cited node statements. Etale base change applies to V->X along U->X with no extra hypotheses. The local-dimension statement applies to the actual prime of an affine chart and its inverse-image prime. The scheme dimension node states the supremum of local ring dimensions, including the empty supremum. Thus dim W <= dim U follows by taking suprema; no density, surjectivity, equidimensionality or geometric-irreducibility assumption is used.

For step 4 I checked the full statement of `thm-sc-finite-type-torsion-cd`, not its proof internals: it is for every finite-type scheme over the field with the given torsion-cd bound. Step 2 proves finite type of W and step 3 proves its dimension bound. Applying it with e=dim W and then 2e+c <= 2d+c yields precisely the degree range. `def-sc-etale-torsion-cd` explicitly quantifies over arbitrary torsion abelian sheaves, so no constructibility restriction is silently imposed. Empty W is removed before assigning it a nonnegative dimension e.

For step 5 I read Stacks Etale Cohomology 03Q8 and Sites 00WK, and the affine-etale covering statements in Topologies 021B/04HR. `sbc-lem-higher-direct-image-presheaf` gives the sheafification on the fibre product, with the restricted coefficient sheaf, exactly as used. `lem-weil-pbc-affine-etale-essentially-small-cover` says every object has an affine covering. `lem-weil-pbc-site-sheafification-sections-local` says every sheafification section locally has presheaf representatives. Its universe convention can be met by choosing a universe containing the small-site data. Refining the representing objects by affine covers makes each representative zero by step 4, after which the sheaf equalizer axiom forces the original section to vanish. This is an argument about sheafification, not the incorrect claim that evaluation of a higher-image sheaf is always the fibre-product cohomology group.

For step 6 I read Sites Cohomology 0D6J(3) and the full statement of `lem-weil-pbc-module-abelian-derived-direct-image-comparison`. That node explicitly states that the fixed canonical transformation is an isomorphism for every scheme morphism and that the forgetting functor is exact. It applies to M[0] over A, independently of properness or flatness. Taking cohomology therefore gives the exact underlying-abelian higher-image comparison this step requires. A zero underlying abelian sheaf implies a zero module sheaf objectwise. The proof does not substitute a mere definition of coefficients or an unproved assertion about preservation of injectives.

Step 7 is only the quantifier check: the bound is 2d+c throughout, whereas A and its exponent were used only for the annihilator calculation. It therefore applies simultaneously to all the indicated coefficient quotients. For edge cases I checked U empty, V empty, W empty even when U is nonempty, a point as U (d=0), disconnected and nonreduced opens, and A=0. The point case permits base-field cohomology up to c and makes no false assertion that all its positive cohomology vanishes.

I checked that every substantive input above is an existing cited statement, every such statement was opened, all uses are in proof_deps, and quotations are copied literally from the statements. No new node duplicates a clause, no proof is moved to a new restatement, and no step exceeds 2000 characters. The longest geometry step retains only the written finite-cover/generator argument plus the two existing Noetherian results, with no hidden comparison lemma. The preliminary server review_split passed; the final full dry run is required before pushing.
