# Stage 1 report: def-sc-intersection-number

## Files written

- `dag/nodes/sec-abelian-varieties/def-sc-intersection-number.json`: definition, split; no Mathlib match.
- `citations.json`: empty, because the item has no proof steps.

## Attachments

None. No corresponding sorry-free declaration was found in either Lean source checkout.

## WANTED

None.

## What was checked

The item was checked against `literature/stacks-project/varieties.tex`, Definition Tag 0BEP (`definition-intersection-number`), as identified by the imported source metadata. The statement matches the source's convention: for a proper scheme of dimension `g` and an ample invertible module, the top self-intersection is the coefficient of the squarefree monomial `n_1 ... n_g` in the Euler-characteristic polynomial evaluated at the sum of the variables. The field, properness, invertibility, and ampleness prerequisites are exactly the existing definition nodes listed in `stmt_deps`.

There are no proof steps for a definition, so no cited statements or hypotheses needed step-level verification and `citations.json` is empty. I searched the whole DAG and found no duplicate definition node. The blueprint ancestor is `lem-sc-mult-n-finite-flat`; its Tag 0BEV proof refers to this intersection-number convention, while the definition itself is sourced from Tag 0BEP.

I ran the required searches through `msearch.py`: LeanFinder for the coefficient/Euler-characteristic formulation and a Hilbert-polynomial formulation, Loogle for intersection-number and Hilbert-polynomial names, grep over `Mathlib/AlgebraicGeometry` for intersection-number/coefficient and HilbertPolynomial/hilbertPoly, and LeanSearch for the multivariate top-self-intersection formulation. The search results contain only unrelated polynomial or incidence-algebra declarations; LeanSearch was unavailable. No Mathlib match exists.

## Review by F1

I read the imported node, its chapter, the `sk-prop-av-isogeny` unit, and the blueprint/source references. I verified that this item is only a definition and therefore requires no new lemma nodes or proof dependencies. I checked each prerequisite against the existing DAG ids (`def-weil-field`, `def-weil-proper-morphism`, `def-sc-invertible-module`, and `def-sc-ample`) and confirmed that none is being restated. I also checked both Lean source checkouts for the item id and for intersection-number declaration names; neither contains a matching declaration. The only correction made was changing the node status from `unsplit` to `split` and adding the required split report; the mathematical statement and dependencies were already consistent with Tag 0BEP.

## What could not be finished

Nothing.

## Second reading by F1

- Item statement: checked line by line against Stacks Project Varieties, Definition Tag 0BEP (`definition-intersection-number`), including the arbitrary closed subscheme `Z`, its dimension `d`, the tuple of invertible modules, the coefficient of the displayed numerical polynomial, the projection-formula equality, and the equal-module notation; the original ample top-self-intersection statement was incorrect and has been repaired.
- New nodes: none; the split contains only the definition item, so B1-B7 and duplicate-node checks have no subordinate node to inspect.
- Proof steps: none, as required for a definition; `citations.json` remains empty.
- Edge cases: `d=0` gives the constant coefficient, `Z=X` gives the usual self-intersection notation, and the empty closed subscheme is permitted by the general closed-immersion formulation.
- Existing definitions: `def-weil-field`, `def-weil-proper-morphism`, `def-weil-closed-immersion`, `def-kun-topological-krull-dimension`, and `def-sc-invertible-module` were checked to supply exactly the notions cited in the repaired statement; no ampleness hypothesis is needed by Tag 0BEP.
- Mathlib/Lean audit: the recorded searches found no Mathlib intersection-number declaration, and neither Lean checkout contains a matching declaration.

### Changes made

- Replaced the narrowed ample top self-intersection formulation with the full Tag 0BEP definition for arbitrary closed subschemes and tuples of invertible modules.
- Added the existing closed-immersion and Krull-dimension definition dependencies and removed the erroneous ampleness dependency.
