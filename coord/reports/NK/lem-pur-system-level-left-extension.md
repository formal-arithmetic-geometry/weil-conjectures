# Stage-1 report: lem-pur-system-level-left-extension

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-system-level-left-extension.json` — the item, split into 13 proof steps.
- `dag/nodes/sec-smooth-purity/lem-pur-system-section-cone.json` — existing statement-only cone lemma copied into the delivery overlay; no new Mathlib leaf.
- `dag/nodes/sec-smooth-purity/lem-pur-system-section-suspension.json` — existing statement-only suspension lemma copied into the delivery overlay; no new Mathlib leaf.
- `citations.json` — verbatim statement quotes for every cited node in every proof step.

## Attachments

No Lean declaration attachment was found. The source checkout has no declaration tagged `(blueprint: lem-pur-system-level-left-extension)`, and no exact sorry-free declaration for this item.

## WANTED

None. The cited literature and blueprint sources are present in the repository.

## Review by NK

I read the item node, its chapter `sec-smooth-purity`, unit `sk-def-sf-operations`, the current `main-20261015` blueprint paragraph for `def-weil-exceptional-inverse-image`, and Zheng Construction 4.1 (printed p. 21). The item has no Lean declaration in `/home/ubuntu/weil-src-slopmaster2`; its `lean_audit` remains `none`. I retained the reviewed 13-step split already present in the shared DAG and copied the two reviewed supporting statements into the sandbox so every citation resolves locally.

For step 1 I checked that `lem-pur-ringed-site-grothendieck-abelian` states the Grothendieck property for modules on a small ringed site and that `lem-weil-pbc-module-sheaves-colimits-forgetful` states sectionwise kernels, cokernels, limits and colimits. These are exactly the facts used to identify strict systems with modules on the product ringed site and to evaluate abelian constructions componentwise. Step 2 cites the K-injective existence proposition, the K-injective Hom computation, and exact-functor derived factorization; their statements provide the resolution, derived Hom identification, and descent of componentwise exact evaluation used for coproducts and detection of isomorphisms and bounds.

Steps 3 and 4 use only the stated ringed-topoi tensor/restriction adjunction. I checked that its statement gives the natural Hom bijection needed for the singleton-level and subsequence left extensions, while the remaining tensor formulas and triangle identities are written out directly in those steps. Step 5 uses the flat model, tensor exactness for flat quotients, preservation of flat K-flat complexes under ringed pullback, the same module adjunction, and derived change of rings; I opened each node and verified the hypotheses match the level maps and that no transition flatness is assumed. Step 6 uses the section rectification statement and the semilinear-section equivalence, which explicitly supply projective section models, componentwise weak equivalences/fibrations, and the identification with strict semilinear systems. Step 7 transposes lifting squares across the adjunction from steps 3–4, using the componentwise fibration clauses from rectification.

Step 8 cites the pointed-model stability criterion and the cone statement. The cone statement itself introduces the same ring sequence, section model, cofibrant section, cone, inclusion, cokernel shift and contraction, so it supplies precisely the cofibration, contractibility and shift facts used. Step 9 cites the suspension statement, whose projection is a componentwise quasi-isomorphism and whose conclusion identifies suspension with `[1]`, together with pointed-model stability. Step 10 cites the enhanced dg Quillen calculus and section rectification; their statements give derived adjunctions, units, counits, composition and coherent localization. Steps 11–13 use the flat-model/K-flat clauses, derived change of rings, pullback preservation, section rectification, semilinear coherent sections, and dg calculus to compute the displayed derived tensor evaluations, transitions, Kan-extension universal properties and composition comparisons. Every entry in `citations.json` is the verbatim statement of the cited node, so the quoted text contains the fact used by its step.

I checked the two new supporting node files against the shared DAG and the existing blueprint references before copying them; both are already reviewed statement-only nodes with their required Mathlib search logs and no Mathlib match. I also checked for duplicate statements by searching the DAG for their ids and cone/suspension keywords. The closest `lem-cbc-projective-cochain-suspension` concerns a single ordinary ring and is not the semilinear section statement, so it is not a duplicate. The item and supporting nodes retain their blueprint ancestry, source places, tool-use declarations, and inherited review metadata. No SGA 4/4½ source is cited, no statement was weakened, and no source or Lean file was modified.

## Not duplicates

`lem-pur-system-section-cone` vs `lem-cbc-projective-cochain-suspension`: the former is for a projective model of strict semilinear sections over an inverse sequence of sheaf rings and proves section-compatible cone cofibration/contractibility; the latter is for a single ordinary ring's projective cochain model.

`lem-pur-system-section-suspension` vs `lem-cbc-projective-cochain-suspension`: the former computes the suspension of the semilinear section model and its natural componentwise shift comparison; the latter treats only ordinary complexes over one ring.

## What could not be finished

Nothing. This is a stage-1 natural-language delivery; no Lean code, compiler, Lake build, or other build tool was run.
