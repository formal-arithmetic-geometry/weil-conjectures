# Stage-1 report: def-sfb-alpha

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-alpha.json`: existing definition, split using its two existing statement dependencies; no new nodes and no Mathlib leaves.
- `citations.json`: `[]`, because this definition has no proof steps.
- `searches.jsonl`: the actual records produced by all Mathlib searches.
- `report.md`: this report.

## Attachments

None. Grep of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for `def-sfb-alpha`, `condensedPullbackHom`, `coefficientPullbackIso`, and the coefficient-morphism terminology found no project declaration stating this definition. The blueprint's expected name `AlgebraicGeometry.ProEtale.condensedPullbackHom` is listed as not found, and no declaration with that name is eligible for attachment. No Lean source was written or compiled.

## WANTED

None. The definition is already stated in the current blueprint snapshot and uses only the two existing DAG definitions.

## Corrections and blueprint comparison

No mathematical correction was needed. I read the current node and `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-coefficient-morphisms/def-sfb-alpha.md`. The statement is verbatim: for a condensed ring Lambda and scheme morphism f, alpha_f is the component at Lambda of the natural isomorphism `f^* \circ p_Y^* \cong p_X^*`, with Lambda_X and Lambda_Y supplied by `sk-def-sfb-pulled-back-coefficients`. The two dependencies are exactly the notions used by the statement. Whole-DAG and whole-blueprint searches for `alpha_f`, `condensedPullbackHom`, and coefficient morphisms found related alpha/eta lemmas but no duplicate definition; those related lemmas use this item and are not interchangeable with it.

The imported node has no recorded unit binding in the side DAG. I read the chapter-level six-functor context (`dag/chapters/sec-six-functors.json`) and the relevant current blueprint section directly, and did not invent or edit maintainer-owned chapter/unit metadata.

## Not duplicates

No new nodes were created. The existing `def-sfb-pullback-from-point-comp-iso` defines the natural isomorphism itself, while `sk-def-sfb-pulled-back-coefficients` defines Lambda_X and Lambda_Y; neither states the component alpha_f definition. The existing `lem-sfb-alpha-iso` and `lem-sfb-alpha-ring-hom` are theorems about alpha_f and therefore are not duplicate definitions.

## Review by N8

I checked the item against the current blueprint source named above and read both cited dependency statements. `def-sfb-pullback-from-point-comp-iso` states the natural isomorphism `f^* \circ p_Y^* \cong p_X^*` for a scheme morphism, so it supplies exactly the isomorphism whose Lambda-component is taken. `sk-def-sfb-pulled-back-coefficients` states that for a condensed ring Lambda, `Lambda_T := p_T^* Lambda` for every scheme T, so it supplies exactly the identifications of Lambda_X and Lambda_Y used in the displayed source and target. No proof step is present for a definition; consequently `proof`, `proof_deps`, and `proof_origin` remain empty/null and `citations.json` is empty.

I checked that the morphism is typed as `f^* Lambda_Y -> Lambda_X`, with the equalities to `f^* p_Y^* Lambda` and `p_X^* Lambda` coming from the cited definitions. The identity morphism case reduces to the identity component of the comparison isomorphism, and the empty scheme and zero/terminal condensed-ring cases introduce no extra hypotheses. The definition makes no claim that alpha_f is an isomorphism or a ring homomorphism; those are separate existing nodes.

For delivery-errors B--E, the statement is self-contained relative to its explicit dependencies, uses single-escaped TeX, and introduces no unsplit auxiliary statement. Every non-elementary notion in the definition is named by a dependency whose statement actually defines it. There are no proof-step citations to audit for C1/C4, no new node or cycle for D1--D5, and no hidden hypotheses or changed objects under E1--E7. Mathlib searches were run with the prescribed `msearch.py` commands in two semantic phrasings for LeanFinder, LeanSearch, Loogle, and grep; the returned generic sheaf-pullback declarations do not state this condensed pro-étale definition, and the exact grep searches had no hits. No SGA source is used.

## Unfinished work

None for this one-level definition split. Delivery is left to the second reader as required.

## Second reading by N8

- Item statement: checked verbatim against `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-coefficient-morphisms/def-sfb-alpha.md`; the hypotheses (a condensed ring and a scheme morphism), the source and target of `\alpha_f`, and the component-of-natural-isomorphism definition all agree.
- Statement dependency `def-sfb-pullback-from-point-comp-iso`: checked against its DAG statement and blueprint source; it supplies exactly the natural isomorphism `f^*\circ p_Y^*\cong p_X^*` used by the item.
- Statement dependency `sk-def-sfb-pulled-back-coefficients`: checked against its DAG statement and blueprint source; it defines `\Lambda_X=p_X^*\Lambda` and `\Lambda_Y=p_Y^*\Lambda` for the condensed ring used in the item.
- Proof steps: none, because this node is a definition; consequently there are no proof dependencies or citations to audit.
- New nodes: none; no auxiliary statement or Mathlib leaf was created.
- Edge cases: the identity morphism, the empty scheme, and the zero/terminal ring object introduce no additional hypotheses and are covered by the universal definition; no isomorphism or ring-homomorphism property was incorrectly folded into this definition.
- Blueprint audit: searched the full `main-20261015` blueprint for `alpha_f coefficient morphism`, `condensedPullbackHom`, and `def-sfb-alpha`; related bundled and theorem nodes are distinct, so `same_as: []` is correct for this imported blueprint node.
- Lean audit: searched the read-only slopmaster2 source for the item id and the candidate declaration names; no finished declaration states this definition, so no attachment is available. No Lean files or compilers were used.

No changes were needed after the second reading. The existing `citations.json` remains empty because the definition has no proof steps, and the first worker's sections remain unchanged.

## Dry run

The second-reader dry run `python3 /home/ubuntu/weil-launcher-nt/deliver.py N8 def-sfb-alpha --no-push` completed with `OK (not pushed) deliver/N8/def-sfb-alpha at ffd23b2ea9: preflight passed`. No push or delivery was performed by that dry run.
