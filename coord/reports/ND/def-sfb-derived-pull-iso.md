# Stage-1 report: def-sfb-derived-pull-iso

## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-derived-pull-iso.json`: definition, split by the five existing statement dependencies; no new nodes and no Mathlib leaves.
- `citations.json`: `[]`, because this is a definition and has no proof steps.
- `report.md`.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for `def-sfb-derived-pull-iso`, `derivedPullIso`, and the blueprint tag `(blueprint: def-sfb-derived-pull-iso)`. No sorry-free slopmaster2 declaration states this item. The declaration `AlgebraicGeometry.ProEtale.CondensedRing.derivedPullIso` in `/home/ubuntu/weil-newtargets-master/WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean` is archived upstream master reference material with the master project's unfinished proof status, so it is not an attachment under the brief.

## WANTED

None. The current blueprint source and all existing statement dependencies are available locally. No SGA source is used.

## Corrections and limitations

No statement dispute. The imported definition statement agrees with `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-coefficient-comparisons/def-sfb-derived-pull-iso.md`: the coefficient morphism is required to have extension of scalars preserving finite limits for every scheme, the comparison has direction `T^X \circ Lf^* \cong Lf^* \circ T^Y`, and it is defined by conjugating the derived restriction/pushforward isomorphism along the derived pullback/pushforward and extension/restriction adjunctions. I kept the existing five `stmt_deps`; each is used directly by the statement. No part of the definition was moved into a new node, and no Mathlib search was needed because this is a project-specific pro-etale condensed-module construction rather than a Mathlib leaf.

## Not duplicates

No new node was created. The existing dependency `def-sfb-conjugate-pull-iso` is the generic conjugate construction; the item defines its specific derived pro-etale application, so there is no duplicate split node.

## Review by ND

I read the target node, its unit `dag/units/sk-def-sfb-coefficient-comparisons.json`, the chapter record `dag/chapters/sec-six-functors-basics.json`, and the current blueprint definition. I also read the statements of every direct dependency:

- `sk-def-sfb-coefficient-change` states the morphism `a_X`, the derived extension `T^X`, and its adjunction to derived restriction of scalars. This supplies the coefficient-change hypothesis and both `T` and `D(Res)` used in the definition.
- `sk-def-sfb-module-derived-pushpull` states the unbounded derived pullback `Lf^*`, derived pushforward `Rf_*`, and the adjunction `Lf^* \dashv Rf_*` for module objects. This supplies the functor and adjunction named in the item.
- `def-sfb-conjugate-pull-iso` defines the conjugate of a natural isomorphism between composites of right adjoints as the corresponding isomorphism between composites of left adjoints. This is exactly the construction invoked by the final clause.
- `def-sfb-derived-comap-lower-star-iso` states the natural isomorphism `D(Res_{a_Y}) \circ Rf_* \cong Rf_* \circ D(Res_{a_X})` under the same finite-limit/flatness hypothesis. Thus the source is precisely the isomorphism being conjugated; no stronger assertion is taken from its proof.
- `sk-def-sfb-derived-extension-of-scalars` states the derived extension/restriction adjunction `S \otimes_R^{\mathrm L}- \dashv D(Res)`, which supplies the two coefficient adjunctions.

The unit's proof paragraph 3 says that the flatness assumption gives exact extension of scalars and K-injective preservation, yielding the derived restriction/pushforward isomorphism; its conjugate is (Pull). The item statement packages exactly that construction, with no extra theorem claim. I checked the direction against the archived master declaration: Lean's `⋙` order corresponds to the displayed `T^X \circ Lf^* \cong Lf^* \circ T^Y`. The zero and identity coefficient-change cases reduce to the identity comparison by the same conjugate construction, so no edge-case hypothesis is missing. There are no proof steps to cite, hence `citations.json` is empty. No files outside the sandbox item directory were changed.

## Dry-run

Second-reader dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py ND def-sfb-derived-pull-iso --no-push` printed `OK (not pushed)` at `35bfce51e7`; preflight passed. The delivery command repeats preflight on the final report.


## Second reading by ND

- Item statement: compared word for word with current blueprint `main-20261015/.../sk-def-sfb-coefficient-comparisons/def-sfb-derived-pull-iso.md` and with the flat derived clause of its unit; all hypotheses, the unbounded categories, functor direction, and specified construction agree. This source is the blueprint, not a Stacks-tagged result, so no Stacks tag or label is applicable.
- Proof steps: none; this is a definition of a specified conjugate, rather than an existence theorem with an omitted proof. Under stage 1 §3.2 its construction is supplied by the statements of its five dependencies, as checked individually below. Empty `proof`, `proof_deps`, and `citations.json` are correct.
- `sk-def-sfb-coefficient-change`: read its statement; it defines $a_X$, $T^X$, the module-derived categories, and $T^X\dashv D(\operatorname{Res}_{a_X})$ for the very same coefficient change. PASS.
- `sk-def-sfb-module-derived-pushpull`: read its statement; it supplies the unbounded module functors $Lf^*$ and $Rf_*$ and their adjunction for each of $\Lambda$ and $\Lambda'$, with arbitrary scheme morphism $f$. PASS; no properness or boundedness is assumed.
- `def-sfb-conjugate-pull-iso`: read its statement and specialized $\mathcal A=D(\Mod_{\Lambda_X})$, $\mathcal B=D(\Mod_{\Lambda'_X})$, $\mathcal A'=D(\Mod_{\Lambda_Y})$, $\mathcal B'=D(\Mod_{\Lambda'_Y})$; $E_1=T^X$, $E_2=T^Y$, $U_1=Lf^*_{\Lambda}$, $U_2=Lf^*_{\Lambda'}$. Its right adjoints are respectively $D(\operatorname{Res}_{a_X})$, $D(\operatorname{Res}_{a_Y})$, $Rf_{*,\Lambda}$, $Rf_{*,\Lambda'}$. Its input and output are therefore exactly the two displayed comparisons, with the required orientation. PASS.
- `def-sfb-derived-comap-lower-star-iso`: read its statement; the hypothesis that extension of scalars preserves finite limits for every scheme is identical, and its isomorphism is precisely $\mathrm{Res}_2 L_2\cong L_1\mathrm{Res}_1$ in the preceding specialization. PASS; no construction inside its proof is used.
- `sk-def-sfb-derived-extension-of-scalars`: read its statement; its derived extension/restriction adjunction agrees with the concrete coefficient-change adjunction already supplied by `sk-def-sfb-coefficient-change`. PASS; the item does not apply the generic ambient-category assertion to an unverified new category.
- New nodes: none; B1–B7 and new-node Mathlib-leaf searches have no instances. Repeated the whole-blueprint search `tools/blueprint_refs.py search 'conjugate'` (20 hits) and `... search 'derivedPullIso'` (zero hits); the generic conjugate node and the underived/open-immersion comparisons have different input data or functors and do not duplicate this derived construction. Read the existing dependency statements instead of creating replacements.
- Source attachment check: independently searched slopmaster2 for the item id, `derivedPullIso`, `derivedComapLowerStarIso`, and `pullIsoOfComapIso`; none occurs. Read upstream master `WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean`, lines 203–243: the universal finite-limit hypothesis and the four adjunction arguments agree exactly. Upstream master remains reference material, not an attachment or proof-status certificate.
- Small cases: on a zero complex both composites give a zero object since the left adjoints preserve initial objects; on the empty scheme the module-derived category is the zero category and the comparison is its unique isomorphism; for $f=\mathrm{id}_{\operatorname{Spec} k}$ the two composites are both $T^{\operatorname{Spec} k}$ up to the specified identity-pullback isomorphisms; for identity coefficient change both composites are $Lf^*$ up to the identity scalar-extension isomorphisms. A complex concentrated in degree $0$ or $1$ has exactly the same typed construction. PASS; no hidden nonemptiness, positive-degree, or nonzero-coefficient restriction is needed.

Changes: retained the correct node statement, its five dependencies, and its empty proof and citations. Added the explicit adjunction specialization and edge-case checks above so the maintainer can verify the definition without reconstructing its types. Kept `## Review by ND` unchanged. The delivery command in the brief has a trailing `.` unsupported by the installed `deliver.py`; its usage requires only group and item, so validation and delivery use that documented syntax.
