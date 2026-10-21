# Stage-1 repair: lem-sfb-dc-upper-star-preserves

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dc-upper-star-preserves.json`: statement, split; replaced the 7153-character expanded proof by a 2016-character assembly in five steps (longest step 701 characters).
- New nodes: none. New Mathlib leaves: none. The arguments that would otherwise need new nodes already have smaller, reviewed nodes in the current DAG.
- `citations.json`: a verbatim statement quotation for each citation in each item step.

## Attachments

None proposed. This is the required stage-1 repair, not another ATTACH claim. The item's inherited Lean attachment metadata is retained for the maintainer; its mathematical validity is not an assumption of this delivery.

## WANTED

None.

## Return repaired and retained work

The return at head `100b8fa832869045abf34c00f31fca7b56574dfe` asked for a finer split of the 7153-character proof, without changing the statement. The sandbox contained only dispatcher marker files, with no node, report, citations or search log. I therefore used the current shared read clone's returned item, whose proof is exactly 7153 characters, retaining its statement verbatim, all fourteen historical Mathlib search records, blueprint and source data, import flags, and all Lean/maintainer metadata. A read-only snapshot is retained in `returned-node.json` inside this sandbox for comparison. No repository or launcher file was written and no git command or compiler was run by me.

The repair changes the actual proof and its dependency union, rather than merely rebasing the return. Old step 1 is now a citation to the existing `det-prop-sfb-module-pullback-exact-main`; old steps 3–8 are covered by the existing `lem-weil-pbc-module-constructible-pullback`. The latter already contains a 1665-character proof of the strictly smaller, underived module assertion. The exactness node's proof is 1706 characters. The cohomology calculation still uses the existing Mathlib leaf `lem-weil-pbc-exact-functor-complex-cohomology`. Thus none of these arguments needs a duplicate new node. Both non-elementary supporting proofs are already well below 3000 characters; the item is now 2016 characters.

## Not duplicates

No new nodes are created. Before extracting the proposed exactness or local-presentation lemmas, I searched the whole DAG by finite presentation, transport, regular module, constructibility and exactness, and ran `tools/blueprint_refs.py ancestor` plus blueprint searches for `finite presentation`, `transport`, `constructible module`, `pullback on module`, and `upper-star-preserves`. This found the existing exactness node and the general module-constructibility node. I opened both complete statements and the receiving-category definition. I also opened `lem-sfb-proetale-fp-local-models-pullback` and `lem-sfb-pullback-constant-model-constructible`: their constant scalar models or restricted coefficient hypotheses are not the general ring-object condition needed here, and neither is used. The blueprint search finds no second imported node stating this entire derived assertion (the restricted-functor definition names the resulting functor, not the preservation theorem). The item's `blueprint.same_as` remains empty.

No new Mathlib search question arises: the item statement is unchanged and there are no new nodes. Its recorded searches were preserved rather than invented or repeated. The existing cohomology leaf is explicitly recorded as the specialization of `CategoryTheory.Functor.homologyFunctorIso` to the three-term short complex in each degree.

## Review by Q25

I read the current main-20261015 item statement, its complete proof file, the restricted-functors unit record and `_section.md`, the chapter record, and the three-level rules in SETUP.md. The route is exact module pullback, cohomology, inverse-image stratification, base-changed pro-étale cover and finite presentations. The repair retains that route by citing the existing nodes for its arguments, rather than choosing an alternative proof. The item is not the key statement of the entire restricted-functor unit, so its unit's realization fields are not changed.

For step 1 I opened `det-prop-sfb-module-pullback-exact-main` and its main-20261015 source statement. It says that the composite `Ext(alpha_f) mapMod(f*_Ab)` is additive and preserves both finite limits and finite colimits, and explicitly allows any commutative condensed ring and any scheme morphism. This is exactly the functor in `def-sfb-module-upper-star`, whose statement I also read. There is no hidden admissible-coefficient or flatness assumption. This replaces all of the old exactness argument and its nine inline dependencies with their already existing theorem.

For step 2 I opened `sk-def-sfb-module-derived-pushpull`: its total left derived composite is computed on a K-flat resolution, not by independently deriving the two factors. I read the full statement of `lem-weil-pbc-exact-functor-complex-cohomology`, which gives the cohomology isomorphism for every integer and an exact additive functor between abelian categories. I checked its cited Stacks sources in `homology.tex`, Tag 010N (`lemma-exact-functor`), and `derived.tex`, Tag 015F (`lemma-right-derived-exact-functor`). Exactness is supplied by step 1 and the quasi-isomorphism from the resolution identifies its cohomology with that of K. Thus no stronger derived comparison is being silently taken from a definition.

For step 3 I read the finite-interval condition in `sk-def-sfb-bounded-constructible`. Sending zero to zero and substituting in step 2 is elementary; the interval is the same interval, including a complex concentrated in one degree and the zero complex.

For step 4 I opened the entire node `lem-weil-pbc-module-constructible-pullback`, including its statement, source, proof, and review record. Its statement explicitly quantifies over arbitrary commutative condensed rings, not only E, even though its definition dependency originally introduces E. I opened `def-weil-pbc-condensed-e-module-category` and compared its construction of `p_T^*`, coefficient comparison alpha and tensor pullback with `def-sfb-module-upper-star`. Both use abelian sheaves, the ring pulled back from profinite sets, and extension after module transport. I also read the actual upstream sources `WeilConjectures/ConstructibleSheaf/ProEtaleModule/Def.lean`, `DerivedCategory.lean` and `lean/Sheaf/AlgebraicGeometry/ProEtaleModuleConstructiblePullback.lean` without compiling them. The module theorem uses exactly `IsConstructibleModuleObject`, defined by local cokernels of arbitrary maps between finite free modules on a finite stratification. I compared this with `def-sfb-constructible-module`, `def-sfb-locally-finitely-presented`, `def-sfb-finitely-presented-module` and `sk-def-sfb-bounded-constructible`. No constant-matrix, locally constant, étale-origin, finite discrete coefficient, completeness, or finite Tor-dimension condition is inserted. In particular the existing module node supplies both coefficient relabelling and the local-presentation argument, which were the long inherited steps 4 and 8. Its statement, not private material from its proof, is what this step uses.

For step 5 I checked the two defining conditions of bounded constructibility again. Module isomorphisms preserve the condition by composing the witness cokernel isomorphisms after transporting to each cover of each stratum; this is elementary from the definition. Steps 2–4 therefore give exactly the input required. Nothing about tensor or internal Hom preserving constructibility is used.

The scheme setting in the item remains separated schemes of finite type over the specified field, with arbitrary morphisms in that setting. Both generic theorems used here allow these schemes and more; no missing hypothesis is supplied by assertion. Small cases checked: identity maps; empty source or target when a morphism exists; the zero coefficient ring; zero presentations and rank zero; modules concentrated in a single degree; and non-flat torsion modules such as Z/2 over Z/4. The last case causes no problem because the pullback changes schemes with cartesian coefficients; no tensor-closure claim over Z/4 is used.

I checked B–E against the files: statements remain self-contained through the same definition dependencies; there are no new nodes to duplicate a clause; every non-elementary step cites a theorem whose complete statement provides its assertion; the proof-dependency list is precisely the union of uses; and the new theorem citations have explicit generic-tool declarations in `split_report.tool_uses`. Citations are copied verbatim from the opened node statements, including hypotheses. There is no statement dispute and no source correction. The only correction requested by this return is the finer proof factorization, which is now present in the node rather than only in this report.

## Unfinished work

None. The required server delivery dry run exited 0 and printed `OK (not pushed)` for commit `018a8581114`; preflight passed. This includes the server DAG/split checks and verbatim citation validation. The push invocation follows the completed dry run.
