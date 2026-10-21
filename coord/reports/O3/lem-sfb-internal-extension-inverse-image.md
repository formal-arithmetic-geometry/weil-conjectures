# Worker report

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-internal-extension-inverse-image.json` (statement, split; no exact Mathlib match), `citations.json` (15 verbatim citation entries), and this report. No new nodes or Mathlib leaves.
2. Attachments: none. The project source under `lean/WeilConjectures/` has no declaration tagged with this item and no `pullbackExtendScalarsIso`. Searches by `mapMod`, `extendScalars`, and their combinations find the coefficient pullback definition in `SixFunctors/ProEtale/ModuleObject/UpperLowerStar/Defs.lean`, not this comparison for arbitrary ring objects. The parent's historical reviewer mentions a side Lean declaration, but that is not an attachment in the authorized live source.
3. WANTED: none.
4. The item was statement-only. Its statement and statement dependencies are unchanged, including the reviewer's symmetric-monoidality correction. The comparison uses actual inverse-image rings, not cartesian coefficients from a point. No statement dispute or unit-route error was found. The blueprint's last sentence omits the compatibility of local presentations with inverse image; the five proof steps now supply that compatibility by its balancing diagram.
5. Nothing remains unfinished in this one-level split. Its cited existing nodes keep their own stage-1 obligations.

## Sources and route

I read `dag/chapters/sec-six-functors-basics.json`, `dag/units/sk-thm-sfb-qlbar-two-colimit.json`, and the main-20261015 `lem-sfb-extend-to-qlbar-constructible.proof.md`. This lemma serves the final sentence about tensoring local finite presentations on strata, below the unit's coefficient-extension cocone. It does not change coefficient descent or the chapter's route. The proof is marked agent-written: the blueprint only sketches this part.

For the two elementary universal-property arguments I read Stacks `categories.tex`, Tag 0038 (`lemma-adjoint-exact`, the displayed Hom-set proof), and Tag 002A (`definition-coequalizers`, including uniqueness). I also read Tag 03EL, `sites-modules.tex`, `lemma-tensor-product-pullback`, as corroborating context; I do not apply it as an uncited theorem or silently identify internal module objects with ordinary ringed-topos modules. No SGA source is used.

The off-unit statement `lem-sfb-finite-upper-star-braided` is declared in `split_report.tool_uses`: it supplies generic symmetric monoidality and preservation of commutative ring objects, not a replacement for a coefficient-descent step. All other proof inputs are existing definition nodes. No unit record is changed because this item is not its key node.

## Searches

Read the existing six Mathlib-search records before searching. They were inherited from the item's creation and are retained. Ran six searches with the prescribed `msearch.py` command; their actual results are in `searches.jsonl`. These include LeanFinder with two phrasings, Loogle, LeanSearch, and two grep patterns. All services answered. The Loogle query and broad grep found no comparison. The monoidal grep found the `mapMod` TODO at `Mathlib/CategoryTheory/Monoidal/Mon.lean:856`, which I read with the adjacent ring-object transport. I read the declaration list of `Monoidal/Mod.lean` (scalar restriction/comap, no transport-extension comparison) and `Sheaf/PullbackFree.lean` (ordinary module-sheaf pullback and free modules). The other hits describe tensor colimit preservation, ordinary ModuleCat change of rings, and bimodule tensor maps; they are not a one-line specialization giving the entire item with its internal module objects. No leaf is claimed.

Whole-DAG keyword searches and `tools/blueprint_refs.py search` were run for coequalizers, extension of scalars, inverse image commuting, monoidal functors, and Tag 0038; `ancestor` confirms the ancestor `lem-sfb-extend-to-qlbar-constructible`. No blueprint node states this exact general-ring comparison, so `same_as` stays empty.

## Not duplicates

No new nodes are proposed. The closest existing comparison, `def-sfb-pull-iso`, uses condensed coefficient maps and the module pullback that includes extension along the cartesian coefficient comparison. The item treats arbitrary ring objects and only `mapMod` of the abelian-sheaf inverse image, with target rings exactly `F(R)` and `F(S)`.

## Review by O3

I checked B–E against the node files and sources, rather than interpreting a cited definition as an unstated theorem. There are no unsplit new-node statements to audit, no relabelled clauses, and no new nodes duplicating the universal-property calculations. The five steps are below 2000 characters each and spell out their equations.

Step 1 uses precisely the coequalizer and induced first-factor action stated in `sk-def-sfb-change-of-scalars`, the commutative-ring conclusion actually stated in `lem-sfb-finite-upper-star-braided`, and the multiplication/module-action formulas of `def-sfb-modobj-transport`. The sheaf tensor categories are symmetric and their tensor functors preserve colimits by the existing statement `sk-def-sfb-sheaf-tensor`, so extension is defined on both sides. No flatness hypothesis is used or needed.

Step 2 uses the natural Hom bijection in `def-sfb-finite-upper-lower-star-adjunction` and the coequalizer from `sk-def-sfb-change-of-scalars`. I wrote the four Hom sets and the relation explicitly; it proves the finite-diagram preservation assertion directly. Thus Tag 0038 is not standing in for an absent cited node or an unproved preservation lemma. The scheme morphism is arbitrary, as that adjunction statement permits.

Step 3 uses the invertible tensorator stated by `def-sfb-finite-upper-star-monoidal`, the exact naturality and associativity equations in `def-sfb-strong-monoidal-functor`, and the transported-action formula in `def-sfb-modobj-transport`. I checked both balancing arrows, including the associator in the action arrow and the actual map `F(phi)` in the multiplication arrow. Opposite-direction maps are obtained from the two coequalizer properties and are inverse by their uniqueness; there is no appeal to a separate comparison theorem.

Step 4 uses the same transport formula, the induced action supplied by change of scalars, the strong-monoidal coherence equations, and the explicit tensor-colimit-preservation clause of `sk-def-sfb-sheaf-tensor`. I checked the equation after `1 tensor q'`, explained why that map is epic from its coequalizer property, and verified that the inverse of the linear isomorphism is linear. Thus an isomorphism merely of abelian sheaves is not substituted for the requested isomorphism of module objects.

Step 5 uses the functorial quotient construction of change of scalars, the functor on linear morphisms in transport, and tensorator naturality. The common composite after `q'_M` is written down. Cancelling that coequalizer proves naturality in every module morphism; the requested orientation is the inverse of the constructed natural isomorphism. I adjusted the step-5 citation quotes to name the naturality equation and the transport-on-morphisms sentence specifically. Every entry of `citations.json` is an exact substring of the cited live statement.

I tested the identity scheme morphism, the identity ring map, the zero module, zero target ring, and a nonflat ring map such as Z to Z/2. The same balancing diagram works in each case: it does not assume exact scalar extension, a nonempty site, or locally constant coefficients. In the identity case both coequalizer maps give the usual identity comparison; for zero data both sides are zero. No conditions on separation, finiteness, or constructibility enter this lemma.
