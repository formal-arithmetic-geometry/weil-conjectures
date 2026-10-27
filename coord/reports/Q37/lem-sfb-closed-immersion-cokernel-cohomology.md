# Q37 stage-1 report: lem-sfb-closed-immersion-cokernel-cohomology

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-immersion-cokernel-cohomology.json`: existing statement, now split in four steps; no Mathlib match for the full item.
- `citations.json`: eight verbatim statement quotations, one for every cited node in every proof step.
- `searches.jsonl`: the required search command's original records, retained unchanged.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The statement and statement dependencies are unchanged.

## Attachments

None. Searched the project library by the exact blueprint id and by closed-immersion, pushforward, module-cohomology and boundary terminology. `TopCat.cohomology_closed_immersion_pushforward` covers abelian groups only. `nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom` and the private comparison in `ProjectiveFiniteSourceCohomologySegment.lean` require quasi-coherence. The module-cohomology source comparison supplies only a comparison of models. The general module long exact sequence alone omits the closed-immersion comparison. No declaration or collection of completed project declarations found states every clause under this item's hypotheses.

## WANTED

None. All sources needed here are available in the local Stacks source.

## What was wrong or needed checking

The item was a statement-only prerequisite; no imported proof needed preserving. It explicitly permits arbitrary module sheaves, so the affine quasi-coherent comparison used in Stacks 0BYD cannot itself be applied in this generality. Instead the proof uses the existing natural module/abelian comparison and the normalized closed-pushforward comparison for arbitrary abelian sheaves. This retains the intent of 0BYD and all of the item's hypotheses.

The natural isomorphism in `lem-sc-cohomology-closed-immersion-pushforward` alone does not specify its degree-zero normalization (its lead note flags this). I therefore cite `lem-sc-closed-pushforward-boundary-naturality`, whose statement specifies the unique morphism of delta-functors extending the identity on sections and states that every component is an isomorphism. I do not infer a normalization from another node's proof.

The ancestor search reports `blueprint.from.node = None`; this is the inherited audit-seed chain. I retained its null ancestor, exact existing place and via list, and searched the current whole blueprint for equivalent statements. There is no equivalent blueprint node for this full arbitrary-module, scalar-compatible cokernel statement. I read the current `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-verdier/thm-sf-ctf-stability.proof.md` and the chapter/unit records. This is a generic cohomology tool below the recorded alteration/genus input, not a replacement for a unit step.

## Searches and reuse

The sandbox initially contained only dispatcher brief markers, with no earlier node, report or search log. Existing searches in the repository item have been preserved. Fresh required command searches are appended to the item's record with the exact queries from the log. Loogle found abelian cohomology definitions, LeanFinder found underived pushforward and open-restriction adjunctions, LeanSearch found closed-immersion definitions, and grep found no closed-embedding cohomology declaration. A second semantic phrasing was run and read. None is a match for this item. No search failure is treated as evidence of absence.

Whole-DAG searches by filenames, closed-immersion/cohomology keywords and Stacks tags 02UV, 03FD and 015B found the existing inputs used here. `tools/blueprint_refs.py search` was run for `closed immersion cohomology`, `closed-immersion`, `module cohomology`, and the broader `cohomology` query. The broad output was large; narrower results and the candidate node statements were read. No new node is necessary.

## Not duplicates

No new nodes. Existing comparisons, scalar endomorphisms, enough injectives and the derived delta-functor theorem are reused directly; the two zero-ended exact sequences are proof steps rather than invented lemmas.

## Review by Q37

I read Stacks `curves.tex`, Tag 0BYD, `lemma-genus-plane-curve`, including the sheaf exact sequence and both concluding cohomology isomorphisms. The original proof uses quasi-coherent relative-affine cohomology; the present arbitrary-module statement is justified instead by `cohomology.tex`, Tag 02UV, `lemma-cohomology-and-closed-immersions`, and `sites-cohomology.tex`, Tag 03FD, `lemma-cohomology-modules-abelian-agree`. Both apply without properness, Noetherianity or quasi-coherence. I read `cohomology.tex` Tag 01DZ's module-valued universal delta-functor paragraph; `derived.tex` Tag 015B, `lemma-higher-derived-functors`, and Tag 05TE, `lemma-right-derived-delta-functor`; and `injectives.tex` Tag 01DI, `lemma-sheaves-modules-space`. No SGA source is used. There are no new nodes whose sources require separate checking.

For Step 1 I opened all three cited nodes. `def-weil-closed-immersion` gives precisely the closed embedding needed by the topological comparison. `lem-sc-zariski-module-abelian-cohomology-agree` explicitly supplies natural additive isomorphisms in every degree and the identity in degree zero, for arbitrary module sheaves. `lem-sc-closed-pushforward-boundary-naturality` supplies the normalized natural closed-pushforward isomorphism in every degree. The equality of the underlying pushforward sheaves is sectionwise, so it needs no geometric comparison theorem. Composing in the stated order gives the desired direction of c and retains degree zero.

For Step 2 I read the entire statement of `lem-weil-pbc-module-cohomology-scalar-endomorphism` and its source, Tag 01DZ's injective-resolution definition. It applies separately to each of X and Y and identifies multiplication on cohomology with the induced coefficient endomorphism. The over-k hypothesis is used exactly to identify i_* of multiplication by lambda with multiplication by the image of lambda on X. The proof writes the naturality equality before substituting the scalar interpretation; no unsupported assertion of linearity is left. This is a short elementary consequence of the cited statement and Step 1, so it is not a new node.

For Step 3 the statement of `lem-sc-ringed-space-module-sheaves-enough-injectives` supplies both abelianness and enough injectives for the module-sheaf category. `def-weil-sheaf-of-modules-category` explicitly computes kernels sectionwise, which proves additive global sections is left exact with values in global-function modules. `lem-weil-pbc-right-derived-universal-delta-functor` permits an arbitrary abelian target, gives exactness and canonical derived connecting morphisms, and identifies degree zero. Thus its target here can be the module category, and its connecting maps are linear there. `def-sc-module-cohomology-boundary` names precisely the triangle-derived boundary, avoiding any silent comparison with a separately constructed horseshoe boundary. Restricting scalars leaves every underlying kernel and image unchanged.

Step 4 uses no additional lemma: the proof explicitly gives the image/kernel formulas for conjugating adjacent arrows and writes both zero-ended segments. The four vanishings are used in their stated degrees: H0(L) and H1(L) for the first segment, H1(E) and H2(E) for the second. In particular, it never assumes H2(L) vanishes. The inverse c appears on the incoming side of the original boundary, so the displayed delta is exactly the required one. No compatibility between two unrelated boundary constructions is claimed.

I tested the statement at i = identity, at an empty closed subscheme (all M cohomology zero and the remaining maps reduce to those of the given sequence), and at a point with arbitrary modules. The comparison and vanishing consequences have the stated directions in all three. Zero coefficients and q = 0 cause no exception. The proof never invokes affine acyclicity for arbitrary modules or preservation of injectives by non-flat scheme pullback. Every step is shorter than 2000 characters and the assembly proof is shorter than 3000 characters. Every non-elementary input is an existing cited statement, all off-unit statement tools are declared in split_report.tool_uses, and citations.json copies only their statements. I checked the B--E return cases: no new nodes, no proof-based citation, no dropped hypothesis, no new coefficient category, no unit-route substitution, no hidden transport, and no cycle introduced by these generic tools.

## Unfinished work

None in the stage-1 split. The maintainer's independent review remains part of the project process.
