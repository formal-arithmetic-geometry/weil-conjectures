# Stage-1 report: lem-sfb-projective-bundle-base-change

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-projective-bundle-base-change.json: statement, split into five proof steps; Mathlib searches found no exact theorem. No new nodes and no new Mathlib leaves.
- citations.json: thirteen entries, one verbatim statement quote for each step/node citation.
- report.md: this report. searches.jsonl was produced by the required search command.

## Attachments

None. Searching the live WeilConjectures source for the blueprint id, projective-bundle spelling variants and projectivity/base-change terms found no declaration stating the item. The existing projective-space OfSections construction concerns finite projective spaces and is not an attachment. The existing tensorPullback_isFiniteType declaration belongs to the already recorded lem-weil-pbc-module-pullback-finite-type; no node is changed for it.

## Wanted literature

None for this split. Stacks morphisms.tex, modules.tex and constructions.tex are present and were read.

## Corrections and route

The statement is mathematically correct, including for finite-type modules that are not locally free. The stored JSON had literal doubled TeX escapes; these were normalized without altering its mathematical statement. No hypothesis was added and there is no STATEMENT-DISPUTED.

The original item had no proof. Tag 02V6 (lemma-base-change-projective) says some details are omitted. The split now supplies the omitted bundle identification, by constructing both maps using the natural classification of line quotients, and then carries the original closed embedding across that identification. This follows the projective-bundle proof of 02V6, using the quotient description of Section 01OA, not the H-projective proof and not an assertion that projectivity is local on an arbitrary base.

The inherited blueprint.from.node was null. Following the already present via chain reaches lem-sfb-admissible-direct-image, whose from.node is the imported det-thm-sf-ctf-stability-direct-images. This exact imported ancestor was restored while preserving the existing via list. tools/blueprint_refs.py ancestor currently prints None for the uncorrected repository item because it follows the created.item value of that older node, Sheaf.SixFunctors.CtfStabilityDirectImages, rather than its explicit blueprint.from.node. The latest blueprint direct-image proof and unit were read; their current paragraph (3) is compressed through the direct-image theorems. This split supplies only the geometric prerequisite exposed by the existing parent nodal-base-change proof; it makes no change to the unit or chapter route.

## Mathlib and duplicate searches

Read the six search results logged for Q128. LeanFinder was run with two different formulations (projective morphism base change; quotient projectivization), LeanSearch with the projective-bundle convention, Loogle with Projective and baseChange, and grep both on AlgebraicGeometry and its Morphisms directory. The hits concern closed immersions, properness, absolute Proj, module presentations, Grassmannians and Weierstrass equations. None supplies projectivity in this convention. Original Q139 search records were retained; the Q128 searches are added exactly as logged.

Searched the whole DAG statements and ids for projective bundles, relative Proj/base change, symmetric algebra/base change, finite-type and quasi-coherent pullbacks, and closed-immersion base change; also searched the blueprint with blueprint_refs.py for projective bundle, projective-bundle, quotients, base change and 02V6. Reused existing nodes throughout. In particular, the finite-rank frame coherence statement lem-pur-projective-bundle-base-change-coherence has a local-freeness hypothesis absent here. The arbitrary relative-Proj statement exists too; the direct quotient argument avoids assembling a new sheaf-algebra base-change lemma or silently using its flat-only sibling. No new node is justified or created.

## Not duplicates

No new nodes: there are no new/existing same-tag pairs to justify.

## Review by Q128

I read Stacks 02V6 in morphisms.tex, including its distinction from H-projectivity and its three proof ingredients. I read Modules 01B6 (lemma-pullback-finite-type), 01BG (lemma-pullback-quasi-coherent), and Constructions 01OB and the following line-quotient discussion in Section 01OA. I also read 01O3 (lemma-relative-proj-base-change), to check that arbitrary change of base is the intended generality, and Morphisms 01QR (lemma-base-change-closed-immersion). The statement is not restricted to Noetherian bases or vector bundles.

In step 1 the projective-bundle definition supplies exactly a finite-type quasi-coherent witness and closed embedding. I opened both cited module-pullback statements: each applies to an arbitrary scheme morphism, and the finite-type one does not demand coherence or finite presentation. Thus they apply to a:S'→S with precisely the stated assumptions. The cited module-pullback definition supplies its functor and composition isomorphism.

In step 2 I opened lem-trf-projective-bundle-quotient-geometry. It explicitly permits any quasi-coherent module, states the universal invertible quotient and the classification for every scheme over S, and includes naturality under arbitrary pullback. Those are exactly the assertions used to construct b, c and t. The module-pullback statement supplies (av)^*≅v^*a^*, and the fibre-product statement supplies t from its two projections. No finite-dimensional or local-free assertion is used.

Step 3 checks the inverse maps, instead of saying only that the two functors agree. The classification identifies bt with the identity because their quotients agree. It identifies cb with u for the same reason, and p'b=v holds because b is over S'. The fibre-product uniqueness then gives tb=id. This is a few-line consequence of the two cited universal properties, not a new geometric lemma or an unsupported appeal to a fully-faithfulness-only Yoneda statement.

In step 4 I checked the cartesian square by its universal property; it is the base change of i along Q→P, not merely a statement about its image. The cited closed-immersion statement says exactly that an arbitrary base change is a closed immersion. The final change of target is an isomorphism, so the two defining conditions of closed immersion are preserved (homeomorphism onto a closed subset and surjection of structure sheaves). Step 5 is exactly the projectivity definition with the witness a^*E already established in step 1. Every node in these steps was opened and every used assertion is covered by its verbatim quote in citations.json. The off-unit quotient geometry and quasi-coherence tools are declared in split_report.tool_uses as generic geometry, not changes to the six-functor route.

I checked B1–B10: no unsplit new statements or new notions, source tags and labels checked, actual searches recorded, no false attachment. I checked C1–C8 and D1–D5: all non-elementary facts are existing cited statements; nothing uses a proof-only construction of a cited node, there is no new relabelled clause, and the omitted comparison is worked out. I checked E1–E7: the base change is arbitrary throughout and the source is correct. Each proof step is under 900 characters, so no step passes the 2000-character long-step threshold.

Small cases: E=0 gives empty projective bundle and hence empty X, preserved by any base change. E of rank one gives P(E)=S when it is invertible, reducing to closed-immersion base change. For a nonfree example take E=~(Z/2) on Spec Z and base change to Spec F_2; its symmetric algebra is Z[t]/(2t), whose Proj is Spec F_2, agreeing with the pulled-back rank-one projectivization. Base change to Spec Q makes both projectivizations empty. This checks the argument genuinely allows nonflat base change and a module with torsion. Empty S' also gives the empty scheme on both sides. No step assumes positivity of rank, a uniform bound on local generators, or flatness.

## Unfinished work

None in the stage-1 split. Its existing dependencies remain owned by their own nodes; they are not newly split here. The required server dry run and delivery follow this report.
