# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-coherent-tor-calculus.json`: existing item split into eleven proof steps; no new nodes.
- `citations.json`: 49 step/node entries, each quoting the cited node statement verbatim.

## Attachments

None. I searched the upstream project source for the item tag and for Tor, coherent, and equivariant declarations; no sorry-free project declaration states this item.

## WANTED:

None. The Stacks sources used here are present locally: `literature/stacks-project/algebra.tex`, `cohomology.tex`, `modules.tex`, and `schemes.tex`.

## What was wrong or incomplete

STATEMENT-DISPUTED: the imported statement referred to “a” without introducing an action. The type check fails before any theorem is applied: the expression `a^* M` contains an unbound morphism, since a field, a group scheme and an F-scheme alone do not specify `a : G ×_F X → X`. I corrected it by explicitly fixing an action `a : G ×_F X → X` and its unit and associativity identities. This is a statement repair, not a weakening: the linearization and all later pullbacks use this action. The proof also makes clear that the identity section need not be flat; its unit identity follows by restricting the cocycle to an invertible idempotent.

The imported item had no proof. Its route is now written in eleven steps. All facts used by those steps are existing DAG statements; I created no duplicate or clause node. The route stays within the unit’s coherent finite-Tor stability context, using ordinary affine Tor calculations as declared generic tool input in `split_report.tool_uses`.

## Review by NV

I read the item source in `literature/stacks-project/cohomology.tex` at Tags 08BP and 06YH, the affine sheaf sources in `schemes.tex` at Tags 01HV, 01IA, 01IB, and 01I7, the module coherence source in `modules.tex` at Tag 01BY, and the ring Tor sources in `algebra.tex` at Tags 00LP, 00LS, 00LR, 00M0, 00M3, 00M7, and 00M8. I also read the current unit text in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-image proof. Mathlib searches for the item were run through `msearch.py`: LeanFinder returned representation-theoretic `Rep.Tor` declarations, LeanSearch returned generic categorical Tor and flat tensor exactness, Loogle returned no scheme-equivariant Tor result, and Mathlib grep returned only unrelated coherent-topology, module-sheaf, and representation hits; none states this item.

For step 1, I checked that a field is Noetherian, that finite type over a Noetherian base is Noetherian, that coherent sheaves are quasi-coherent finite-type locally, and that the existing finite-free-resolution and affine sheafification nodes provide the augmented resolution used. I deliberately use a chosen Noetherian affine cover in step 1; the arbitrary-affine assertion is obtained separately using the natural derived-module Tor comparison, so the proof does not silently assume that a chosen cover contains every affine open. For step 2, I read the statements of the ringed finite-free tensor calculation, affine derived pullback/tensor, affine derived equivalence, natural derived homology comparison, affine tilde/global-sections equivalence, and the Tor definition; together they give the actual derived tensor and its affine Tor sections. For step 3, I checked the coherent kernel/cokernel statement and the resolution-lift naturality statement, so cycles, boundaries, and their quotients are coherent and maps are the canonical Tor maps.

For step 4, I checked the existing complex long-exact-sequence and naturality statements, the K-flat fixed-tensor triangulated statement, and the finite-free tensor calculation. The proof therefore supplies all connecting maps in every degree and their naturality in both variables; it does not use a first-Tor-only assertion. For step 5, I verified the affine flatness criterion, exact tensoring by a flat module, the Tor definition, and affine pullback sections. The displayed chain map is the standard free-resolution flat base-change map, and the kernel/image argument applies degreewise without a boundedness assumption. For step 6, I checked the free-resolution lifting, augmented-resolution homotopy, homotopy invariance on homology, Tor map formula, module pullback, long-exact naturality, and exactness of flat pullback nodes. These justify resolution independence, affine restriction, identity/composition coherence, and boundary compatibility.

For step 7, I checked the field-flatness, base-change-flatness, flat-composition, and group-scheme definition nodes. The action map is flat because `(g,x) ↦ (g,a(g,x))` identifies it with a projection; the same argument handles multiplication and the action-nerve face maps. For step 8, I checked the pullback and Tor-definition statements. The linearization is transported by the canonical flat comparisons, and the unit axiom is obtained without assuming the unit section flat: its pullback is an invertible idempotent. For step 9, I checked long-exact naturality, exact flat pullback, coherent kernels/cokernels, and pullback functoriality; these give equivariant kernels, images, and connecting maps. For step 10, I checked the coefficient-action Tor node, fixed-tensor triangulated node, long-exact naturality, and resolution-map node; multiplication on the first factor gives the coherent equivariant P-module structure and kills the ideal action when P is a quotient algebra. For step 11, I checked the finite-free tensor calculation, module pullback tensor comparison, and exact-derived-cohomology comparison. Local finite freeness makes tensoring exact, the reassociation is canonical and equivariant, and the degree-zero/positive-degree assertions follow from the degree-zero flat model.

I tested edge cases in the statement while reviewing: the trivial group gives the ordinary Tor statements and the empty scheme makes the sheaf assertions vacuous; `q=0` is the ordinary tensor product; rank-zero locally free modules give zero Tor; codimension or action stabilizers do not enter the argument; and no flatness is assumed for the identity section. Every proof step has `elementary: false` except the explicit cocycle-idempotent step, which uses only the definition and cancellation of an isomorphism. `proof_deps` is the union of the cited nodes, and `citations.json` quotes the exact statements used by each step.

## What I could not finish

Nothing. The split is complete and the initial server review check passed. The full delivery dry run also printed OK (not pushed), commit d5f6c22354a. This final report clarification is rechecked before pushing.

## Not duplicates

No new nodes were created. Existing Tor, affine-resolution, coherence and flat-pullback nodes were reused. Blueprint searches for equivariant coherent Tor and coherent Tor found no blueprint node stating the whole item.
