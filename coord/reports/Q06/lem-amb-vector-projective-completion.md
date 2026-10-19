# Stage-1 report: lem-amb-vector-projective-completion

## Files written

- `dag/nodes/sec-smooth-purity/lem-amb-vector-projective-completion.json`: statement, split; six proof steps; not a Mathlib leaf. No statement change.
- `citations.json`: 22 step/node entries, each quoting the cited statement verbatim.
- `searches.jsonl`: five real searches for the item, including two semantic phrasings; results read. No new nodes and no Mathlib leaves.

## Attachments

None. Searches of the read-only project `WeilConjectures/` by the exact blueprint id, projective-completion names and projective/vector-bundle terminology found no declaration giving the entire statement. Absolute Proj open charts and projective-space properness are only parts of the result. Upstream master is reference material, not closed-proof evidence.

## WANTED

None. All necessary source text is available in `literature/stacks-project/` and the current blueprint.

## Corrections and route

The item was statement-only, so there was no prior proof to retain. Its mathematical statement is correct and is retained verbatim. The proof now realizes the first sentence of the current `main-20261015` proof of `thm-amb-vector-bundle-purity`: the vector bundle is compactifiable by its projective completion. This is a scheme-geometric prerequisite for unit `sk-prop-an` Step 7, not an alternative purity route. No SGA source is used.

I replaced the historical source-place remark about a returned step with the actual tags and new step number. During self-review I corrected the label attached to Tag 01T5 to `lemma-immersion-locally-finite-type`. No statement dispute or change was necessary. The split distinguishes the degree-one generator `t` in the graded algebra from its local nonvanishing charts; it does not require `t` to be a function on all of projective space. Affine intersections are handled by affine refinements, without a separatedness assumption on S.

## Existing nodes and generic tools

DAG searches by projective-bundle, relative-Proj, projective-space, scheme-morphism gluing and finite-type/Noetherian terminology, and whole-blueprint searches `projective bundle` and `relative Proj`, were read before choosing dependencies. The existing `lem-pur-projective-bundle-tautological-geometry` contains projective-bundle properness and local models but does not contain the distinguished-chart construction or frame compatibility of this item. I reused the smaller relative-Proj, standard-chart and properness nodes already present instead of creating new nodes or replacing the item by that larger interface.

All off-unit nonclosed statements used as generic tools are declared in `split_report.tool_uses`: the symmetric algebra and polynomial descriptions, relative-Proj construction/functoriality, scheme-morphism gluing, Noetherianity tools, finite-type composition, and closed-immersion base change. None proves or bypasses a cohomological step of the unit. Existing projective-space properness and target-local properness are already closed nodes.

## Mathlib searches

The five calls in `searches.jsonl` all succeeded: two LeanFinder queries, LeanSearch, Loogle, and the prescribed source grep. The first LeanFinder phrasing returned topological vector bundles; the second returned absolute Proj standard-chart constructions. LeanSearch and Loogle returned `AlgebraicGeometry.Proj.awayι`, `basicOpenIsoSpec` and related chart lemmas. I read `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean`, including `basicOpenIsoSpec` at line 161, `awayι` at line 186, its open-immersion instance at line 193 and the range equality at line 196. Their parameters are a single graded ring; they do not construct relative Proj of a locally free sheaf over an arbitrary Noetherian scheme or establish the frame-compatible identification in this item. The AlgebraicGeometry grep for `SymmetricAlgebra|ProjectiveBundle|projectiveBundle` returned zero hits. There is no exact match or one-line specialization for the whole statement. Inherited N3 searches remain recorded, and only actually executed Q06 searches were appended.

## Not duplicates

No new nodes were created; there are no new/existing pairs to compare.

## Review by Q06

I read the chapter and unit records and the current blueprint's `thm-amb-vector-bundle-purity.md` and `.proof.md`. For the item I read Stacks Constructions Tags 01OA/01OB on the convention P(F)=Proj Sym(F), Tag 01OE on the free case and compatibility with base change, Tag 01NG on the standard affine charts, and the relative-Proj gluing section. I also read Morphisms Tags 01WC (its proof of properness for projective space), 01W2, 01T6, 01T5, 01T3 and 01QR, Schemes 01KU, and Properties 01OW/01OZ. The proof is marked agent-written because it supplies an explicit frame-compatibility calculation and assembles these existing interfaces. There are no new nodes requiring separate sources.

For step 1 I opened each cited statement. `def-amb-finite-locally-free-module` explicitly includes quasi-coherence; adding the fixed first basis vector makes O plus E rank d+1. The quasi-coherent symmetric-algebra statement gives both quasi-coherence and affine sections, the grading statement supplies degree components, and the free-module statement supplies the polynomial algebra with the specified generators. Its grading compatibility is checked on degree-one generators, rather than assumed as an extra theorem. `lemma-nagata-relative-proj-exists` supplies existence and restriction compatibility, while `prop-nagata-relative-proj-functoriality` actually states that a graded equivalence induces the Proj isomorphism. I use that statement, not an unpublished construction in its proof.

For step 2 the vector-bundle definition explicitly gives its affine charts. The relative-affine-space-open-immersion statement explicitly identifies the chart via T_i/T_0 and states it is over S and compatible with base change, so it supplies all local chart claims, including d=0. The coordinate-ring isomorphism is written in the direction used by the item's statement, and its inverse is dehomogenization.

For step 3 the vector-bundle definition contains the exact frame formula y'_j=sum_i g_ij y_i. The relative-Proj definition contains homogeneous-localization restriction maps. I wrote t'=t and x'_j=sum_i g_ij x_i and then divided by t; equality of the resulting polynomial-algebra maps follows on the base ring and generators. This is a short explicit calculation, not a hidden comparison lemma. The scheme-morphism-gluing statement gives existence and uniqueness for maps on arbitrary open covers. I apply it both to the maps and their inverses, and use uniqueness for their composites and the equality over S. Overlaps need not be affine: they are refined by affine opens. This verifies precisely the clause that the original creation report had left to a later split.

For step 4 the projective-space-properness statement applies over every scheme V and the finite index set of d+1 coordinates. The target-locality statement explicitly applies to an open cover with proper restrictions. The definition of proper includes finite type. The finite-type-over-Noetherian statement has exactly the hypotheses obtained: S is Noetherian, and r is finite type. No projectivity descent or global choice of a frame is asserted.

For step 5 the open-subscheme lemma explicitly includes quasi-compactness as well as local Noetherianity. Applied first to U and then to every open j^{-1}(W), it checks the quasi-compactness hypothesis required by the open-immersion-finite-type lemma. The composition node explicitly says that two finite-type morphisms have finite-type composite. For separatedness I identify the pullback of Delta_r along E times_S E -> Ebar times_S Ebar with the diagonal copy of E, using that E is an open subscheme. The permanence node explicitly includes base change for closed immersions, and the proper-morphism definition explicitly defines separatedness by a closed diagonal. Thus I have not used a properness definition alone as a substitute for a permanence theorem.

For step 6 the compactification definition has no density requirement. Its auxiliary-base hypotheses hold by taking that base to be S, with S -> S the identity and E -> S finite type as proved. At d=0 the irrelevant ideal is (t), so D_+(t) is all of Proj R[t], its chart ring is R, and both structural maps are identities. The gluing lemma then identifies the global maps, without assuming rank is positive. The empty scheme and zero-ring affine chart are harmless, since their local maps are empty identities. A nontrivial line bundle is also covered by the frame calculation (x'=u x and x'/t=u(x/t)); no triviality of E globally is used. Nonseparated Noetherian bases are allowed throughout.

I checked B–E of the delivery errors against the actual nodes: no new statements, no hidden clause-restatement nodes, no tags standing in for dependencies, no use of a cited proof instead of its statement, no unverified affine intersections, and no extra hypothesis or changed coefficient setting. Every use has a verbatim statement quote in `citations.json`. All steps are below 2000 characters (largest 1319), and each has its complete argument. The final step is marked elementary because it just checks the compactification definition and the rank-zero chart from preceding steps; all non-elementary gluing it uses is explicitly cited. I leave the independent server checks to verify the entire graph overlay.

## Unfinished work

None in this one-level split. Existing cited unsplit nodes retain their own queue responsibilities; no new proof obligations were manufactured.
