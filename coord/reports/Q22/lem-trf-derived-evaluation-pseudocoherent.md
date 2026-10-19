## Worker report

Files written: `dag/nodes/sec-trace-formula/lem-trf-derived-evaluation-pseudocoherent.json` (the item, statement, split; no Mathlib match), `citations.json`, this report. No new nodes and no new Mathlib leaves. The auxiliary sandbox script writes only these sandbox records. No Lean was written or compiled and no live project or launcher file was changed.

Attachments: none. Searching all of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint id, pseudo-coherent terminology and derived evaluation found no declaration giving the item's statement. The occurrence of pseudo-coherent terminology in `AlgebraicGeometry/Cohomology/DirectImage/FiniteFreeComplex.lean:124` is a comment about Kiehl's theorem, not this algebraic evaluation theorem. The project's homotopy-category tensor-Hom adjunction and bounded dual-complex constructions do not assert this pseudo-coherent evaluation isomorphism. There is no finished attachment here.

WANTED: none. The Stacks sources used are already local.

What changed: the item had no proof or proof dependencies. Its statement, hypotheses, source, ancestry, creation record and inherited Mathlib searches are retained. Its proof now follows Tag 0A68(2), with the finite index estimates made explicit and the canonical signed map verified. The finite injective dimension hypothesis is already defined inline as a bounded injective representative; `def-sp-injective-resolutions` only defines injectivity and ordinary resolutions, and is not being used to infer a bounded representative. No statement correction or dispute was needed.

Nothing remains unfinished in this one-level split. Every non-elementary resolution or derived-operation input has an existing cited node; there are no newly deferred statements.

## Sources and searches

I read `more-algebra.tex`, lemma-internal-hom-evaluate-isomorphism (Tag 0A68), case (2), in full, and its cited chain construction lemma-evaluate-and-more (0A60), remark-sign-explanation (0A61), and lemma-internal-hom-evaluate (0A67). I also read definition-pseudo-coherent (locally Tag 064Q, clause (2)), lemma-derived-tor-quasi-isomorphism (064K), lemma-RHom-out-of-projective (0A66), and `derived.tex` lemma-injective-resolutions-exist (013K) and lemma-bounded-below-injectives-K-injective (070J). The node for pseudo-coherence has an older 064P tag in its source metadata, but its actual definition agrees with the local 064Q text. No other worker's source metadata is edited.

Read the fixed chapter `sec-trace-formula` and the unit `sk-i-curve-zero`. This item is a generic commutative-algebra input deep in the existing relative-duality branch of `lem-trf-local-term-locality`. Its blueprint ancestor and complete inherited via chain are preserved. The proof supplies the specific Tag 0A68(2) component identified by `blueprint.from.place`; it changes no chapter or unit route. Whole-blueprint searches for evaluation, pseudo-coherent, double Hom, and internal-hom-evaluate found no equivalent imported blueprint statement. Whole-DAG searches for Tags 0A68/0A60, the source labels, bounded-above projective models, K-flatness, injective models and finite-projective tensor-Hom revealed the existing nodes reused here. No new node is justified by those searches.

The sandbox `searches.jsonl` records every Mathlib search I ran, through the required msearch command: LeanFinder in two formulations, LeanSearch, Loogle and grep. The full returned hits were read. LeanSearch returned ordinary `dualTensorHomEquivOfBasis`, `lTensorHomEquivHomLTensor`, and injective-resolution comparisons; I read the two Contraction declarations at lines 170 and 312. They concern single ordinary module Homs and are not the derived double-Hom comparison. The first LeanFinder query returned Ext/Tor and support facts; the second returned total tensor and total-flip infrastructure. None has this statement. Loogle's valid quoted-name query returned zero hits, as did the homology-source grep. The inherited searches from Q82 remain unchanged and are distinguished from my new logged searches; I am not claiming to have rerun them.

## Tool uses

The proof declares three off-unit generic tools in `split_report.tool_uses`: `lem-pc-module-bounded-flat-kflat` gives the K-flatness criterion for the finite-free model, `lem-pc-source-kflat-module-tensor-model` computes derived tensor on that model with an arbitrary other factor, and `lem-pc-kflat-resolution` supplies the resolution used in checking the transposed morphism. These are algebraic infrastructure for the source's representative calculation; they replace no step of the unit's geometric route. Definitions and the two injective-resolution/enough-injectives Mathlib leaves provide the other notions and tools.

## Not duplicates

No new nodes were created. In particular, I did not create another evaluation theorem, finite-free module evaluation lemma, or bounded-support lemma: the last two are elementary calculations written in the item's steps. The existing sibling canonical-map node supplies the map and its normalization, not its invertibility, and is used only for that statement.

## Review by Q22

I checked the unchanged item against 0A68(2): the ring is commutative, K is pseudo-coherent, L is cohomologically bounded below, and M has a bounded injective representative. No Noetherian condition, perfectness of K, or boundedness above of L is introduced. Finite-freeness is available from the definition of pseudo-coherence itself. No new nodes need a separate source review.

Step 1 uses the actual definition in `def-pc-ring-pseudo-coherent-complex` to choose P, the statement of `lem-weil-pbc-ring-modules-enough-injectives` for the necessary category hypothesis, and both clauses of `lem-weil-pbc-dplus-injective-representative` for J and K-injectivity. The bounded I is the hypothesis, and that same lemma's second clause makes it K-injective. I checked that the latter node applies to an arbitrary abelian category with enough injectives, not only to scheme sheaves.

Step 2 uses `lem-pc-module-bounded-flat-kflat` on P after proving its terms flat by the finite direct-sum argument. `def-pc-module-kflat-complex` states the equivalent categorical convention, and `lem-pc-source-kflat-module-tensor-model` has no boundedness or flatness condition on the other factor. Thus it really applies to H. The ordinary symmetry is the explicit Koszul symmetry. This avoids citing a sheaf/scheme-only tensor comparison for ordinary modules.

Step 3 uses `def-pur-derived-internal-hom` exactly for its stated construction on a K-injective target and its independence of the chosen K-injective representative. Specializing its small ringed site to the singleton category gives ordinary R-modules; J is used as a target only for A, and I for H and B. `def-sc-module-total-hom-complex` gives the displayed terms and differential, which I compared with the source. No projectivity of A or H is asserted or needed.

Step 4 is finite integer arithmetic applied to those Hom and tensor definitions. The crucial lower bound on s is n-b+ell; it uses the upper bound b for I and lower bound ell for J. The inner Hom has the separate finite range ell-k <= s <= u. These estimates justify both passages through products, including Hom out of the inner product; there is no claim that Hom commutes with an infinite product. All identifications are just finite projections, inclusions and restriction to finite sums.

Step 5 writes the actual signed chain map and checks all three differential contributions using the two cited definitions. The recurrences are those of 0A60 with its variables renamed p,r,s. The printed source has a stray index in the displayed epsilon subscript, but its exponent and three recurrences are unambiguous; the split consistently uses epsilon_{p,r,s}=(-1)^{s(r+1)}.

Step 6 reads the statement of `lem-trf-derived-evaluation-canonical-map`, whose transpose is exactly the composite used here. The signs kh and kn, with n=h+s, give ks and then s(r+1) modulo 2. This is the verification that our component map is the required canonical morphism. The cited derived-Hom and tensor-model statements justify using these representatives. During self-review I noticed that checking the transpose after replacing A also uses existence of a K-flat resolution; I added `lem-pc-kflat-resolution`, read its full statement, and applied it only on the singleton ringed site. It gives precisely a K-flat complex mapping by a quasi-isomorphism to A. This fact is now cited rather than implicit.

Step 7 is the complete finite-basis inverse calculation, using the finite-free conclusion of the pseudo-coherent definition. For the composition on beta I checked the identity f=sum_i iota_i(f(e_i)); for the composition on g tensor x I checked the tensor balancing identity sum_i x_i g tensor e_i=g tensor x. Thus the unsigned components, their signed versions and their finite sums are invertible. This is a few-line module calculation, not a new node or a black-box appeal to a source tag.

Step 8 uses only the chain-map equation and the localization functor of `def-weil-abstract-derived-category`. The equation for the inverse follows by multiplying by degreewise inverses, so no unquoted theorem on quasi-isomorphisms is needed to conclude. Every dependency in every step has a verbatim quotation in `citations.json` copied from its current statement. No step exceeds 2000 characters or conceals a separate non-elementary comparison.

I tested the zero ring, zero complexes, rank-zero free terms and empty degree ranges: the finite-basis sums and direct sums are then empty and the maps are the unique zero-object isomorphisms. The estimates allow P unbounded to the left and J unbounded to the right; a single-degree shift changes the bounds without changing the argument. Characteristic two makes the signs equal to 1 and leaves the same equations valid. These tests also explain exactly why the finite-free, lower-bound and bounded-injective hypotheses are used. I found no source or statement error and corrected only the missing resolution citation noted above.

## Validation

Server `review_split`: PASS, 0 new nodes. Full `deliver.py Q22 lem-trf-derived-evaluation-pseudocoherent --no-push`: exited successfully with `OK (not pushed)` at b0f332daf0; all server preflight checks passed. The statement is unchanged, all 18 step citations are verbatim, and the longest step is 1236 characters. Only this validation paragraph was updated after that dry run.
