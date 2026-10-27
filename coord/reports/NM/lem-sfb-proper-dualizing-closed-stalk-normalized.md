# Stage-1 report: lem-sfb-proper-dualizing-closed-stalk-normalized

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-proper-dualizing-closed-stalk-normalized.json` (item, split, original statement unchanged); `dag/nodes/sec-six-functors-basics/lem-sfb-coherent-bounded-below-rhom-stalk.json` (statement, unsplit, no Mathlib match). Also `citations.json`, this report and the actual `msearch.py` search log. No Lean, compiler, Lake, repository write, git invocation or other agent was used.
2. Attachments: none. Searched the exact blueprint tag and coherent-duality / normalized-dualizing terminology in the live `lean/WeilConjectures` source. The numerous étale dualizing-complex declarations have different coefficient categories; none states this item. The existing coherent stalk comparison only has two sheaf arguments and gives cohomology isomorphisms.
3. WANTED: none. The Stacks sources are present locally.
4. Faults corrected: the seed had no proof. Its source 0AWL does assert the result, but quoting it as a new node would only restate the item. The proof now carries the closed-point argument itself. The finite-extension dual must not be identified by the field trace: that trace can vanish for inseparable extensions. Step 6 explicitly uses a nonzero coordinate functional instead. A per-degree stalk comparison with a degree-zero second argument cannot be applied to K, so the actual derived comparison of 0GM8(2) is isolated as a general supporting input.
5. Unfinished: no part of the item's natural-language proof. The single new statement is deliberately left unsplit for the queue.

## Sources and route

Read `duality.tex`, Tag 0AWL (`lemma-good-dualizing-normalized`), its complete proof, and 0AWI (`example-proper-over-local`) and the following field example. Also read the finite-duality statement and proof 0AX2 (`lemma-finite-twisted`), 0AA2 (`lemma-shriek-closed-immersion`), the proper good-dualizing identification, and the proper-composition statement. Read `morphisms.tex` 01TF, which gives finiteness for a closed fibre point, not only rational points. For the new node read `cohomology.tex` 0GM8 (`lemma-stalk-internal-hom`), case (2) and proof, and `perfect.tex` 08E8 (`lemma-identify-pseudo-coherent-noetherian`). 0GM8 explicitly gives an isomorphism of derived objects; naturality is that of its canonical pullback-Hom comparison.

Read the item's chapter and unit records and the latest blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/{_section.md,sk-thm-sf-ctf-stability-direct-images.proof.md}`. The current proof (3) no longer displays the old alteration expansion from the inherited ancestry; it invokes proper base change and coefficient finiteness. This is an already queued ordinary coherent-duality prerequisite from that expansion. No chapter/unit route was edited. `blueprint_refs.py ancestor` reports null, matching the inherited ancestry: kept this value and prepended this item in the new node's via list. Whole blueprint searches for dualizing, duality, skyscraper, internal Hom, closed immersion, closed point, stalk and 0GM8 found no blueprint node stating the new derived comparison. Whole DAG searches by the tags and by the Hom/stalk/coherent/duality concepts found the distinct candidates below.

## Review by NM

I checked the split against B–E with each cited node's statement open, and generated the citation file from those statements. The item introduces all objects itself; it has no missing dimension or rationality hypothesis and needed no statement correction. The new node introduces X, F, E, x and A, spells out bounded-below cohomology, and cites the coherent, derived-category, stalk and internal-Hom definitions. It contains no proof sketch or proof steps. Its searches were all actually run with the required search command and their returned types/descriptions read; the Mathlib hits concern ordinary tilde stalks, smooth sheaves, condensed Hom, ring homomorphisms surjective on stalks, or generic derived Ext, none the comparison claimed here. A second semantic phrasing using pseudo-coherence also found no match. Search output is retained in searches.jsonl, and the recorded queries match it exactly. The item was searched independently by proper coherent duality and closed-point normalization, with no match.

Step 1 uses properness only for finite type, the existing finite-type-over-Noetherian node for X Noetherian, and `lem-sfb-proper-field-algebraic-dualizing` exactly for bounded coherent K and its local dualizing properties. Its statement explicitly includes finite injective dimension as a bounded injective representative and algebraic dualizing stalks; bounded coherent cohomology implies finite cohomology at each stalk. I did not use an étale dualizing result or assume X smooth, reduced, connected or a curve.

Step 2 uses `lem-kun-closed-point-field`(a) for L/k finite with arbitrary k, and the exact closed-point immersion criterion (a Mathlib leaf). Closed-immersion finiteness and properness are separate existing statements, not assumptions. The definition of finite morphism on Spec L and field-flatness give pi finite flat; both spectra and X are Noetherian. The existing Noetherian-direct-image-adjoint theorem supplies the two adjoints, so no existence is hidden in notation. The actual residue map is the one inducing the scalar action A to L.

Step 3 uses the full finite-flat-duality evaluation statement, which supplies both degree-zero concentration and the precomposition L-action on Hom_k(L,k). The affine quasi-coherent derived equivalence is cited for reading this as an L-module complex. Its hypotheses are met without separability or any nonzero trace hypothesis. Step 4 applies proper composition to the proper maps i and f between Noetherian schemes, with the given right adjoint a. It concludes the comparison of their adjoint objects, rather than assuming an arbitrary choice of dualizing complex is already normalized.

Step 5 uses finite pushforward coherence exactly on i_*O, finite duality for the finite map i with the bounded-below object K, and the new derived stalk comparison with coherent first argument F. Each cited statement says this, including the bounded-below restriction and the algebra action in finite duality. I wrote out the remaining stalk/exactness calculation: a sheaf pushed from the closed singleton has sections M on opens containing x and zero otherwise. Thus direct image is exact, its derived functor is represented termwise, and its stalk is precisely the restriction of the original L-module through A to L. The result is an isomorphism in D(A), not a collection of unassembled cohomology isomorphisms.

Step 6 is an elementary finite-dimensional linear-algebra argument written explicitly. A nonzero functional lambda gives b maps to (c maps to lambda(bc)); multiplication by nonzero b is invertible, so the map is injective, and equal finite k-dimensions give surjectivity. This constructs an L-linear, hence A-linear, isomorphism V with L. Nothing uses a trace pairing. This proves the remaining normalization assertion and does not outsource a clause of the item to a renamed node.

The only new node is an actual general comparison for arbitrary coherent F and bounded-below E, independent of any proper morphism, right adjoint, field or dualizing complex. It is neither the item nor one of its clauses. Small-case checks: F=0 or E=0 gives zero on both sides; a one-point field scheme gives the identity comparison; shifts of a sheaf E are allowed (the old node does not allow them); singular Noetherian schemes are allowed because pseudo-coherent, not perfect, is required. For the item X empty is vacuous; X=Spec k gives k[0]; X=Spec L for a finite inseparable extension gives Hom_k(L,k)[0], which is L[0] by the explicit pairing. For k=F_p(t), L=k(t^(1/p)), a coordinate functional nonzero on 1 still works whereas the field trace is zero. Nonreduced Artinian proper schemes and disconnected proper schemes satisfy the same argument point by point.

No non-elementary step exceeds 2000 characters; all are below 800. All dependencies' statements were opened; no argument uses a cited node's proof instead of its statement. Generic off-unit tools are explicitly declared in split_report.tool_uses, with their role, and no SGA source or finite-coefficient purity route is involved. Existing/new nodes were checked for reverse reachability to avoid a cycle; the server's DAG check is the final check. Every new statement remains independent of the item. No source error or statement dispute was found.

## Not duplicates

lem-sfb-coherent-bounded-below-rhom-stalk vs lem-sc-derived-hom-finite-free-model-aux: computes a chosen finite-free sheaf Hom model; it has no stalk comparison.

lem-sfb-coherent-bounded-below-rhom-stalk vs lem-sc-hom-complex-dual-total-comparison: compares a total double complex with the Hom short complexes, without any stalk or derived comparison.

lem-sfb-coherent-bounded-below-rhom-stalk vs lem-sc-finite-free-internal-hom-exact-sequence: proves exactness for one finite-free sheaf and a short complex, not a derived stalk comparison.

lem-sfb-coherent-bounded-below-rhom-stalk vs lem-sc-coherent-pseudo-coherent: states pseudo-coherence of a coherent sheaf; no derived Hom or stalk assertion.

lem-sfb-coherent-bounded-below-rhom-stalk vs lem-pc-noetherian-bounded-coherent-pseudo-coherent: states pseudo-coherence of bounded coherent objects; no Hom or stalk comparison.

lem-sfb-coherent-bounded-below-rhom-stalk vs lem-pc-proper-flat-single-open-pseudo-coherent: asserts pseudo-coherence of a restricted proper direct image, not derived Hom at stalks.

lem-sfb-coherent-bounded-below-rhom-stalk vs lem-sc-affine-projective-complex-derived-hom: computes ring-derived Hom from a projective complex; it has no comparison from sheaves to stalks.

lem-sfb-coherent-bounded-below-rhom-stalk vs lem-sc-derived-internal-hom-stalk-localization: only compares individual cohomology modules when BOTH arguments are degree-zero sheaves; the new node permits an arbitrary bounded-below second complex and asserts the comparison isomorphism in D(A).

lem-sfb-coherent-bounded-below-rhom-stalk vs lem-sc-ext-stalk-localization: only compares per-degree Ext for two coherent sheaves, not a bounded-below second complex or a derived-object isomorphism.

lem-sfb-coherent-bounded-below-rhom-stalk vs lem-sc-derived-hom-finite-free-model: computes sheaf derived Hom by a finite-free resolution; no stalk comparison is stated.

lem-sfb-coherent-bounded-below-rhom-stalk vs lem-sc-bounded-hom-exact-columns: proves acyclicity of a Hom total complex from column exactness; no derived stalk comparison.

lem-sfb-coherent-bounded-below-rhom-stalk vs lem-sc-bounded-above-finite-free-hom-acyclic: proves acyclicity of a Hom complex against an acyclic complex, without a stalk assertion.

lem-sfb-coherent-bounded-below-rhom-stalk vs lem-sc-finite-free-internal-hom-exact: states exactness for a single finite-free sheaf; no derived comparison or stalk isomorphism.
