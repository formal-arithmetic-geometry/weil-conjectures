# Stage-1 report: lem-sfb-infinitesimal-isogeny-unipotence-reflection

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-infinitesimal-isogeny-unipotence-reflection.json`: statement item, split; Mathlib searches found no matching theorem. Statement and statement dependencies retained.
- `citations.json`: one verbatim full-statement quotation for each dependency of each numbered proof step.
- `report.md`: this report. `searches.jsonl` is the search command's unedited log; `milne.txt` is a sandbox-only extraction for reading the source.

## New nodes

None. Zero new nodes and zero Mathlib leaves. The existing Jordan matrix theorem, rational-point reconstruction, faithful representation, affine scalar-extension results, and geometric unitriangular embedding criterion suffice. In particular I did not create a node restating reflection or one of its clauses.

## Attachments

None. Searches for the exact blueprint tag and for infinitesimal isogeny, unipotence, and Jordan decomposition in `lean/WeilConjectures/` found no declaration stating the item. The unipotent biproduct and Weil-complex occurrences are unrelated.

## WANTED

None for this split. Milne's book is available locally. WANTED material named far above this item in the inherited blueprint provenance is not used here.

## Errors and changes

No statement dispute or source error was found. The original statement is kept, including the arbitrary base field and the finite faithfully flat radicial hypothesis. The proof actually needs only geometric-point injectivity of the homomorphism, besides smoothness and finite type of the source and the target's stated embedding. This proves the given statement without changing it. Connectedness and smoothness of the target are harmless unused hypotheses.

The node previously had no proof. I filled its four proof steps, proof dependency union, origin, split report, and appended the actual searches from this group's log. Existing provenance and prior search records are retained. The blueprint's current direct-image proof provides only the ancestor context; the inherited group-theoretic subproblem is resolved along the Milne route already specified in this item's source. `blueprint_refs.py ancestor` reports a null nearest imported ancestor, which is retained rather than invented.

## Searches and reuse

I searched the whole DAG for Jordan decomposition, Milne 9.18, 14.5, 14.9, 14.12, geometric unipotence and related phrases, and read the candidate statements and their dependencies. `tools/blueprint_refs.py search 'unipotent'` found only the unrelated finite local-system Sylow/trace node. The searches for Jordan and infinitesimal isogeny also found no blueprint counterpart to this item. No new node was needed, so no duplicate-tag pair arises.

For the item, the prescribed `msearch.py` calls ran LeanFinder twice with different formulations, LeanSearch, Loogle, and a source grep. Their exact query strings and returned names are in `searches.jsonl` and appended to `mathlib_searches`. The hits concerned formally unramified morphisms, an elliptic-curve point injection, abstract group facts, or biproduct matrices, not unipotent affine group schemes. I read the biproduct declarations at Mathlib/CategoryTheory/Preadditive/Biproducts.lean:740--762 and the field-point SL subgroup at Mathlib/LinearAlgebra/Projectivization/PSL/Stabilizer.lean:31--48; neither supplies this statement. The prior searches stored on the live item were read and retained.

## Not duplicates

No new nodes, so there are no new/existing pairs to distinguish.

## Review by Q102

I read Milne, Algebraic Groups, Proposition 17.81 and its isogeny paragraph on printed pp.378--379; Theorem 9.18 and paragraphs 9.19--9.21 on pp.170--171; and Theorem 14.5, Corollaries 14.9--14.12 on pp.281--283 in the locally supplied PDF. Theorem 9.18's proof explicitly constructs group points from the families of matrix Jordan factors using Theorem 9.2. Corollary 14.12 is exactly the smooth geometric-point test required at the end. No SGA route is used. There are no new nodes requiring additional sources.

Step 1 uses `lem-sfb-affine-group-faithful-linear-representation` for a positive-dimensional faithful closed representation over k. Its statement explicitly includes injectivity on all algebra-valued points and on scalar extensions; I verified that this is stronger than injection on geometric points. `lem-weil-pbc-fibre-product-affine-spectra` states the coordinate tensor formula and affineness, and `lem-weil-pbc-algebra-tensor-pushout-universal-property` states existence and uniqueness of tensor algebra maps. These give the identification of K-algebra-valued points and finite algebra generators in a few lines. The target embedding is an assumption unpacked from the item's own definition of unipotence. Radicial injectivity is used only on K-valued points, directly under the item's stated meaning. This avoids requiring a theorem that radicial morphisms are closed immersions (which would be false).

Step 2 uses the actual statement of `lem-sfb-multiplicative-jordan-linear-compatibility`, not a presumed theorem about closed subgroups: it supplies invertible unipotent factors, compatibility with intertwiners and tensor products, and uniqueness. I checked every hypothesis of `lem-sfb-tannaka-rational-point-reconstruction`: K is algebraically closed, G_K is affine of finite type by Step 1, the family consists of invertible maps on all finite-dimensional rational representations, it is natural on every equivariant linear map, multiplicative for tensor products, and identity on the trivial representation. The zero representation is explicitly allowed by both nodes. Consequently reconstruction really supplies a point h of G_K; matrix decomposition alone would not justify that assertion.

Step 3 uses only the matrix theorem's uniqueness clause beyond the previous step and the assumptions. I expanded strict-upper-triangular nilpotence by increasing index chains, including n=1. Since j_K F(g) is already unipotent, its unipotent factor equals itself. The identity in the composite representation therefore gives equality after j_K, then after F, and finally h=g by the two injections. This is elementary assembly, not an uncited functorial Jordan decomposition theorem. In particular no semisimple-point lifting, torus lifting, or equivalence of isogenies with isomorphisms is asserted.

Step 4 takes the matrix unipotent-factor clause to deduce nilpotence of rho_K(g)-I. I checked the full statement of `lem-sfb-geometric-unipotence-unitriangular-embedding`: it assumes exactly a smooth affine finite-type group over k, a positive-dimensional representation injective on all algebra points, and nilpotence at every algebraic-closure point. All are now verified. Its statement explicitly concludes a closed immersion into the unitriangular group over k itself; hence no unsupported descent of a geometric flag is hidden in the last step. Its dependency graph does not lead back through the item or its torus-free parent.

I checked B--E of delivery-errors.md against these files: the statement introduces its objects and retains its definition citations; there are no statement-only new nodes or possible restatements, no unlogged new search, no mismatched theorem quote, and no hidden non-elementary comparison. Every proof dependency has been read in its live JSON statement, and citations.json quotes those statements verbatim. The tensor algebra citations are Mathlib leaves; all other proof nodes are in the same unit, so no off-unit tool-use declaration is needed. All four steps are below 2000 characters.

For edge cases I checked the trivial group (choose the one-dimensional trivial faithful representation), n=1 (the target matrix is the identity), positive characteristic Frobenius on the additive group (radiciality does not mean a scheme isomorphism, but the proof only uses geometric injectivity), and imperfect fields (the argument applies decomposition only over the algebraic closure and uses the existing over-k criterion at the end). Dropping smoothness would make the statement false: in characteristic p, the radicial finite faithfully flat map mu_p to the trivial group has source not unipotent. The retained smoothness hypothesis is thus essential to the last cited criterion. No correction of the item was necessary.

## Unfinished work

None in the mathematical split. Final delivery status is determined by the required server dry run and push.
