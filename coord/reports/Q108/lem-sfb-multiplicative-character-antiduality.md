# Q108: lem-sfb-multiplicative-character-antiduality

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-multiplicative-character-antiduality.json — item, statement unchanged; seven-step split, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-geometrically-diagonal-coalgebra-separable-basis.json — statement-only coalgebra lemma, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-galois-hopf-algebra-descent.json — statement-only finite Galois Hopf descent, unsplit; no Mathlib match.
- citations.json — actual statements of every cited node, copied verbatim per proof step.

## Attachments

None. Searched lean/WeilConjectures for the item tag, multiplicative characters, antiduality, diagonalizable group schemes, group-like elements, Hopf ideals and Galois descent. The project has Hopf-ideal and matrix-descent work, but no declaration covering the item. The existing group-algebra group-like node already has its Mathlib match; it is reused without modification.

## WANTED

None. All mathematical sources used are in literature/milne-algebraic-groups_iAG2017.pdf.

## Corrections and scope

The item was statement-only; it contained no proof to retain. No repair note or earlier sandbox split existed. The statement is correct, including non-smooth multiplicative-type groups, and is unchanged. In particular it does not claim full faithfulness under arbitrary field extension: only geometric characters are unchanged and the Galois action is restricted.

The inherited blueprint ancestor is null. Running tools/blueprint_refs.py ancestor on the item explicitly returned None. Its inherited place and via still identify the direct-images proof (3) and the chain through the largest-subtorus lemma. The current literature/blueprint/latest direct-images proof was read; it retains direct-image stability in (3). The null ancestor is existing metadata, not a newly invented blueprint id. New nodes use exactly the ancestor result, extend the via list, and specify the precise Milne supporting argument. No unit file is changed; this item is not its unit's key statement.

## Not duplicates

lem-sfb-geometrically-diagonal-coalgebra-separable-basis vs lem-sfb-split-torus-subgroups-diagonalizable: the existing node classifies a subgroup over an algebraically closed field, whereas the new node descends a geometrically split coalgebra basis to the separable closure, without a Hopf algebra or finite-type hypothesis.

lem-sfb-geometrically-diagonal-coalgebra-separable-basis vs lem-sfb-group-algebra-group-like-basis: the existing node computes group-like elements of an already given group algebra. It does not produce group-like elements over a separable closure from geometric diagonalizability.

lem-sfb-geometrically-diagonal-coalgebra-separable-basis vs lem-sfb-comodule-finite-subrepresentation: finite-dimensional rational submodules are not the separable splitting of a geometrically diagonal coalgebra.

lem-sfb-galois-hopf-algebra-descent vs lem-sfb-galois-descent-affine-subgroups: subgroup descent inside an existing ambient group does not construct an arbitrary descended Hopf algebra or descend arbitrary equivariant Hopf maps.

lem-sfb-galois-hopf-algebra-descent vs lem-sc-matrix-descent-scalar-map-bijective: matrix conjugation forms are special algebras with a prescribed matrix realization; the new statement handles any commutative Hopf algebra with a finite Galois semilinear action.

lem-sfb-galois-hopf-algebra-descent vs lem-sfb-flat-affine-action-algebra-descent: the latter is quasi-coherent algebra descent on a quotient stack for a rational group-scheme action, not semilinear descent along a field extension.

lem-sfb-galois-hopf-algebra-descent vs lem-sfb-hopf-coaction-linearization: that node translates an action-groupoid linearization into a comodule structure. It does not make such data effective over the smaller field.

Neither new node restates a clause of the item: one is about arbitrary coalgebras and separable splitting, the other is general Hopf descent. The proof itself establishes the finite splitting field, character equivalence, invariant group-algebra construction, independence, immersion criterion and scalar-extension identities. The same Milne section is also cited by the item and several existing group-scheme nodes, but their specific assertions differ as described above.

## Review by Q108

I read the source in Milne, printed pp.230–240, particularly the character/group-like dictionary, Lemma 12.4, Theorems 12.8 and 12.9, Theorem 12.18(c)–(d), Corollary 12.19, and the construction and proof of Theorem 12.23. I also read Appendix A.64–A.66 on printed pp.580–581. The first new node isolates the coalgebra content of 12.18(c)–(d): a geometrically diagonal coalgebra has finite-dimensional subcoalgebras whose duals are finite étale algebras, hence these split over a separable closure. This argument is not a claim that the base field is perfect. The second new node is the explicit Hopf consequence of A.64, including its fully faithful descent of morphisms; its finite-generation clause follows by expressing finitely many algebra generators in scalar-extended invariant elements. Both new nodes are self-contained statements, with no proof steps or hidden proof in the statements.

For step 1 I opened the existing affine-group-coordinate-Hopf node, the affine-spectrum node and G_m definition. The first states the actual counit and antipode identities; the second states the full spectrum Hom bijection, not merely faithfulness; the third gives the Laurent coordinate group. The proof checks invertibility and both directions of the character dictionary by these equations.

For step 2 I opened split-torus-subgroups-diagonalizable and verified that its algebraically closed field hypothesis is satisfied over bar k. Its statement supplies the group algebra with its Hopf operations, which gives the geometric coalgebra hypothesis of the new separable-basis node. The new node supplies an actual basis over k^s. The Hopf node supplies closure under inversion via S. The finite generation of the character group and the finite coefficient field argument are written out, rather than cited from the proof of an existing node. In particular injectivity of the finite-stage map follows after scalar extension, while surjectivity uses the chosen polynomial expressions for the original finite algebra generators.

For step 3 I opened group-algebra-group-like-basis: it gives precisely that normalized group-like elements are basis symbols, for any field and any abelian group. This proves the formula for every Hopf map, not merely the endomorphisms of G_m. The spectrum Hom bijection then supplies the group homomorphism and all naturality formulas are explicit.

For step 4 the new descent node is used only after constructing the finite Galois action and checking its compatibility with all Hopf operations on ae_m. Its statement gives the invariant algebra, scalar-recovery isomorphism and finite generation. The affine-spectrum and closed-immersion definitions give the descended scheme and the closed embedding from a surjective group-algebra map. The finite quotient acting on M is justified from its finite generating set and open stabilizers, not asserted for an arbitrary infinitely generated module.

For step 5 the new descent node explicitly includes equivariant Hopf morphisms and full faithfulness. It therefore says what is needed to descend character homomorphisms and evaluation isomorphisms. Independence of L is checked over a compositum by an identity on indexed basis elements; uniqueness of descent supplies coherence, and the character labels remain fixed. No unsupported appeal to descent of geometric point maps is used (that would be wrong for mu_p).

For step 6 I opened the closed-immersion definition and checked that its affine equivalence is surjectivity of the coordinate map. Field extension detects this by a vector-space complement; the split map's image is computed as a basis span. Thus no assumption of smoothness or reducedness enters this clause.

For step 7 the same group-like node applies over K^s. The tensor identification is written with its inverse on basis symbols, and naturality is checked by e_n mapping to e_{f^*(n)}. The Galois compatibility follows by restricting conjugation on coefficients along the chosen compatible closures. This works for transcendental and purely inseparable K/k as well as separable extensions.

I checked delivery-errors B through E: all notions are defined inline or have actual definition nodes, all non-elementary supporting claims have cited statements, new nodes have statement-only status and real searches, no source is SGA, no inline lemma longer than 2000 characters is hidden (the longest step has 1514 characters). Whole-DAG statement searches and tools/blueprint_refs.py searches for multiplicative type, Galois descent, semilinear, coalgebra, Hopf and group-like found no duplicate theorem. I read every Mathlib search hit: group-like linear independence does not provide a separable-splitting theorem, separable polynomial splitting does not provide a coalgebra comparison, and fixed-field invariance does not descend general Hopf algebras. Search outputs are retained in search-results.jsonl, and the exact executed queries and outcomes are recorded in the nodes and searches.jsonl.

Small cases checked: C=0 (empty basis), C=k (one group-like element), M=0 (trivial group), M=Z (G_m), M=Z/n (mu_n), and mu_p in characteristic p. The latter has character group Z/p despite only one geometric rational point, so the proof consistently uses Hopf algebras, never point counts. The sign-action on Z over R gives the nonsplit norm-one torus and the invariant algebra construction; after extension to C its character group remains Z and only the action changes. Finite Galois descent allows L=k and infinite-dimensional L[M]; it never uses averaging by the order of the Galois group. These cases support all new hypotheses and preserve the source's intended scope.

## Unfinished work

The two new supporting nodes are intentionally unsplit, as required for a one-level split. No other mathematical part of the item is left out. Server dry-run and delivery results will be recorded below.

## Final citation check

The first server dry run passed at 341e7d5a7ca. I then added the existing Mathlib leaf lem-weil-pbc-finite-set-in-finite-galois-subextension to steps 2 and 4, after reading its full statement and Mathlib match. It explicitly gives the finite normal closure inside a Galois extension for any finite coefficient set. Here k^s/k is normal as well as separable algebraic: every conjugate of a separable algebraic element lies in the separably closed field k^s. Thus its hypotheses hold. This removes an implicit use of the normal-closure theorem, with no new node. citations.json was regenerated from the actual cited statements.
