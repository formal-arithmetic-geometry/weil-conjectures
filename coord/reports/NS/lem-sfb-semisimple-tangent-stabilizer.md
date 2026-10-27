# Stage-1 delivery: lem-sfb-semisimple-tangent-stabilizer

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semisimple-tangent-stabilizer.json: statement split in seven steps; Mathlib verdict no match; no new nodes and no Mathlib leaves.
- citations.json: one entry for every node citation in every proof step, quoting the cited statement verbatim.
- searches.jsonl: five searches run through the required msearch.py command. The existing five item-search records were retained in substance and refreshed with the actual NS search responses.
- report.md: this report.

The sandbox contained only dispatcher marker files, with no previous item, proof, report or search log to preserve. I started from the live item. Statement and stmt_deps are unchanged. I did not edit Lean, run a compiler or build tool, write to the shared repository, run git there, or start agents.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag, semisimplicity, tangent stabilizers and relevant group/Lie files found no declaration proving every clause. The available Lie and tangent declarations do not supply smoothness of this stabilizer. The existing general dual-number and Lie-functor nodes are cited rather than treated as completed attachments.

## WANTED

None. The proof source is the locally available literature/milne-algebraic-groups_iAG2017.pdf, Proposition 17.76, printed p.377, with its reference to Lemma 13.6, printed p.256, and Sections 10.14, 10.19--10.23, printed pp.190--193.

## Problems found and changes

The item had no proof. Milne's phrase about modifying 13.6 is not a complete proof by itself; the existing lem-sfb-semisimple-derivation-zero-smooth already states precisely the general smoothness theorem needed for that modification, so I reused it. The work left in this item is the scheme-level construction and the verification of that theorem's hypotheses, rather than a new node restating smoothness of this same stabilizer.

Proposition 17.74 discusses perfect-field Jordan decomposition and its wording about arbitrary Lie representations is not needed here. Our proof diagonalizes only the matrix in the fixed faithful representation, exactly as the item assumes; it uses no Jordan decomposition over the original field and no claim about arbitrary abstract Lie representations. The spectrum of the explicit quotient represents the stabilizer for every test algebra, including nonreduced algebras.

The inherited blueprint ancestor is null. tools/blueprint_refs.py ancestor returned exactly `a node created for lem-sfb-semisimple-tangent-stabilizer has blueprint.from.node = None`; I preserved its null node and inherited via chain. Its from.place already specifies Milne 17.76. The current blueprint was read at literature/blueprint/latest/, including the six-functor stability unit. Searches for semisimple, tangent stabilizer, semisimple derivation and fixed subscheme found no blueprint equivalent. The item is a supporting node of the direct-image alteration chain, not the unit's key statement, so no unit realization was edited.

## Not duplicates

No new nodes are introduced. Whole-DAG searches by 17.76, semisimplicity, derivations and fixed-scheme smoothness located and opened the existing lem-sfb-semisimple-derivation-zero-smooth, lem-sfb-affine-group-dual-number-calculus, lem-sfb-affine-group-lie-tangent-calculus, lem-sfb-torus-fixed-scheme-smooth, lem-sfb-algebraic-lie-additive-jordan, and lem-sfb-infinite-field-semisimple-centralizer-reduction. The last node is a stronger conclusion under different hypotheses (an infinite field and existence of a noncentral geometric element), and is not used to prove this item. The derivation lemma is the generic prerequisite we actually use; its statement is not the stabilizer assertion.

## Review by NS

I read Milne 17.76 itself, its dual-number formula, the proof of 13.6 and its setup on pp.255--256, and the tangent/adjoint formulas in 10.14 and 10.19--10.23. For all cited nodes I opened the statement, checked it against the use below and copied that statement into citations.json. There are no new nodes requiring separate source or hypothesis review.

Step 1 uses def-sc-general-linear-group for the localized polynomial coordinate presentation and universal matrix, def-weil-closed-immersion for the quotient presentation and the resulting closed immersion, and def-weil-affine-spectrum for maps out of the quotient. These statements actually contain the coordinate presentation and affine quotient characterization. The given closed immersion makes the coordinate algebra a quotient of the indicated finitely generated algebra. Its quotient by the explicitly written commutator ideal is real data, with no representability theorem left implicit.

Step 2 uses lem-sfb-affine-group-dual-number-calculus: it explicitly states tangent injectivity for closed subgroups, arbitrary-R infinitesimal points and adjoint compatibility. lem-sfb-affine-group-lie-tangent-calculus explicitly gives the GL_n formula 1+delta M. I wrote out why injectivity survives extension to a possibly nonflat-looking test algebra: a linear left inverse over the field tensors to a left inverse over every algebra. Thus matrix fixedness is equivalent to tangent fixedness without restricting to field-valued points.

Step 3 uses the statement of lem-weil-pbc-fibre-product-affine-spectra, namely the product spectrum with its two coordinate inclusions, to evaluate the two universal points. def-weil-affine-spectrum turns their product into a morphism because it kills I; inverse and identity use the same explicit quotient factorization. def-sc-group-scheme-subgroup defines exactly the pointwise closed subgroup condition satisfied here. This is an elementary universal-point construction from these interfaces. The affine-product theorem is the only off-unit tool use, declared in split_report.tool_uses as required; it does not alter the unit route.

Step 4 uses the same two Lie-calculus statements to obtain an infinitesimal point of G itself with matrix 1+delta M. Hence conjugation is an actual automorphism of the base-changed G. Its coefficient is a derivation by multiplying (a+delta D(a))(b+delta D(b)); it has the displayed matrix values, and inverse determinant has derivative zero. Since these elements generate the coordinate algebra, the product rule proves equality of the derivation ideal with the commutator ideal. This checks the potentially missing defining-ideal stability argument rather than assuming ambient conjugation preserves G.

Step 5 has no external theorem hidden in it. Conjugating the universal matrix by a constant diagonalizing matrix gives eigenvector algebra generators, including an invariant inverse determinant. The product rule makes their monomials eigenvectors. Finite polynomial expressions show spanning by eigenvectors; the explicitly displayed finite interpolation polynomial proves directness. This verifies local finiteness and the direct-sum eigencondition on the actual coordinate quotient, not merely on a tangent representation. All its arguments are elementary algebra and linear algebra in the step, with no separate auxiliary lemma to extract.

Step 6 uses precisely the statement of lem-sfb-semisimple-derivation-zero-smooth: finite-type algebra with smooth spectrum, derivation geometrically decomposed as a direct sum of eigenspaces, ideal generated by its values, and smoothness of its zero scheme. The finite-type input is step 1, smoothness is a hypothesis of the item, and the remaining hypotheses are steps 4--5. Its statement explicitly allows imperfect fields and arbitrary characteristic, so no descent or perfectness hypothesis was silently added.

Step 7 uses subgroup tangent injectivity and membership of infinitesimal points from the dual-number calculus, and bracket preservation and the GL_n matrix bracket from the Lie-tangent calculus. The coefficient of epsilon in the commutator equation is written out. Injectivity identifies vanishing of this coefficient with [Y,X]=0, so the result is equality of the mapped tangent subspace, not just equality of dimensions.

I checked delivery-errors B--E point by point. There are no unsplit new nodes, missing new-node searches, fabricated search records, unsupported tag citations, off-route replacements, or dependencies taken from a cited proof instead of its statement. All statements needed by the steps exist and their quoted clauses match the uses. The abstract Mathlib centralizer/adjoint-centre/Cartan hits do not assert representability or scheme-theoretic smoothness, so they are not matches. Both semantic phrasings, Loogle, grep and LeanSearch actually ran and returned available responses.

Small cases checked: X=0 gives I=0, D=0, C=G and all of Lie(G); G=GL_1 gives the same conclusion for all X; diagonal M with repeated eigenvalues retains precisely the block centralizer; distinct eigenvalues in GL_n give the diagonal centralizer; in characteristic p, eigenvalue sums can vanish and are correctly grouped into the zero eigenspace without division by p. In characteristic 2 the minus signs in commutators change together and the coefficient argument still holds. For a subgroup with noncentral X the construction still uses its quotient algebra and imposes no centrality assumption. No connectedness is required of C. Smoothness of the ambient G is essential and is available. No step exceeds 2000 characters, and none transfers a clause of this item wholesale into a new node.

## Checks and unfinished work

Server-only srvcheck check_dag: OK, no finding introduced by the sandbox or on its nodes.
Server-only srvcheck review_split: PASS, 0 new nodes; informational note that the unit has no realization recorded yet.
The required deliver.py dry run and push follow this report. No mathematical work remains unfinished in this one-level split; its reused unsplit prerequisites remain independently assigned DAG items.
