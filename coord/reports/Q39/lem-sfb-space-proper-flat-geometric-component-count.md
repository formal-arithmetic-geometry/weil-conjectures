# Stage-1 delivery: lem-sfb-space-proper-flat-geometric-component-count

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-flat-geometric-component-count.json: item, unchanged statement, six-step split.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-flat-proper-components-lower-semicontinuous.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-global-algebra-components.json: statement, unsplit, no Mathlib match.
- citations.json: verbatim statement quotes for every step/node citation.

Two new nodes; zero Mathlib leaves. No Lean or unit files written, and no compiler or build run.

## Attachments

None. Searched lean/WeilConjectures by the item's blueprint tag and proper/flat/reduced and geometric-component terminology. The hits concern schemes or different components, not this general algebraic-space result. Mathlib is likewise scheme-based in AlgebraicGeometry/Geometrically/Connected.lean (read its declarations). A source-only declaration with sorry would not qualify.

## WANTED

None. All mathematical sources used are in literature/stacks-project.

## Problems corrected in the split

The item was statement-only, not a proof. Its statement is correct and remains verbatim. I kept its maintained metadata, including the inherited null nearest-blueprint ancestor, unchanged. The item's blueprint.from.place already identifies its final geometric-component shrinking purpose. I read the latest blueprint's six-functor unit and direct-images proof; this is a foundational auxiliary input to that route, not an alternative route for its direct-image theorem. The stored unit has historical chapter/path differences from the latest blueprint; I did not edit it.

I initially searched for a separate h0 upper-semicontinuity node. The existing proper-flat-space derived-base-change theorem and perfect jump-loci theorem give that input directly, so I did not create it. Similarly the field-independence, connectedness criterion, and openness arguments are steps, not nodes. I did not replace algebraic spaces by schemes or assume that their fibres have dimension at most one.

## Searches and existing nodes

All new-node and current-item Mathlib searches were actually run through batch2/msearch.py. searches.jsonl and the per-node search-results.json files retain the returned results. Each retained new node has LeanFinder, Loogle, grep, LeanSearch, and a second semantic phrasing; every service answered. Read the returned scheme properness/finite-global-sections and topological/idempotent declarations. finite_appTop_of_universallyClosed (Mathlib/AlgebraicGeometry/Morphisms/Proper.lean:162) assumes an integral scheme and proves a finite ring map, not the algebraic-space decomposition; PrimeSpectrum.isIdempotentElemEquivClopens only treats the prime spectrum of a ring. Algebra.Etale.iff_exists_algEquiv_prod is an algebra statement and does not identify the geometric global algebra or its components. Thus these are not one-line matches.

Searched the whole DAG by tags 0E1E, 0E1D, 0E0R, 0DMY, 0A12, 0A13, 0A10 and by global sections, components, semicontinuity, Stein factorization, proper global functions and perfect complexes. Ran blueprint_refs.py searches on those tags and on component, global sections, global function, Artinian local, lower semicontinuous, upper semicontinuous. The last finds scheme semicontinuity; it is not the space statement. The scheme lower-semicontinuity node and scheme proper-reduced global-functions product node do not cover algebraic spaces. Reused the already-existing sepclosed-space components theorem, space proper-base-change, proper-flat-space derived-base-change, scheme perfect jump-loci, common field extension and point-open calculus. Read every cited statement rather than relying on its proof or title.

## Not duplicates

lem-sfb-space-proper-global-algebra-components vs lem-sfb-space-proper-connected-function-field: the existing node assumes reducedness and connected nonemptiness and concludes a single finite field; the new node handles arbitrary proper spaces, including disconnected and nonreduced ones, identifies the finite clopen component decomposition with local Artinian factors, and allows the empty space. Its full decomposition is not an application of that single-component theorem.

lem-sfb-space-proper-global-algebra-components vs lem-sfb-space-proper-field-global-functions: the existing node assumes geometric reducedness and geometric connectedness and concludes the scalar map is an isomorphism. The new node requires neither and gives all local Artinian component factors; the old statement cannot supply that decomposition.

lem-sfb-space-proper-global-algebra-components vs lem-sfb-space-proper-flat-geometric-component-count: the new node concerns one proper space over an arbitrary field, without flat families or local constancy; the item obtains local constancy by a separate semicontinuity argument. It is not a clause of the item restated as a family theorem.

lem-sfb-space-proper-global-algebra-components vs lem-sfb-smooth-space-proper-component-neighbourhood: the existing node constructs a proper smooth relative open neighbourhood of a given geometric component. The new node is a global-function algebra theorem over one field and constructs no neighbourhood.

lem-sfb-space-flat-proper-components-lower-semicontinuous vs lem-weil-pbc-flat-proper-component-count-lower-semicontinuous: the latter is explicitly for schemes; the new node allows non-schematic algebraic-space sources. The new result is only a one-sided inequality, valid even without geometric reducedness, so it does not restate the local-constancy item.

lem-sfb-space-proper-global-algebra-components vs lem-weil-pbc-proper-reduced-algclosed-global-sections-product: the existing node has a reduced scheme over an algebraically closed field. The new node includes algebraic spaces over arbitrary fields and the nonreduced Artinian factors.

## Source error

The local copy of Tag 0DMY, lemma-proper-geometrically-reduced-global-sections, clause (7), says geometrically reduced and connected implies A=k. This is false as printed: X=Spec L for a nontrivial finite separable extension L/k is connected, proper and geometrically reduced, but A=L. The printed proof also uses geometric irreducibility which connectedness alone does not supply. Our split uses only clauses (1)--(3), and over an algebraically closed field only the elementary fact that a finite field extension is that field. It never uses clause (7). The existing lem-sfb-space-proper-field-global-functions has the stronger, correct geometric connectedness hypothesis. No statement dispute affects this item and no statement correction is needed.

## Review by Q39

I read Stacks spaces-more-morphisms.tex Tag 0E1E, lemma-proper-flat-geom-red, its first lower-semicontinuity dependency Tag 0E1D, and the geometric count comparison Tag 0E1B. The item has exactly the hypotheses of 0E1E over a scheme target. The proof below follows the source's lower/upper argument, not the later finite-etale Stein theorem, which would be circular because its proof uses 0E1E.

For the new lower-semicontinuity node I read 0E1D's statement and full proof: proper geometric fibres have finitely many components; Stein splitting separates their pieces after an etale neighbourhood and flat finite presentation keeps each nonempty on an open. The statement does not require reduced fibres, nor a Noetherian target. It is strictly weaker than local constancy and is false with local constancy substituted (components can merge in a nonreduced special fibre), which explains its separate role. For the new global-algebra node I read spaces-over-fields.tex 0DMY(1)--(3) and its proof by finite global algebra, idempotents and Noetherian fibre topology. The new statement introduces k, X, A, the components and the precise meanings of local, Artinian and reduced, and has no proof hidden in its statement. The clopen component structures use the existing open-subspace definition. Its algebraically closed specialization is exactly what 0E1E uses on a geometric fibre.

Step 1 uses the common-extension field statement (it gives embeddings over k), the algebraic-closure definition (including existence), the fibre-product theorem (its categorical universal property gives the scalar-extension identification), and the separably-closed-space theorem (it explicitly gives component bijections for arbitrary field extensions). Algebraically closed fields are separably closed, and we use no finite-type hypothesis here. This proves the arbitrary-algebraically-closed-extension clause, not just uniqueness up to algebraic closure isomorphism.

Step 2 uses space proper-base-change, whose statement really allows arbitrary algebraic-space base change, followed by the new global-algebra statement's reduced algebraically closed clause. The item supplies reducedness on every geometric fibre; we do not infer reducedness merely from flatness. Finiteness and the equality of the vector-space dimension with the component count are explicit in the cited statement. The empty product is the zero ring, so no nonemptiness was silently imposed.

Step 3 uses the existing proper-flat-space derived-base-change theorem. I read its whole statement: it produces a perfect Zariski complex and gives its canonical derived comparison for every scheme base change, including residue fields and algebraically closed fields. O_Y is finitely presented as a module over itself and quasi-coherent; its relative flatness is precisely the assumed flatness of h. Reading spaces-perfect.tex Tag 0CTM and the proof of 0E0R confirms that there is no dimension or Noetherian assumption. Its degree-zero interpretation follows directly from the kernel at degree zero in a nonnegative resolution, not from an unjustified underived cohomology-and-base-change assertion. The perfect-complex definition explicitly supplies the bounded finite-projective local model used for finiteness over a field.

Step 4 uses lem-sc-perfect-jump-loci, whose statement gives both upper semicontinuity and arbitrary-base-change invariance for perfect complexes, and the new lower-semicontinuity node, whose statement gives exactly the opposite local inequality. I read perfect.tex Tag 0BDI, lemma-jump-loci, including its finite-free local proof. Steps 2 and 3 identify their functions before combining the inequalities. The open upper bound is the strict sublevel beta_0<n(t)+1, so it works at n(t)=0 as well. Intersecting the two opens is elementary and needs no new node.

Step 5 uses the existing sepclosed-space component statement for extensions of the chosen algebraic closure, common extensions for an arbitrary L/k, and lem-a1-space-point-open-calculus. I read the last statement: it asserts continuity for every space morphism and the exact fibre-product point-image formula, which yields surjectivity of field projections. Thus no definition node is used as if it proved continuity or surjectivity. Connected images follow by pulling back a separation, written explicitly. This agrees with spaces-over-fields.tex Tags 0A10 and 0A13, whose statements and proofs I read, but the step cites the actual supporting nodes instead of silently importing those tags. Step 6 is the elementary union-of-constant-neighbourhoods argument, after identifying the locus with n=1.

I tested both new statements and the assembly on the empty space, a single geometric point, a disjoint union of r proper reduced connected pieces, a finite separable field spectrum, and Spec(k[epsilon]/epsilon^2). The last has one component and a two-dimensional global algebra: the global-algebra node permits it but correctly withholds the reduced dimension=count clause. For a nontrivial finite separable extension, geometric component count is its degree although the original field spectrum is connected. This checks that geometric rather than ordinary connectedness is used. No surjectivity of h, nonempty base, smoothness, or scheme representation was added. All non-elementary steps have their supporting statements named; none exceeds 2000 characters. New nodes are statement-only, have sources with tags and labels, genuine logged searches and complete blueprint.from.place/same_as fields. I checked the cited dependency closures contain no path back to the item. Generic off-unit uses are declared in split_report.tool_uses; no maintained tool_uses or reviewed field was set.

## Unfinished work

No part of the one-level split is unfinished. The two new statement-only nodes intentionally enter the stage-1 queue, as required by the brief.
