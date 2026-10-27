## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-linearized-line-sections-coaction.json`: statement item, now split; Mathlib searches found no theorem constructing this relative section coaction. No new nodes and no new Mathlib leaves.
- `citations.json`: thirteen verbatim statement quotations covering every use in the seven proof steps.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log.

## Attachments

None. The project source search for the exact blueprint tag, linearized invertible/line sheaves, and coactions found no declaration with every clause of this item. Existing affine-flat-descent coactions concern different objects. No Lean was written or compiled.

## WANTED

None. The substantive external input is already present as Stacks Tag 02KH, `coherent.tex`, label `lemma-flat-base-change-cohomology`, and the existing DAG node `lem-pc-flat-base-change-cohom`. The remaining argument is explicitly agent-written from the action and linearization identities in the item; it is not attributed to a nonexistent equivariant statement of 02KH.

## Corrections and route

The original item was statement-only, with no Lean audit attachment. Its mathematical statement is retained. I removed the reference `[def-sc-gm-ga]` and its statement dependency: that node defines multiplicative groups over a field, whereas this item works over an arbitrary ring and already fully specifies its relative torus by a Laurent basis and Hopf maps. This is citation cleanup, not a change of hypotheses or conclusion. All other imported fields and the inherited blueprint ancestry are retained.

The chapter and unit records and their latest blueprint counterparts were read. This is a supporting algebraic-geometric input in the inherited relative torus/projective-embedding chain, not the key statement of its six-functor unit, so no unit record was written. `blueprint_refs.py ancestor` reports `None` for this existing created-node chain; I retained its inherited `from.node`, place and via rather than manufacturing a blueprint origin. Whole-blueprint searches for `linearized` and `coaction` found only unrelated linearized-adjunction definitions and no equivalent statement. The existing flat-base-change theorem is reused as a generic tool, not replaced or copied into a new node.

## Unfinished work

None in the stage-1 split. There are no new statement-only obligations. This report does not assert a Lean proof of the item.

## Review by Q38

I read the item, its parent projective-embedding statement, the chapter and unit route, Stacks `coherent.tex` at 02KH including its hypotheses and degree-zero conclusion, and the full statements of every cited node. I also read `schemes.tex` at 01KK/01K7 (the separated-implies-quasi-separated paragraph) and `morphisms.tex` at 01U5, label `lemma-flat-characterize`. Those are the sources for the two auxiliary geometric implications. There are no new nodes requiring separate sources or duplicate comparisons. I checked delivery-errors B through E, including both copies of those sections in the file.

Step 1 uses `def-weil-finite-type-morphism` for quasi-compactness and `lem-pc-separated-quasi-separated` for quasi-separatedness of f, exactly as those statements say. `def-sc-invertible-module` explicitly includes quasi-coherence, rather than merely defining a tensor inverse. The Laurent and double-Laurent bases are part of the item's explicit data; the direct-sum calculation written in this step proves their module flatness using the injectivity definition in `def-weil-pbc-flat-ring-map`. `lem-weil-pbc-flat-ring-map-iff-flat-affine` then supplies flatness of Spec C and Spec(C tensor C) over S. No Noetherian or field assumption occurs in either implication.

Step 2 uses the unit and functorial pullback in `def-pc-module-pullback` to define beta on pure tensors. The full statement of `lem-pc-flat-base-change-cohom` covers an arbitrary quasi-coherent sheaf and qcqs morphism and includes the affine-base formula in every degree; at degree zero it supplies exactly beta_C and beta_D. I did not use the structure-sheaf-only node `lem-weil-pbc-flat-base-change-global-sections-qcqs`, which would not cover L. `def-pc-fibre-product` supplies induced maps after changes of rings. Naturality of the displayed beta is proved on s tensor b in the step, including for nonflat target algebras; no nonflat section-comparison is inverted.

Step 3 uses the universal property in `def-pc-fibre-product` to define b and q, and composition of module pullbacks in `def-pc-module-pullback` to type b*theta as q*L -> p*L. In particular using theta on a* sections without the inverse action would give the wrong normalization. I checked a b = p and p b = q by the given scheme-action identities. The actual section K(s), and hence c, is constructed here rather than hidden in an existence node.

Step 4 again uses the functorial module pullback statement. Pulling back beta_C(c(s)) along the morphism induced by ev_g gives the claimed equality in Gamma(X_B,L_B). The calculation gives equality of sheaf sections, even over nonreduced rings; it does not test equality only at geometric points. This proves the normalization for every B without assuming beta_B is injective or surjective.

Step 5 is direct substitution into the item's cocycle, with the necessary pullback compositions supplied by `def-pc-module-pullback`. The substitution y = h^{-1}g^{-1}x produces exactly the two factors in g acting on h acting on a section. The action is B-linear because the scheme automorphisms are over Spec B and theta is a module morphism. This is an explicit computation for arbitrary sections, not a new theorem imported without citation.

Step 6 writes both tensor maps as finite sums and evaluates at the universal pair over D, not at an arbitrary collection of rational points. The normalization from Step 4 identifies those sums with the sections in the cocycle computation. The sole additional use, `lem-pc-flat-base-change-cohom`, supplies injectivity of beta_D, already established in Step 2 with verified flatness. Thus equality of sections really implies the tensor equality. Step 7 substitutes the identity and a pure Laurent weight into the already proved normalization. It needs no additional node.

The elementary steps are explicit constructions, substitutions or finite tensor sums; none appeals to a hidden standard comparison lemma. Every step is shorter than 2000 characters. I checked the zero ring, empty X, rank r = 0, and a trivial torus action with a linearization character chi: the construction gives c(s) = s tensor chi, confirming the sign. The argument also works for an infinite section module and nilpotents. Disconnected X and arbitrary nonflat B require no changes. This checks E1/E4 as well as the normalization. No statement dispute was found.

Searches used the required msearch command for LeanFinder, Loogle, grep and LeanSearch, followed by a second LeanFinder phrasing. I read the returned types: LaurentPolynomial Hopf/comultiplication declarations assert coordinate algebra identities, and section/tilde declarations assert basic sheaf constructions. Neither constructs a coaction from a linearized sheaf. The prior searches already on the live item are retained, and the new searches are recorded verbatim from the command log. There is no new node that duplicates an elementary proof step, the item, a blueprint node, or an existing theorem.
