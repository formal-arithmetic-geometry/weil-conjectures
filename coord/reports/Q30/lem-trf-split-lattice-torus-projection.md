## Files written

- `dag/nodes/sec-trace-formula/lem-trf-split-lattice-torus-projection.json`: item, statement unchanged, now split into six steps; Mathlib searches found ingredients but no complete match.
- `citations.json`: one verbatim statement quotation for each of the 12 step citations.
- No new nodes or Mathlib leaves were created. `searches.jsonl` records five actual searches made for the item; previous recorded searches were retained.

## Attachments

None. Searches for the exact blueprint tag and for split lattice / torus terminology in the project's `lean/WeilConjectures/` found no declaration stating all clauses. The surrounding `lean/Sheaf/AlgebraicGeometry/ToricRealizationFiniteType.lean` is a larger theorem with a sorry and is not an attachment for this item.

## WANTED

None. I read the local ILO PDF through a text extraction in the sandbox and the local Stacks TeX sources.

## What changed and what was wrong

The item was statement-only with no Lean audit and no existing sandbox split. The statement is true as written and was retained. I reused `lem-trf-lattice-torus-coordinates-action` for its unconditional coordinate/presentation assertions; the additional monoscheme assumptions apply to its action assertion and are not required here. This avoided a duplicate Laurent-presentation node. I reused `lem-trf-monoid-algebra-domain-fraction` for the domain assertion and `lem-trf-geometrically-reduced-base-change` for arbitrary reduced algebras, rather than duplicating either. The scheme conclusion uses the existing Mathlib leaf `lem-weil-pbc-affine-scheme-reduced-iff`.

The imported ancestor reference is historical: the latest blueprint's `lem-trf-local-term-locality.proof.md` uses contracting correspondences and does not contain the earlier alteration branch. I read it and the latest unit `_section.md`; this delivery proves the assigned existing auxiliary algebraic geometry statement and changes no chapter, unit statement or route. The item is not the unit's key node, so no unit realization record was written.

The source ILO VIII 3.2.12(i), p.104, calls smoothness obvious. I supplied the unit-lifting calculation, rather than treating that word as a proof. In particular I avoided an invalid shortcut: for a test map from an affine thickening to an arbitrary nonaffine Y one cannot assume it factors through one affine chart of Y. The proof instead lifts its map to the affine k-scheme T globally and pairs it with the already specified map to Y. The finite-presentation assertion comes separately from the coordinate node.

## Not duplicates

No new nodes. Whole-DAG title/statement searches for Laurent rings, group algebras, smooth polynomial/localization maps and reduced affine spectra located the four existing results used here. `tools/blueprint_refs.py search` was run for torus, group algebra, Laurent, smooth polynomial, split lattice and geometrically reduced; none states the complete item. Blueprint matches such as `def-sc-gm-ga` define the rank-one group rather than this arbitrary-rank projection and reduced-product result. The existing perfect-field geometric-reducedness theorem would not cover arbitrary fields and was not used. Dependency-closure searches confirmed that none of the four result nodes cited reaches this item.

## Review by Q30

I checked B--E with the item, its cited statements and the sources open. I read ILO VIII 3.2.12(i), printed p.104, including the assertion that a smooth monoscheme morphism realizes to a smooth scheme morphism, and 3.2.19, p.106, where the smooth torus action is used. Those explain the intended torus input; the explicit square-zero argument is my expansion, so the proof is honestly marked agent-origin. I also read Stacks `more-morphisms.tex`, Tag 02H0 (`definition-formally-smooth`), `algebra.tex`, Tag 034N (`lemma-geometrically-reduced-any-reduced-base-change`), and `schemes.tex`, Tag 01J2 (`lemma-affine-reduced`). No SGA route is used.

Step 1 takes exactly the finite-basis coordinate identification, arbitrary-Y affine pullback charts and local finite presentation from `lem-trf-lattice-torus-coordinates-action`. I read its complete statement: its first and last assertions do introduce just k and L, and its affine-chart clause explicitly identifies the inverse images under the projection, so no affine-fibre-product theorem is being silently taken from a mere definition.

Step 2 uses the square-zero affine model explicitly stated by `def-sbc-first-order-thickening`, the affine ring-map correspondence of `def-weil-affine-spectrum`, the pairing universal property of `def-pc-fibre-product`, and the lifting-plus-finite-presentation definition of `def-sbc-smooth-morphisms`. The actual lifting is written out: if v w = 1+d with d in I and I squared zero, the corrected inverse is w(1-d). Images of the basis therefore lift to units, and the basis-coordinate formula gives the whole algebra homomorphism, including negative powers. This is an elementary calculation from the definitions, not an uncited formal smoothness theorem. Its map is over k because B has the k-algebra structure induced by the prescribed map to Y. Pairing then makes it over Y.

Step 3 uses only the two universal-property definitions just read. The augmentation is explicitly multiplicative, and the composite of its section with the projection is the identity. Thus surjectivity is pointwise even for reducible or empty Y, and smoothness of T follows by choosing the one-point base.

Step 4 uses the generators and balanced-tensor universal property stated in `def-weil-pbc-module-tensor-product`. I checked both inverse formulas, the orientation A tensor K, the K-algebra structure on its second factor, and multiplication on pure tensors. Finite support makes both displayed sums legitimate. This is an explicit elementary generator calculation.

Step 5 applies the statement of `lem-trf-monoid-algebra-domain-fraction`, not a fact hidden in its proof: choose Q to be the monoid generated by the given basis; it is finitely generated, generates L as a group, and L is torsion-free. The node's statement explicitly says that the group algebra is a domain, over any field, so apply it with K as coefficient field. A nilpotent in a domain is zero by induction on its nilpotence exponent. The hypothesis of `lem-trf-geometrically-reduced-base-change` is then exactly Step 4 plus that domain conclusion for EVERY field extension, not just algebraic extensions. Its conclusion explicitly permits arbitrary reduced R, including zero. I read the whole statement and local Stacks proof; no finiteness is smuggled in.

Step 6 uses both directions of the ring/affine-scheme reducedness equivalence explicitly stated by `lem-weil-pbc-affine-scheme-reduced-iff` (Mathlib Properties.lean:122, also read), together with the sections/local-ring characterization in `def-pc-reduced-scheme`. The affine opens are precisely those provided in Step 1; local rings on them are the local rings on the product. It does not assume Y affine or its affine-open intersections affine.

I tested r=0 (A=k, projection the identity), R=0 (zero tensor and empty spectrum), Y empty, and a reducible reduced base such as k[x,y]/(xy). The field K may be transcendental or inseparable over k: the torsion-free monoid-algebra domain input has no separability assumption. The inverse-unit computation holds in characteristic two as well, since (1+d)(1-d)=1-d squared in all characteristics. No new statement needs testing and no clause is relocated into a new node. Every step is shorter than 2000 characters. All citation quotes are copied verbatim from the cited statements; none refers to a proof in place of its conclusion.

The five new Mathlib searches were actually run through msearch.py and their returned records copied into the node. I read the returned types and relevant Mathlib sources: LaurentPolynomial.isLocalization handles one variable; generic standard-smooth and polynomial formal-smoothness results are ingredients; Algebra.IsGeometricallyReduced still uses algebraic-closure reducedness and has a TODO for arbitrary field extensions. None is a one-line match for the full item. No fabricated search or unavailable-service verdict is recorded.

## Unfinished work

None in the requested stage-1 split. There is no Lean writing or compilation in this delivery.
