## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedUnionPushout` states both clauses of
`lem-trf-closed-union-pushout`. It adds no definitions. The two named theorems have
`sorry` as their entire proof and docstrings containing the corresponding natural-language
proof. The source read was Stacks Project `morphisms.tex`, Tag 0C4J,
`lemma-scheme-theoretic-union`, including its affine exact sequence and its mapping-property
proof (local lines 554 onward). The node's five proof steps were read in full.

Hypothesis and conclusion correspondence:

- A scheme X and two closed subschemes are `{X Y Z : Scheme.{u}}`, `i : Y ⟶ X`,
  `j : Z ⟶ X`, `[IsClosedImmersion i]`, `[IsClosedImmersion j]`. No further
  hypotheses on the schemes or immersions are imposed.
- The scheme-theoretic union W is exactly `(i.ker ⊓ j.ker).subscheme`. These are the
  kernel ideal-sheaf data of the recorded closed immersions, their intersection, and
  the existing ideal-sheaf subscheme construction, as in the recorded union theorem.
  Its map to X is `(i.ker ⊓ j.ker).subschemeι`.
- The inclusions a and b into W are existentially supplied with the two factorization
  equations `a ≫ ...subschemeι = i` and `b ≫ ...subschemeι = j`. These equations
  specify them uniquely because the subscheme inclusion is mono. They are consequently
  the same canonical inclusions supplied by `scheme_theoretic_union`, rather than
  arbitrary arrows. They are closed immersions by cancellation of closed immersions
  from their composites i and j; the dependency already supplies this property.
- E is the chosen `pullback i j`, with its recorded projections `pullback.fst i j`
  and `pullback.snd i j`; this is the scheme-theoretic intersection, including its
  possibly nonreduced scheme structure.
- The pushout assertion is
  `IsPushout (pullback.fst i j) (pullback.snd i j) a b`. Its definition includes the
  commutative square and an `IsColimit` for the span's pushout cocone.
- The explicit extension clause for every target scheme T is exactly the universal
  property in that `IsColimit`: its `desc` gives the extension of compatible f and g,
  `fac` gives both restriction equations, and `uniq` gives uniqueness. The target is
  unrestricted in `Scheme.{u}`, not assumed affine. No chosen global pushout instance
  or arbitrary map to T is added as a hypothesis.
- The affine identity is the second declaration,
  `CommRingCat.isPullback_quotient_inf_sup`. Its four maps are
  `CommRingCat.ofHom (Ideal.Quotient.factor ...)`, respectively induced by
  `I ⊓ J ≤ I`, `I ⊓ J ≤ J`, `I ≤ I ⊔ J`, `J ≤ I ⊔ J`.
  Their domains and codomains are precisely R/(I intersect J), R/I, R/J, and
  R/(I+J). Here `⊔` is the sum of ideals. `IsPullback` asserts the canonical
  isomorphism to the fibre product with both projections specified. This gives the
  ring identity including its maps, rather than an arbitrary abstract ring isomorphism.
  For an affine open U of X take R = Gamma(X,U), I = i.ker.ideal U,
  J = j.ker.ideal U; `IdealSheafData.ideal_inf` identifies the union ideal.
  Quantification over all commutative rings and ideals is equivalent to this affine
  clause: any R,I,J arise from X = Spec R and its two quotient closed subschemes.
- The final sentence imposing no reducedness, Noetherianity or separatedness is
  respected: none occurs in either signature. There is no nontrivial-ring or
  nonempty-scheme assumption. The universe u is explicitly declared and arbitrary.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.SchemeTheoreticUnion`:
  `AlgebraicGeometry.scheme_theoretic_union`, with the exact kernel-infimum subscheme,
  affine quotient charts, and the factorizations through its canonical inclusion.
  This module is publicly imported and its existing constructions are used verbatim.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, with the scheme
  pullback instance from publicly imported `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.IsColimit`,
  as used by `CategoryTheory.IsPushout` from the publicly imported
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`.
- `Mathlib.RingTheory.Ideal.Quotient.Defs`: `Ideal.Quotient.factor` gives all four
  canonical ring maps without new helper definitions.

The proof imports are `Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout`
(`AlgebraicGeometry.isPushout_spec_pullbackCone_of_surjective`),
`Mathlib.AlgebraicGeometry.AffineScheme` (`Scheme.isBasis_affineOpens`), and
`Mathlib.AlgebraicGeometry.Gluing` (`Scheme.Cover.glueMorphisms`). The remaining
recorded proof dependencies (closed immersions, union, scheme pullbacks, affine
pullback spectra, Spec and colimit) are already in the public statement imports.
No recorded proof dependency with an available module is omitted.

Edge cases checked mathematically before writing:

- R the zero ring, hence all four spectra empty: the same quotient square and the
  unique maps from the empty schemes satisfy the stated universal property.
- J = top, so Z is empty: W = Y and E is empty; the quotient pullback is R/I.
- I = J: E and W identify with the same closed subscheme; the pushout is along
  identities and the ring pullback is the diagonal copy of R/I.
- I = bottom: Y = X, W = X and E = Z, giving the identity-side pushout.
- Disjoint supports, for example (2),(3) in the integers: the intersection scheme
  is empty and the matching-pairs ring is the product; no disjointness is assumed.
- Nonreduced example k[e]/(e^3) with ideals (e),(e^2): the union retains the
  (e^2) quotient. No radical is inserted and no reduced structure is substituted.
- Nonseparated X is allowed: the proof covers intersections of affine opens by
  smaller affine opens and never assumes that an affine-open intersection is affine.

Searches actually run on 2026-10-24:

- `msearch.py ... leanfinder` query "A scheme theoretic union of two closed
  subschemes is their categorical pushout over their intersection": eight hits,
  including coproduct, open-gluing, ideal-support and open-intersection statements;
  none gives this closed-union theorem.
- `msearch.py ... loogle` query `"IsPushout", AlgebraicGeometry.IsClosedImmersion`:
  zero hits.
- `msearch.py ... grep` query
  `scheme.?[Tt]heoretic.?[Uu]nion|[Uu]nion.*[Pp]ushout|[Pp]ushout.*[Uu]nion`
  in Mathlib/AlgebraicGeometry: zero hits.
- `msearch.py ... leansearch` query "The scheme theoretic union of two closed
  subschemes is the pushout along their intersection": eight hits. They concern
  open intersections, coproducts, gluing, ring pushout generators and vanishing
  ideals, not closed-union pushouts.
- A further `leanfinder` query "The canonical square R/(I intersection J), R/I,
  R/J, R/(I plus J) is a pullback of commutative rings": eight hits, including
  `Ideal.quotientInfEquivQuotientProd` and its projection formulas. These require
  coprime ideals and give a product, whereas this node allows arbitrary I,J and
  requires the fibre product over R/(I+J). The returned signatures and the source
  in `Ideal/Quotient/Operations.lean` were read.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` with the union/pushout
  patterns found the existing union theorem, generic ring pushout results, and
  downstream proof-plan mentions. No theorem already states this item. The
  prescribed blueprint-id search in `lean/WeilConjectures` returned no matches.
  Further `rg` searches for quotient-infimum pullbacks and the proposed names in
  Mathlib, the two project roots, and `dag/lean_names_upstream.json` found no exact
  existing declaration. The two declaration names are fresh.

No new nodes, dependency repairs, statement changes or statement disputes are needed.
The node copy changes only `lean`. The file compiled cleanly through the prescribed
`scompile.py`, both as sandbox and as library module (about 1.3 and 1.4 seconds).

## Second reading by Q11

Author's second reading under the dispatcher direct-delivery brief; no independent
worker was started. The maintainer supplies the independent review.

Reopened the node and the completed file. The two closed-immersion instance binders
match exactly the two closed-subscheme hypotheses. The infimum of the actual kernels
matches the scheme-theoretic union; the chosen scheme pullback matches the intersection.
The equations specifying a and b prevent replacement by another cocone. Reading the
Mathlib `IsPushout` and `IsColimit` definitions verifies commutativity, existence of
extensions to every target scheme, both restriction equations, and uniqueness.
The second theorem includes all four canonical quotient maps and the sum ideal in
the common target, so it expresses exactly the displayed affine identity, without
assuming coprimality. Checked that arbitrary R,I,J are realized by affine closed
subschemes and thus do not strengthen the mathematical assertion. Checked all universes
and variables are explicit, both proofs are only `sorry`, both source/proof docstrings
carry the node id, and all lines have at most 100 characters. No mismatch was found
and no correction of the natural-language statement was made.
