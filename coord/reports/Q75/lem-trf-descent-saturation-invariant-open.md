## Worker report

The module Sheaf.AlgebraicGeometry.DescentSaturationInvariantOpen states
CategoryTheory.Over.DescentDatum.exists_descentDatum_saturation_open, with sorry.
It adds no definition and changes only the node's lean record. The live item has
a reviewed stage-1 split but no lean record or reviewed_lean record. No repair
note or returned Q75 delivery was present. The sandbox initially contained only
dispatcher markers, so this delivery was written afresh.

Hypothesis and conclusion correspondence:

- The affine schemes A and B are `{A B : Scheme.{u}} [IsAffine A] [IsAffine B]`.
- The morphism p is `(p : A ⟶ B)`; flatness and surjectivity are `[Flat p]`
  and `[Surjective p]`.
- Finite presentation is precisely `[LocallyOfFinitePresentation p]`,
  `[QuasiCompact p]`, and `[QuasiSeparated p]`, as the statement specifies.
- The scheme over A and its structure morphism π are `{V : Over A}` and
  `V.hom`; its underlying scheme is `V.left`.
- The original isomorphism over A ×_B A and its cocycle are
  `(D : Over.DescentDatum p V)`, the dependency's existing transport presentation.
  Its docstring explicitly identifies it with the usual isomorphism presentation
  by Yoneda; identity and inverses follow from the cocycle and invertibility.
- The affine open C is `(C : V.left.Opens) (_hC : IsAffineOpen C)`.
- The map r_C is the canonical `pullback.map` induced by `C.ι`, identity on A,
  and identity on B, followed by `D.toHom`. The latter is the V-component of
  the original isomorphism on V ×_B A, by its definition using universal transport.
- The open saturation with its open subscheme structure is `(W : V.left.Opens)`
  and `_hW : (W : Set V.left) = Set.range (...)`. Thus W is exactly the specified
  image, with the assumption that this image is open; it is not an arbitrary
  invariant open or an extra invariance assumption. The two `by simp` terms
  merely establish commutativity needed by the canonical fibre-product map.
- The restricted descent isomorphism and the same cocycle are expressed by
  `∃ E : Over.DescentDatum p (Over.mk (W.ι ≫ V.hom))`. This is the same recorded
  descent notion, so the isomorphism is over the double base and the cocycle is
  part of the datum. No new notion of descent or arbitrary substitute map is used.
- Every test scheme and maps a,b with equal composite to B appear explicitly as
  `∀ (Z : Scheme.{u}) (a b : Z ⟶ A) (h : a ≫ p = b ≫ p)`.
- A map v into W over a is the morphism
  `v : Over.mk a ⟶ Over.mk (W.ι ≫ V.hom)`; its over-category condition is
  exactly π ∘ ι_C ∘ v = a.
- The final equation says that `E.transport` followed by `W.ι` equals
  `D.transport` of `v ≫ Over.homMk W.ι rfl`, with equality of scheme morphisms,
  not merely underlying point functions. By Yoneda this specifies restriction
  of the original descent isomorphism on the universal test scheme as well.
- No property of V → A, such as separatedness, local quasi-finiteness or
  quasi-compactness, occurs among the binders. The explicit universe u covers
  the schemes and all test schemes in the size convention.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: AlgebraicGeometry.Flat.
- Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap: AlgebraicGeometry.Surjective.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  AlgebraicGeometry.LocallyOfFinitePresentation.
- Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact and QuasiSeparated:
  AlgebraicGeometry.QuasiCompact and AlgebraicGeometry.QuasiSeparated.
- Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion,
  the standard Scheme.Opens inclusion and its open subscheme.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  CategoryTheory.Limits.pullback, its projections, and pullback.map.
- WeilConjectures.CategoryTheory.Comma.Over.DescentDatum:
  CategoryTheory.Over.DescentDatum, its transport, identity and cocycle fields,
  and its existing universal morphism toHom.
- The two convention nodes introduce no declaration; the scheme-conventions
  record specifies the finite-presentation conjunction used above, and the
  size convention is rendered by explicit universe binders.

The proof imports include WeilConjectures.AlgebraicGeometry.DescentOrbitSaturated
(descent_orbit_saturated) and Mathlib.AlgebraicGeometry.PullbackCarrier
(Scheme.image_preimage_eq_of_isPullback). The other proof dependencies are in
the public OpenImmersion import: IsOpenImmersion.lift, lift_fac, lift_uniq,
isOpenImmersion_stableUnderBaseChange and IsOpenImmersion.mono. The docstring
reproduces the five proof steps of the reviewed node.

Edge cases checked before writing: for C empty the range is empty and the
restricted empty scheme has its unique transport; for empty V this is the same
case. If A is empty then V and C are empty, and surjectivity forces B empty.
For p the identity the saturation is C and the datum restricts to the identity.
For a nontrivial datum exchanging components, saturation takes the entire orbit,
and the equation retains the original action rather than replacing it by identity.
The range is a range on all scheme points, including nonclosed points; the test
scheme equation uses all morphisms, including nonreduced test schemes.

Searches for an existing statement:

- msearch.py leanfinder, query: "A scheme descent datum restricts to the open
  saturation of an affine open subscheme, preserving transport and cocycle".
  Eight results concerned affine refinements, affine transition limits and
  affine-open restriction; none states saturation invariance or restriction of
  a scheme descent datum to its saturated open.
- msearch.py loogle, query: `"DescentDatum"`. Zero results.
- msearch.py grep in AlgebraicGeometry, query:
  `saturat.*descent|descent.*saturat|restrict.*[Dd]escent`. Zero results.
- rg in lean/WeilConjectures and lean/Sheaf for saturation, descent restriction,
  and the proposed declaration name found the orbit-saturation theorem and
  related effective-descent or invariant-neighbourhood results, but no statement
  of this restriction result. The grep for the item's exact id upstream found
  no declaration. The existing DescentDatum.toHom supplies the needed canonical
  morphism without introducing a helper definition.

The source read was literature/stacks-project/more-morphisms.tex, the proof of
lemma-separated-locally-quasi-finite-morphisms-fppf-descend, second paragraph
(Tag 02W8). No statement correction, new node, or dependency repair is needed.

Validation: scompile.py compiled the delivered file in both sandbox and library
module contexts, with no errors or warnings (6.7 and 12.0 seconds respectively).

## Second reading by Q75

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
