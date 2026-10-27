## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceUniversallyClosedAffineTests` states
`AlgebraicGeometry.AlgebraicSpace.mapIsUniversallyClosed_of_affine_tests`, with `sorry`.
Source read: `literature/stacks-project/spaces-morphisms.tex`, definition-closed and
lemma-universally-closed-local (Tag 03IT), especially (3) and its descent proof.
The declaration docstring gives all four steps of the node's proof, including the
point-fibre-product surjectivity needed for the inverse-image/image equality.

Hypothesis and conclusion correspondence:

- The base scheme is `{S : Scheme.{u}}`; the arbitrary spaces over it are
  `{X Y : AlgebraicSpace S}` and the morphism is `(f : X ⟶ Y)`.
- Every scheme T over S is `(T : Over S)`, and every map T → Y is the natural
  transformation `(a : yoneda.obj T ⟶ Y.obj.obj)`. It need not be representable,
  étale, surjective, or affine as a morphism. `IsAffine T.left` requires only
  that the source scheme be affine.
- The actual presheaf fibre product of X with h_T over Y is
  `Limits.pullback f.hom.hom a`. Presheaf limits of sheaves give the sheaf fibre
  product; the algebraic-space closure is supplied by the recorded fibre-product
  node. `Point` and `pointTopologicalSpace` give its usual field-valued point
  classes and final étale topology, with no new point construction.
- Every closed subset is `C : Set (Point (Limits.pullback f.hom.hom a))` with
  `IsClosed C`. Its projection image on point classes is
  `mapPoint (Limits.pullback.snd f.hom.hom a) '' C`.
- To state closedness on the ordinary scheme T, that image is pulled back along
  `schemePointMap (𝟙 (yoneda.obj T))`. This is the residue-field identification
  of an ordinary scheme point with its field-valued point class. Explicitly, the
  resulting subset contains t exactly when a point x of C projects to the class
  of Spec κ(t) → T. Thus `IsClosed` here uses the actual scheme topology of T,
  exactly as the node requires. No arbitrary inverse or choice is introduced.
- The conclusion `MapIsUniversallyClosed f` is the existing definition
  `∀ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y),
  IsClosedMap (mapPoint (Limits.pullback.snd f.hom g.hom).hom)`.
  It includes all algebraic-space base changes, with the sheaf fibre products
  and the final point topology. `IsClosedMap` means the image of every closed
  subset is closed. No quasi-compactness, separatedness, or finite-type
  hypothesis is imposed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`; morphisms are those of the full subcategory.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, together with its full signature
  and proof docstring. Its sheaf fibre product is used in the existing conclusion.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace` and `PointRepresentative.map`;
  the imported `AlgebraicSpacePointClasses` supplies `Point` and `schemePointMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsUniversallyClosed`. Its landed owning node
  `def-sfb-space-morphism-properties` is added to `stmt_deps`, as permitted for
  already-landed notions. This avoids redefining universal closedness.
  Its public dependency `ProperCurveModuli` supplies the existing canonical
  `AlgebraicSpace.mapPoint`; its construction and docstring were read.
- Proof-only imports:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover`, declaration
  `exists_affine_etale_cover_and_point_topology`, and
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus`, declaration
  `point_open_calculus`. Their full statements and docstrings were read.

Edge cases checked before writing: empty affine T, empty X, and empty arbitrary
base change Y' cause no exceptional assumption; C can be empty or the whole
source. Nonrepresentable f and nonschematic X ×_Y T remain allowed. The atlas
may have infinitely many components, and the point fibre product need only map
surjectively to the set-theoretic fibre product. The single explicit universe u
is inherited from the algebraic-space framework for S, its scheme tests and
field representatives; no independent smaller test universe or equality of
unrelated universes is introduced. `autoImplicit` is disabled. There are no
new definitions, helper theorems, dependency repairs, or statement corrections.
No statement fault or dispute was found.

Searches made:

- `msearch.py ... leanfinder`: “A morphism of algebraic spaces is universally
  closed if all its affine scheme base changes are closed on underlying points”.
  Eight hits, including `AlgebraicGeometry.UniversallyClosed`,
  `universallyClosed_iff`, and `UniversallyClosed.universally_isClosedMap`.
  Their signatures quantify over schemes, not general algebraic spaces.
- `msearch.py ... leansearch`: “Universal closedness of algebraic-space morphisms
  is detected by affine scheme base changes”. Eight hits, again scheme-only
  universal-closedness declarations; no matching criterion for algebraic spaces.
- `msearch.py ... loogle`: `"UniversallyClosed", "IsClosedMap"`.
  One hit: scheme-only `UniversallyClosed.universally_isClosedMap`.
- `msearch.py ... grep`: `universallyClosed|AlgebraicSpace` in AlgebraicGeometry.
  Twenty-five hits, all displayed universal-closedness results concern schemes.
  Read Mathlib `Morphisms/UniversallyClosed.lean`, including the class and iff.
- `rg` on `lean/WeilConjectures/AlgebraicGeometry` for
  `universallyClosed|universally_closed|UniversallyClosed` found scheme results;
  the item's id has no occurrence in `lean/WeilConjectures`.
- `rg` on `lean/Sheaf/AlgebraicGeometry` found the existing
  `MapIsUniversallyClosed` definition and scheme criteria, not this affine-test
  criterion. Read the definition and use it. `mapPoint` is reused from
  `ProperCurveModuli`, not redeclared.
- Name search for `universallyClosed_of_affine_tests` and
  `universallyClosed_of_affine_scheme_tests` in Mathlib, the upstream name index,
  `lean/Sheaf`, and `lean/WeilConjectures` found no declaration.

## Second reading by Q97

Author's second reading (the maintainer supplies independent review): re-read the
node beside the module. S, X, Y and f have the same generality. The hypothesis
quantifies over all affine schemes over S and all their maps to Y. Its closed
image is tested in the ordinary topology on T, using the canonical residue-field
point identification; the source is the full sheaf fibre product, even when it
is not a scheme. The conclusion unfolds to closedness after every algebraic-space
base change. Neither direction restricts the morphisms to be representable or
étale. C is an arbitrary closed subset, not just the full source or a closed
subspace. The proof docstring explains both inclusions of the key image equality
and the quotient-topology descent. The only DAG change beyond `lean` adds the
already-landed node owning the conclusion's definition; no mathematical statement
is changed. No mismatch was found and no second-reading edit was needed.
