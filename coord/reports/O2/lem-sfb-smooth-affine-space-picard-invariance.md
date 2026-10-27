## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothAffineSpacePicardInvariance` defines the
canonical zero section of the actual chosen fibre product and states
`AlgebraicGeometry.smooth_affineSpace_picard_invariance`. Its sole theorem proof is
`sorry`. No statement correction, new notion, dependency repair or dispute is needed.

Hypothesis and conclusion correspondence:

- Any field F: `(F : Type u) [Field F]`, with no perfectness, characteristic,
  algebraic-closure or rational-point assumption.
- X a scheme over F: `(X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of F))`.
- Affine: `[IsAffine X]`.
- Smooth: `[Smooth f]`, the recorded Mathlib class, affine-locally smooth ring maps.
- Geometrically integral: `[GeometricallyIntegral f]`. Its definition tests integral
  schemes after field base change; integral includes reducedness and nonempty
  irreducibility. In particular the empty scheme is excluded by precisely the
  stated hypothesis. The existing DAG node `def-pc-geometrically-irreducible` supplies
  this notion and is added to stmt_deps.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, precisely the conjunction
  recorded by `def-weil-finite-type-morphism`. These assumptions are retained to
  render both clauses of the node, even though smoothness and affineness imply them
  here.
- Every integer n >= 0: `(n : ℕ)`, with coordinate type `ULift.{u} (Fin n)` so the
  Mathlib affine space is in the scheme universe. No n > 0 restriction occurs.
- The product X times affine n-space over F is exactly
  `pullback f (AffineSpace (ULift.{u} (Fin n)) (Spec (CommRingCat.of F)) ↘ Spec ...)`.
  Its projection is exactly `pullback.fst f ...`, not an unspecified isomorphic model.
- Pic(Y) is the existing `Y.Pic` for every scheme Y, from
  `WeilConjectures.AlgebraicGeometry.PicardFunctor`. It is the subtype of invertible
  objects of the skeleton of `Y.Modules`, hence isomorphism classes of line modules.
  The existing node `def-sc-picard-group` is added to stmt_deps. Its upstream
  declaration is already for every scheme, although that node discusses curves.
- The tensor group law is the existing `Scheme.Pic.instCommGroup` from
  `WeilConjectures.AlgebraicGeometry.Picard.Group`. This API writes tensor product
  multiplicatively, so the isomorphism is a `≃*`; this is just notation for the
  node's abelian group with tensor product as addition.
- Pullback is the existing `Scheme.Pic.mapHom`, whose underlying map is `Pic.map`:
  the skeleton class of `(Scheme.Modules.pullback g).obj M`. Mathlib's pullback is
  left adjoint to the usual pushforward. The dependency's explicit
  `tensorPullback` is left adjoint to the same pushforward by the imported
  `tensorPullbackSectionAdjunction`; uniqueness of left adjoints identifies their
  objects up to isomorphism. Thus they induce exactly the same map on Picard classes;
  no scalar normalization affects a class. No new pullback notion is introduced.
- Isomorphism assertion: `∃ e : X.Pic ≃* (pullback ...).Pic`, followed by the equality
  `e.toMonoidHom = Scheme.Pic.mapHom (pullback.fst f ...)`. This pins the forward
  homomorphism, beyond merely asserting that the two groups are abstractly isomorphic.
- Inverse assertion: `e.symm.toMonoidHom = Scheme.Pic.mapHom
  (affineSpaceProductZeroSection f n)`. The helper is literally `pullback.lift (𝟙 X)
  (AffineSpace.homOfVector f (fun _ ↦ 0))`. `homOfVector` has structure map f and
  zero coordinate sections; the fibre-product compatibility is proved by
  `AffineSpace.homOfVector_over`. The helper therefore is exactly s_0(x) = (x,0).
  It has real data and contains no sorry or arbitrary choice.

Dependencies read and reused:

- `def-weil-field`: Mathlib `Field`, Algebra/Field/Defs.lean:180.
- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme, `Scheme` and `Scheme.Hom`.
- `def-sbc-smooth-morphisms`: Mathlib.AlgebraicGeometry.Morphisms.Smooth, `Smooth`.
- `def-weil-finite-type-morphism`: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `LocallyOfFiniteType`; Morphisms.QuasiCompact, `QuasiCompact`.
- `def-weil-affine-spectrum`: Mathlib.AlgebraicGeometry.Scheme, `Spec`, `Spec.map`;
  affineness is the existing `IsAffine` in Mathlib.AlgebraicGeometry.AffineScheme.
- `def-sbc-affine-space`: Mathlib.AlgebraicGeometry.AffineSpace, `AffineSpace`, its
  canonical projection, and `AffineSpace.homOfVector` with `homOfVector_over`.
- `def-pc-fibre-product`: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `pullback`, `pullback.fst`, `pullback.lift`, using scheme pullback existence.
- `def-sc-invertible-module`: WeilConjectures.AlgebraicGeometry.Modules.Invertible,
  `Scheme.Modules.IsInvertible`. Picard.Group's `Pic.isInvertible_fromSkeleton`,
  `Pic.ofIsInvertible` and `Modules.IsInvertible.of_sheafOfModules` identify the
  Picard class predicate with exactly this existing local rank-one predicate.
- `def-pc-module-pullback`: Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction,
  `Scheme.Modules.tensorPullbackSectionAdjunction`, importing the explicit tensor
  formula. Its full signature and section-normalized docstring were read.
- `def-pc-geometrically-irreducible`: Mathlib.AlgebraicGeometry.Geometrically.Integral,
  `GeometricallyIntegral` (the node's existing record).
- `def-sc-picard-group`: WeilConjectures.AlgebraicGeometry.PicardFunctor, `Scheme.Pic`.
  The group's `instCommGroup` and `mapHom` are read in Picard.Group, not duplicated.

The statement dependencies are public imports. The stated proof dependencies are
plain imports: Regular (`IsRegular.of_smooth`), RegularNormalDecomposition
(`regular_normal_and_normal_decomposition`), Mathlib Pullbacks (`pullbackSpecIso`),
Morphisms.Flat (`Flat.SpecMap_iff`), Noetherian (`LocallyOfFiniteType.isLocallyNoetherian`),
Polynomial.UniqueFactorization (`MvPolynomial.uniqueFactorizationMonoid`),
Modules.PullbackMonoidal (`Scheme.Modules.pullbackMonoidal`), and
AffineSpaceInvertibleTrivial (`Scheme.Modules.nonempty_iso_unit_of_mvPolynomial_field`).
`lem-sfb-normal-noetherian-generic-line-pullback` has no recorded Lean declaration or
Mathlib match in the read clone; it is a proof-only dependency, not needed to type
this statement, so there is no module to import yet. Its exact role remains in the
five-step natural-language proof docstring. The other Mathlib proof inputs are
available through the listed imports. No import cycle is introduced.

Edge cases checked before writing: n = 0 gives an empty coordinate type and the
canonical zero-dimensional affine space; its product projection and zero section
are mutually inverse isomorphisms, hence so are the Picard maps. X = Spec F and
nonempty zero-dimensional smooth schemes are admitted. The empty scheme is excluded
by geometric integrality, not by an additional hypothesis. Imperfect fields and all
positive characteristics are admitted. There is no chosen rational point of X.
Universes are explicitly bound, with both auto-implicit options disabled. Schemes and
fields share the usual scheme universe u; coordinate ULift avoids forcing u = 0.

Searches (2026-10-24):

- msearch.py leanfinder, "Pullback on Picard groups along the projection from affine
  space over a smooth geometrically integral affine variety is an isomorphism":
  eight results, including `AffineSpace.isPullback_map`, `AffineSpace.SpecIso_inv_over`
  and projective-spectrum pullback isomorphisms; none states Picard invariance.
- msearch.py loogle, `"Pic", "Polynomial"`: zero hits.
- msearch.py grep, `Picard|Pic\.map|GeometricallyIntegral`, AlgebraicGeometry:
  twelve hits, chiefly the existing geometric-integrality class and affine-space
  integrality, no scheme Picard homotopy-invariance statement.
- msearch.py leansearch, "Picard group is unchanged by product with affine space over
  a smooth integral variety": eight results, ring Picard groups and their scalar
  extension functoriality; none states polynomial or scheme homotopy invariance.
- rg over lean/Sheaf and lean/WeilConjectures, `Picard|picard|def Pic|picPullback|
  GeometricallyIntegral`, and focused searches for Pic.mapHom, PicardGroup,
  picardPullback: found PicardFunctor and Picard/Group, which are reused.
- rg over Mathlib, Sheaf and WeilConjectures for `picard.*[Ii]nvarian|
  [Ii]nvarian.*[Pp]ic|affineSpaceProductZeroSection|picard_affineSpace`: no exact result;
  the landed affine-group field-invariance theorem is a consumer, not this statement.
- rg for the item's exact id in WeilConjectures and dag/lean_names_upstream.json:
  no existing declaration for this item.

Source checks: read local Stacks varieties.tex Tag 0BEH, whose proof explicitly
says every line on X times U descends to X; take U equal to affine n-space and
combine with the zero-section left inverse. Also read chow.tex Tag 02TT and
divisors.tex Tag 0BE9 at their recorded labels. The node's proof gives the
necessary regularity, normality, finite-type and integral-fibre verifications;
none requires perfectness. The supplied five-step proof is reproduced in the
theorem docstring with its dependency ids.

Validation: scompile.py compiled this file in both sandbox and library module mode
on 2026-10-24 (1.8 seconds and 1.7 seconds respectively), with no errors or unexpected
warnings. The prescribed deliver2.py --no-push completed successfully: commit
573ed7e2fae passed preflight and compiled. The delivery wrapper repeats both checks
when publishing the final packet.

## Second reading by O2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
