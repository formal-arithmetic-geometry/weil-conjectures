## Worker report

The new module `Sheaf.AlgebraicGeometry.RosenlichtProductUnitFactorization` states
`AlgebraicGeometry.rosenlicht_product_unit_factorization`, with its proof `sorry`.
Two real helper constructions, `AlgebraicGeometry.rosenlichtSliceX` and
`AlgebraicGeometry.rosenlichtSliceY`, provide the canonical slice inclusions using
Mathlib's `pullback.lift`. They are declarations of this node's own notion, recorded
in `lean.declarations`, rather than independent new notions. Their commutativity
certificates are explicit compositions of category laws and the point's structure
map equation. Neither construction contains postponed data or a postponed proof.
Every binder and universe is explicit; `autoImplicit` and `relaxedAutoImplicit` are false.

The source read was Milne, Algebraic Groups (2017), Proposition 12.48, printed
pp. 246-247, identity (79), and Remark 12.50, printed p. 247. The printed proof
starts with normal basepoints; factorization immediately gives the same identity
for arbitrary basepoints, and the DAG's bounded-inverse proof directly starts at
arbitrary basepoints. No normality assumption is added. The node is unchanged
except for `lean`. There are no new nodes, dependency repairs, statement corrections,
or statement disputes.

Hypothesis and clause correspondence:

- An algebraically closed field F is `(F : Type u) [Field F] [IsAlgClosed F]`.
- The schemes are `(X Y : Scheme.{u})`, with explicit structure morphisms
  `f : X ⟶ Spec (.of F)` and `g : Y ⟶ Spec (.of F))`.
- Nonempty integral schemes are `[IsIntegral X] [IsIntegral Y]`. The
  `IsIntegral.nonempty` field supplies nonemptiness, so no redundant hypothesis
  is added. The same class gives domains on nonempty open sets.
- Separated over F is `[IsSeparated f] [IsSeparated g]`, whose defining field
  is that the relative diagonal is a closed immersion.
- Finite type is `[LocallyOfFiniteType f] [QuasiCompact f]` and the corresponding
  two assumptions for g, exactly the interface of def-weil-finite-type-morphism.
- The product is `pullback f g` in the category of schemes, with projections
  `pullback.fst f g` and `pullback.snd f g`. It is not a product of rings.
- The arbitrary invertible regular function is `(u : (Γ(pullback f g, ⊤))ˣ)`.
  Mathlib `Units` consists of an element, its inverse, and their multiplication
  identities, which is the node's primary description of this object. The
  mention of morphisms to G_m is an equivalent description, not a replacement
  for the global-section objects or an additional premise. The recorded
  def-sc-gm-ga module is imported publicly; no second G_m is introduced.
- The first conjunct quantifies `a : (Γ(X, ⊤))ˣ` and `b : (Γ(Y, ⊤))ˣ` existentially.
  Its equation is `u = Units.map prX.appTop.hom.toMonoidHom a *
  Units.map prY.appTop.hom.toMonoidHom b`. `appTop` is actual pullback of global
  sections and `Units.map` carries it to unit groups.
- The second conjunct quantifies *every* pair `x₀ : Spec (.of F) ⟶ X` and
  `y₀ : Spec (.of F) ⟶ Y`, together with `hx : x₀ ≫ f = 𝟙 _` and
  `hy : y₀ ≫ g = 𝟙 _`. These equations express exactly F-rational points;
  arbitrary morphisms of underlying schemes would not express that condition.
- `rosenlichtSliceX f g y₀ hy` is `(id_X, f ≫ y₀)`, the map x ↦ (x,y₀).
  `rosenlichtSliceY f g x₀ hx` is `(g ≫ x₀, id_Y)`, the map y ↦ (x₀,y).
  Thus pulling u back by these maps and then by the projections gives the
  two terms `u(x,y₀)` and `u(x₀,y)` on the full product.
- `x₀ ≫ rosenlichtSliceX f g y₀ hy` is the paired basepoint. Its pullback of
  u is in `Γ(Spec F, ⊤)ˣ`; its inverse is pulled to the product by
  `pullback.fst f g ≫ f`. Under `Scheme.ΓSpecIso` this is the constant
  `u(x₀,y₀)⁻¹` in Fˣ. This choice avoids adding an arbitrary scalar map.
  Multiplying the three factors yields exactly the displayed normalized
  identity. Equality in Units is equivalent to equality of their underlying
  regular sections, by injectivity of the coercion; it asserts no uniqueness
  of the existential factors.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs; def-weil-algebraic-closure:
  `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic (the node's mathlib_match
  explicitly names this for algebraic closedness; no closure extension is needed).
- def-pc-scheme: `AlgebraicGeometry.Scheme` and its `Hom` interface,
  Mathlib.AlgebraicGeometry.Scheme.
- def-pc-integral-scheme: `AlgebraicGeometry.IsIntegral`,
  Mathlib.AlgebraicGeometry.Properties.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and `AlgebraicGeometry.QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- def-sc-gm-ga: `AlgebraicGeometry.StandardGroupSchemes.multiplicative` and
  `multiplicativeGroup`, Sheaf.AlgebraicGeometry.StandardGroupSchemes; these
  supply the existing equivalent G_m interpretation.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, and `pullback.lift`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback, with scheme
  pullback instances from Mathlib.AlgebraicGeometry.Pullbacks.
- The explicitly requested separatedness uses `AlgebraicGeometry.IsSeparated`,
  Mathlib.AlgebraicGeometry.Morphisms.Separated, whose full definition was read.

All stated proof dependencies are imported: Mathlib.AlgebraicGeometry.Morphisms.FiniteType
(Jacobson space), Mathlib.AlgebraicGeometry.AlgClosed.Basic (closed-point residue field),
Mathlib.AlgebraicGeometry.Pullbacks (affine spectra and open fibre products),
Sheaf.RingTheory.BoundedInverseUnitLines (`Units.finite_boundedInverse_scalarOrbits`),
WeilConjectures.Mathlib.RingTheory.Nullstellensatz
(`eq_zero_of_forall_algHom_apply_eq_zero` and the other recorded declarations), and
Mathlib.AlgebraicGeometry.FunctionField (`germ_injective_of_isIntegral` and
`Scheme.germToFunctionField_injective`). These imports and the full six-step DAG proof
are present for stage 3; proof-only imports are not public.

Edge cases checked before writing: the empty scheme is excluded by the node's
integrality condition, which already includes nonemptiness. For X or Y equal to
Spec F the formula reduces to cancellation of the evaluated unit. Constant units
have the scalar factor c*c*c⁻¹ = c. Units need not be constant: G_m times G_m
allows nonconstant units from both factors. Singular integral schemes are
included: no normality, smoothness, properness, affineness, or geometric hypotheses
are added. Positive characteristic is unrestricted. The identity is an equality
of global sections, not merely equality at F-points. A shared arbitrary universe
for F and its finite-type schemes matches Mathlib's scheme category and does not
introduce a universe-restricted test-object quantifier.

Searches for existing declarations, run before creating the module:

- msearch.py leanfinder: "An invertible regular function on the scheme product
  of integral varieties over an algebraically closed field factors as units
  from the two factors". Eight hits: `isField_of_universallyClosed`, rational-map
  construction, `Scheme.SpecToEquivOfField`, structure-sheaf cancellation lemmas,
  and other nonmatches. None is Rosenlicht factorization.
- msearch.py loogle: "AlgebraicGeometry.Scheme.Hom.appTop, Units.map,
  CategoryTheory.Limits.pullback.lift". Zero hits for that combined query.
- msearch.py grep in AlgebraicGeometry: "Rosenlicht|rosenlicht|unit.*factor|factor.*unit".
  One irrelevant comment in Mathlib.AlgebraicGeometry.Group.Affine.
- Direct rg in Mathlib/AlgebraicGeometry for Rosenlicht and product-unit names:
  no matching theorem. Direct rg in lean/WeilConjectures for the node id:
  no result. Direct rg in lean/Sheaf/AlgebraicGeometry and
  lean/WeilConjectures/AlgebraicGeometry for Rosenlicht and the intended name:
  only proof/docstring references in RelativeGroupUnitAxisFactorization,
  NormalLineBundlePowerLinearization, BorelCharacteristicPicardSequence,
  and SplitReductiveCharacteristicSequence; no declaration of this result.
- Direct rg for slice helper names in Mathlib and project geometry sources:
  TheoremOfCube.CrossIdeal has three-factor slices in a monoidal Over-category
  setting, not the two scheme pullback maps here. No rosenlichtSliceX,
  rosenlichtSliceY, or rosenlicht_product_unit_factorization exists in the
  upstream name index. The new helpers only abbreviate the canonical universal
  construction, with no new mathematical structure or choice.

The reference CompactObject Sheaf module is now withdrawn; its node records
WeilConjectures.CategoryTheory.CompactObject. That upstream module was read for
the current public-module, source-docstring, and node-record conventions.

Validation: scompile.py compiled this file both in sandbox and library namespaces
without errors or non-sorry warnings (2.8 s and 1.8 s respectively). The node's
signature is copied verbatim from the theorem keyword to before `:=`; JSON uses
indent 1, Unicode, and a final newline. A structural comparison confirmed that
only the `lean` field differs from the repository node.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
