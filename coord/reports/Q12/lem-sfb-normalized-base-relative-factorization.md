## Worker report

The delivery states `AlgebraicGeometry.normalized_base_relative_factorization` in
`Sheaf.AlgebraicGeometry.NormalizedBaseRelativeFactorization`. The theorem has only
`sorry` as its proof. No definition, statement correction, or dependency repair is needed;
the node is changed only in `lean`.

I read the item's statement and seven proof steps, every statement dependency and its
recorded interface, the upstream normalization definitions and function-field definition,
and the relevant Mathlib class definitions. Source passages read: Stacks
`algebra.tex`, lemma-integral-closure-localize (Tag 0307), and `more-morphisms.tex`,
lemma-quasi-finite-Noetherian-universally-open (Tag 0F32). The former identifies the
localized normalization charts; the latter is used through the recorded normal-base
specialization, not as a theorem with its geometrically-unibranch hypothesis omitted.
The node's source explicitly describes the rest as an agent affine argument supporting
de Jong §§3.2 and 3.5. Its entire seven-step argument is carried in the theorem docstring.

Hypotheses, with the exact Lean representations:

- The field k is `(k : Type u) [Field k]`.
- The schemes S and X and their integrality are `(S X : Scheme.{u})`,
  `[IsIntegral S]`, `[IsIntegral X]`. Their function fields K and F are respectively
  `S.functionField` and `X.functionField`, the existing generic stalks.
- Normality of S is `hS`: for every point s, the local ring is both `IsDomain`
  and `IsIntegrallyClosed`. This is precisely the inline meaning given by the node.
- S is over k by `p : S ⟶ Spec (.of k)`; finite type is `[LocallyOfFiniteType p]`
  and `[QuasiCompact p]`. For X the two corresponding binders concern `f ≫ p`,
  so its k-structure agrees with f. No projectivity, separatedness, smoothness,
  relative dimension, or flatness hypothesis is added.
- Dominance is `[IsDominant f]`, whose Mathlib definition is dense range.
- The generic fibre is `pullback f S.fromSpecFunctionField`; its structure map
  to Spec K is `pullback.snd f S.fromSpecFunctionField`. Geometric integrality
  is the `GeometricallyIntegral` instance on this map, with every field extension
  allowed by Mathlib's scheme-size convention.
- L/F and E/K are the displayed `Field`, `Algebra`, `FiniteDimensional`, and
  `Algebra.IsSeparable` binders. The inclusion E into L is `[Algebra E L]`.
- The K-algebra structures on F and L and the two `IsScalarTower` instances
  express agreement of the embeddings on K. The equation `hcompat` says that
  Spec L maps to S through f by the specified K inclusion. This records that the
  K-to-F embedding is the one induced by f; it is not an arbitrary independent
  field embedding or an additional geometric restriction. Given the source data,
  take the induced K-to-F algebra and the compatible composite K-to-L algebra.

Conclusions, clause by clause:

- T and Y are the existing `S.normalizationIn E` and `X.normalizationIn L`;
  q and nu are their `fromNormalizationIn` maps. No surrogate normalization is used.
- `∃! g` ranges over Y-to-T maps satisfying both `g ≫ q = nu ≫ f` and the
  equation after precomposition with the canonical Spec L-to-Y map. The latter
  is exactly induction of the specified E-to-L embedding, rather than uniqueness
  of all maps over S without that condition.
- The subsequent `∀ g` supplies the properties of that unique map. Its hypotheses
  are precisely the same two equations; existence is already the first conjunct.
  The map h is literally `pullback.lift (X.fromNormalizationIn L) g hfg.symm`.
  `IsFinite` and `Surjective` concern that map to the full chosen fibre product
  `pullback f (S.fromNormalizationIn E)`, including every point, rather than a
  component or a reduction. `IsDominant g` is the separate dominance clause.
- `IsField (X.functionField ⊗[S.functionField] E)` states that the existing
  tensor-product commutative ring is a field; it does not select a second ring
  structure. `Function.Injective (Algebra.TensorProduct.productMap ... ...)`
  is injectivity of the multiplication map. The Mathlib formula
  `productMap_apply_tmul` sends `a ⊗ e` to the product of their prescribed images.
- The final isomorphism has source `Spec (F ⊗[K] E)` and target the fibre of
  W-to-X at `X.fromSpecFunctionField`. Its first projection is Spec of the
  F-algebra map; its projection through W to T is Spec of `includeRight` followed
  by the canonical Spec E-to-T map. Thus the isomorphism has the canonical maps,
  and is not merely an abstract isomorphism of schemes.
- For the generic-fibre normalization, the explicit `pullback.lift` of Spec L
  to `pullback f S.fromSpecFunctionField` is the canonical generic map. Its
  `.normalization` is by definition the normalization of X_K in L; using this
  existing relative normalization avoids assuming a chosen identification of
  k(X_K) with F or introducing another generic-lift definition.
- The existential c is the E-structure on that normalization, characterized by
  its composite with Spec L being `Spec.map (algebraMap E L)`. It is constructed
  in the conclusion, not supplied as an arbitrary map in a hypothesis. The
  isomorphism e from `pullback g jE` respects c, commutes with both projections
  to X and Spec K (hence with the map to X_K), and sends the canonical Spec L
  map to the canonical Spec L-to-Y map. This last equation says it induces the
  identity on L. Here `jE = (S.fromSpecOfAlgebraFunctionField E).toNormalization`
  is the canonical generic point of T: the already existing
  `Scheme.exists_iso_toNormalization_normalizationIn` identifies it with
  `Spec k(T)` via E, with its commuting equation. Hence the fibre is exactly
  the fibre under the node's canonical identification k(T)=E.

Dependency declarations reused:

| Node | Module and declarations |
| --- | --- |
| def-weil-field | Mathlib.Algebra.Field.Defs: `Field` |
| def-pc-integral-scheme | Mathlib.AlgebraicGeometry.Properties: `IsIntegral` |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`; Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `QuasiCompact` |
| def-sc-function-field | WeilConjectures.AlgebraicGeometry.FunctionField imports Mathlib.AlgebraicGeometry.FunctionField: `Scheme.functionField`, `Scheme.fromSpecFunctionField` (the arbitrary integral-scheme clause of this node, not its component-product specialization) |
| def-pc-field-extension | Mathlib.Algebra.Algebra.Defs: `Algebra`, `algebraMap` |
| def-pc-geometrically-irreducible | Mathlib.AlgebraicGeometry.Geometrically.Integral: `GeometricallyIntegral` |
| def-fin-normalization-extension | WeilConjectures.Mathlib.AlgebraicGeometry.Normalization: `Scheme.normalizationIn`, `Scheme.fromNormalizationIn`, `Scheme.fromSpecOfAlgebraFunctionField` |
| def-weil-finite-integral-morphism | Mathlib.AlgebraicGeometry.Morphisms.Finite: `IsFinite` |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift` |

Proof-only imports include the landed normal-base universal-openness theorem and the
recorded Mathlib affine-fraction, affine-pullback, integral-closure-localization,
localization-tensor, affine-locality, properness, and finite-fibre interfaces. The
proof-only node `lem-sfb-finite-normalization-model-functoriality` currently has no
recorded declaration, so there is no module for it to import. Nothing in the present
statement requires an unstated prerequisite.

Searches actually run:

- msearch.py LeanFinder: “For a dominant morphism with geometrically integral generic
  fibre normalization in a finite separable field extension factors finitely surjectively
  through the normalized intermediate base”. Eight hits, including `normalizationDesc`,
  integral and dominant normalization instances, and their equations. Read the relevant
  signatures and docstrings. These give individual ingredients, not this combined result.
- msearch.py Loogle: `"normalization", "pullback"`. Seven hits, chiefly
  `normalizationPullback`, its equations, and its isomorphism for smooth base change.
  Read that comparison's definition and docstring. It does not give the finite surjective
  factorization or the field/multiplication assertions.
- msearch.py grep: `normalizationPullback|normalizationDesc` in
  `AlgebraicGeometry/Normalization.lean`: five reported hits, the factorization API.
  Additional grep queries against `WeilConjectures` and `Sheaf` reported zero hits;
  these were supplementary, and direct rg source searches were also performed.
- Direct rg of the actual Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` sources
  for `normalizationIn`, `normalizationPullback`, `normalizedBase`, and
  `relativeFactorization`. The existing `finite_normal_relative_curve_model`
  was read in full where relevant. It assumes a projective relative smooth curve
  setup and states many extra conclusions, so it is not the same statement.
- Direct grep of the item id in `lean/WeilConjectures`: no match. Direct rg of
  `normalized_base_relative_factorization` in the upstream name index and both
  project roots: no match. The new declaration name is available.

Edge cases checked mathematically before finishing the statement: E=K; L=F;
f=id on a normal base; S=Spec k; arbitrary characteristic, including positive
characteristic with precisely the stipulated separability; nonnormal integral X;
nonflat f and the full fibre product, which need not be replaced by a component.
Integral schemes exclude empty S and X exactly as the source does. No dimension
or nonempty-affine-choice hypothesis appears. All universes and variables are
explicitly bound, with `autoImplicit false`. A common scheme/field universe is
used consistently, without an unrelated smaller test-field universe.

No STATEMENT-DISPUTED issue was found. The theorem was compiled with scompile.py
in both sandbox and its real module path: clean, without any warnings. Earlier
syntax and long-line issues were repaired before this report's final form.

## Second reading by Q12

This is the dispatched worker's second pass, not a claim of independent review;
the brief reserves independent review for the maintainer and forbids spawning
another agent. I reopened the node and final Lean file and checked each binder
and conjunct using the correspondence above. In particular I checked the easily
lost clauses: uniqueness includes the E-to-L embedding; h targets the full fibre
product; the tensor ring itself is a field and its actual multiplication map is
injective; g is dominant; the generic-fibre isomorphism respects E, both maps to
X_K, and the specified L identification. The existing relative-curve theorem's
extra projectivity/smoothness/purity hypotheses were not copied. No private
notion or arbitrary-map hypothesis remains. No node statement change is made.
