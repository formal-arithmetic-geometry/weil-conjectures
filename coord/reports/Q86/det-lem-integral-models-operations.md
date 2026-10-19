## Worker report

The module `Sheaf.Paper.IntegralModelsOperations` states
`AlgebraicGeometry.ProEtale.CondensedRing.integralModelsOperations` with one `sorry`.
It introduces no definitions and changes only the item's `lean` record.
The statement is the conjunction of the four original clauses; the reviewed DAG's
11-step proof is reproduced in the theorem docstring. No proof is supplied in stage 2.

Hypothesis and conclusion correspondence:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. A finite extension of Q_ell is
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)`, the upstream subtype of intermediate
  fields with `FiniteDimensional ℚ_[ℓ] E.val`. This is the project's existing
  representation in a fixed algebraic closure: every finite extension admits such
  a representation. The integer coefficient ring is the existing
  `Profinite.padicIntegersRingObj ℓ E.val`, continuous functions into its valuation
  ring, and the coefficient ring on T is `condensedRingObj ... T`.
- Every scheme in each clause is `Scheme.{u}` with an explicit `[IsNoetherian ...]`.
  There is no base field, finite type, separatedness, characteristic or
  invertibility-of-ell hypothesis. The site is the small `Scheme.ProEt.topology T`
  with `Ab.{u + 1}`, following the recorded module-object framework.
- Dbc membership is `constantModelBoundedConstructible ... T K`, from the recorded
  `sk-def-sfb-constructible`: boundedness of the standard t-structure and finite
  constant scalar-model constructibility of every cohomology module. This is the
  exact convention fixed by the item's reviewed proof opening; it is not replaced
  by the broader arbitrary-matrix `boundedConstructible` predicate. As in the node,
  no completeness condition is added. The recorded general bounded-constructible
  module is also imported for its conventions, but its broader predicate is not
  substituted for the item's explicitly specified Dbc.
- Clause (1) universally binds arbitrary `f : X ⟶ Y` and ambient K, assumes precisely
  Dbc(Y) membership, and concludes Dbc(X) for
  `(upperStar ... f).mapDerivedCategory.obj K`. The existing exact module inverse
  image is applied termwise; the upstream
  `leftDerivedUpperStarIsoMapDerivedCategory` identifies it with total derived
  pullback. No preservation or exactness hypothesis is added to f.
- Clause (2) universally binds K and M, assumes each lies in Dbc(X), and concludes
  Dbc(X) for `((derivedTensor ... X).obj K).obj M`. The existing tensor is the
  K-flat derived relative tensor over the pulled-back integer ring, on the ordinary
  unbounded derived category. No completion operation occurs.
- Clause (3) names S, Z and X, with `j : S ⟶ Z` an `[IsOpenImmersion j]` and
  `i : Z ⟶ X` an `[IsClosedImmersion i]`. Here Z is the node's overline S and
  j is its u. The expression for a_! is explicitly
  `(lowerStar ... i).rightDerivedFunctor.obj
    ((openImmersionLowerShriek ... j).mapDerivedCategory.obj L)`.
  It assumes Dbc(S) membership and concludes Dbc(X) membership. Closed direct image
  is exact on Noetherian schemes, so its total right-derived functor is the node's
  termwise i_*. The chosen factorization itself specifies a_!=i_*u_!; no arbitrary
  map or chosen compactification replaces it. No density condition is imposed on j,
  since the node only asks for an open-then-closed factorization.
- Clause (4) repeats exactly that immersion factorization, but L and M range over
  the entire unbounded ambient derived categories. `Nonempty ( ... ≅ ... )` asserts
  the displayed isomorphism `(a_!L) tensor^L M ≅ a_!(L tensor^L a^*M)`. Both occurrences
  of a_! are the same explicit composite as in clause (3), both tensors are the
  recorded relative derived tensors, and a^* is `(upperStar ... (j ≫ i)).mapDerivedCategory`.
  Neither Dbc membership, a bound, perfectness, nor finite Tor amplitude is assumed
  in this clause. `Nonempty` wraps only the theorem's isomorphism assertion; it is
  not used to choose or define any functor or canonical construction.

Recorded statement dependencies read and used:

- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible` and
  `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible`.
- `sk-def-sfb-bounded-constructible`:
  `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`,
  `AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible_of_weakSerre`,
  with imported `boundedConstructible`, its full subcategory and membership lemma.
  These are the general convention, while the item uses the scalar-constant
  specialization expressly recorded by its constructibility dependency.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing` and `condensedRingObj`.
- `sk-def-sfb-derived-categories`:
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, and the existing
  `DerivedCategory`, `Functor.mapDerivedCategory` and total `rightDerivedFunctor`
  conventions described by its recorded note. Here all module categories are
  Grothendieck, so their existing total derivation interface applies.
- `sk-def-sfb-derived-tensor-hom`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`,
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedHom` and its imported
  `derivedTensor`. Only the latter is needed in this item's signature.
- `sk-def-sfb-module-lower-shriek`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`,
  `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek` and the
  existing exactness/adjunction declarations, together with `lowerStar` from its
  imported `ModuleObject.UpperLowerStar.Defs`.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding and surjective stalk maps).

Additional existing interfaces read: the condensed EllAdic definitions, the
`PadicAlgCl.FiniteIntermediateField` subtype and its finite-dimensional instance,
and the `ModuleObject.Derived.UpperLowerStar` exact inverse-image comparison.
The module imports the recorded modules of every already stated proof dependency;
`det-prop-integral-criterion-constant-coefficients` has no declaration yet, so
there is no module to import for that proof-only prerequisite. Cartesian coefficient
identities are already in the imported `ModuleObject.Basic`.

Edge cases checked mathematically before writing: empty schemes and empty strata
are allowed; all three schemes can be empty, and none has a nonemptiness binder.
Zero complexes and the zero module are admitted by Dbc. Tensor bounds can enlarge
by the DVR Tor degree; no false bound or finite-sum-of-shifts claim is inserted.
Identity open and closed immersions recover the tensor identity; an empty open
source gives zero on both sides of the projection formula. Purely open and purely
closed cases arise by taking the other immersion to be the identity. Arbitrary
unbounded L and M remain permitted in clause (4). The base extension E=Q_ell is
included. There is no characteristic restriction, and no extra universe equality:
the site retains object size u+1 and morphism size u.

Searches for an existing statement:

- `msearch.py leansearch`: "Inverse image tensor product extension by zero preserve
  bounded constructible integral l-adic complexes". Eight unrelated hits including
  `ObjectProperty...IsClosedUnderExtensions...` and adic-completion tensor facts;
  none states the four clauses.
- `msearch.py leanfinder`: "On Noetherian schemes inverse image tensor and extension
  by zero preserve bounded constructible integral l-adic complexes". Eight hits,
  including `Scheme.Hom.isConstructible_image`, an inverse-limit section lemma and
  LightCondensed monoidal instances; no matching sheaf/derived theorem.
- `msearch.py loogle`: `"constructible", "tensor"`: zero hits.
- `msearch.py grep`: `constructible.*(tensor|pullback)|((tensor|pullback).*constructible)`
  in Mathlib AlgebraicGeometry: zero hits.
- `rg` of the upstream WeilConjectures tree for the blueprint id: no hit.
  Name/concept searches of that tree and `lean/Sheaf` find no
  `integralModelsOperations` / `integral_models_operations`. Searches for
  `constantModelBoundedConstructible` identify the dependency and other heart,
  continuity and coefficient-comparison statements, none these four operations.
  `AlgebraicGeometry.ProEtale.CondensedRing.integralTensorInverseImage` in
  `Sheaf.SixFunctors.IntegralTensorInverseImage` was read:
  it has finite-type-over-a-field hypotheses, a different general constructibility
  predicate, a completion comparison, and no arbitrary locally closed projection
  formula, so it does not match the item.
- The upstream name index was consulted by blueprint id and proposed declaration
  name; it has no competing match.

No new nodes, dependency repairs, statement correction or disputed statement.
Validation: `scompile.py Q86 det-lem-integral-models-operations` compiled the delivered
file cleanly in both its sandbox check and library check, with no errors or warnings.
The wrapper enforces the per-file compiler limit after acquiring a server slot.
The delivery preflight is the next required check.

## Second reading by Q86

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
