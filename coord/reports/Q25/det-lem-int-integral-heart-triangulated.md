## Worker report

The module `Sheaf.Paper.IntegralConstantModelHeart` states
`AlgebraicGeometry.ProEtale.integralConstantModelHeart`, with exactly one postponed
proof, and supplies the real-data size-transport helper
`AlgebraicGeometry.ProEtale.integralHeartCoefficientRingObj`. It does not change
the node's natural-language statement or its dependency lists.

Hypotheses and coefficients, matched to the node:

- The arbitrary field k and positive characteristic p are `(k : Type u) [Field k]`
  and `(p : ℕ) [CharP k p] (_hp : 0 < p)`. No finiteness or perfection is assumed.
- The prime ell different from p is `(ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ p)`.
- A finite extension of Q_ell is `(E : Type v) [Field E] [Algebra (Padic ℓ) E]`
  together with `[FiniteDimensional (Padic ℓ) E]`. Its universe v is independent of u.
- X is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`, with `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact` on its structure morphism. The last
  two are precisely finite type, rather than a strengthened finiteness hypothesis.
- The valuation ring is the recorded `Padic.coefficientExtensionIntegers` with
  the spectral norm from `spectralNorm.normedField`. The recorded dependency
  also fixes `Padic.coefficientExtensionUniformizer`; the conclusion contains
  no uniformizer, so there is no extra choice binder or dependence on a generator.
- The upstream continuous-function API accepts rings in Type 0. To cover E in
  every universe, the helper obtains `Small.{0} E` by `Module.Finite.small`,
  uses `Shrink.algEquiv (Padic ℓ) E` to transport the field and algebra, and
  transports finite dimensionality by `LinearEquiv.finiteDimensional`.
  It equips this small field with its spectral norm and takes the existing
  `Profinite.continuousMapRingObj` of its recorded valuation ring. This is the
  size transport of the specified O_E, whose absolute value is the unique one
  extending the p-adic absolute value. It requires no chosen embedding into an
  algebraic closure, no independent topology, and no equality of universes.
  All helper data are actual existing constructions; no proof is postponed in it.
- `condensedRingObj` inside the recorded constructibility predicates is exactly
  p_X^* of that condensed valuation ring, not a constant sheaf. Their ambient
  category is `DerivedCategory (Mod (Sheaf ... Ab.{u + 1}) (condensedRingObj ... X))`,
  the ordinary unbounded derived category of internal modules.

Conclusion clauses, in the same order as the statement:

1. `ObjectProperty.IsClosedUnderIsomorphisms` and `ObjectProperty.IsTriangulated`
   on `constantModelBoundedConstructible ... X` give the full triangulated
   subcategory in the specified sense (zero, every integer shift, and distinguished
   triangles with outside vertices in the property, up to isomorphism). The
   recorded `ConstantModelBoundedConstructible` is its full subcategory, so
   fullness, inherited triangles, and exact inclusion are the Mathlib construction.
   The quantified object clause states `DerivedCategory.TStructure.t.bounded K`.
   For every `n : ℤ`, its next two conjuncts put both
   `(DerivedCategory.TStructure.t.truncLE n).obj K` and
   `(DerivedCategory.TStructure.t.truncGE n).obj K` back in the same property.
2. The functor `ObjectProperty.ι (IsConstantModelConstructible ... X) ⋙
   DerivedCategory.singleFunctor _ 0` is stated to be `Full` and `Faithful`.
   Its `essImage K` is equivalent to bounded constructibility together with
   `DerivedCategory.TStructure.t.le 0 K` and `.ge 0 K`, exactly concentration
   in degree zero. Thus the assertion includes both objects and all morphisms,
   rather than merely membership of degree-zero modules.
   `Nonempty (Abelian (ConstantModelConstructible ... X))` states that the full
   category of constructible modules is abelian (Abelian contains structure and
   must be wrapped in Nonempty in a proposition).
   `ObjectProperty.IsClosedUnderKernels` and `.IsClosedUnderCokernels` state
   membership of every actual ambient kernel/cokernel of a map between objects
   of this property; their definitions quantify over the ambient universal cones.
   `ObjectProperty.IsClosedUnderExtensions` quantifies over ambient short exact
   sequences with constructible outside terms.
   `EssentiallySmall.{u + 1} (ConstantModelConstructible ... X)` gives a set of
   representatives in the fixed site/coefficient universe, not the vacuous
   essentially-small assertion in the larger object universe.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: published module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and its
  geometric setting. The setting is rendered by explicit binders; the chosen
  compactification is irrelevant to this statement but its recorded module is imported.
- `def-weil-l-adic-coefficient-extension`:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, importing
  `Sheaf.NumberTheory.Padics.CoefficientExtension`; the actual
  `Padic.coefficientExtensionIntegers`, spectral absolute value and chosen
  uniformizer are unchanged. The recorded positive-level finiteness theorem
  supplies the proof's finite residue coefficient fact.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.condensedRingObj` and
  `isCommMonObj_condensedRingObj`; `coefficientRing` and `coefficientRing_X`
  identify this unbundled encoding with the bundled inverse image.
- `sk-def-sfb-derived-categories`: ordinary Mathlib `DerivedCategory`; the
  recorded convention module
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` is imported.
  Its right-derived-functor convention is not replaced by any new category.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`,
  `IsConstantModelConstructible`, `ConstantModelConstructible`,
  `constantModelBoundedConstructible`, and `ConstantModelBoundedConstructible`.
  Their complete definitions and source docstrings were read. They require
  constant scalar matrices; upstream `IsConstructibleModuleObject` instead
  admits arbitrary local presentation matrices and is not substituted.
- `def-sbc-standard-tstructure-derived-category`: Mathlib
  `Algebra.Homology.DerivedCategory.TStructure`, `DerivedCategory.TStructure.t`,
  with cohomological `isLE_iff` / `isGE_iff`, and Mathlib's `truncLE` / `truncGE`.
- `def-weil-size-convention`: metatheoretic convention, implemented through
  explicit u and v, the existing site `Scheme.ProEt`, coefficient values in
  `Ab.{u + 1}`, the actual small coefficient transport and essential smallness
  in u+1. The node expressly has no separate definiendum or Lean declaration.
- `def-weil-triangulated-subcategory`: Mathlib
  `CategoryTheory.Triangulated.Subcategory`, `ObjectProperty.IsTriangulated`.
  Its full class signature and inherited full-subcategory structures were read.

The imports also retain all presently recorded proof-dependency modules, including
finite-coefficient triangulation/origin, derived scalar extension, the homology
sequence, the single-functor and short-exact-triangle APIs, site and module-sheaf
conventions, coefficient inverse images and Noetherian stratum detection.
`sk-lem-integral-models`, `det-pe-derived-nakayama-first-reduction`, and
`det-lem-int-integral-heart-local-model` currently have no recorded declaration;
they are used in the nine-step proof docstring, not replaced by new assumptions.
No missing proof dependency is needed to type the statement.

Edge cases checked before drafting:

- Empty X: the empty stratification and zero module/category satisfy every clause;
  no `Nonempty X`, connectedness, geometric point or chosen stratum is required.
- Zero objects: boundedness holds on any finite interval, all truncations stay zero,
  and zero is in the triangulated property and degree-zero essential image.
- Zero maps and isomorphisms of constructible modules: the cone has H^-1 equal to
  the kernel and H^0 equal to the cokernel. The zero map has source as kernel and
  target as cokernel; an isomorphism gives zero in both places.
- Multiplication by a uniformizer on the rank-one integral module: the cokernel
  is the residue module, so torsion is allowed. No flatness, lisse, finite-Tor,
  torsion-free or rational-coefficient restriction is added.
- Arbitrary positive characteristic p, with ell different from p, is retained;
  k is not required to be a finite field. All truncation indices are integers.
- All finite coefficient extensions, independently of their original universe,
  are represented by the actual algebra equivalence to their small models.

Searches for an existing statement or construction:

- `msearch.py leanfinder`, query: “Bounded constructible integral proetale complexes
  form a triangulated category stable under truncations with essentially small
  abelian constructible heart”. Eight hits: ambient derived triangulation,
  standard t-structure, homotopy triangulation, homological kernels and truncation
  bounds; none state the integral constant-model theorem or its small heart.
- `msearch.py loogle`, query: `"Constructible", "IsTriangulated"`: zero hits.
- `msearch.py grep`, query:
  `constructible.*(triangulated|abelian)|integral.*constructible`: zero Mathlib hits.
- `rg` on the source project's WeilConjectures and side project's lean/Sheaf,
  including `IntegralHeart`, `integral.*Triangulated`,
  `constantModelBoundedConstructible`, and `ConstantModelConstructible`:
  the constant-model definition exists and is used; older integral triangulation
  modules concern completed sheaves/uniform reductions, and the upstream derived
  category module concerns arbitrary local matrices. None state this node.
- Node-id search in upstream WeilConjectures: no hits.
- Exact proposed-name search in upstream WeilConjectures, lean/Sheaf and
  `dag/lean_names_upstream.json`: no collision for either declaration.
- Further coefficient searches located the existing spectral norm, valuation-ring
  definition, continuous-function ring, `Module.Finite.small`, `Shrink.algEquiv`
  and finite-dimensional transport, allowing the real-data coefficient helper.

Validation: scompile.py checked both the isolated sandbox form and the actual
library-module form cleanly (3.3 s and 3.8 s). There is no statement dispute, no
statement correction, no dependency-record repair and no new node.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
