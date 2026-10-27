## Worker report

The module `Sheaf.Paper.SupportedTorReductionPropagation` states
`WeilConjectures.supported_tor_reduction_propagation`, with exactly one postponed
proof (`sorry`). All other declarations have real data: they package hypotheses,
spell out their restriction, or specialize existing coefficient constructions.
No statement correction, new DAG node, or dependency replacement is required.
The module is in module mode, has `autoImplicit false`, explicitly binds every
universe, and uses neither private notions nor local notation/instances.

The source read was the full current blueprint proof
`main-20261015/blueprint/sec-smooth-purity/sk-prop-sf-localization/prop-sf-localization-all-stages.proof.md`,
in particular finite Tor clause (2') and Other stages (also the expanded parent
proof's steps 18–19). The item's accepted six-step split is reproduced in the
theorem docstring. This conditional lemma does not import the parent localization
proposition, assume its finite-Tor conclusions, or introduce a dependency cycle.

Hypothesis-by-hypothesis translation:

- The field is `(k : Type u) [Field k]`; the coefficient prime is `(l : ℕ)
  [Fact l.Prime]`, and invertibility in k is `_hl : IsUnit (l : k)`.
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`
  is the stated finite extension. The valuation ring, uniformizer, and quotients
  are exactly `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionUniformizer`, and `Padic.coefficientExtensionRing`.
  Index `n : ℕ` consistently means exponent `n+1`, including every positive level.
- `t : X ⟶ Spec (.of k)`, `[IsSeparated t]`, `[LocallyOfFiniteType t]`, and
  `[QuasiCompact t]` express separated finite type over k. `i : Z ⟶ X` with
  `[IsClosedImmersion i]`, `j : U ⟶ X` with `[IsOpenImmersion j]`, and
  `_hij : Set.range j = (Set.range i)ᶜ` specify the complementary pair.
- `F n : SupportedTorFiniteSetup l E n X Z U` uses the actual
  `intrinsicFiniteTorsionConstructible` full subcategories, on the intrinsic
  `proEtaleDerivedCategory` of modules over the constant coefficient sheaf.
  `I : SupportedTorIntegralSetup l E X Z U` uses precisely the recorded
  `sfIntegralConstructibleCategory`: derived completeness, all constructible
  reductions, and one common cohomological interval. No constant integral sheaf
  replaces the completed coefficient sheaf, and no auxiliary finite field is used.
- Each `SupportedTorSetup` contains the specified five functors between these
  constructible categories. Thus preservation of constructibility is in their
  codomains. `_finiteOperations` and `_integralOperations` identify the four
  ordinary operations with their existing derived pullbacks and direct images;
  the exceptional functor is the given right adjoint, not an arbitrary replacement
  for any ordinary operation.
- `closedAdjunction`, `openAdjunction`, and `exceptionalAdjunction` are the actual
  adjunction data for i^*, i_*, j^*, Rj_*, and J. `closed_counit` states exactly
  invertibility of i^*i_* -> 1. `boundary` and `distinguished` express the
  supported distinguished triangle whose first arrow is the exceptional counit
  and whose second arrow is the open unit. No uniqueness of the boundary,
  orthogonality, exceptional-open vanishing, or invertible exceptional unit is
  assumed by this package.
- `_reductions` supplies `SupportedTorReduction I (F n)` along the existing
  `scalarReductionDerivedExtension`, restricted using `ObjectProperty.lift` and the integral object’s membership proof.
  Its five natural isomorphisms express the reductions of i_*, i^*, j^*, Rj_*, J.
  Its six equations preserve both unit and counit of each given adjunction using
  those very isomorphisms. They are explicit commuting squares, not mere
  nonemptiness of an unspecified map. The given comparisons are hypotheses,
  rather than constructions chosen from a postponed existence theorem.
- `N : ℕ` expresses a nonnegative bound independent of the separately quantified
  finite level n. `hfinite` uses `SupportedTorInputBounds (F n)` and the recorded
  `HasProEtaleTorAmplitude` on each actual finite category. Its four conjuncts
  preserve [a,b] for i_*, i^*, j^* and give [a,b+N] for Rj_*. These predicates
  quantify over ALL module-sheaf tests, not only residue fields or constructibles.

Conclusion-by-conclusion translation:

- The first conjunct quantifies over every finite level, constructible K, and
  integer endpoints a,b. Given its recorded all-module Tor interval, it asserts
  the same Tor predicate on `(F n).exceptional.obj K` with `[a,b+N+1]`.
- The next two conjuncts inside that finite assertion are
  `SupportedTorResidueBound` for i_* J K on X and J K on Z. Its residue ring is
  literally `A_(n+1) ⧸ Ideal.span {image of the recorded uniformizer}`. It applies
  the existing `AlgebraicGeometry.Scheme.derivedTensorRing` along the quotient
  homomorphism on every K-flat resolution of every representative isomorphic to
  the given object, and asserts `IsZero` of standard homology for `q<a` or
  `b+N+1<q`. Thus both tensors and both bounds in the node are present; no
  flatness or perfectness of kappa is assumed.
- The next main conjunct is `SupportedTorInputBounds I` with interval predicate
  `a ≤ b ∧ ∀ n, HasProEtaleTorAmplitude ... (scalarReductionDerivedExtension.obj K)`.
  This states all four integral estimates using a single interval of the actual
  reductions: unchanged for i_*, i^*, j^*, enlarged by N for Rj_*.
- The following conjunct states that J has interval `[a,b+N+1]` at every
  reduction whenever K has `[a,b]` at every reduction. Quantification order
  retains uniformity. It does not infer an inverse-limit cohomological estimate.
- `SupportedTorRestriction (F n)` and `SupportedTorRestriction I` use exactly
  `finiteTorConstructible` and `finiteTorConstructibleIntegral`, pulled back to
  their respective constructible domains. They assert existence of restricted
  functors, with equality of each composite with the full-subcategory inclusion
  to its original composite. They retain all six original unit/counit maps by
  HEq under those equalities, and the identical ambient connecting arrow. The
  restricted supported triangles are distinguished in the same ambient category.
  This is the inherited-triangle description of the full triangulated subcategory,
  not merely an assertion of objectwise membership.
- For EACH of X, Z, U the conclusion explicitly asserts repleteness and
  `ObjectProperty.IsTriangulated` for both ambient finite and integral ctf
  predicates. Mathlib's full-subcategory construction therefore supplies the
  inherited shifts and distinguished triangles, and the inclusions are exact.
- Within each `SupportedTorRestriction`, the last two implications say that any
  ambient `∀ G, IsZero (J (Rj_* G))` and `∀ Q, IsIso (exceptional unit at Q)`
  restrict to the full subcategories. These are conditional consequences and are
  not silently added as assumptions of the theorem.
- The two final clauses instantiate `finiteTorFieldCoefficientCategory` at the
  actual rational constructible category and at the actual common-stage
  algebraically closed constructible category, for every scheme Y. These are
  literal definitional equalities, precisely the node's equality by definition.
  Their equality of types is also equality of the inherited category and of every
  functor/triangle/adjunction read there; there is no additional restriction.
  The algebraic closure has its own universe v, independent of the scheme
  universe u, so larger algebraically closed coefficient fields are included.

Dependency declarations read and used (their complete signatures and docstrings
were inspected in the local live source):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; it publicly supplies the original
  `CoefficientExtension` constructions named above.
- `Sheaf.Paper.SfIntegralConstructible`:
  `WeilConjectures.sfIntegralConstructible` and
  `WeilConjectures.sfIntegralConstructibleCategory`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `WeilConjectures.scalarReductionDerivedExtension`, on the existing
  `scalarReductionSource` and `scalarReductionTarget` with their exact site
  universes. The theorem spells out `ObjectProperty.lift` directly using the existing
  object's constructibility proof; it introduces no new reduction construction.
- `Sheaf.Paper.FiniteTorAmplitudeSites` (recorded finite-Tor dependency): its
  retained `Sheaf.Paper.FiniteTorAmplitude` definitions
  `finiteTorConstructible`, `finiteTorConstructibleIntegral`, and
  `finiteTorFieldCoefficientCategory`; and its retained
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude` from
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor` is
  publicly retained by that recorded dependency. Its fixed-ModuleCat endpoints
  differ from the recorded intrinsic constructible categories. The residue
  formula uses the ALREADY EXISTING intrinsic presentation
  `AlgebraicGeometry.Scheme.derivedTensorRing` in
  `Sheaf.Algebra.Homology.DerivedTensor`, already publicly imported through the
  Tor predicate. This is the same ordinary K-flat total tensor, with the actual
  constant quotient module; there is no second derived tensor definition.
- `Sheaf.Paper.SfDerivedDirectImage`:
  `WeilConjectures.sfCompletedDerivedDirectImage` and the retained
  `AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage`.
- `Sheaf.Paper.DerivedPullbackTensorHom`:
  `WeilConjectures.finiteDerivedPullback` and its retained
  `WeilConjectures.integralDerivedPullback`, plus the actual field-stage
  categories used in the final clauses. No new pullback is defined.
- The scheme-property convention node defines no declaration: its referenced
  Mathlib classes `IsClosedImmersion`, `IsOpenImmersion`, `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact` are used directly.
- The triangulated-category leaf's `CategoryTheory.Pretriangulated`,
  `CategoryTheory.Pretriangulated.distTriang`, and `Triangle.mk`; the
  triangulated-subcategory leaf's `CategoryTheory.ObjectProperty.IsTriangulated`.
- Plain proof imports: `Sheaf.Paper.FiniteCtfTriangulated` with
  `AlgebraicGeometry.Scheme.finite_ctf_isTriangulated`;
  `Sheaf.AlgebraicGeometry.ProEtaleTorIntervalTriangle` with
  `AlgebraicGeometry.Scheme.coefficientProEtale_tor_interval_triangle`;
  `Sheaf.Paper.SfIntegralConstructibleTriangulated` with
  `WeilConjectures.sfIntegralConstructible_isTriangulated` and repleteness;
  `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, retaining the generic
  ringed-site universal derived change-of-rings pair of its recorded dependency.
  Its ordinary-module extension is not substituted for the ringed-site reduction.
  The proof will transport the coefficient-sized Tor-triangle theorem to the
  intrinsic presentation, as its docstring states. No API replacement is claimed.

Edge cases checked mathematically before the statement:

- n=0 is exponent 1, never the zero quotient A_0. All n>=1 are covered.
- N=0 gives `[a,b+1]` for J; no strict positivity is used. Signed endpoints and
  single-degree intervals a=b remain allowed. The recorded Tor predicate itself
  requires a<=b, so an impossible interval does not create a false conclusion.
- Zero K, empty X/Z/U, i or j an identity, and a zero exceptional/open functor
  are permitted. There is no nonempty-scheme or positive-dimension hypothesis.
- For n>1, kappa need not be perfect or flat over A_n; no such binder exists.
  Quantification over its K-flat resolutions and all-module Tor tests is essential.
- Integral bounds refer to reductions only; derived completeness is retained by
  the actual category. No equality of site object and morphism universes is
  imposed, and no false finite-field hypothesis is used.
- Exceptional-open vanishing or invertibility of the exceptional unit need not be
  supplied to obtain the interval and restriction conclusions; if supplied, the
  final implications of the restriction predicate retain them.

Searches for existing notions/statements, 2026-10-22:

- `msearch.py ... leanfinder "Supported localization triangle Tor amplitude a to
  b plus N plus one uniform integral reduction restriction adjunction"`: 8 hits
  (`DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`, `IsGE`, `IsLE`, canonical
  t-structure and localization bounds). None states this coefficient-aware
  supported bound plus integral restriction.
- `msearch.py ... loogle "CategoryTheory.ObjectProperty.lift,
  CategoryTheory.Adjunction"`: zero hits. The local Mathlib full-subcategory
  source nevertheless gives `ObjectProperty.lift`, used for canonical reduction.
- `msearch.py ... grep
  "(TorAmplitude|torAmplitude).*(support|reduction)|supportedLocalization"`:
  zero Mathlib hits. Raw launcher search records remain in sandbox searches.jsonl.
- Local `rg` on `lean/WeilConjectures` and `lean/Sheaf` for supported Tor,
  `sfSupported`, and the intended declaration names, and `grep -rn` of the item
  id in `lean/WeilConjectures`: no duplicate of this statement or helper names.
  The parent `SfLocalizationAllStages` has stronger, all-stage existence packages;
  it is downstream of this lemma and cannot be used as its hypothesis. Its
  hypotheses include uniqueness/orthogonality and Tor conclusions absent here;
  this module packages only the smaller conditional data actually specified by
  this node. Existing finite/integral category notions and Tor tests are reused.

Validation: server-only `scompile.py` accepted the complete statement; the first
pass found eight long-line warnings, all fixed. Its next complete run was clean
(sandbox 37.5 seconds; library 17.5 seconds). The delivery dry run then passed with commit 178ffc5f804. A final
interface audit inlined the canonical reduction restriction with `ObjectProperty.lift`
instead of naming a helper also present in the downstream parent proposition;
the final dry run and delivery recheck this last change. No global build or live-file
edit was performed. No statement dispute or node fault was found.

## Second reading by Q150

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
