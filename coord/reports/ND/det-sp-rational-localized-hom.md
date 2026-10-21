## Worker report

The module `Sheaf.Paper.RationalLocalizedHom` states
`AlgebraicGeometry.ProEtale.RationalLocalizedHom.rationalLocalizedHom`, with `sorry`.
All other declarations are concrete coefficient, scalar-action, functor, or proposition
interfaces belonging to this statement; their names are recorded in `lean.declarations`.
No new independent notion, dependency replacement, or statement correction is delivered.

Hypotheses and objects, clause by clause:

- The prime is `ℓ : ℕ` with `[Fact ℓ.Prime]`. The base is `k : Type u` with
  `[Field k]`, `[Fact (ringChar k).Prime]`, and `[Fact (ringChar k ≠ ℓ)]`.
  A prime ring characteristic is exactly positive characteristic in the node.
- `T : Scheme.{u}` and `[T.Over (Spec (.of k))]` fix the structural morphism.
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on that morphism express
  separated finite type; `[IsNoetherian T]` is the stated Noetherian condition.
- `E : PadicAlgCl.FiniteIntermediateField ℓ` uses the published embedded finite
  coefficient-field convention. Its integers are `PadicAlgCl.integers ℓ E.1`.
  It includes the base coefficient field and ramified finite extensions. The induced
  norm and ultrametric instances are the existing canonical ones.
- `integral` and `rational` abbreviate the ambient derived categories of internal
  modules on the small pro-etale site, over `condensedRingObj` of respectively
  `Profinite.padicIntegersRingObj ℓ E.1` and `Profinite.continuousMapRingObj E.1`.
  These are continuous condensed coefficients, not discrete constant rings.
- `integralConstructible` and `rationalConstructible` abbreviate the published general
  `boundedConstructible` predicates. Thus the categories are precisely the full
  bounded constructible subcategories specified in the node; there is no substituted
  constant-model or finite-Tor-amplitude condition. The integral derived-complete
  interpretation is the identification referred to in the node, not an additional
  hypothesis or a newly defined completion. `integral_models` is publicly imported.
- `extend` is `(Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor`.
  Thus it is exactly derived extension along the continuous coefficient inclusion.
- The first conjunct quantifies over every rational ambient object satisfying
  `rationalConstructible`, and supplies an integral ambient object satisfying
  `integralConstructible` together with `Nonempty (F.obj K₀ ≅ K)`.
- The second conjunct quantifies over both integral constructible objects and every
  `q : ℤ`. It supplies an `E.1`-linear equivalence from
  `E.1 ⊗[PadicAlgCl.integers ℓ E.1] (K₀ ⟶ L₀⟦q⟧)` to the rational shifted Hom.
  Coefficient-first tensor notation is the symmetric form of the node's Hom-first
  tensor product; it supplies the usual left E-module structure without a second
  tensor-product definition. Full subcategory Hom is the same ambient Hom.
- The formula on every `e ⊗ₜ h` is precisely multiplication by `e` of `F.map h`,
  composed with the canonical `F.commShiftIso q` component. This uniquely specifies
  the natural map, rather than merely asserting existence of an abstract isomorphism.
  The scalar action comes from constant continuous scalar sections, through the
  actual published continuous module equivalence and its derived equivalence.
- `Comparisons ℓ k E` quantifies over all `f : X ⟶ Y` in the over-category of
  `Spec k`, with both objects Noetherian separated finite type. Such a morphism is
  automatically separated finite type, so there is no extra restriction on f.
- The pullback membership conjuncts assert that integral pullback is integral
  constructible and rational pullback of the rationalization is rational constructible.
  `IsIso (Functor.whiskerLeft ... (CondensedRing.derivedPullIso ...).inv)` asserts
  invertibility of the canonical natural comparison on the full integral subcategory,
  with the orientation written in the node. The other endpoint is constructible by
  the published bounded-constructible scalar-extension preservation interface.
- The compact-support membership conjuncts make both analogous restrictions valid.
  `shriek` is the ambient `rightDerivedLowerShriekOfCompactification` using the
  standing `compactificationOverField f`. In particular it is the prescribed ambient
  composite, not a replacement compact-support functor. `shriekComparison` uses
  `CondensedRing.derivedLowerShriekHom`, with exactly that same compactification.
  Its whiskering by the full integral inclusion is asserted `IsIso`; inversion gives
  the orientation in the node. These are natural-transformation statements, so the
  canonical comparisons are natural in K₀ and M₀, not isolated objectwise isomorphisms.

Dependency declarations read and used (publicly imported, also through their published
parent modules):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`,
  `AlgebraicGeometry.ProEtale.boundedConstructible`, and `BoundedConstructible`.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` and continuous
  coefficient ring objects.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing` and `condensedRingObj`.
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`:
  `coefficientBoundedConstructibleProEtale` and its exported general bounded
  constructibility interface. The specialized discrete predicate is not substituted.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` and the ordinary
  derived-category framework it imports.
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  `CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction` and the canonical
  `leftDerivedFunctor` of scalar extension.
- `Sheaf.Paper.IntegralModels`: `AlgebraicGeometry.ProEtale.integral_models`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`:
  `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the embedded coefficient-field interface.
- The proof-dependency modules are imported for stage 3: coefficient localization,
  ringed-site Grothendieck abelianness, pro-etale site, Ext continuity, integral
  generators, triangulated derived categories and triangle isomorphism lemmas,
  canonical coefficient comparisons, cartesian coefficients, integral operations,
  constructibility, restricted pushforwards, and bounded direct-image continuity.
  The theorem docstring records the proof through these dependencies, including the
  common lower bound, denominator clearing, cone lifting, and compactification steps.

Edge cases checked mathematically before writing: the empty scheme and zero complexes
satisfy the same formulations; zero Hom modules are allowed; all negative, zero, and
positive shifts are quantified. No nonzero model or Hom, nonempty scheme, dimension
bound, uniformizer choice, or unramified condition is imposed. Integral ell-power
 torsion may rationalize to zero, as required; the theorem never asserts integral
faithfulness. The identity morphism, open immersions, and proper morphisms are included
in `Comparisons`. The characteristic assumptions permit ell = 2 with any different
positive characteristic. One site universe u is arbitrary, while the ambient module
and derived universes are the published u+1 (the auxiliary continuous-module encoding
uses its standard u+2 derived localization); no equality between site universes is added.

Searches for an exact existing statement:

- `msearch.py ND det-sp-rational-localized-hom leanfinder` with query
  "Rational constructible pro-etale complexes admit integral models and their Hom
  groups are obtained by tensoring with the l-adic field": returned eight unrelated
  BDeRham/BDeRhamPlus and etale finite-presentation hits, no exact statement.
- `msearch.py ... loogle "TensorProduct.lift, LinearMap"`: found tensor-product
  lift/basic linear-algebra interfaces, no statement of this geometric theorem.
- `msearch.py ... grep "rational.*[Hh]om|localized.*[Hh]om|integral.models"`:
  categorical localization and other results, no exact aggregate statement.
- Direct `rg` searches in the project's `WeilConjectures` and `Sheaf` for rational
  Hom, localized Hom, integral models, and scalar-action interfaces, and a search
  for the exact node id in upstream sources, found no exact declaration.
  `EllAdicRationalization` is used for its published coefficient interface; its
  localization theorem does not specify this natural tensor Hom map and compact
  support clause. `ConstructibleRationalHomComparison` uses a different intrinsic
  completed-category interface and does not state this aggregate node.

All helper definitions contain actual data. The single postponed theorem is the
matching DAG statement, with its natural-language proof in the docstring. No node
fault or STATEMENT-DISPUTED flag is raised. The node's other fields are unchanged.
Compilation uses only the prescribed server `scompile.py`; the final delivery dry run
also compiles the file and runs the maintainer's preflight.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
