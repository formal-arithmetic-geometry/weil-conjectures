## Worker report

Item: lem-pur-clopen-completed-operation-towers. Module:
`Sheaf.Paper.ClopenCompletedOperationTowers`, namespace
`WeilConjectures.ClopenCompletedOperations`.

The main theorem asserts two comparison propositions with existential data. These are conclusions,
not assumptions: `TensorComparison` and `ScalarComparison` retain the strict tower,
their generator formulas, the chain Roos isomorphisms with both coordinates normalized,
the natural derived isomorphism, and its computation on every good representative.
All postponed proofs are named theorems with source and proof docstrings.

Hypotheses and clauses, in the order of the node:

- `X : Scheme.{t}`, `I : Type w`, `[Finite I]`, `Xi`, `j`, the two immersion
  instance families, `hd : Pairwise ... Disjoint ...`, and `hc : ∀ x, ∃ i, ...`
  express precisely a finite disjoint clopen partition. No nonemptiness is required.
- `[Fact l.Prime]` and `hl : IsUnit (l : Γ(X, ⊤))` express primeness and
  invertibility on X. `E`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]` are the finite local coefficient extension.
  Valuation, integer ring, uniformizer and quotients are the recorded Padic constructions.
  The natural number n denotes exponent n+1, so every positive level is included.
- The site is `Scheme.ProEt` with topology `Scheme.ProEt.topology`, with object
  universe t+1 and morphism universe t. Coefficients and module sections live in
  max u (t+1); t and u are independent.
- `ringIso` and `finiteIso` select the existing `clopen_integral_coefficients`
  comparisons, whose specification preserves constant sections, projections,
  coefficient transitions and the map from integral constants. As ring isomorphisms
  these preserve 1. They are not arbitrary coefficient identifications.
- `restriction` is actual sectionwise `clopenModuleRestriction` followed by
  `SheafOfModules.restrictScalars` along the inverse completed coefficient iso.
  `cxRestriction` applies it degreewise, `dRestriction` is exact derived restriction,
  and `towerRestriction` is whiskering in the strict inverse-system category.
- The resolving objects are the existing `integralOperationsGoodComplex` full
  subcategory: K-flat plus flat terms, with no degree bounds. `goodRestriction`
  records that their restrictions are still admissible. No completeness assumption
  is imposed. A resolution of M is an identification Q(P) ≅ M; naturality of the
  derived comparison and the equation for every P imply the same equation after
  conjugating by any such identification, and similarly for N.
- `tensorTower` is the existing `integralOperationsTensorTowerFunctor` restricted
  to good pairs. Its level is exactly Res_n(P_n total-tensor Q_n). The tower witness
  of `TensorComparison` is an isomorphism of functors with values in strict towers,
  hence includes all quotient transition squares and naturality in P and Q.
- `tensorPure` uses the existing `unrestrictedIntegralTensorSection` twice and
  `integralOperationsTotalTensorSection` to insert the result into each (p,q)
  direct-sum summand. The tensor equation gives exactly the formula in the node;
  the coefficient sections are carried by `finiteIso` and module sections by
  sectionwise restriction. The total tensor has the existing signed differential.
- The derived witness of `TensorComparison` compares the actual completed tensor functors on
  all unbounded derived inputs, naturally in both arguments.
- `productMap` is piComparison followed by the product of the specified tower maps.
  `RoosNormalized` fixes both mapping-fibre coordinates to this same map, namely
  (y,x) ↦ (Ay,Ax). `roos_restriction` states this naturally for ALL strict towers
  and strict tower morphisms, including maps unrelated to resolutions.
- The existential `roos` comparison and its normalization retain that chain
  comparison for all strict towers. `resolution` is an equality with the existing representative comparisons
  and exact restriction's `mapDerivedCategoryFactors`, so the derived comparison
  is induced by this cone map, independently of resolution choices.
- For every `L` with the same finite-extension instances and every algebra embedding
  `ι : E →ₐ[Padic l] L`, `scalarTower` uses `integralScalarTowerFunctor`.
  This uses exactly `integralScalarRho = pi_E ≫ integralScalarQuotientSheafMap`;
  no replacement coefficient map is assumed. The tower witness of `ScalarComparison` compares
  restriction over the completed L ring with extension after restriction over E.
- The tensor equation of `ScalarComparison` gives p tensor a ↦ r(p) tensor r(a), and the unit equation
  specializes this to a=1. Naturality in the tower index includes every transition
  p tensor a ↦ p tensor bar(a), with the original quotient maps and inclusion.
  The Roos, cone, derived, and resolution clauses give the identical strict-cone
  normalization and representative independence for integral scalar extension.
- `clopen_completed_operation_towers` quantifies over all components and all such
  L and ι. There is no unramifiedness, boundedness, completeness, finite-type or
  quasi-compactness assumption, and no functorial-cone assertion for a bare
  triangulated category.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`; OpenImmersion:
  `AlgebraicGeometry.IsOpenImmersion`; Morphisms.ClosedImmersion:
  `AlgebraicGeometry.IsClosedImmersion`; Sites.Proetale: `Scheme.ProEt` and topology.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`, the
  transparent existing `SheafOfModules` presentation.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`, `DerivedCategory.Q`;
  ExactFunctor: `Functor.mapDerivedCategory` and `mapDerivedCategoryFactors`.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite and its public dependency:
  `Padic.finite_coefficientExtensionRing`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, `coefficientExtensionRing`.
- Sheaf.Paper.CompletedIntegralConstantMapOfUniverses and its public dependencies:
  `integralConstantToCompletionOfUniverses`, `integralCoefficientSheaf`,
  `completedIntegralCoefficientSheafUnrestricted`, the system and projections.
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients:
  `CochainComplex.IsKFlatIndependentCoefficients`; FlatOnSite:
  `SheafOfModules.IsFlatOnSite`, used inside the existing good-complex predicate.
- Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction:
  `scalarReductionDerivedExtension`; IntegralReductionTowerUnrestricted:
  `unrestrictedIntegralFiniteComplex`, `unrestrictedIntegralTensorSection`.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses: the recorded
  monoidal tensor; Mathlib.Algebra.Homology.BifunctorShift: total cochain tensor;
  Mathlib.CategoryTheory.Functor.OfSequence: `Functor.ofOpSequence`;
  Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings: `restrictScalars`.
- Sheaf.Paper.IntegralDerivedOperationsOnSlices publicly retains
  `integralCompletedTensor` and `integralCompletedTensorComparison`; its global
  comparison identifies the slice-interface global tensor with this strict-Roos model.
- Sheaf.Paper.IntegralOperationsWellDefined: the good class, localized good class,
  finite tensor levels, transitions, tensor generators, strict tensor tower and Roos functor.
- Sheaf.Paper.IntegralScalarExtensionUniverses: `integralScalarExtensionOfUniverses`
  and `integralScalarExtensionComparisonOfUniverses`; its public dependencies give
  `integralScalarRho`, `integralScalarTensorSection`, and `integralScalarTowerFunctor`.
- The clopen module-gluing, total-tensor/K-flat detection, unbounded-localization,
  and strict-tower/Roos modules are imported, with their actual interfaces read.
  Other already stated proof dependencies are imported without `public`.
  `lem-pur-clopen-derived-scalar-compositor` has no recorded module in this checkout;
  it is a proof dependency only and supplies no notion needed to type this statement.

Edge cases checked before writing: I empty forces X empty by hc; empty components
have zero module categories; singleton partitions and identity immersions; zero P or Q;
positive level one (n=0); L=E with identity ι; ramified finite extensions (the existing
quotient inclusion works since varpi_E^m O_L is contained in varpi_L^m O_L);
unbounded P,Q and arbitrary independent scheme/coefficient sizes.

Searches performed through msearch.py:

- LeanFinder: "Clopen restriction commutes with strict towers defining completed tensor
  products and integral coefficient extension with pure tensor maps" returned eight
  hits, including `AdicCompletion.ofTensorProduct_naturality`, tensor maps and integral
  closure, none about the pro-etale strict towers in this item.
- Loogle: "Functor.ofOpSequence, SheafOfModules.restrictScalars" returned zero hits,
  with the diagnostic "unknown identifier 'Functor.ofOpSequence'". This was a search
  service limitation; the actual local source declaration was read and used.
- Mathlib grep via msearch: `clopen.*(completed|scalar)|completed.*clopen` returned zero hits.
- rg in lean/WeilConjectures and lean/Sheaf with the same pattern and the item id found
  clopen coefficient and scalar-calculus dependencies and the narrower existing
  ClopenRoosIntegralDescent consumer, but no exact theorem. The latter imposes a
  finite-field/finite-type setting and cannot state this arbitrary-scheme item.

`tensorRoosIso` and `scalarRoosIso` are reflexive identifications with the actual
strict Roos models. `tensorModelComparison` and `scalarModelComparison` compose
the recorded derived representative comparisons with those identifications.
`roosMap` is the actual composite of the normalized restriction Roos map and
RoosFunctor applied to the strict tower isomorphism. These helpers contain real
data and do not introduce any independent notion. The comparison propositions
use existential witnesses and conjunctions to avoid expensive structure recursors.

No node correction, new independent notion, or dependency-record repair is required.
The existing helper draft in this sandbox was retained and repaired; its failing
reducibility override and unscoped heartbeat option were removed. No live file was edited.

## Second reading by NE

The worker reread the node and complete module; the maintainer's independent review
is still required and no independent subagent was started (dispatcher instruction).
The comparison propositions are existential conclusions of the main theorem, not added
hypotheses. Checked the directions of ringIso.inv (component ring to restricted
ambient ring), tower and derived comparisons, and both representative squares.
Checked that scalar restriction changes the action only, so the section variables
in the pure-tensor formulas have the intended types. Checked that the cone record
uses the same product comparison on both coordinates and that resolution equations
refer to the recorded operation comparisons. The unrestricted operations and the
actual pro-etale site are retained. The node statement is unchanged.

Validation: scompile.py compiled both the sandbox and final library module cleanly,
with no errors or warnings (40.6 s and 33.8 s respectively).
