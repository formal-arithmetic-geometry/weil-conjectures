## Worker report

Repair of the immutable returned head b5b95a9ba84d (L, H13/H2). The saved
packet was first checked unchanged: `deliver2.py --no-push` passed at 01809830479.
Its mechanical pass did not resolve the independent review's dependency-record fault.
The repair below retains the accepted item statements and changes helper ownership.

The module `Sheaf.Paper.PointAutomorphismDerivedTransportInverse` states the inverse
in three theorems: `AlgebraicGeometry.ProEtale.point_automorphism_sections_inverse`,
`AlgebraicGeometry.ProEtale.point_automorphism_finite_transport_inverse`, and
`AlgebraicGeometry.ProEtale.point_automorphism_integral_transport_inverse`.
All three transport proofs and the named exactness helper proof are `sorry`;
definitions have actual data.

Hypotheses and objects, clause by clause:

- `D : FiniteFieldDatum.{t}` binds p, a, q, k0 and its fixed algebraic closure k.
  `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`, `E : Type u`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, and `[FiniteDimensional ℚ_[l] E]` are exactly the coefficient
  hypotheses. The valuation ring, uniformizer and quotients reuse the recorded Padic
  constructions; no new choices of coefficient objects are introduced.
- `g : Spec (.of D.k) ⟶ Spec (.of D.k)` and `[IsIso g]` permit every scheme
  automorphism. There is no hypothesis that g is over k0 or is Frobenius.
- `pointRestrictionRing ... (some n)` is the finite constant coefficient sheaf of
  A_(n+1); `none` is the completed integral coefficient sheaf. Thus every positive
  finite exponent occurs, including exponent one. `pointRestrictionInverseImage`
  and `inverseImageFiniteDerived` / `inverseImageIntegralDerived` use exactly the
  action transported by the inverse of the recorded coefficient structure map.
- All complexes are `CochainComplex ... ℤ`, all derived categories are the ordinary
  unbounded `DerivedCategory`. The finite theorem quantifies over all such objects.
  The integral inverse alone uses `IsDerivedCompleteUnrestricted`, the global branch
  of the recorded `IntegralOnSlice.IsComplete`. No constructibility, boundedness,
  finite Tor amplitude or Weil structure is assumed. Site universe t and coefficient
  universe u are independent, with module size `max u (t + 1)`.
- U is `ProEt.mk (𝟙 _)`; V is `(proEtaleIsoPostcompose g).obj U`.
  `pointInverseEvaluation` and `pointInverseInsertion` are the actual evaluation and
  colimit-insertion maps in the canonical sectionwise model of the recorded inverse
  image. In this model both underlying additive maps are identity: the dependency
  restriction-naturality lemma explicitly identifies the actual distinguished
  coprojection followed by sheafification with identity in these coordinates.
  The sections theorem explicitly equates insertion's inverse with evaluation and
  gives evaluation's scalar formula with c inverse. This is the transported linear
  action on M(V); invertibility gives the corresponding linearity of insertion.
- `pointInverseRestriction` directly extracts the already specified sheaf natural
  transformation from `point_automorphism_restriction_natural`.
  `pointInverseRestrictionArrow` has underlying arrow `inv g` and is U to V.
  The sheaf isomorphism σ has this very transformation as its hom and has
  `M.val.map (pointInverseRestrictionArrow D g).op` as its inverse. With evaluation
  identity in the recorded model, that formula is exactly res_(g inverse) after E.
- `pointInverseSections` is Mathlib's `mapDerivedCategory` applied to the recorded
  `pointRestrictionSections`, and its factor isomorphism is `mapDerivedCategoryFactors`.
  The algebraic-closure instance is derived from D, and the item-owned helpers below
  expose the exactness instances for the two independent universes. No functor
  is selected from an unconstrained existence assertion. Its target is the derived category of modules over the
  recorded lifted scalar ring, hence D(Lambda) in the established size convention.
- The uniquely normalized derived natural isomorphism in the sections theorem
  agrees with the class of termwise σ on every representative, including all
  localization comparison maps. `pointInverseSigmaIso` selects precisely this
  unique isomorphism. Its inverse is rho and is natural in derived morphisms.
  Isomorphisms encode both inverse identities, not merely an isomorphism on cohomology.
- The finite theorem gives chain maps δ inverse on both sides to
  `inverseImageFiniteComparisonComplex`. Its local formula is evaluated on b times
  the recorded pullback generator restricted along `proEtaleIsoCommaArrow`:
  this is the sheafified x tensor b. The answer is
  `(inv (inverseImageFiniteCoefficientMap ...)).hom.app (op U) b • x`, exactly
  c_A inverse(b) x. No assertion that all sheafified sections are pure tensors is used.
  The next clause is naturality in chain maps. The derived transformation κ agrees
  with `inverseImagePullbackComparisonFinite` on every localized complex; Δ is its
  inverse natural isomorphism and its hom is explicitly the class of δ, with the
  exact-functor localization comparisons. Thus the representative formula is tied
  to the very specified derived comparison, for every derived object.
- The finite natural isomorphism T has hom σ followed by Gamma(κ) and inv Gamma(δ)
  followed by rho. This is precisely t and its proposed two-sided inverse in D(A_n).
  T and Δ are natural isomorphisms, so both maps are natural in all derived morphisms.
- The integral theorem introduces a coefficient-system calculus S with its existing
  coherence condition, not an additional input hypothesis. Its unit is literally
  `S.adjunction.unit.app N`. Its θ is natural on the entire ambient category and
  satisfies `inverseImagePullbackComparisonDerived ... M ≫ (θ M).hom = G.map unit`
  as whole derived maps for every M. This is the recorded normalization interface,
  without substituting an unspecified completion isomorphism or checking only
  finite reductions.
- For every derived-complete N the integral Δ has inv equal to that very κ.
  ε has hom exactly `G.map (S.adjunction.unit.app N)` and is an isomorphism; the
  displayed formula `(Δ N hN).hom = (θ N).hom ≫ ε.inv` is δ = G(u_N)^(-1) θ
  in Lean's left-to-right composition convention. Δ supplies both inverse identities
  on the entire derived objects. Its explicit naturality square covers every derived
  morphism between complete objects. Integral T has the specified hom and inv as
  above, and both naturality squares are stated explicitly.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the reexported
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing` constructions and their positive-level finiteness.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`, `ProEt.mk`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the reexported completed
  integral sheaf and `integralConstantToCompletionOfUniverses`, used through the
  recorded restriction scalar/sections constructions.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`: `inverseImagePullbackComparisonDerived`
  and reexported finite comparison, finite/integral inverse images, and coefficient maps.
- `Sheaf.Paper.DerivedCompleteOnSlices`: reexported `IsDerivedCompleteUnrestricted`,
  exactly its `IntegralOnSlice.IsComplete ... none` branch.
- `Sheaf.Paper.PointAutomorphismRestrictionNatural`: `point_automorphism_restriction_natural`,
  `pointRestrictionRing`, `pointRestrictionScalars`, `pointRestrictionScalarAt`,
  `pointRestrictionSections`, `pointRestrictionInverseImage`, `pointRestrictionRaw`.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`: its canonical evaluation
  model, `proEtaleIsoPostcompose`, and `proEtaleIsoCommaArrow` reexports.
- `Sheaf.Paper.PointProEtaleSectionsExact`: `pointModuleSections` and
  `point_proEtale_sections_exact`, the unchanged landed general-ring interface.
  The item module supplies `pointRestrictionSections_exact` and its two exactness
  instances for the existing `pointRestrictionSections` at independent universes.
- `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization`:
  `isomorphismDerivedPullbackComparisonNormalization`, its coefficient calculus and
  strict-system-limit declarations, used unchanged for the integral conclusion.
- Added already-landed statement dependency `def-weil-frobenius-point-transport`:
  `Sheaf.SixFunctors.FrobeniusPointTransport`, `WeilConjectures.frobeniusPointPrimeUnit`.
  Only its generic consequence l being invertible at every stalk of Spec k is used
  as the existing comparison's input. This theorem depends on D, l and hl alone;
  using it places no Frobenius restriction on g. No copy of that theorem is written.
- Proof import `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`:
  `SheafOfModules.exists_scalarExtensionRingIso`, the existing proof dependency.

Edge cases checked: g = identity; finite exponent one (`some 0`); zero complex;
arbitrary shifts and unbounded finite complexes; integral complete objects without
constructibility. Restriction along g and its inverse have the required opposite
slice directions. Integral incompleteness is not silently ignored: σ exists on every
ambient object, while Δ and T require completeness, precisely where the unit is inverted.
The empty scheme is excluded by the specified object Spec of a field, not by an added
hypothesis. The two independent universes retain the small pro-etale site's object
universe t+1 and morphism universe t.

Searches actually made with the prescribed msearch.py NP/item wrapper:

- LeanFinder: "Explicit inverse of derived sections transport for a scheme automorphism
  at an algebraically closed point with finite or completed integral coefficients".
  Eight hits concern SpecToEquivOfField, affine-space equivalences and structure-sheaf
  inverse formulas, including Scheme.inv_appTop; none states this module-category theorem.
- LeanSearch: "The inverse of natural transport on sections for a point scheme
  automorphism with completed coefficient sheaves". Eight hits include sheafHomSectionsEquiv,
  Scheme.inv_app, and Scheme.Modules.pushforwardId_inv_app_app. These concern other
  section functors and do not state the finite/completed comparison or its inverse.
- Loogle: `Functor.mapDerivedCategory, IsIso` reported unknown identifier, and is not
  used as evidence of absence. The successful replacement query
  `CategoryTheory.IsIso, CategoryTheory.inv` returned twelve generic categorical
  inverse facts; these do not identify any of the specified geometric maps.
- Mathlib grep via msearch: `point.*[Tt]ransport|automorphism.*transport|transport.*[Ii]nverse`
  in CategoryTheory returned thirteen unrelated enriched/monoidal transport hits.
- Direct rg searches of `lean/WeilConjectures` and `lean/Sheaf` for that vocabulary,
  then `pointAutomorphism|point_automorphism.*inverse`, found the restriction/naturality
  and scalar-extension modules, and Frobenius-specific transports. The scalar-extension
  module concerns coefficient change; FrobeniusCohomologyTransportIso restricts to
  Frobenius and constructible categories. Neither states the arbitrary-automorphism
  unbounded inverse theorem. The exact node-id grep in WeilConjectures found nothing.
  Every recorded dependency signature and docstring used here was read in source.

Source reading: the blueprint's `def-weil-global-geometric-frobenius.md` at the exact
recorded master path, with both displayed first arrows, and Deligne's PDF printed
pp. 150--152, especially (1.1.7), (1.1.10) and (1.1.11). The more general unbounded
completed-coefficient verification is correctly labelled agent work by the node.
The six current DAG proof steps are retained verbatim, and appear in the theorem docstrings.
There is no statement correction, new node, dependency-record change or disputed
statement. The exactness specialization is an item-owned helper, as requested by L.

## Second reading by NP

The dispatcher forbids starting another agent; this is a separate self-reading of the
node and final module, for the maintainer's subsequent independent review. Checked
all coefficient choices, the actual insertion/evaluation normalization, the inverse
slice arrow's direction, the positive-exponent indexing, the finite tensor-generator
formula, the exact localization comparison directions, and the integral formula's
composition order. The finite inverse is natural on all unbounded derived objects;
the integral inverse is natural between all complete objects. The completion unit is
the actual adjunction unit, and κ remains the specified resolution/Roos comparison.
No per-degree-only replacement or extra geometric/constructibility hypothesis is present.
The additional statement dependency only supplies prime invertibility already implied
by the node's hypotheses. The repair self-reading also checked the general NB
signature against its landed record: every clause stays registered there, and the
item imports it directly. The three moved helpers retain independent t and u,
quantify over algebraically closed k and both Option coefficient cases, and assert
finite-limit and finite-colimit preservation of the existing sections functor.
They now belong only to the item record. The primary recorded theorem signature
matches the source verbatim; the only item-field differences from the current
read clone are lean and the already accepted prime-invertibility stmt_dep.
Compilation and preflight results are recorded below.


## Returned H13/H2 repair

The dependency node `lem-weil-point-proetale-sections-exact` is omitted from this
packet, so its entire current sheaf-dag record stays identical, including NB's
`Sheaf.Paper.PointProEtaleSectionsExact`, `pointModuleSections` and
`point_proEtale_sections_exact` declarations and every general-ring,
derived, triangulated and cohomology clause. No dependency-record superset or
reverse import is introduced. The item imports that general module directly.

Moved `pointRestrictionSections_exact` and its two instance projections from the
old helper module into `Sheaf.Paper.PointAutomorphismDerivedTransportInverse`,
inside a section with explicit l, E, k and a binders. All three are now listed in
this item's `lean.declarations` and their docstrings name this item. The separate
helper module and dependency node copy were removed from the packet. The accepted
item's three transport theorem signatures, construction bodies and primary
`lean.statement` remain unchanged.

Universe reason: the landed general-ring interface fixes the ring and module
universe to t+1, while this item has independent coefficient universe u and module
size max u (t+1). Its sections functor also restricts the actual section-ring action
along the recorded constant-scalar map. The restriction-naturality module's
arbitrary-universe exactness fact is private. The item-owned helper exposes
exactness of precisely that existing finite/completed sections functor, with
independent universes and no additional hypothesis. Its proof docstring gives the
weak-contractibility, exact evaluation and exact scalar-restriction argument;
the instance bodies merely project the named theorem. No replacement functor or
derived category is selected. This is the exact-sections step of the item's own
proof, not a replacement record for the more general dependency.

## Validation

The saved packet's initial dry run passed at 01809830479 before this repair.
The repaired single module compiled cleanly with the prescribed `scompile.py NP
lem-weil-point-automorphism-derived-transport-inverse` command: sandbox check 9.3 s,
library-path check 9.7 s, with no errors or unexpected warnings. Auto-implicit
binding is disabled. The exact primary signature, unique declaration list, line
width and absence of the rejected dependency node/helper module were checked.
The final packet contains only the item module, item node and report. Delivery
preflight is run on that packet through the prescribed wrapper.

The repaired-packet dry run printed `OK (dry run): commit 8e3c8335b18 passes the
preflight and compiles; nothing pushed`, staging exactly those three files.
