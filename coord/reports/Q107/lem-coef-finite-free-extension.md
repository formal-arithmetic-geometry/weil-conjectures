## Worker report

This delivery states `WeilConjectures.FiniteFreeCoefficients.finite_free_coefficient_extension`
in `Sheaf.Paper.FiniteFreeCoefficientExtension`. It retains the node's statement and proof.
The only postponed theorem is the item itself; helper definitions have real data.

### Hypotheses and clauses

- The global datum is `D : FiniteFieldDatum.{u}`. Its fields specify the finite field,
  characteristic prime, cardinality, and algebraic closure. The prime coefficient
  characteristic is `(l : ℕ) [Fact l.Prime]`; `_hl : l ≠ D.p` is the required inequality.
- `E : Type (u + 1)` with `Field E`, `Algebra (Padic l) E`, and
  `FiniteDimensional (Padic l) E` is an arbitrary coefficient field. The successor
  universe accommodates the real p-adic field even when the schemes have universe zero.
- `Stage l E`, imported from `FiniteCoefficientAdjointComparisons`, retains an actual finite
  coefficient extension, its embedding of E, and a positive exponent. `Stage.parameter`
  is the image of the BASE uniformizer. `Stage.ring` is precisely O_L/(varpi_E^n),
  not O_L/(varpi_L^n). `baseCoefficientEquiv` identifies the identity-field stages
  with the already recorded O_E/(varpi_E^n).
- The first conjunct supplies a positive `e : ℕ+` and unit `z : s.integersˣ`, with
  `s.parameter = z * coefficientExtensionUniformizer ... ^ e`. It asserts equality
  of the power ideals at every n and `∀ r, ∃ n : ℕ+, r ≤ e*n`, the cofinality clause.
- The second conjunct says equal-level `Arrow`s are `Arrow.IsFiniteFree`, the existing
  predicate `Module.Finite ∧ Module.Free` for the actual quotient-map algebra structure.
- The third conjunct quantifies over T, X, Z over Spec D.k. Each structure morphism
  is separated, locally finite type and quasi-compact, hence separated finite type.
  The f binder has exactly these morphism properties and is a morphism over the base;
  i is a closed immersion over the base. The compactification c supplies the same
  structure-morphism exceptional adjunction used to define the dualizing object.
- `Cat` is the recorded ordinary etale module derived category. `Sites.D false` is
  that category; `Sites.D true` is the ordinary module derived category of the actual
  small pro-etale site. Both retain object universe u+1 and morphism universe u for
  the site, with coefficients in u+1.
- `Ctf` uses the recorded finite-value `isBoundedConstructible`, together with
  `∃ a b : ℤ, a ≤ b ∧ hasTorAmplitudeIn ... a b`. The latter tests every degree-zero
  module sheaf. Pro-etale inputs use exactly `ProEtale.DerivedCategory.constructibleFiniteTor
  (ModuleCat A) X`, including its own Tor tests on every pro-etale sheaf. No etale-origin
  replacement of that object property is defined here.
- `Sites.Calculus.direct_iso` asserts invertibility of the canonical
  `finiteCoefficientDirectImageMap` / `finiteCoefficientChangeDirectImageMap` on K
  in Dctf(T,A). Their prescribed coefficient-adjunction normalization fixes the
  direct-image projection arrow; it is not a freely chosen endpoint isomorphism.
- `closed_iso` concerns the scalar-extended ordinary etale right adjoint of i_*;
  on the pro-etale side the functor is precisely nu_Z^* i^times Rnu_X,*.
  `Normalized.etale_closed` fixes its arrow by the exceptional counit transpose,
  and `closed_counit` writes the counit square explicitly.
- `omega_iso` concerns `omega = upper.obj one`, where `upper` is the ordinary etale
  compact-support right adjoint of the structure morphism, transported to the
  pro-etale realization. `Normalized.etale_omega` fixes the scalar-extended
  compact-support counit transpose, followed by the regular coefficient-unit map.
  `compact_support_iso` supplies its inverse domain and `omega_counit` its equation.
- `hom_iso` is the fourth displayed comparison. `homMap` is the transpose of
  scalar-extended evaluation using the ordinary normalized tensor balancing map.
  `tensor_normalized` ensures the tensorator is the published ordinary comparison.
- `dual_iso` is the fifth displayed comparison: `dualMap` is `homMap` at omega,
  followed by Hom of `omegaMap`. This fixes the actual Verdier map.
- `evaluation_eq` and `bidual_eq` are the evaluation and double-dual commuting
  diagrams. The dual-first evaluation includes the signed tensor symmetry;
  the double-dual map is its tensor-Hom transpose.
- The `*_natural` fields give object-map naturality; the `*_unit` fields give the
  identity field embedding and identity quotient cases. The `*_comp` fields use
  the existing `Arrow.ringMap_comp` and canonical tensor reassociations to give
  composition for further field extension, coefficient reduction, and mixed squares.
  In particular the two paths A_n -> B_n -> B_m and A_n -> A_m -> B_m have the same
  composite Arrow, so these equations are exactly the required reduction squares.
- `Normalized.closed_site`, `omega_site`, `hom_site`, and `dual_site` retain the
  actual canonical site bridges and their coefficient squares, including the
  invertibility clauses on their specified finite-Tor domains.
- `DirectGeometry`, `HomGeometry`, and `ExceptionalGeometry` state the commuting
  Cartesian squares for every scheme isomorphism. The exceptional square allows
  its base scheme to move. The actual `ClosedGeometry` square handles i separately, while its structure-morphism
  specialization gives dualizing naturality; Verdier is their specified
  Hom/dualizing composite. This includes geometric Frobenius id x Spec(gamma)
  and does not assume the absolute Frobenius of an arbitrary scheme is invertible.

### Dependency declarations used

- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `cor-coef-finite-verdier`: `Sheaf.SixFunctors.FiniteCoefficientVerdier`, `WeilConjectures.finite_coefficient_verdier`.
- `lem-weil-finite-duality-site-comparison`: `Sheaf.SixFunctors.FiniteDualitySiteComparison`, `WeilConjectures.finite_duality_site_comparison`.
- `lem-coef-finite-dualizing`: `Sheaf.SixFunctors.FiniteDualizing`, `WeilConjectures.finiteDualizingCoefficientComparisons`.
- `lem-coef-finite-closed-shriek`: `Sheaf.Paper.FiniteClosedShriek`, `WeilConjectures.finiteCoefficientClosedShriek`.
- `lem-weil-duality-pairing`: `Sheaf.Paper.DualityPairing`, `AlgebraicGeometry.Etale.ambient_duality_pairing`.
- `thm-coef-finite-hom`: `Sheaf.Paper.FiniteCoefficientHomChange`, `WeilConjectures.finiteCoefficient_derivedHom_change`.
- `lem-coef-finite-direct-image`: `Sheaf.Paper.FiniteCoefficientDirectImage`, `AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_isIso`.
- `def-sf-evaluation-hom-site-comparison`: `Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison`, `AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom`.
- `def-weil-global-geometric-frobenius`: `Sheaf.Paper.GlobalGeometricFrobenius`, `WeilConjectures.globalGeometricFrobenius`.
- `def-per-exceptional-coefficient-maps`: `Sheaf.Paper.ExceptionalCoefficientComparison`, `AlgebraicGeometry.Etale.ExceptionalCoefficients.compactSupportMap`.
- `def-weil-pbc-constructible-complexes`: `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`, `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `def-pur-exceptional-coefficient-base-change-square`: `Sheaf.Paper.ExceptionalCoefficientComparison`, `AlgebraicGeometry.Etale.ExceptionalCoefficients.BaseChangeCompatibility`.
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `lem-pur-derived-change-of-rings`: `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`, `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `def-kun-projection-formula-map`: `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`, `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`.
- `def-weil-finite-torsion-constructibility`: `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`, `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `def-coef-finite-coefficient-stages`: `Sheaf.Paper.FiniteCoefficientAdjointComparisons`,
  `AlgebraicGeometry.FiniteCoefficientAdjoints.Stage` and the Stage/Arrow declarations
  listed in that definition node. The unrelated adjoint-comparisons theorem is no longer
  a statement dependency.
- `lem-weil-proetale-direct-image-restriction-of-scalars`:
  `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`,
  `AlgebraicGeometry.ProEtale.fixedScalarRestrictionDirectImage`, used for the
  canonical pro-etale scalar/pullback comparison.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`, `CategoryTheory.derivedInternalHomOfUniverses`.
- `def-weil-exceptional-inverse-image`: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, `WeilConjectures.ConstructibleExceptionalCoefficients.System`.
- `thm-amb-etale-exceptional-adjoint`: `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`, `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
- `lem-exc-closed-ambient`: `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`, `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.

The existing canonical exceptional coefficient arrows, their geometric square, and the
canonical site Hom comparison remain reused. The new owning definition node records the
published Stage/Arrow interface. The item uses no conclusion chosen from the theorem
`finite_coefficient_adjoint_comparisons`.

### Edge cases

Identity extensions have e=1 (up to the unit for the chosen uniformizer), and all
identity Arrow cases are retained in the five unit equations. Stage exponents are positive,
so n=1 and m=n are included while the excluded n=0 is not accidentally required.
The ideal equality is also asserted at zero power, where both sides are the unit ideal.
An empty scheme is allowed; no positive dimension, nonzero complex, nonzero rank, or
nonempty stratum hypothesis is imposed. The zero complex is tested by the same ordered
Tor interval, for example [0,0]. Ramification uses the base uniformizer at all stages;
unit multiples leave the ideal unchanged. A further extension over a stage is still finite
because all stage fields are finite over Q_l. Mixed reductions have the actual quotient
maps, including the identity reduction. Scheme isomorphisms need not be linear over a
fixed base field: the base may also move, as geometric Frobenius requires.

### Searches

- `msearch.py ... leanfinder`: "Finite free extension of coefficient rings commutes with
  derived direct image exceptional inverse image internal Hom and Verdier duality".
  Eight hits, concerning ordinary free sheaf pullback and light condensed internal Hom;
  none states the five comparisons and their coefficient/geometric coherence.
- `msearch.py ... loogle "Module.Free, Module.Finite"`: twelve hits giving finite free
  module foundations, including Module.finBasis; no derived coefficient theorem.
- `msearch.py ... leansearch`: "finite free coefficient extension derived direct image
  internal Hom". Eight hits on ordinary free sheaves or condensed modules; no item match.
- `msearch.py ... grep "finiteFree.*[Dd]erived|[Dd]erived.*finiteFree"`: zero Mathlib hits.
- `rg` over Mathlib monoidal categories finds the ordinary curried braiding API, not
  the coefficient comparison item. Source and side-project searches for
  `finite_free_coefficient_extension|FiniteFreeCoefficients|lem-coef-finite-free-extension`
  find only downstream proof docstrings and the finite-etale-descent prerequisite.
- `rg` over the source and side project for Stage/Arrow and canonical coefficient
  maps finds `FiniteCoefficientAdjointComparisons`, `ExceptionalCoefficientComparison`,
  `FiniteCoefficientDirectImage`, and `EvaluationHomSiteComparison`; these are reused.

The source statement and proof were read in main-20261015,
sec-smooth-purity/sk-lem-sp-tower/lem-coef-finite-free-extension(.proof).md.
The retained node has a resolved stage-1 re-split repair note, not a released stage-2
interface defect. Its current 18-step proof is reproduced in the theorem docstring.
No statement correction or disputed mathematical claim is proposed.

## Second reading by Q107

The dispatcher requires this worker to work alone, with the maintainer's independent
review after delivery. I performed a separate pass with the node, source and module open.
The correspondence above checks each hypothesis and all five displayed formulas, evaluation,
biduality, counits, identities, field composition, reduction, the two sites, geometry,
and ramified cofinality. The retained work initially omitted its node record and report;
these were supplied. The compiler diagnostics were repaired without changing the statement.
The pro-etale symmetry is characterized componentwise by the canonical signed braiding,
and ordinary definitions keep large functor expressions from repeatedly unfolding.
The tensor comparison is characterized by the existing representative normalization,
with heterogeneous equality retaining the actual canonical arrow. Typed wrappers
`homAction`, `scalarSite`, `siteHom`, and `scalarPull` give the ordinary bifunctor action
and the existing coefficient/site/pullback comparisons, with no new choices.

The compact-support counit equation now uses the compactification actually selected by
the recorded exceptional adjunction. `NormalizedAux` makes that instance explicit;
`Normalized` supplies it from the given compactification. This fixes the definitional
presentation of the same canonical adjunction and adds no hypothesis. The equations
still include identities, reductions and arbitrary scheme isomorphisms.

The complete repaired module passed both server compile modes through `scompile.py`:
30.5 seconds in the sandbox namespace and 34.1 seconds as its library module, with no
errors or unexpected warnings. The final packet is also checked by the required
server delivery preflight and per-file compiler below.


## Returned-delivery repair (L, immutable head e08263117f25)

1. H2: added `def-coef-finite-coefficient-stages` as an existing definition node owning
   Stage, its integer/parameter/ideal/quotient definitions, baseStage/baseCoefficientEquiv,
   stageFinite, Arrow, its ideal containment, ringMap, IsFiniteFree and ringMap identity and
   composition facts. Replaced the theorem dependency by this node. No library source is moved
   or duplicated, and the theorem's existence or conclusions are not used for those definitions.
2. H4, domain: `Sites.Ctf true` is now exactly the published
   `ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat A) X`. It no longer substitutes
   an etale-origin existential. The etale property is unchanged.
3. H4, closed geometry: `ClosedGeometry` now states the square for
   `FiniteFreeCoefficients.closedMap` itself. `closedPull` transposes the pulled-back counit
   of the actual adjunction `Ri_* ⊣ closedUpper`; it does not use the compact-support
   adjunction of `Compactification.ofIsProper i`. `ProClosedGeometry` states the same square
   for `proClosedMap`, constructed from this etale map using the canonical site/scalar mate.
   The item explicitly equates its `pro.closedMap` with that map on its full recorded domain.
4. H4, both sites: `ProDirectGeometry` uses actual pro-etale derived base change and
   `finiteCoefficientChangeDirectImageMap`. `ProHomGeometry` uses pro-etale pullback of
   evaluation and the tensor comparisons normalized on representatives at X and Y.
   `ProOmegaGeometry` uses the base-changed compactification and regular-unit identification,
   with its coefficient arrow fixed by the existing omega site square. The item equates
   its `pro.omegaMap` with this canonical arrow. The Hom and omega equations give the
   Verdier equation because the latter map is their specified composite. Together with the
   retained etale equations these cover all five geometric comparisons on both sites,
   allow the base scheme to move and include geometric Frobenius and identity isomorphisms.

The additional helpers are real constructions of these same maps and squares. `rnuScalar`
and `rnuPull` are transposes through the published comparison adjunction. `sitePull` derives
its ordinary site square. `proScalarPull` is the conjugate of the canonical derived
restriction/direct-image isomorphism. `inverseOnDomain` is the ordinary inverse when invertible
and zero elsewhere; the geometric assertions use it on the isomorphism domain. No additional
postponed theorem is introduced.

## New nodes

`def-coef-finite-coefficient-stages` owns the already published Stage/Arrow interface in
`Sheaf.Paper.FiniteCoefficientAdjointComparisons`, with `existing: true`. Its self-contained
statement specifies the finite field extensions, base embedding, positive level, actual
base-uniformizer quotient, the over-base embedding and decreasing-level arrows, their
quotient homomorphisms and the finite/free predicate for that homomorphism. Source:
main-20261015, sk-lem-sp-field-extension-towers. LeanSearch and LeanFinder returned eight
unrelated quotient/perfection hits each; Mathlib grep returned four unrelated Arrow hits.
The project search found exactly this concrete interface, and the DAG search found it
only under the theorem's declaration list, with no definition node owning it. It is reused
without a new Lean module. Raw query records are in the new node and searches.jsonl.

### Repair self-check by Q107

As required by the dispatcher, this worker works alone; the maintainer supplies the
independent review. I reread the item, the owning definition node, and all geometry definitions
against the return. Finite stages still use the image of the base uniformizer; no equal
coefficient/site universe assumption is added. All geometry equations use actual pullback
schemes and canonical scalar/pullback isomorphisms. Closed right adjoints and compact-support
right adjoints remain distinct. The pro-etale domains use the recorded property. Identity
isomorphisms, empty schemes, zero objects, ramified stages, equal levels and mixed reductions
remain included. The single postponed proof is the item theorem; the new node reuses
published declarations.

### Final verification

The saved packet initially passed the required dry run (`8c59052e78`), but inspection showed
that the returned H2/H4 points still needed repair. The repaired packet is compiled and
preflighted again before delivery; the final checks below supersede the older packet's checks.


Resumed self-check (2026-10-19): the complete saved repaired module and the generated
existing-declaration check compiled through the prescribed wrapper against the current live
library. The first resumed dry run rejected only the new definition node's `blueprint.from.via`:
since the item itself is a blueprint node, the required ancestry path is empty. This metadata
was corrected to `[]`. The item signature exactly matches its recorded `lean.statement`;
the source statement and proof are unchanged, and its sole `sorry` is the item theorem.
The preflight advisory about `lem-weil-proetale-direct-image-restriction-of-scalars` is
intentional: `proScalarPull` uses `fixedScalarRestrictionDirectImage`, whose data is the
inverse of the fixed canonical mate, supplied by its named `IsIso` theorem. This proof
determines that inverse uniquely; it is not a plain unowned definition of the kind returned
under H2. The new Stage/Arrow definition node owns all the plain declarations named in
that return. The closed geometry equations explicitly use `closedMap` and `proClosedMap`;
the recorded pro-etale property and all four pro-etale geometry predicates occur in the
final theorem. Identity isomorphisms and arbitrary moving base isomorphisms remain included.
