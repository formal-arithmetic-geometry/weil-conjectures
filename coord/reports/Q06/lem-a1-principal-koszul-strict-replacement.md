## Worker report

The module `Sheaf.Paper.PrincipalKoszulStrictReplacement` states the node through
six named theorems and gives concrete definitions of its canonical maps and towers.
All theorem proofs are `sorry`; the definitions contain actual data. No node statement
or dependency interface is changed, and no new node is needed. The helper theorems
are clauses of this same node, not independent additional mathematical assertions.

Clause-by-clause reading:

- The prime and finite extension are `l : ℕ`, `[Fact l.Prime]`, `E : Type u`,
  `[Field E]`, `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`.
  The coefficient ring and chosen uniformizer are exactly
  `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionUniformizer l E`.
- The arbitrary scheme is `W : Scheme.{t}`. There is no characteristic restriction,
  finite-field datum, nonemptiness, Noetherianity or separation assumption on W.
  The small pro-etale site is the existing `W.ProEt`, object universe t+1 and morphism
  universe t. The coefficient/module universe is max u (t+1), with t and u independent.
  The three public instance wrappers supply canonical size/sheafification proofs only.
- `Modules l E W` is the category of sheaves over the recorded actual limit
  `completedIntegralCoefficientSheafUnrestricted l E W`. Its derived category is the
  imported `DerivedCategory`; the node's given K-flat representative P is kept at
  the complex level, so no extra choice of localization is necessary.
- `residue ... n` is the unit module of the actual constant quotient ring sheaf
  `integralCoefficientSheaf ... n`, restricted along `limit.π` of the recorded
  inverse system. Everywhere n encodes positive exponent n+1, including n=0.
- `uniformizer` is the constant uniformizer section sent along the canonical
  `integralConstantToCompletionOfUniverses`. Its section compatibility is the
  naturality of that map and of the sheafification unit. It is not an arbitrary scalar.
- `koszul ... n` is the existing `principalKoszul` mapping cone on the power n+1
  of the existing `globalSectionMultiplication`. It has degrees -1 and 0.
  `sourceTower` uses the existing `principalKoszulTower`, hence the transitions
  have components (t,1); tensoring retains the order P tensor Q.
- `projection` is the actual completed projection as a module map: the unit-Hom
  equivalence extends the constant section 1 linearly, giving x maps to pi_n(x).
  `multiplication_projection` states its vanishing on t^(n+1). `quotientComparison`
  is cokernel.desc of that projection, not a chosen quotient isomorphism.
  `augmentation` composes the existing principal augmentation with this canonical
  cokernel map, so it is zero on the shifted summand and pi_n on degree zero.
- `coefficient_datum` supplies an `AdicCoefficientDatum` with ideal exactly (t).
  Its inherited fields are Noetherianity, finite generation, positive-integer
  additive torsion of A/(t), and perfectness of every positive quotient.
  `quotientFinite` gives every quotient finite. The same conclusion explicitly
  asserts injectivity, Function.Exact and surjectivity of the two-term free
  coefficient resolution with differential multiplication by t^(n+1).
- `completed_exact` is ShortExact for multiplication followed by the actual
  projection. It also states IsIso of the projection-normalized cokernel comparison.
- `tensorWith` specializes the already recorded total-tensor bifunctor from
  `KFlatTotalTensorModel.tensor.map₂CochainComplex`. This is direct-sum totalization
  with the usual cochain sign, not a new tensor construction.
- `residueStep` has section maps exactly `integralCoefficientSheafTransition`.
  Its R-linearity uses the actual limit-cone equation. `targetTower` is the strict
  sequence of these modules in degree zero, tensored on the left by P. Thus it is
  precisely the node's strict reduction tower on its given representative P of [P],
  with quotient actions restricted along the specified projections.
- `augmentation_compatible` states equality of adjacent chain-map squares, before
  localization, for every P. `comparison` uses NatTrans.ofOpSequence with exactly
  the components id_P tensor epsilon_n. Its type therefore supplies the required
  strict tower morphism and compatibility with all longer composites as well.
- The main theorem binds the given K-flat hypothesis as
  `IsKFlatIndependentCoefficients (R := completedIntegralCommRingSheafUnrestricted ...) P`
  and flat terms as `∀ i, IsFlatOnSite (P.X i)`. For every n it asserts QuasiIso
  of the actual comparison component, independent-coefficient K-flatness of its
  source, and flatness of every source term. This is precisely objectwise K-flat
  replacement; no assertion of K-flatness in the tower category is substituted.
- `sourceTowerMap` and `targetTowerMap` are whiskerings of the same tensor
  bifunctor's map on f, so their components are f tensor identity and they are
  strict tower morphisms. `comparison_naturality` is equality of their composites
  with comparison in the strict functor category, not only after localization.
  These functorial identities require no K-flatness and in particular give all
  naturality requested between the flat-term K-flat representatives.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; it reexports the recorded integer ring,
  uniformizer, finite quotient, ideal and quotient transition constructions.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, `integralCoefficientSheafSystem`,
  `integralCoefficientSheaf`, `integralCoefficientSheafTransition`,
  `completedIntegralCoefficientSheafUnrestricted`, and
  `completedIntegralCommRingSheafUnrestricted`. The commutative presentation forgets
  to the very same limit ring sheaf.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, the recorded acyclic-total-tensor
  predicate, not a specialized universe variant.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and
  `Functor.map₂CochainComplex`, via the existing explicit tensor wrapper in
  `Sheaf.Algebra.Homology.KFlatTotalTensorModel`.
- `Sheaf.Paper.AdicCoefficientDatum`: `Scheme.AdicCoefficientDatum`, including its
  `CompleteCoefficientDatum` fields and quotient finiteness. The ring-only datum
  accepts the coefficient universe independently of the scheme universe.
- `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers`: `principalKoszul`,
  `principalQuotient`, `principalAugmentation`, `principalKoszulTower`, `endoPow`,
  `globalSectionMultiplication`. These already give precisely the principal cone,
  quotient and transition constructions required here.

All already stated proof-dependency modules are imported as well, including the DVR,
finite-valued-quotient, Noetherian and perfect-module interfaces, exact constant-module
functor, completed-constant flat quotients/reduction, bounded-flat K-flat theorem,
K-flat tensor quasi-isomorphism theorem, and flat-term total tensor model theorem.
Proof docstrings give the eight node proof steps across the relevant clause theorems.

Sources opened: sites-modules.tex lemma-completion-flat (093M), proetale.tex
section-derived-completion-noetherian (099L), sites-cohomology.tex
lemma-K-flat-resolution (06YS), and the main-20261015 finite-map-purity statement and
proof (the blueprint ancestor). The item is the extracted coefficient/Koszul argument,
not a change to that unit's purity statement.

Edge cases checked before finalizing: exponent 1 is n=0, so no positive quotient is
lost and no exponent-zero quotient is added to the theorem; P=0 and zero terms satisfy
the same comparison; P may be unbounded in both directions; empty W and empty site
objects are allowed; no enough-points premise enters exactness or K-flatness; ell=2
is included; t and u remain independent. There is no disputed statement or node fault.

Searches actually run for this item:

- msearch leanfinder: "Principal Koszul resolutions of completed coefficient sheaf
  quotients form a strict natural tower of K-flat replacements". Eight hits, including
  localCohomology.diagram and AdicCompletion.flat_of_isNoetherian; none states this
  ringed-site strict replacement assertion.
- msearch loogle: "HomologicalComplex, QuasiIso". Twelve hits, including QuasiIso,
  quasiIso_iff and quasiIso_comp; these provide the quasi-isomorphism notion, not
  the claimed Koszul replacement theorem.
- msearch grep: "Koszul.*(KFlat|K.flat|resolution)|[Kk]flat.*[Tt]ower|[Kk]oszul.*[Tt]ower".
  Zero Mathlib hits.
- msearch leansearch: "A two term Koszul resolution of powers of a nonzerodivisor
  tensored with a K flat complex gives compatible replacements of quotient towers".
  Eight hits, including Module.Flat.lTensor_shortComplex_exact and its right-tensor
  counterpart; no completed-sheaf tower theorem.
- rg searches of lean/WeilConjectures and lean/Sheaf for principal Koszul,
  Koszul replacement and this item's id found the reusable PrincipalKoszulQuotientTowers
  module and nearby reduction statements, but no statement of this item. The requested
  grep by the item id in lean/WeilConjectures returned no hits. The nearby point-only
  principal coefficient exactness and normalized DVR reduction-model theorems have
  different statements; none is substituted for arbitrary W and the principal tower.

Validation: scompile.py compiled the module both as a sandbox and at its library
module path without errors or unexpected warnings. The delivery dry run is the final
validation of the complete packet and its explicit proof imports.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
