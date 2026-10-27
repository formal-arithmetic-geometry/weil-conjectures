## Worker report

Attached the exact existing declaration
`WeilConjectures.scalarPullbackLevel_existsUnique` in
`Sheaf.Paper.IntegralOperationsScalarComparisonModels`, lines 118–125.
No module is written and no theorem is proved. Its existing proof remains `sorry`.
The signature is copied verbatim into `lean.statement`; only the item's `lean`
field changes. There is no repair note for this item. The current live server
source was also read using `scompile.py --source` and agrees with the local source.

Source read: `literature/stacks-project/sites-modules.tex`,
`section-tensor-product`, lines 3551–3645, and
`lemma-tensor-product-pullback` (Tag 03EL), lines 3649–3693.
The node's explicitly cited project specialization is the existing theorem and
its normalization predicate at lines 88–109. The latest blueprint's
`def-weil-derived-pullback-tensor-hom` was also read; this delivery attaches the
specified ordinary finite-level assertion, without changing any derived target.

Hypothesis and clause correspondence:

- Prime ell: the source section binds `(l : ℕ) [Fact l.Prime]`.
- Finite extensions E and L: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]` and the corresponding binders for L.
- The embedding is `(ι : E →ₐ[ℚ_[l]] L)`; field algebra homomorphisms are
  injective. It is not restricted to an identity or an intermediate-field inclusion.
- The chosen valuation rings, uniformizers and quotients are the dependency's
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal` and `coefficientExtensionRing`. The same chosen
  constructions are used on both sides; uniformizer powers define the quotient.
- The sites are `X.ProEt` and `Y.ProEt`, with `Scheme.ProEt.topology`. The source
  uses schemes in universe u, site objects in u+1 and site morphisms in u, and
  module sections in u+1. Thus it does not equate the two site universes and the
  site is small relative to the module universe. The common ambient universe u
  is the existing source's size convention for schemes and coefficient fields.
- Completed rings and quotient projections are
  `completedIntegralCommRingSheafUnrestricted` and
  `completedIntegralCommRingProjectionUnrestricted`. The constant coefficient
  tower has level n equal to the quotient with exponent n+1.
- The embedding-induced quotient maps are `integralScalarQuotientSheafMap`;
  `integralCompletedScalarMap` is their limit map. Its defining uniqueness theorem
  prescribes every composite with a quotient projection. This is the node's j_W.
- Ordinary S_W is `integralOrdinaryScalar l E L ι W`. Its witness specifies both
  objects as `SheafOfModules.changeOfRings` along that completed map and morphisms
  as `changeOfRingsHom`; it is not the Roos/completed scalar functor. Applying
  `.mapHomologicalComplex (ComplexShape.up ℤ)` gives termwise scalar extension,
  with differential 1 tensor d.
- `(f : X ⟶ Y)` binds every scheme morphism. `(n : ℕ)` includes n=0.
  `integralOperationsLevelPullback` uses the ring
  `Padic.coefficientExtensionRing l E (n + 1)`, so there is no exponent-zero level.
- P^F_(f,n) is exactly `integralOperationsPullbackLevel l F f n`: its definition
  is `unrestrictedIntegralFiniteComplex` followed by termwise ordinary finite
  module pullback followed by `integralOperationsRestrict`. This is reduction,
  pullback, then restriction through the completed projection, in that order.
- The existential is `∃! α` in the natural-transformation type from
  `integralOperationsPullbackLevel l E f n ⋙ S_X` to
  `S_Y ⋙ integralOperationsPullbackLevel l L f n`. Lean's left-to-right `⋙`
  is exactly the node's S_X composed with P^E and P^L composed with S_Y.
  Since the codomain is cochain complexes of completed L-module sheaves,
  components are R_(L,X)-linear chain maps. Naturality is for every chain map.
- The predicate `scalarPullbackLevelNormalization` quantifies
  `(P : CochainComplex (integralTowerModules l E Y) ℤ)`, `(i : ℤ)`, `(V : Y.ProEt)`
  and `(x : (P.X i).val.obj (op V))`, exactly the four quantifiers in the node.
- Its left side evaluates `((α.app P).f i).val.app` on the fibre-product object
  `(Scheme.proEtaleBaseChange f).obj V`, at
  `integralOrdinaryTensorSection ... 1
    (integralOperationsPullbackGenerator ...
      (unrestrictedIntegralTensorSection ... 1 x))`.
  These are, respectively, the ordinary scalar-extension unit, the finite
  module-pullback unit, and the quotient scalar-extension unit. This is precisely
  α(1 tensor f*(1 tensor x)).
- Its right side is `integralOperationsPullbackGenerator` applied to
  `unrestrictedIntegralTensorSection ... 1
    (integralOrdinaryTensorSection ... 1 x)`, namely
  f*(1 tensor (1 tensor x)). The tensor-section definitions use the canonical
  sheafification unit, and the pullback-generator definition uses the canonical
  finite-pullback adjunction unit. No global pure-tensor decomposition is asserted.
- The theorem has no hypotheses of flatness, K-flatness, boundedness,
  constructibility, finite-field origin or invertibility of ell on either scheme.

Dependency declarations read and used (including their full source signatures
and docstrings):

- `def-weil-pbc-proetale-site`: `AlgebraicGeometry.Scheme.ProEt` and its topology,
  `Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `def-weil-completed-integral-coefficients`:
  `WeilConjectures.integralConstantToCompletionOfUniverses` and its quotient cone,
  `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`; the retained completed
  rings and projections occur in the existing finite-level source.
- `def-pur-change-of-rings-complex`: `SheafOfModules.changeOfRingsComplex`,
  `Sheaf.Algebra.Homology.ChangeOfRingsComplex`; termwise construction is also
  expressed by the existing functor's `mapHomologicalComplex`.
- `def-pur-sheaf-tensor-product`: `SheafOfModules.cochainModulesMonoidal`,
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, retaining the
  sectionwise tensor/sheafification construction.
- `def-sfb-scalar-extension-pure-tensor-section`:
  `SheafOfModules.scalarExtensionRingIsoTmul`,
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`. Its body is
  the sheafification-unit image of s tensor x for arbitrary a. The older existing
  normalization uses `integralOrdinaryTensorSection` in
  `Sheaf.Paper.ScalarExtensionComposition` (lines 125–134), the same canonical
  unit formula transported along the prescribed scalar functor's object equality.
- `lem-pur-integral-operations-well-defined`:
  `WeilConjectures.integralOperationsWellDefined` and its recorded
  `integralOperationsLevelPullback`, `integralOperationsPullbackLevel`,
  `integralOperationsRestrict`, `integralOperationsPullbackGenerator`, in
  `Sheaf.Paper.IntegralOperationsWellDefined`. The latter declarations give the
  ordinary level functor and its canonical unit, not a choice of a derived map.
- `def-weil-proetale-inverse-image`:
  `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`, `proEtaleBaseChange`,
  `proEtaleCoefficientInverseImageMap`, `proEtaleConstantModulePullback`, in
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`. The finite module specialization
  retained by the operations module uses its canonical coefficient adjunction.
- `def-pc-sheaf-restrict-scalars`: `SheafOfModules.restrictScalars`,
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, lines 33–43; this
  keeps the underlying sheaf and restricts its scalar action.
- `def-weil-integral-scalar-extension`:
  `WeilConjectures.integralScalarExtensionOfUniverses`,
  `Sheaf.Paper.IntegralScalarExtensionUniverses`, which retains
  `Sheaf.Paper.IntegralScalarExtension`. In the retained module, lines 79–177,
  `integralCompletedScalarMap_existsUnique`, `integralCompletedScalarMap`,
  `integralOrdinaryScalarWitness`, and `integralOrdinaryScalar` give the actual
  compatible quotient limit map and ordinary tensor functor needed here.
- `def-weil-l-adic-coefficient-extension`:
  `Padic.finite_coefficientExtensionRing`,
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, retaining the coefficient
  constructions in `Sheaf.NumberTheory.Padics.CoefficientExtension`.

Edge cases checked by reading the definitions and binders: n=0 gives exponent 1;
E=L with identity embedding; a genuinely ramified embedding; f an identity;
the empty scheme; zero complexes and zero sections; unbounded and non-flat
complexes; and schemes in characteristic ell. None is excluded. In particular
ramification does not require the quotient inclusion to be injective, and the
statement does not assert an isomorphism. The uniqueness proof plan in the node
uses local surjectivity of the completed projection, followed by scalar and
pullback adjunctions; it does not assume that all site objects are base changes.
No node fault or statement correction was needed.

Searches actually run:

- `msearch.py leansearch`: "A unique natural transformation commuting extension
  of scalars and pullback of complexes of sheaves of modules, characterized on
  tensor generators". Eight hits, including `ModuleCat.extendScalars`, its
  extension/restriction adjunction, and a sheaf pullback/free-module lemma; no
  exact Mathlib completed-coefficient finite-level statement.
- `msearch.py leanfinder`: "unique natural scalar extension finite quotient
  pullback chain map normalized on pure tensor sections". Eight hits, including
  `ModuleCat.ExtendScalars.hom_ext` and `hom_ext_iff`; these are general algebraic
  tools, not this sheaf-complex assertion.
- `msearch.py loogle`: "SheafOfModules.restrictScalars, NatTrans, ExistsUnique".
  Zero hits because `NatTrans` was an unknown identifier to that service. Repeated
  with "SheafOfModules.restrictScalars": four hits giving the exact restriction
  functor, additivity and the underlying presheaf formulas, read in source.
- `msearch.py grep`: `scalarPullbackLevel|changeOfRings.*pullback|pullback.*changeOfRings`.
  No Mathlib hits.
- Direct `rg` in `lean/WeilConjectures` for
  `scalarPullbackLevel_existsUnique|scalarPullbackLevelNormalization|integralOrdinaryScalar`
  and `grep -rn` there for the item id: no matches.
- Direct `rg` in `lean/Sheaf` found the exact theorem and predicate in
  `IntegralOperationsScalarComparisonModels.lean`, with further uses downstream.
  These definitions and the theorem were read in full, not inferred from names.

Validation: the required `deliver2.py --no-push` checks the existing declaration
with a real module-mode server `#check` through the prescribed scompile wrapper,
then runs the maintainer preflight.

Dry run completed successfully on 2026-10-27: `OK (dry run): commit
e016c8b7a42 passes the preflight and compiles; nothing pushed`. The packet has
only the node attachment and this report; no new Lean source or axiom is added.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
