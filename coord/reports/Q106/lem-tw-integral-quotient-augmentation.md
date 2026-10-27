## Worker report

Attach existing declarations; no new Lean module, definition, proof, dependency repair,
or natural-language statement change. The module is
`Sheaf.Paper.OrdinaryCompletedIntegralPullback`, primary declaration
`WeilConjectures.ordinaryIntegralQuotientAugmentation_existsUnique` (lines 276–298).
Its proof is still `sorry`, as required for a stage-2 statement. The same module already
contains the actual augmentation, product augmentation, chain condition, and prescribed
completion chain map (lines 300–370). The additional declarations are recorded in `lean`.
This attachment is different from the prior unchanged-node packet: it adds the missing
Lean record to a stage-1-split node. Q138's stage-1 review is retained without alteration.

Hypotheses and objects, read against the full existing signatures and definitions:

* Prime ell: `(l : ℕ) [Fact l.Prime]` in the module variables.
* Finite extension: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. Its ring, uniformizer, and quotients are the recorded
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `coefficientExtensionRing`, imported via `CoefficientExtensionFinite`.
* Schemes and morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`. The node's invertibility
  assumption specializes the existing assertion, which needs no invertibility. There
  is no Noetherian, dimension, separatedness, or finite-field hypothesis on this theorem;
  such assumptions occur only on the different theorem at the end of the source file.
* The sites are `X.ProEt` and `Y.ProEt`, with `ProEt.topology`; Mathlib's site retains
  object universe u+1 and morphism universe u. The module uses a common ambient size
  for E and schemes and module coefficients in u+1; it does not equate site object and
  morphism universes.
* `integralCoefficientSheaf l E W n` is the constant sheaf of the quotient with exponent
  n+1. Thus index 0 is the statement's first positive level, not a quotient by t^0.
  `completedIntegralCoefficientSheafUnrestricted` is its inverse limit, and `limit.π`
  gives precisely the quotient projections.
* `ordinaryIntegralDirectRingMap_existsUnique` fixes the direct-image ring map by all
  finite projections, with `ordinaryIntegralFiniteDirectRingMap` the constant-section
  map. `ordinaryIntegralModulePull` is the recorded sheafified module pullback along
  that map, and `ordinaryIntegralModuleAdjunction` is its module adjunction. This is
  the prescribed completed coefficient structure, with no arbitrary ring map.
* `ordinaryIntegralPullComplex` applies that additive pullback termwise to every
  cochain complex. Its domain is `CochainComplex (integralTowerModules l E Y) ℤ`.
* `integralOperationsPullbackTowerFunctor` has level `integralOperationsPullbackLevel`:
  first `unrestrictedIntegralFiniteComplex`, then finite module pullback, then
  `integralOperationsRestrict`. Its transitions are the coefficient-induced
  `integralOperationsPullbackTransition`, characterized by the reduction of generators.

Every asserted clause:

* Existence and uniqueness are `∃! a`. The type of a is a natural transformation from
  `ordinaryIntegralPullComplex ⋙ Functor.const ℕᵒᵖ` to the specified pullback tower functor.
* The generator equation quantifies over all complexes P, levels n, degrees i,
  site objects V, and `x : (P.X i).val.obj (op V)`. Its left side applies a to the
  image of x under `ordinaryIntegralModuleAdjunction.unit`; its right side is
  `integralOperationsPullbackGenerator` applied to `unrestrictedIntegralTensorSection`
  with scalar 1. This is exactly the equivalent adjunction-unit normalization that
  the node explicitly permits. Completed scalar linearity yields the displayed
  b-tensor-q formula; it does not require lifting arbitrary finite coefficients.
* Each component of a is a morphism of complexes of module sheaves, hence is
  B_X-linear and commutes with differentials. No separate linearity assumption is added.
* For each P, `a.app P` is a natural transformation of strict ℕᵒᵖ towers. Its naturality
  for `(homOfLE (Nat.le_succ n)).op` is the strict equation r_n a_(n+1) = a_n.
* Outer naturality of a for an arbitrary chain map v is precisely
  T_f(v)_n a_(P,n) = a_(P',n) f_B^*(v), after evaluation at `op n`.
* `ordinaryIntegralProductAugmentation` is `Pi.lift` of those exact components.
  `ordinaryIntegralCompletionChain_condition` asserts its composite with 1-s is zero
  in the Hom complex; the other summand is the differential of the zero cochain.
* `ordinaryIntegralCompletionChain` is the concrete `mappingCocone.lift` of that product
  augmentation and the zero degree -1 cochain. Its target is
  `integralOperationsPullbackComplexFunctor`, namely the Roos mapping cocone of the
  actual strict pullback tower. Thus its unshifted coordinate is the product of a_n
  and its shifted coordinate is zero. This is the concrete Cone(1-s)[-1] model.
* Naturality of this chain map is checked in the existing module's private helper
  `ordinaryIntegralCompletionChain_natural` (lines 402–442), for all cochain maps;
  the proof uses outer naturality of the same augmentation and both cone coordinates.
  We do not invent a public name for this private helper or add a duplicate theorem.
* No flatness, boundedness, constructibility or completeness is imposed on P anywhere
  in these declarations. The good-complex conditions in other declarations of the
  source module are not hypotheses of the attached statement or chain construction.

Dependency declarations used (all existing; no copies):

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the imported coefficient constructors.
* `def-weil-scheme-morphism-properties` is a convention node without a declaration;
  `Scheme` and its categorical morphisms supply the objects needed here.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses`, with the imported
  `integralCoefficientSheaf`, `integralCoefficientSheafSystem`, and
  `completedIntegralCoefficientSheafUnrestricted`.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleBaseChange`, `proEtaleSheafDirectImage`,
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`, and constant coefficient maps.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  abbreviation of `SheafOfModules` whose category has module-linear morphisms.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, using the shared sheaf tensor construction.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`. This lemma itself remains at the cochain level.
* `Sheaf.Paper.OrdinaryCompletedIntegralPullback`: the ordinary ring map, module
  pullback, adjunction, and complex pullback recorded by
  `def-sf-ordinary-integral-pullback-construction`; this already owns the attached names.
* `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: the public import retains the global
  operations from `IntegralDerivedOperations` and `IntegralOperationsWellDefined`,
  including the actual finite reduction and strict pullback tower described above.
* `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimit` and `IsDerivedLimitTriangle`. These give the derived
  Roos interpretation; the concrete cone uses the cochain mapping-cocone convention.

Edge cases checked: zero and unbounded complexes, arbitrary chain maps (including zero
and identity), the identity scheme morphism, empty schemes, level n=1 (Lean index 0),
and torsion/non-flat modules. All remain in the quantified domain. No resolution,
truncation, constructibility witness, or completeness witness appears in the attached
signature. The normalization is an equation on all original unit sections, not a false
claim that those sections generate on each individual object of the source site.

Searches actually run:

* msearch leanfinder, query `unique natural strict quotient tower augmentation ordinary
  integral pullback completed coefficients Roos cone`: eight hits on adic-complete
  extension identities, Dold–Kan, light diagrams and a Cech nerve; no exact match.
* msearch loogle, query `NatTrans, Functor.const`: zero hits, unknown identifier NatTrans;
  no assertion of a successful semantic search from this result.
* msearch grep, query `QuotientAugmentation|mappingCocone.lift|towerTransitionEndomorphism`
  in `Algebra/Homology`: three hits in Mathlib's Factorizations/CM5a, general cocone API.
* msearch leansearch, query `natural augmentation from ordinary sheaf module pullback
  to the tower of finite coefficient quotients`: eight hits on the general
  `SheafOfModules.pullback` and its adjunction/free-object interfaces, no exact statement.
* rg on WeilConjectures and Sheaf for quotient augmentation and the exact declaration:
  the exact statement is `Sheaf/Paper/OrdinaryCompletedIntegralPullback.lean:287`;
  its definition, product and cone condition/construction follow in the same module.
  Other quotient augmentations concern ordinary completion or open tensor operations.
* The literal node-id search in WeilConjectures and Sheaf has no occurrence: the exact
  existing declaration has the parent blueprint id in its docstring. This does not
  prevent attaching it to the extracted stage-1 node.

No new nodes or dependency modules. No STATEMENT-DISPUTED finding and no statement
correction. The inherited reference to cone conventions of derived-limit is understood
through the explicit cochain cone conventions already in stmt_deps, as Q138 observed.

## Second reading by Q106

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
