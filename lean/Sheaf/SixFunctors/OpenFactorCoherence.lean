/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.SixFunctors.ConstructibleTensorCompletion
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.CompletedOpenExchangeTransport
public import Sheaf.Paper.IntegralCompactSupportCoefficientData
-- Existing reduction and open scalar mate: def-sf-open-reduction-coefficient-mate.
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison

public import Sheaf.SixFunctors.OpenFactorTensorModel

import Sheaf.Paper.DerivedCompleteOnSlices
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.AdicCoefficientDatum
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts
import Sheaf.Paper.ExactProductFunctorStrictLimit
import Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.CompletedRlimFunctor
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Compactness.Compact
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-! # Completion coherence for the open factor

Source: blueprint main-20261015, sk-prop-sf-pf-coherence, base-change paragraph;
Bhatt--Scholze, Definition 3.4.10 and Lemmas 6.5.5, 6.5.8; Stacks 099N, 09BN, 0GL1
(blueprint: lem-sf-pf-open-factor-coherence).

All operations are the published operations. The records below present their
normalizations, rather than assuming preservation or choosing new operation functors.
Natural-number level n always means exponent n+1. A tower comparison is an isomorphism
of strict complex-valued functors, with its components fixed before localization.

## Main definitions

- `Open` and `Assertion`: the normalized open-factor assertions.
- `gamma` and `beta`: completed projection and exchange, with their actual units.

## Main statements

- `openFactorCoherence`: the three clauses of the source node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport

namespace WeilConjectures.OpenFactorCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option genSizeOf false in
set_option genInjectivity false in
/-- Canonical completion/open commutation and all of clauses (1) and (2).
The strict tower comparison is fixed by the actual quotient augmentation.
Source: Stacks 099N, 09BN, 0E8I
(blueprint: lem-sf-pf-open-factor-coherence). -/
structure Open {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] where
  tower : jCx l E j ⋙ IntegralOnSlice.tower.{u, u} l E X none ≅
    IntegralOnSlice.tower.{u, u} l E U none ⋙
      (Functor.whiskeringRight ℕᵒᵖ (Cx l E U) (Cx l E X)).obj (jCx l E j)
  tower_unit : ∀ (P : Cx l E U) (n : ℕ),
    ((IntegralOnSlice.augmentation.{u, u} l E X none).app ((jCx l E j).obj P)).app
        (op n) ≫ (tower.hom.app P).app (op n) =
      (jCx l E j).map (((IntegralOnSlice.augmentation.{u, u} l E U none).app P).app (op n))
  tower_unique : ∀ v : jCx l E j ⋙ IntegralOnSlice.tower.{u, u} l E X none ⟶
      IntegralOnSlice.tower.{u, u} l E U none ⋙
        (Functor.whiskeringRight ℕᵒᵖ (Cx l E U) (Cx l E X)).obj (jCx l E j),
    (∀ (P : Cx l E U) (n : ℕ),
      ((IntegralOnSlice.augmentation.{u, u} l E X none).app ((jCx l E j).obj P)).app
          (op n) ≫ (v.app P).app (op n) =
        (jCx l E j).map
          (((IntegralOnSlice.augmentation.{u, u} l E U none).app P).app (op n))) →
      v = tower.hom
  commutes : J l E j ⋙ C l E X ≅ C l E U ⋙ J l E j
  unit_commutes : ∀ K : D l E U,
    (eta l E X).app ((J l E j).obj K) ≫ commutes.hom.app K =
      (J l E j).map ((eta l E U).app K)
  commutes_unique : ∀ v : J l E j ⋙ C l E X ⟶ C l E U ⋙ J l E j,
    (∀ K : D l E U, (eta l E X).app ((J l E j).obj K) ≫ v.app K =
      (J l E j).map ((eta l E U).app K)) → v = commutes.hom
  restriction_complete : ∀ K : D l E X, IsSfDerivedComplete l E X K →
    IsSfDerivedComplete l E U ((star l E j).obj K)
  extension_complete : ∀ K : D l E U, IsSfDerivedComplete l E U K →
    IsSfDerivedComplete l E X ((J l E j).obj K)
  pull : Pull l E j
  pull_unit : ∀ K : D l E X, IsSfDerivedComplete l E X K →
    IsIso ((pull.unit l E).app K)
  restrictionIso : J l E j ⋙ star l E j ≅ 𝟭 (D l E U)
  section_unit : ∀ K : D l E U,
    (openDerivedAdjunction (completed l E) j).unit.app K ≫ restrictionIso.hom.app K = 𝟙 K
  fullyFaithful : ∀ (K L : D l E U), IsSfDerivedComplete l E U K →
    IsSfDerivedComplete l E U L → Function.Bijective
      (fun f : K ⟶ L ↦ (J l E j).map f)
  constructible : ∀ K : D l E U, sfIntegralConstructible l E U K →
    sfIntegralConstructible l E X ((J l E j).obj K)
  restriction_constructible : ∀ P : D l E X, sfIntegralConstructible l E X P →
    sfIntegralConstructible l E U ((star l E j).obj P)
  reduction_iso : ∀ (K : D l E U) (n : ℕ), sfIntegralConstructible l E U K →
    IsIso ((PurCompactSupport.openComparison
      (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) j).app K)
  interval : ∀ (K : D l E U) (n : ℕ) (a b : ℤ),
    sfIntegralConstructible l E U K →
    proEtaleCohomologicalSupport ((scalarReductionDerivedExtension.{u, u} l E U n).obj K) ⊆
      Set.Icc a b →
    proEtaleCohomologicalSupport ((scalarReductionDerivedExtension.{u, u} l E X n).obj
      ((J l E j).obj K)) ⊆ Set.Icc a b

/-- Completion of the actual ambient open tensor map, transported to the recorded
completed tensor. This is the supplied gamma of def-exchange-projection.
Source: Stacks 0GL1 and Bhatt--Scholze 3.4.10
(blueprint: lem-sf-pf-open-factor-coherence). -/
def gamma {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j]
    (o : Open l E j) (tU : Tensor l E U) (tX : Tensor l E X)
    (K : D l E U) (P : D l E X) :
    (integralCompletedTensor.{u, u} l E X).obj ((J l E j).obj K, P) ⟶
      (J l E j).obj ((integralCompletedTensor.{u, u} l E U).obj (K, (star l E j).obj P)) :=
  tX.comparison.inv.app ((J l E j).obj K, P) ≫
    (C l E X).map ((openProjectionIso (completed l E) j
      tU.ordinary tX.ordinary K P).hom) ≫
    o.commutes.hom.app (tU.ordinary.tensor.obj (K, (star l E j).obj P)) ≫
    (J l E j).map (tU.comparison.hom.app (K, (star l E j).obj P))

/-- The ordinary pullback square, with the published composition normalization.
Source: Stacks 0D6D (blueprint: lem-sf-pf-open-factor-coherence). -/
def theta {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} (sq : OpenImmersionSquare a j' j h) :
    star l E h ⋙ star l E j' ≅ star l E j ⋙ star l E a :=
  (geometricPullComposition (completed l E) j' h (completedPull_comp l E j' h)).symm ≪≫
    eqToIso (congrArg (fun f : U' ⟶ X ↦ star l E f) sq.w.symm) ≪≫
    geometricPullComposition (completed l E) a j (completedPull_comp l E a j)

set_option genSizeOf false in
set_option genInjectivity false in
/-- The ambient base-change map is fixed by the inverse open-unit transpose.
Source: Stacks 09BN (blueprint: lem-sf-pf-open-factor-coherence). -/
structure OrdinaryExchange {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : OpenImmersionSquare a j' j h) where
  comparison : J l E j ⋙ star l E h ≅ star l E a ⋙ J l E j'
  inverse : ∀ K : D l E U,
    (openDerivedAdjunction (completed l E) j').homEquiv _ _ (comparison.inv.app K) =
      (star l E a).map ((openDerivedAdjunction (completed l E) j).unit.app K) ≫
        (theta l E sq).inv.app ((J l E j).obj K)

/-- The strict-reduction completed exchange, expressed through the quotient completion
comparisons. Pull.model retains the strict finite maps; Open.unit_commutes fixes the
extension/limit comparison. Source: Stacks 099N and 09BN
(blueprint: lem-sf-pf-open-factor-coherence). -/
def beta {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    {sq : OpenImmersionSquare a j' j h} (b : OrdinaryExchange l E sq)
    (oh : Pull l E h) (oa : Pull l E a) (oj' : Open l E j') (K : D l E U) :
    (integralDerivedPullback.{u, u} l E h).obj ((J l E j).obj K) ⟶
      (J l E j').obj ((integralDerivedPullback.{u, u} l E a).obj K) :=
  oh.comparison.inv.app ((J l E j).obj K) ≫
    (C l E X').map (b.comparison.hom.app K) ≫
    oj'.commutes.hom.app ((star l E a).obj K) ≫
    (J l E j').map (oa.comparison.hom.app K)

set_option genSizeOf false in
set_option genInjectivity false in
/-- The complete open-factor assertion. Its data are conclusions, and every displayed
map is fixed by a quotient unit, a strict-tower comparison, or an open-unit transpose.
Source: blueprint sk-prop-sf-pf-coherence, base-change paragraph
(blueprint: lem-sf-pf-open-factor-coherence). -/
structure Assertion {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : OpenImmersionSquare a j' j h) where
  openData : Open l E j
  openData' : Open l E j'
  tensorU : Tensor l E U
  tensorX : Tensor l E X
  horizontal : Pull l E h
  horizontalU : Pull l E a
  ambientExchange : OrdinaryExchange l E sq
  tensor_complete : ∀ (M N : D l E X), sfIntegralConstructible l E X M →
    sfIntegralConstructible l E X N → IsIso ((tensorX.chi l E).app (M, N))
  tensor_completeU : ∀ (M N : D l E U), sfIntegralConstructible l E U M →
    sfIntegralConstructible l E U N → IsIso ((tensorU.chi l E).app (M, N))
  gamma_unit : ∀ (K : D l E U) (P : D l E X), sfIntegralConstructible l E U K →
    sfIntegralConstructible l E X P →
    (tensorX.chi l E).app ((J l E j).obj K, P) ≫ gamma l E openData tensorU tensorX K P =
      (openProjectionIso (completed l E) j tensorU.ordinary tensorX.ordinary K P).hom ≫
        (J l E j).map ((tensorU.chi l E).app (K, (star l E j).obj P))
  gamma_iso : ∀ (K : D l E U) (P : D l E X), sfIntegralConstructible l E U K →
    sfIntegralConstructible l E X P → IsIso (gamma l E openData tensorU tensorX K P)
  tensorRestriction :
    integralCompletedTensor.{u, u} l E X ⋙ star l E j ≅
      ((star l E j).prod (star l E j)) ⋙ integralCompletedTensor.{u, u} l E U
  restriction_unit : ∀ (M N : D l E X), sfIntegralConstructible l E X M →
    sfIntegralConstructible l E X N →
    (star l E j).map ((tensorX.chi l E).app (M, N)) ≫
        tensorRestriction.hom.app (M, N) =
      (proEtaleCanonicalTensorComparison j ((completed l E).ring X)
        ((completed l E).ring U) ((completed l E).pull j)
        tensorX.ordinary tensorU.ordinary).hom.app (M, N) ≫
          (tensorU.chi l E).app ((star l E j).obj M, (star l E j).obj N)
  gamma_restriction : ∀ (K : D l E U) (P : D l E X), sfIntegralConstructible l E U K →
    sfIntegralConstructible l E X P →
    (star l E j).map (gamma l E openData tensorU tensorX K P) ≫
        openData.restrictionIso.hom.app ((integralCompletedTensor.{u, u} l E U).obj
          (K, (star l E j).obj P)) =
      tensorRestriction.hom.app ((J l E j).obj K, P) ≫
        (integralCompletedTensor.{u, u} l E U).map
          (Prod.mkHom (openData.restrictionIso.hom.app K) (𝟙 _))
  completedSquare : integralDerivedPullback.{u, u} l E h ⋙ star l E j' ≅
    star l E j ⋙ integralDerivedPullback.{u, u} l E a
  square_unit : ∀ K : D l E X,
    (star l E j').map ((horizontal.unit l E).app K) ≫ completedSquare.hom.app K =
      (theta l E sq).hom.app K ≫ (horizontalU.unit l E).app ((star l E j).obj K)
  beta_iso : ∀ K : D l E U, sfIntegralConstructible l E U K →
    IsIso (beta l E ambientExchange horizontal horizontalU openData' K)
  beta_unit : ∀ K : D l E U, sfIntegralConstructible l E U K →
    (horizontal.unit l E).app ((J l E j).obj K) ≫
        beta l E ambientExchange horizontal horizontalU openData' K =
      ambientExchange.comparison.hom.app K ≫
        (J l E j').map ((horizontalU.unit l E).app K)
  beta_unique : ∀ (K : D l E U), sfIntegralConstructible l E U K →
    ∀ v : (integralDerivedPullback.{u, u} l E h).obj ((J l E j).obj K) ⟶
        (J l E j').obj ((integralDerivedPullback.{u, u} l E a).obj K),
      (horizontal.unit l E).app ((J l E j).obj K) ≫ v =
        ambientExchange.comparison.hom.app K ≫
          (J l E j').map ((horizontalU.unit l E).app K) →
      v = beta l E ambientExchange horizontal horizontalU openData' K
  beta_restriction : ∀ K : D l E U, sfIntegralConstructible l E U K →
    (star l E j').map (beta l E ambientExchange horizontal horizontalU openData' K) ≫
        openData'.restrictionIso.hom.app ((integralDerivedPullback.{u, u} l E a).obj K) =
      completedSquare.hom.app ((J l E j).obj K) ≫
        (integralDerivedPullback.{u, u} l E a).map (openData.restrictionIso.hom.app K)

/-- Completed open restriction, constructibility, and normalization of the actual open maps.
Source: blueprint main-20261015, sk-prop-sf-pf-coherence, base-change paragraph;
Bhatt--Scholze 3.4.10, 3.5.1--3.5.2, 6.5.5, 6.5.8; Stacks 099M, 099N, 09BN, 09BP, 0GL1
(blueprint: lem-sf-pf-open-factor-coherence).

Proof plan (the eleven steps of this DAG node):
1. Finite type over Spec k implies Noetherian and qcqs. Every open is quasi-compact.
   The coefficient DVR has finite quotients and their two-term finite-free resolutions;
   its uniformizer ideal therefore satisfies def-weil-pbc-adic-coefficient-datum.
   Open localization identifies coefficients by every quotient projection.
2. lem-weil-pbc-constant-completion-equivalence and the ringed Koszul reflector identify
   the quotient completion and its unit with intrinsic completion. The Roos-triangle
   predicate IsSfDerivedComplete is equivalent to invertibility of that actual unit:
   two fibers of the same product-shift are isomorphic, hence intrinsically complete;
   reflection then makes the actual unit invertible. Do not choose an arbitrary fiber map.
3. Exact restriction preserves countable products. The augmentation-normalized comparison
   lem-cbc-exact-product-functor-strict-limit passes it through Roos and its unit. Tensor
   pullback identifies the entire reduction towers. This gives Pull and open.pull_unit.
4. lem-sf-open-tensor-normalization fixes the open unit and ambient full faithfulness.
   lem-cbc-completed-extension-zero-comparison preserves completeness. Restrict this
   adjunction to the full complete categories to obtain the stated Hom bijection.
5. Apply the ambient open tensor normalization to B to A_n. Its scalar-adjunction mate is
   the augmentation-normalized strict comparison. Scalar restriction commutes with
   direct sums and sheafification defining extension. These are strict-tower maps,
   yielding Open.tower and tower_unit; tensor generation gives tower_unique.
6. Exact extension preserves cohomology and each cohomological interval. Extend the finite
   constructible stratification by the reduced closed complement, on which the extension
   is zero, using ringed open/closed localization. The same interval works for every
   reduction. Restricting a partition proves restriction_constructible. No Tor condition.
7. The ordinary gamma is the inverse open-unit transpose. Its reductions are the finite
   gamma maps, and tensor balancing (x tensor y) tensor a goes to
   (x tensor a) tensor (y tensor 1). This formula commutes with every quotient map,
   including the strict quotient augmentation, before applying derived limits.
8. det-sf-open-closed-extension-zero-limits and exact countable products give Open.commutes,
   normalized by the actual augmentation. Apply functorial Roos to the strict maps of
   step 7. The resulting completed map is gamma as defined here. The quotient-augmentation
   square gives gamma_unit, with precisely the chi of constructible tensor completion.
9. lem-fix-constructible-tensor-completion makes both chi maps invertible on the domains
   of step 6. Restrict gamma_unit; ordinary gamma restricts to identity and restriction
   preserves the actual completion unit. Cancel chi to obtain gamma_restriction.
10. Apply lem-cbc-completed-extension-zero-comparison to the square. The strict finite
    exchanges are the inverse open-unit transposes, compatible with every coefficient
    quotient by lem-cbc-finite-open-exchange-scalars. Pull.tower and Open.commutes retain
    those strict models and units, so their transported Roos composite is exactly beta.
11. Reflection makes precomposition with the actual pull-completion unit bijective
    for the complete target. Thus beta_unique identifies the preceding strict-reduction
    map with the displayed completion composite, before any evaluation at reductions.
    Restrict the strict finite inverse-unit formula. Pullback composition and the open
    units give identity on that system; functorial Roos preserves its equality. The
    restricted extension/limit comparison is identity on every product projection and
    both Roos summands. This gives square_unit and beta_restriction as actual equalities,
    without using evaluation at finite reductions to detect completed morphisms. -/
theorem openFactorCoherence (F : FiniteFieldDatum.{u}) (_hl : l ≠ F.p)
    (U' U X' X : Over (Spec (.of F.k)))
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (h : X' ⟶ X)
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (sq : OpenImmersionSquare a.left j'.left j.left h.left) :
    Nonempty (Assertion l E sq) := by
  sorry

end WeilConjectures.OpenFactorCoherence
