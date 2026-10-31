/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SbcExchangeFormal
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChangeCoefficients
import WeilConjectures.AlgebraicGeometry.ProperBoundedConstructible
import WeilConjectures.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingMap
import WeilConjectures.AlgebraicGeometry.CondensedAmbientExchange
import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.AlgebraicGeometry.ConstantModuleSheavesForgetColimits
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Proper direct image and exchange along a product projection

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-lem-tf-independent-base-change/det-tf-ibc-proper-step.md and its proof
(blueprint: det-tf-ibc-proper-step).

The exchange uses the canonical constant-ring presentation of the ordinary uncompleted
pro-etale derived category. Its bounded-constructible predicate is the recorded
continuous-function predicate, evaluated through the canonical realization equivalences.

The product Y ×[k] T is `pullback aY aT`. We use the equally canonical product model
X ×[Y] (Y ×[k] T) for X ×[k] T; the first projection is `pullback.fst` and f × id_T
is `pullback.snd`. Thus no choice of a product-square comparison is a hypothesis.

## Main definitions

* `continuousCoefficientModel`: canonical transport to the recorded coefficient presentation.
* `productExchangeArrow`: the published product exchange with its endpoints packaged.

## Main statements

* `proper_product_baseChange`: preservation of Dbc and invertibility of product exchange.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.SbcExchange

/-- Canonical change of coefficient presentation, from modules over the constant
commutative ring sheaf to modules over the sheafified continuous-function ring.
First restrict to constant scalars using the inverse of the published intrinsic
realization equivalence, then apply the published continuous-function realization.
Both are exact equivalences; the displayed functor is their termwise derived descent.
It lets the statement use the recorded bounded-constructible predicate verbatim.
Source: blueprint det-tf-ibc-proper-step, N in Dbc, with the coefficient convention
of def-weil-pbc-proetale-modules (blueprint: det-tf-ibc-proper-step). -/
@[irreducible] def continuousCoefficientModel (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] :
    proEtaleDerivedCategory X A ⥤
      ProEtale.FiniteCoefficientDerivedCategory X (ULift.{u + 1, u} A) :=
  ((sfIntrinsicModuleEquivalence X A).inverse ⋙
    ProEtale.finiteCoefficientRealization X (ULift.{u + 1, u} A)).mapDerivedCategory

set_option maxHeartbeats 1600000 in
-- Allow kernel comparisons of the large ringed-site derived-category instances.
/-- The canonical product exchange, packaged as an arrow in the target derived category.
Its underlying morphism is exactly the published counit mate on the literal pullback
square. Packaging the endpoints avoids repeatedly expanding the large module-category
instances in the theorem. The source product is X ×[Y] (Y ×[S] T), the canonical
model of X ×[S] T for an S-morphism f.
Source: blueprint det-tf-ibc-proper-step, displayed base-change map
(blueprint: det-tf-ibc-proper-step). -/
@[irreducible] def productExchangeArrow (A : Type u) [CommRing A]
    {X Y T S : Scheme.{u}} (aY : Y ⟶ S) (aT : T ⟶ S) (f : X ⟶ Y)
    (N : proEtaleDerivedCategory X A) :
    Arrow (proEtaleDerivedCategory (pullback aY aT) A) :=
  Arrow.mk ((exchange A
      (f := f) (g := pullback.fst aY aT)
      (g' := pullback.fst f (pullback.fst aY aT))
      (f' := pullback.snd f (pullback.fst aY aT))
      { toCommSq := ⟨pullback.condition⟩
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app N)

set_option maxHeartbeats 1600000 in
-- Allow kernel checking of the transported constructibility predicate and derived mate.
/-- Proper pushforward preserves Dbc, and the canonical product-projection exchange
is invertible. All schemes are separated and of finite type over the fixed global
field k. The coefficient hypothesis includes the zero ring: a positive power of ell
annihilates its identity. Bounded constructibility is tested through the exact
coefficient-presentation functor above, using the dependency's predicate unchanged.
Source: blueprint det-tf-ibc-proper-step, statement and both proof paragraphs
(blueprint: det-tf-ibc-proper-step).

Proof, following the four steps of the node:
1. The essential-image criterion of def-weil-pbc-proetale-modules gives a bounded
   constructible etale complex L and an isomorphism from its comparison image to N.
   A positive ell-power annihilates A and hence all cohomology sheaves of L; it is
   invertible over k. The iterated fibre product below is X ×[k] T, by
   def-pc-fibre-product and the equation that f is over k. The product square is
   cartesian. Properness is stable under this base change
   (lem-weil-pbc-proper-base-change). Both proper edges are qcqs, by finite type
   and the closed-immersion diagonal (def-weil-proper-morphism,
   def-weil-finite-type-morphism, def-weil-quasi-separated-morphism,
   def-weil-closed-immersion).
2. Apply lem-fin-proper-bounded-constructible to L and f. The derived direct-image
   comparison prop-weil-pbc-comparison-direct-image, followed by the pushforward
   of the origin isomorphism, realizes Rf_*N as the comparison image of Rf_et,*L.
   The same essential-image criterion proves its bounded constructibility.
3. Forget the A-action on L with def-pur-etale-module-abelian-forget. This functor
   is exact: it preserves colimits (lem-weil-pbc-constant-module-sheaves-forget-colimits)
   and computes kernels sectionwise. Its cohomology is therefore torsion. Apply
   thm-weil-pbc-bounded-below to the proper cartesian square. The canonical
   comparisons lem-weil-pbc-module-abelian-inverse-image-comparison and
   lem-weil-pbc-module-abelian-derived-direct-image-comparison identify the
   underlying module exchange with this invertible abelian exchange, by
   lem-weil-pbc-module-abelian-derived-exchange-compatibility. The forgetful
   functor reflects sheaf isomorphisms, so every cohomology map of the module
   exchange is invertible. Conclude with lem-weil-pbc-derived-plus-iso-on-cohomology.
4. The constant-ring identifications on all four edges are the canonical ones
   (prop-weil-pbc-proetale-constant-ring-map). Apply
   lem-weil-pbc-transport-identifies-exchange, using the pullback and direct-image
   comparisons (lem-weil-pbc-comparison-pullback,
   prop-weil-pbc-comparison-direct-image), to transport step 3 to the ambient
   ringed exchange def-weil-pbc-ambient-ringed-exchange. This is precisely the
   counit transpose specified in det-sbc-exchange-formal. Its naturality with
   respect to the origin isomorphism proves invertibility at N. The canonical
   coefficient-realization equivalences preserve these operations and their
   units and counits, so this calculation is in the displayed ordinary category.
-/
theorem proper_product_baseChange (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ ringChar D.k)
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (hA : ∃ r : ℕ, 0 < r ∧ ((ell ^ r : ℕ) : A) = 0)
    {X Y T : Scheme.{u}}
    (aX : X ⟶ Spec (.of D.k)) (aY : Y ⟶ Spec (.of D.k))
    (aT : T ⟶ Spec (.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (f : X ⟶ Y) [IsProper f] (hf : f ≫ aY = aX)
    (N : proEtaleDerivedCategory X A)
    (hN : ProEtale.isBoundedConstructibleFiniteCoefficient X (ULift.{u + 1, u} A)
      ((continuousCoefficientModel X A).obj N)) :
    ProEtale.isBoundedConstructibleFiniteCoefficient Y (ULift.{u + 1, u} A)
      ((continuousCoefficientModel Y A).obj ((directImage A f).obj N)) ∧
    IsIso (productExchangeArrow A aY aT f N).hom := by
  sorry

end AlgebraicGeometry.Scheme.SbcExchange
