/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.InvertibleTorsionOrders
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Sheaf.Paper.ExchangeIdentityPasting
import Sheaf.AlgebraicGeometry.FieldExtensionExchange
import Sheaf.AlgebraicGeometry.SeparableClosureConservative
import Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees

/-!
# Reduction of open-immersion exchange to a separable closure

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
node order 1769 (blueprint: lem-kun-0f1h-sep-reduction).

The product is `Y ×_S X`. Its pullback along `j : U → X` is used as the chosen
model of `Y ×_S U`; the exchange map is evaluated on the sheaf in degree zero.
Scalar extension uses the existing functor `Over.pullback` on all three schemes
and on the open immersion, and the ordinary sheaf inverse image on its coefficient.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical open-product exchange map. Here `q` is the second projection of
`Y ×_S X`, and `p,h` are the two projections of its pullback along `j`.
Source: Weil blueprint, node order 1769 (blueprint: lem-kun-0f1h-sep-reduction).
This is the recorded unbounded exchange, with the coefficient placed in degree zero. -/
noncomputable def openProductExchange {S : Scheme.{u}} {U X : Over S}
    (j : U ⟶ X) (Y : Over S)
    (F : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (D((pullback.snd Y.hom X.hom)^*[AddCommGrpCat.{u + 1}])).obj
        ((R((j.left)_*[AddCommGrpCat.{u + 1}])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ⟶
      (R((pullback.snd j.left (pullback.snd Y.hom X.hom))_*[AddCommGrpCat.{u + 1}])).obj
        ((D((pullback.fst j.left (pullback.snd Y.hom X.hom))^*[AddCommGrpCat.{u + 1}])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) :=
  (exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
    (IsPullback.of_hasPullback j.left (pullback.snd Y.hom X.hom)).toCommSq).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)

/-- Isomorphy of open-product exchange descends from a separable closure.
Source: Weil blueprint, node order 1769 (blueprint: lem-kun-0f1h-sep-reduction).

Proof, following the node's five steps:
1. Finite type over a field makes `U,X` Noetherian, quasi-compact and quasi-separated
   (lem-weil-pbc-finite-type-over-noetherian and
   lem-weil-pbc-locally-noetherian-quasi-separated). The permanence statement
   lem-weil-pbc-qcqs-morphism-permanence makes `j` and its pullback `h` qcqs.
2. Place `F` in degree zero. Exact inverse image, from
   prop-weil-pbc-inverse-image-modules-exact, and lem-kun-stalk-as-pullback identify
   the stalks of `p⁻¹F` with those of `F`, preserving the elementwise torsion condition.
3. Apply lem-kun-0f1c-exchange to `j,F` and `h,p⁻¹F`. This supplies the canonical
   field-extension exchange isomorphisms `a` and `b`. Inverse-image composition
   (lem-weil-pbc-derived-inverse-image-composition) identifies the cube's pullbacks.
4. Lem-kun-unbounded-exchange-agrees identifies these maps with bounded-below
   exchange. Full faithful inclusion reflects isomorphisms. Pullback pasting and
   lem-weil-pbc-exchange-identity-pasting, applied to both factorizations of the outer
   rectangle, identify the extended original exchange with the new exchange:
   `Rh_L,*(C_U) ∘ b ∘ r_Z⁻¹(beta) ∘ C_X = beta_L ∘ q_L⁻¹(a)`.
   Here `C_U` and `C_X` are the inverse-image composition isomorphisms, and
   lem-weil-pbc-cartesian-square-pasting supplies the outer cartesian rectangles.
5. The assumed isomorphy of `beta_L` and the isomorphy of `a,b,C_U,C_X` make
   `r_Z⁻¹(beta)` invertible. Lem-kun-sep-closure-conservative then makes `beta`
   invertible on the original product. No uniform annihilator is used. -/
theorem isIso_openProductExchange_of_separableClosure
    (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L] [IsSepClosure K L]
    (U X Y : Over (Spec (.of K))) (j : U ⟶ X) [IsOpenImmersion j.left]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (F : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionOfInvertibleOrder K U F)
    (hL : IsIso (openProductExchange
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map j)
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj Y)
      ((upperStar AddCommGrpCat.{u + 1}
        (pullback.fst U.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))).obj F))) :
    IsIso (openProductExchange j Y F) := by
  sorry

end AlgebraicGeometry.Etale
