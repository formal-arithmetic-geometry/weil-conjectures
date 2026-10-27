/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D8
-/
module

public import Sheaf.Paper.SmoothPurityTowerShriekData

/-! # Constant-section geometric coordinates on strict ell-power systems

Source: Zheng Construction 4.1 and Lemma 4.10; blueprint operations proof (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Inverse and direct image can be normalized to the actual constant quotient
sheaves, with ordinary inverse-image composition and its localized evaluation
equation. This does not construct open extension or an open tensor comparison.
Source: Zheng Construction 4.1 and Lemma 4.10; blueprint operations proof (2),
constant-section transport and inverse-image composition; Stacks 07A4 and 06YS.
(blueprint: lem-sp-strict-geometric-coordinates).

Proof: on each ringed sequence site use the calculus recorded by b. For a scheme
map f the constant-section inverse-image comparison identifies each coefficient
sheaf with the specified coefficient sheaf on the source. Its naturality in
the coefficient ring identifies all adjacent quotient maps. Transport the
algebraic inverse-image construction through these comparisons, using b's fixed
source and target tensor models. Define direct image by the same sectionwise
coefficient action. Transport the two level functors and their adjunction as
one dependent package, not by independent choices of adjunctions. Their units
and counits retain the underlying set-sheaf normalization, so deriving the
ordinary adjunction on K-injective systems gives the specified geometric data,
including transition and projection evaluation. The signed K-flat tensor model
is the transport of the ordinary inverse-image pure-tensor comparison. Compose
the ordinary inverse-image operations by their adjunctions and the canonical
sectionwise direct-image compositor. On every ordinary section its level
evaluation is the canonical constant-ring pullback compositor: both are the
transpose of the same constant-section map. Apply the exact cochain functors
and localization to this square. The geometric pullEvaluation_model identifies
its edges, and the canonical pullback-composition normalization identifies the
last edge with proEtaleConstantRingPullbackComposition. Naturality transports
the equation from Q(P) to every derived object. The construction uses no
flatness of the quotient maps and includes identity maps and empty schemes. -/
theorem strictGeometricCoordinates (b : Base l E) :
    ∃ geometry : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Geometry l E b f,
      ∃ ordinaryComp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
        (geometry g).pull ⋙ (geometry f).pull ≅ (geometry (f ≫ g)).pull,
      ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (K : D l E Z),
        (Ev l E X n).map
            (((Functor.mapDerivedCategoryCompIso (geometry g).pull (geometry f).pull).symm ≪≫
              Functor.mapDerivedCategoryNatIso (ordinaryComp f g)).hom.app K) ≫
            ((geometry (f ≫ g)).pullEvaluation n).hom.app K =
          ((geometry f).pullEvaluation n).hom.app ((pull l E b (geometry g)).obj K) ≫
            (proEtaleConstantRingDerivedPullback (R l E n) f).map
              (((geometry g).pullEvaluation n).hom.app K) ≫
            (proEtaleConstantRingPullbackComposition f g (R l E n)).hom.app
              ((Ev l E Z n).obj K) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerShriek
