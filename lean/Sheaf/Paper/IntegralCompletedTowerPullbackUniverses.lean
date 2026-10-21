/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-! # Integral completed strict-tower interfaces at independent universes

Source: Stacks Project, Tags 099N(5), 03D2, 03D3, 06YS, 06YY and 06XN
(blueprint: def-a1-integral-completed-tower-pullback-universes).
This is the O_E specialization at independent scheme and coefficient sizes.
It retains the actual completed sheaf and quotient transitions on the small site.
It does not replace the general adic datum or the Rlim completed-pullback interface.

## Main definitions

* `reductionPair` is strict derived reduction with its universal computation counit.
* `directRingMap` is the adjoint completed structural map fixed by all projections.
* `pull` is its ordinary ringed module pullback, fixed by its adjunction unit.
* `derivedPull` is the universal derived pullback of strict towers, before Rlim.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedTowerIndependent
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded completed module category, at its actual coefficient size.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
abbrev Modules (W : Scheme.{t}) := SheafOfModules.{max u (t + 1)}
  (completedIntegralCoefficientSheafUnrestricted l E W)

/-- Strict inverse sequences of completed modules.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
abbrev Towers (W : Scheme.{t}) := ℕᵒᵖ ⥤ Modules l E W

/-- The standard localization of the strict tower category.
Source: Stacks 05RU (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
instance towerDerived (W : Scheme.{t}) : HasDerivedCategory (Towers l E W) :=
  HasDerivedCategory.standard _

/-- Transposition of the existing strict diagrams, with every transition retained.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def transpose (W : Scheme.{t}) : (ℕᵒᵖ ⥤ CochainComplex (Modules l E W) ℤ) ⥤
    CochainComplex (Towers l E W) ℤ :=
  PrincipalQuotientCompletion.transpose (completedIntegralCommRingSheafUnrestricted l E W)

/-- The canonical resolving-class pair, including its computation morphism.
Source: Stacks 06XN (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
structure DerivedPair (W Z : Scheme.{t})
    (F : CochainComplex (Modules l E W) ℤ ⥤ CochainComplex (Towers l E Z) ℤ) where
  functor : DerivedCategory (Modules l E W) ⥤ DerivedCategory (Towers l E Z)
  counit : DerivedCategory.Q ⋙ functor ⟶ F ⋙ DerivedCategory.Q
  universal : functor.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (Modules l E W) (.up ℤ))
  computes : ∀ P : CochainComplex (Modules l E W) ℤ,
    integralOperationsGoodComplex l E W P → IsIso (counit.app P)

/-- The existing actual quotient tower, transposed into a complex of strict towers.
Source: Stacks 06YY (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def reductionComplex (W : Scheme.{t}) : CochainComplex (Modules l E W) ℤ ⥤
    CochainComplex (Towers l E W) ℤ :=
  (Functor.ofOpSequence (X := fun n ↦ unrestrictedIntegralComplexFunctor l E W n)
    (unrestrictedIntegralTransition l E W)).flip ⋙ transpose l E W

/-- Reduction has the universal left-derived pair with its actual K-flat computation.
Source: Stacks 06YS, 06YY, 06XN (blueprint: def-a1-integral-completed-tower-pullback-universes).
Proof: flat-term K-flat resolutions exist. Quotient tensoring preserves their
quasi-isomorphisms by change of rings. Exactness of towers is levelwise, so the
resolving-class theorem derives the whole strict construction with its counit. -/
theorem reduction_exists (W : Scheme.{t}) : Nonempty (DerivedPair l E W W
    (reductionComplex l E W)) := by
  sorry

/-- The derived strict reduction, selected with its universal computation counit.
Source: Stacks 06XN (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def reductionPair (W : Scheme.{t}) : DerivedPair l E W W (reductionComplex l E W) :=
  Classical.choice (reduction_exists l E W)

end WeilConjectures.CompletedTowerIndependent

namespace WeilConjectures.CompletedTowerIndependent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- Direct image of ring sheaves on the original small sites.
Source: Stacks 00VC (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
abbrev ringPush := (Scheme.proEtaleBaseChange g).sheafPushforwardContinuous
  RingCat.{max u (t + 1)} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The finite component of the adjoint completed structural map.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def component (n : ℕ) : completedIntegralCoefficientSheafUnrestricted l E Y ⟶
    (ringPush.{t, u} g).obj (integralCoefficientSheaf l E X n) :=
  limit.π (integralCoefficientSheafSystem l E Y) (op n) ≫
    (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (Scheme.coefficientProEtaleDirectRingMap g
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

/-- The finite components commute with every quotient transition.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes).
Proof: the limit-cone equation identifies the two source projections, and the
constant-section direct-image map is natural in the coefficient quotient homomorphism.
Sheafification preserves this equality of constant-presheaf maps. -/
theorem component_naturality {a b : ℕᵒᵖ} (f : a ⟶ b) :
    component l E g a.unop ≫
        (ringPush.{t, u} g).map ((integralCoefficientSheafSystem l E X).map f) =
      component l E g b.unop := by
  sorry

/-- The adjoint of c_g, constructed by the target limit, rather than chosen arbitrarily.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def directRingMap : completedIntegralCoefficientSheafUnrestricted l E Y ⟶
    (ringPush.{t, u} g).obj (completedIntegralCoefficientSheafUnrestricted l E X) :=
  (isLimitOfPreserves (ringPush.{t, u} g)
    (limit.isLimit (integralCoefficientSheafSystem l E X))).lift
      { pt := completedIntegralCoefficientSheafUnrestricted l E Y
        π := { app := fun n ↦ component l E g n.unop
               naturality := fun _a _b f ↦
                 (Category.id_comp _).trans (component_naturality l E g f).symm } }

/-- The sectionwise module direct image with the action through the structural map.
Source: Stacks 03D2 (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def push : Modules l E X ⥤ Modules l E Y :=
  SheafOfModules.pushforward (F := Scheme.proEtaleBaseChange g) (directRingMap l E g)

/-- The canonical ringed module pullback exists as the left adjoint to this pushforward.
Source: Stacks 03D2 (blueprint: def-a1-integral-completed-tower-pullback-universes).
Proof: transport to the coefficient-sized AsSmall site model. Sheafify module Kan
extension along the transported directRingMap; its adjunction transports back to
exactly this pushforward on the original sites. This uniquely fixes G up to its unit. -/
@[instance] theorem push_isRightAdjoint : (push l E g).IsRightAdjoint := by
  sorry

/-- Ordinary ringed module pullback G, fixed by its canonical adjunction.
Source: Stacks 03D2 (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def pull : Modules l E Y ⥤ Modules l E X := (push l E g).leftAdjoint

/-- The adjunction also fixes the inverse-image tensor generators.
Source: Stacks 03D2 (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def adjunction : pull l E g ⊣ push l E g := Adjunction.ofIsRightAdjoint _

/-- Ordinary pullback is additive; exactness is not asserted.
Source: Stacks 03D2 (blueprint: def-a1-integral-completed-tower-pullback-universes).
Proof: sectionwise pushforward is additive, so its left adjoint is additive by the
preadditive adjunction criterion. -/
@[instance] theorem pull_additive : (pull l E g).Additive := by
  sorry

/-- Pullback of every object and transition of a strict tower.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def towerPull : Towers l E Y ⥤ Towers l E X :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pull l E g)

/-- The termwise additive structure on strict tower pullback.
Source: Stacks 099N (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
instance towerPull_additive : (towerPull l E g).Additive := inferInstanceAs
  (((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pull l E g)).Additive)

/-- The universal derived strict tower pullback, with objectwise K-flat computation.
Source: Stacks 06YS, 06YY, 06XN (blueprint: def-a1-integral-completed-tower-pullback-universes).
Proof: resolve strict diagrams by objectwise flat-term K-flat complexes; ordinary
ringed pullback preserves quasi-isomorphisms between these. Apply the resolving-class
left-derived theorem to the termwise additive functor. Its shifts are the derived
termwise shifts, and it is computed on every objectwise K-flat tower. -/
theorem towerPull_exists :
    ∃ (V : DerivedCategory (Towers l E Y) ⥤ DerivedCategory (Towers l E X))
      (ε : DerivedCategory.Q ⋙ V ⟶
        (towerPull l E g).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      V.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Towers l E Y) (.up ℤ)) ∧
      (∃ (_ : V.CommShift ℤ), V.IsTriangulated) ∧
      ∀ P : CochainComplex (Towers l E Y) ℤ,
        (∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
          (R := completedIntegralCommRingSheafUnrestricted l E Y)
            (P.asFunctor.obj (op n))) → IsIso (ε.app P) := by
  sorry

/-- The universal derived functor V_g before completion or inverse limit.
Source: Stacks 06XN (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def derivedPull : DerivedCategory (Towers l E Y) ⥤ DerivedCategory (Towers l E X) :=
  (towerPull_exists l E g).choose

/-- The universal counit, retaining the actual strict tower representative.
Source: Stacks 06XN (blueprint: def-a1-integral-completed-tower-pullback-universes). -/
def derivedCounit : DerivedCategory.Q ⋙ derivedPull l E g ⟶
    (towerPull l E g).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (towerPull_exists l E g).choose_spec.choose

end WeilConjectures.CompletedTowerIndependent

