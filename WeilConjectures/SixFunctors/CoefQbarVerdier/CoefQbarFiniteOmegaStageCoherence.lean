/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarFiniteOmegaTransitionTower
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarOperationStageTransitionTower

/-! # The finite dualizing comparison in the recorded stage system

Source: thm-coef-qbar-verdier, finite coefficient transport in steps 4--5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)
open GeneralAlgebraicallyClosedCoefficients (Stage stageSystem)

/-- The finite dualizing comparison, transported along the recorded transition equality. -/
def finiteOmegaStageComparison (F : Finite D l hl Ω X)
    {E L : Index l Ω} (h : E ≤ L) :
    ((stageSystem l Ω X).T h).obj
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
        (F.omega E).omega) ≅
      (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).obj
        (F.omega L).omega :=
  (operationStageTransitionIso l Ω X E L h).app _ ≪≫ (F.scalar E L h).omega

private theorem iso_tower_transport
    {C D : Type*} [Category C] [Category D]
    (K R : C ⥤ D) {A B C' : C} {F G H : D}
    (qEL : A ⟶ B) (uEL : B ⟶ C')
    (qLM : K.obj C' ⟶ R.obj C') (qLM' : K.obj B ⟶ R.obj B)
    (aR : R.obj B ⟶ H) (aT : K.obj A ⟶ G) (qEM : G ⟶ H)
    (uLM : R.obj C' ⟶ F) (uEM : H ⟶ F)
    (hn : K.map uEL ≫ qLM = qLM' ≫ R.map uEL)
    (hs : K.map qEL ≫ qLM' ≫ aR = aT ≫ qEM)
    (hu : R.map uEL ≫ uLM = aR ≫ uEM) :
    K.map (qEL ≫ uEL) ≫ qLM ≫ uLM = aT ≫ qEM ≫ uEM := by
  calc
    K.map (qEL ≫ uEL) ≫ qLM ≫ uLM =
        K.map qEL ≫ K.map uEL ≫ qLM ≫ uLM := by
      rw [K.map_comp]
      simp only [Category.assoc]
    _ = K.map qEL ≫ qLM' ≫ R.map uEL ≫ uLM := by
      rw [reassoc_of% hn]
    _ = K.map qEL ≫ qLM' ≫ aR ≫ uEM := by
      simp only [← Category.assoc, hu]
    _ = aT ≫ qEM ≫ uEM := by
      simp only [← Category.assoc, hs]

/-- The normalized finite dualizing comparisons obey the stage associator equation.
Source: thm-coef-qbar-verdier, finite coefficient transport in steps 4--5;
lem-coef-integral-finite-extension, composition of u.
(blueprint: lem-coef-qbar-finite-omega-stage-coherence).

Proof: replace each rational omega map by the localization of its normalized integral
u map, using F.normalized. The composition clause of integral finite extension gives
T(u(E,L)) followed by u(L,M) equal to the integral balanced tensor associator followed
by u(E,M). Localize this equality. The rational scalar functor sends the localized
integral u to its localized scalar extension; its associator is the localization of
the same balanced tensor associator. The coefficient-inclusion composition law
identifies the composite coefficient map with the direct inclusion. Finally transport
along operationStageTransitionIso and the specified stage associator equality.
Naturality of these equality isomorphisms cancels the intermediate transports.
This argument includes repeated fields, zero objects, and the empty scheme. -/
theorem finiteOmegaStageComparison_tower (F : Finite D l hl Ω X)
    {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M) :
    ((stageSystem l Ω X).T k).map (finiteOmegaStageComparison D l hl Ω X F h).hom ≫
        (finiteOmegaStageComparison D l hl Ω X F k).hom =
      ((stageSystem l Ω X).assoc h k).hom.app
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
            (F.omega E).omega) ≫
        (finiteOmegaStageComparison D l hl Ω X F (h.trans k)).hom := by
  let W : Stage l Ω X E :=
    (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
      (F.omega E).omega
  have hn := (operationStageTransitionIso l Ω X L M k).hom.naturality
    (F.scalar E L h).omega.hom
  have hs := operationStageTransitionIso_tower l Ω X h k W
  have hu := finiteOmegaTransition_tower D l hl Ω X F h k
  exact iso_tower_transport
    ((stageSystem l Ω X).T k)
    (GeneralAlgebraicallyClosedCoefficients.transition l Ω X L M k)
    ((operationStageTransitionIso l Ω X E L h).hom.app W)
    (F.scalar E L h).omega.hom
    ((operationStageTransitionIso l Ω X L M k).hom.app
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).obj
        (F.omega L).omega))
    ((operationStageTransitionIso l Ω X L M k).hom.app
      ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h).obj W))
    ((GeneralAlgebraicallyClosedCoefficients.associator l Ω X E L M h k).hom.app W)
    (((stageSystem l Ω X).assoc h k).hom.app W)
    ((operationStageTransitionIso l Ω X E M (h.trans k)).hom.app W)
    (F.scalar L M k).omega.hom (F.scalar E M (h.trans k)).omega.hom
    hn hs hu

end WeilConjectures.CoefQbarVerdier
