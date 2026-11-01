/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ModelSemilinearComparison.CondensedModelFrobeniusOperatorsBase
import WeilConjectures.TraceFormula.FiniteFieldDatum.FrobeniusOpenSquare

/-! The unit followed by normalized proper/open interchange on a fixed compactification. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

open CondensedOpenProper

/-- The normalized open units are constructed from the actual adjunction units.
Source: the open adjunction and its full faithfulness
(blueprint: def-fd-condensed-compact-support-model-unit).
The ordinary open unit is invertible, hence so is its exact derived unit. -/
def canonicalOpenUnits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :
    OpenUnits Λ where
  unitIso j := by
    intro hj
    have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
      Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
    exact asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit
  normalized j := by
    intro hj
    rfl

/-- The explicit map on a fixed compactification, before a coefficient structure is used.
Source: the unit/proper-open-mate calculation in the global comparison
(blueprint: def-fd-condensed-compact-support-model-unit).
Insert the model pullback unit, move the model direct image past extension by zero,
compose direct images, then use the model map's equality over the point. -/
def compactModelUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Z S : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ S)
    (φX : X ⟶ X) (φZ : Z ⟶ Z)
    (wj : φX ≫ j = j ≫ φZ) (wp : φZ ≫ p = p) (K : D Λ X) :
    (J Λ j ⋙ R Λ p).obj K ⟶ (J Λ j ⋙ R Λ p).obj ((P Λ φX).obj K) :=
  (J Λ j ⋙ R Λ p).map
      ((upperStarLowerStarAdjunction Λ φX).mapDerivedCategoryRightDerivedAdjunction.unit.app K) ≫
    (R Λ p).map ((gamma Λ (canonicalOpenUnits Λ) (CommSq.mk wj.symm)).app
      ((P Λ φX).obj K)) ≫
    (rComp Λ φZ p).hom.app ((J Λ j).obj ((P Λ φX).obj K)) ≫
    eqToHom (congrArg (fun f ↦ (R Λ f).obj ((J Λ j).obj ((P Λ φX).obj K))) wp)

variable (D₀ : WeilConjectures.FiniteFieldDatum.{u})
  (X₀ : Over (Spec (.of D₀.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

omit [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] in
/-- The compactification is finite type over the model field.
Source: properness of a compactification
(blueprint: def-fd-condensed-compact-support-model-unit). -/
theorem modelCompactificationLft (c₀ : Compactification X₀.hom) :
    LocallyOfFiniteType (Over.mk c₀.g).hom := by
  change LocallyOfFiniteType c₀.g
  infer_instance

omit [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] in
/-- The compactification is quasi-compact over the model field.
Source: properness of a compactification
(blueprint: def-fd-condensed-compact-support-model-unit). -/
theorem modelCompactificationQc (c₀ : Compactification X₀.hom) :
    QuasiCompact (Over.mk c₀.g).hom := by
  change QuasiCompact c₀.g
  infer_instance

attribute [local instance] modelCompactificationLft modelCompactificationQc

/-- The iterated model square on the base-changed compactification.
Source: Frobenius open square, including iterate zero
(blueprint: def-fd-condensed-compact-support-model-unit).
Apply the Cartesian model Frobenius square to the model open immersion and unfold
the definitions of the base change and the iterated model endomorphism. -/
theorem modelCompactificationSquare (c₀ : Compactification X₀.hom) (m : ℕ) :
    (frobeniusIterate (modelEnd D₀ X₀) m).left ≫
        (geometricCompactification D₀ X₀ c₀).i =
      (geometricCompactification D₀ X₀ c₀).i ≫
        (frobeniusIterate (modelEnd D₀ (Over.mk c₀.g)) m).left := by
  let j₀ : X₀ ⟶ Over.mk c₀.g := Over.homMk c₀.i c₀.comm.symm
  have : IsOpenImmersion j₀.left := inferInstanceAs (IsOpenImmersion c₀.i)
  have h := (D₀.frobenius_open_square X₀ (Over.mk c₀.g) j₀ m).1.w
  simpa only [frobeniusIterate_left, modelEnd,
    WeilConjectures.FiniteFieldDatum.schemeFrobenius,
    WeilConjectures.FiniteFieldDatum.relativeFrobenius,
    geometricCompactification, Compactification.baseChange,
    Compactification.ofIsPullback, Over.pullback_map_left, Over.homMk_left,
    End.asHom, WeilConjectures.FiniteFieldDatum.geometricFiber,
    Over.pullback_obj_left, Over.mk_hom, Over.mk_left, j₀] using h

/-- The model compactification endomorphism is over the geometric point.
Source: relative Frobenius projections
(blueprint: def-fd-condensed-compact-support-model-unit).
This is precisely the structure-morphism equation of the over-category morphism. -/
theorem modelCompactificationOver (c₀ : Compactification X₀.hom) (m : ℕ) :
    (frobeniusIterate (modelEnd D₀ (Over.mk c₀.g)) m).left ≫
        (geometricCompactification D₀ X₀ c₀).g =
      (geometricCompactification D₀ X₀ c₀).g :=
  Over.w _

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
