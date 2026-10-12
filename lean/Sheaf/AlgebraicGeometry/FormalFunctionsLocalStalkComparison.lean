/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module
public import Sheaf.AlgebraicGeometry.FormalFibreCohomology
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import Sheaf.AlgebraicGeometry.ModulePullbackFiniteType
import Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Sheaf.Paper.HigherDirectImagePresheaf
import Sheaf.Topology.PresheafModuleStalkFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Canonical comparison of the stalk with local-base-change cohomology

Source: Stacks Project, Tags 02OD, 02KH and 01E4.
(blueprint: lem-weil-pbc-formal-functions-local-stalk-comparison)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Cohomology on the local base change, with the action of the local ring.
Source: Stacks Project, Tag 02OD.
(blueprint: def-weil-pbc-formal-functions-local-comparison) -/
abbrev formalFunctionsLocalCohomology {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (p : ℕ) : ModuleCat.{u} (Y.presheaf.stalk y) :=
  (RingedSpace.moduleCohomology (pullback (Y.fromSpecStalk y) f).toRingedSpace p ⋙
    ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
        (pullback.fst (Y.fromSpecStalk y) f).appTop).hom).obj
    ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)

/-- The local comparison sends a germ to the pullback of its representative.
Source: Stacks Project, Tags 02KH, 01E4 and 01FB.
(blueprint: def-weil-pbc-formal-functions-local-comparison) -/
def IsFormalFunctionsLocalComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (p : ℕ)
    (a : formalFunctionsStalk f y F p →ₗ[Y.presheaf.stalk y]
      formalFunctionsLocalCohomology f y F p) : Prop :=
  ∀ (I : InjectiveResolution F)
    (K : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))
    (V : Y.Opens) (hy : y ∈ V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f (Y.fromSpecStalk y) F I K V)
    (xi : (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F))),
    Scheme.Modules.moduleCohomologyFMap
      ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
      ((Scheme.Modules.restrictAdjunction
        ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)) p
      (a (TopCat.Presheaf.germ
        (((Scheme.Modules.pushforward f).rightDerived p).obj F).presheaf V y hy
        ((Scheme.Modules.resolutionSectionClass D.source.resolution
          (((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            I.cocomplex) V D.source.sections p ≫
          Scheme.Modules.Hom.app
            (I.isoRightDerivedObj (Scheme.Modules.pushforward f) p).inv V) xi))) =
    Scheme.Modules.moduleCohomologyFMap
      ((pullback.snd (Y.fromSpecStalk y) f).resLE (f ⁻¹ᵁ V)
        ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p xi

/-- The uncompleted stalk comparison, including the germ formula needed downstream.
Source: Stacks Project, Tag 02OD, first half of its proof; Tags 02KH and 01E4.
(blueprint: lem-weil-pbc-formal-functions-local-stalk-comparison)

Proof: c : Spec O_y → Y is flat and identifies the local ring at its closed point
with O_y. Properness implies qcqs and coherence implies quasi-coherence. Apply flat
base change 02KH to c^*(R^p f_*F) → R^p f'_*F'. Taking closed-point stalks gives an
isomorphism from (R^p f_*F)_y. Every open containing the closed point of Spec O_y is
the whole spectrum, so 01E4 identifies the other stalk with H^p(X', F'). The scalar
map is O_y → Gamma(X', O), giving the displayed linear equivalence. The section-class
formula for the base-change map identifies its value on every germ with pullback
of a representative on a neighbourhood V; this is exactly the predicate above.
Independence of injective-resolution comparisons gives the formula for every I, K
and D. These identifications apply also in degree zero and to the zero module or
empty base change. No finite quotient or completed cohomology is involved. -/
theorem formalFunctions_local_stalk_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p : ℕ) :
    ∃ a : formalFunctionsStalk f y F p ≃ₗ[Y.presheaf.stalk y]
      formalFunctionsLocalCohomology f y F p,
      IsFormalFunctionsLocalComparison f y F p a.toLinearMap := by sorry

end
end AlgebraicGeometry
