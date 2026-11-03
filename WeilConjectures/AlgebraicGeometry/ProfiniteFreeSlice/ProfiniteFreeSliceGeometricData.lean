/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.InternalBar.CondensedInternalBarResolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.DisjointUnion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-! # Slice sections and the fixed unit map

Source: Stacks Project Tags 08FI, 08J7; HRS Section 3.
(blueprint: new-c1-profinite-free-slice-geometric-data).

The section map is the fixed map defined in the comparison data, rather than
an arbitrary isomorphism between its source and target. The restriction
comparison and adjunction identities prove that this particular map is invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u vC uC vD uD vA uA
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
open ModuleObjectRingedComparison WeilConjectures
attribute [local instance 1000001] sectionRingHasSheafCompose sectionModulesGrothendieck
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (P : Profinite.{u})

private lemma unit_section_isIso {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {A : Type uA} [Category.{vA} A]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    (N : Cᵒᵖ ⥤ A) (Q : Dᵒᵖ ⥤ A) (α : Q ⟶ G.op ⋙ N)
    (e : N ≅ F.op ⋙ Q)
    (hα : ∀ W : D, α.app (op W) ≫ e.hom.app (op (G.obj W)) =
      Q.map (a.counit.app W).op) (U : C) :
    IsIso (α.app (op (F.obj U)) ≫ N.map (a.unit.app U).op) := by
  have he : (α.app (op (F.obj U)) ≫ N.map (a.unit.app U).op) ≫
      e.hom.app (op U) = 𝟙 _ := by
    have hn : N.map (a.unit.app U).op ≫ e.hom.app (op U) =
        e.hom.app (op (G.obj (F.obj U))) ≫ Q.map (F.map (a.unit.app U)).op :=
      e.hom.naturality (a.unit.app U).op
    rw [Category.assoc, hn, ← Category.assoc, hα]
    change Q.map (a.counit.app (F.obj U)).op ≫
      Q.map (F.map (a.unit.app U)).op = 𝟙 _
    have ht : F.map (a.unit.app U) ≫ a.counit.app (F.obj U) = 𝟙 (F.obj U) :=
      a.left_triangle_components U
    rw [← Q.map_comp, ← op_comp, ht]
    exact Q.map_id (op (F.obj U))
  have : IsIso ((α.app (op (F.obj U)) ≫ N.map (a.unit.app U).op) ≫
      e.hom.app (op U)) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_right _ (e.hom.app (op U))

private theorem general_unit_section_isIso {Y : Scheme.{u}}
    (f : Y ⟶ X) (h : WeaklyEtale f) (M : Internal Λ X) (U : Y.ProEt) :
    IsIso ((((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M).hom.hom.app
      (op ((MorphismProperty.Over.map (f := f) ⊤ h).obj U))) ≫
      ((CondensedRing.upperStar Λ f).obj M).X.obj.map
        ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f h trivial).unit.app U).op) := by
  let F := MorphismProperty.Over.map (f := f) ⊤ h
  let A := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f h trivial
  let N := (CondensedRing.upperStar Λ f).obj M
  let k := CondensedRing.upperStarUnitHom Λ f M
  let c := upperStarIsoLocalizationRestriction Ab.{u + 1} f h
  let eS : N.X ≅ (localizationRestriction Ab.{u + 1} f h).obj M.X :=
    (asIso k).symm ≪≫ c.app M.X
  let e : N.X.obj ≅ F.op ⋙ M.X.obj :=
    (sheafToPresheaf _ Ab.{u + 1}).mapIso eS
  have heS : ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M).hom ≫
      (lowerStar Ab.{u + 1} f).map eS.hom =
        (localizationRestrictionLowerStarAdjunction Ab.{u + 1} f h).unit.app M.X := by
    rw [CondensedRing.upperStarLowerStarAdjunction_unit_app_hom,
      Category.assoc, ← Functor.map_comp]
    change (upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X ≫
      (lowerStar Ab.{u + 1} f).map (k ≫ inv k ≫ (c.app M.X).hom) = _
    rw [IsIso.hom_inv_id_assoc]
    exact Adjunction.unit_leftAdjointUniq_hom_app
      (upperStarLowerStarAdjunction Ab.{u + 1} f)
      (localizationRestrictionLowerStarAdjunction Ab.{u + 1} f h) M.X
  have hα : ∀ W : X.ProEt,
      (((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M).hom.hom.app
        (op W)) ≫ e.hom.app (op ((Scheme.proEtaleBaseChange f).obj W)) =
          M.X.obj.map (A.counit.app W).op := by
    intro W
    have hc := congrArg (fun t ↦ t.hom.app (op W)) heS
    exact hc.trans (by
      simp [localizationRestrictionLowerStarAdjunction,
        Adjunction.sheafPushforwardContinuous, Adjunction.whiskerLeft]
      congr 2)
  exact unit_section_isIso A N.X.obj M.X.obj
    (((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M).hom.hom) e hα
    U


/-- The fixed unit-and-diagonal section map is invertible.
Source: Stacks Project Tag 08J7; HRS Section 3
(blueprint: new-c1-profinite-free-slice-geometric-data).

Proof: write f for the weakly etale test-object morphism, F for
postcomposition by f and G for base change along f. The canonical
upperStarIsoLocalizationRestriction identifies pullback with restriction
along F, and upperStarUnitHom identifies its underlying abelian sheaf.
The uniqueness-of-left-adjoints unit equation identifies the module unit
with the unit induced by F ⊣ G. At each U of the source site, naturality
of this comparison followed by the adjunction triangle shows that the
unit at F(U), followed by restriction along the unit U→G(F(U)), is inverse
to the comparison at U. Both components of the latter are isomorphisms.
Taking U to be V×_X X[P] is exactly the defined sectionToSlice map.
The same adjunction argument includes empty P and empty V. -/
theorem sectionToSlice_isIso (M : Internal Λ X) (V : X.ProEt) :
    IsIso (sectionToSlice Λ X P M V) := by
  dsimp only [sectionToSlice, product, baseChanged, restriction, directImage]
  apply general_unit_section_isIso

end AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
