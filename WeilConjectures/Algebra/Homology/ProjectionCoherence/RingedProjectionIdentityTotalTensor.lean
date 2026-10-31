/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionCoherenceData
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorTotalComponent

/-! # The identity comparison on ordinary total tensor complexes

Source: Stacks Project, Tags 03EL, 07A4 and 0FPI.
(blueprint: lem-sfb-ringed-projection-identity-total-tensor)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory MonoidalCategory
namespace SheafOfModules.ProjectionCoherence
open RingedTensor

attribute [local irreducible] monoidalCategory CanonicalRingedTensorComparison.totalIso

private theorem module_identity {X : RingedTensorCorner.{u, w}}
    (h : RingedTensorEdge X X) (s : Identity h) (M N : X.mateModules) :
    (h.ordinaryTensor.mu M N).hom ≫
      (monoidalCategory X.ring).tensorHom (s.modules.hom.app M) (s.modules.hom.app N) =
        s.modules.hom.app ((monoidalCategory X.ring).tensorObj M N) := by
  let U := underlying X.ring
  let T := (monoidalCategory X.ring).tensorObj M N
  let P := U.obj M ⊗ U.obj N
  let x : P ⟶ U.obj M := CartesianMonoidalCategory.fst _ _
  let y : P ⟶ U.obj N := CartesianMonoidalCategory.snd _ _
  have factor {L : X.mateModules} (v : P ⟶ U.obj L) :
      h.inverse.map v ≫ h.insertion L ≫ U.map (s.modules.hom.app L) =
        s.sets.hom.app P ≫ v := by
    rw [s.insertion]
    exact s.sets.hom.naturality v
  have hp : h.inverse.map (pureSheaf X.ring M N) ≫ h.insertion T ≫
      U.map (h.ordinaryTensor.mu M N).hom =
      CartesianMonoidalCategory.lift (h.inverse.map x ≫ h.insertion M)
        (h.inverse.map y ≫ h.insertion N) ≫
        pureSheaf X.ring (h.pullback.obj M) (h.pullback.obj N) := by
    ext W t
    exact h.ordinaryTensor.pure M N P x y (pureSheaf X.ring M N)
      (by intros; rfl) W t
  let v := (h.ordinaryTensor.mu M N).hom ≫
    (monoidalCategory X.ring).tensorHom (s.modules.hom.app M) (s.modules.hom.app N)
  have hv : h.inverse.map (pureSheaf X.ring M N) ≫ h.insertion T ≫ U.map v =
      s.sets.hom.app P ≫ pureSheaf X.ring M N := by
    dsimp only [v]
    rw [U.map_comp, reassoc_of% hp,
      ← pureSheaf_natural X.ring (s.modules.hom.app M) (s.modules.hom.app N)]
    rw [← Category.assoc, CartesianMonoidalCategory.lift_map]
    simp only [Category.assoc]
    rw [factor x, factor y, ← CartesianMonoidalCategory.comp_lift]
    have hid : CartesianMonoidalCategory.lift x y = 𝟙 P :=
      CartesianMonoidalCategory.lift_fst_snd
    rw [hid]
    erw [Category.comp_id]
    rfl
  have hi : h.inverse.map (pureSheaf X.ring M N) ≫ h.insertion T =
      (s.sets.hom.app P ≫ pureSheaf X.ring M N) ≫ U.map (s.modules.inv.app T) := by
    exact (Iso.eq_comp_inv (U.mapIso (s.modules.app T))).mpr
      (factor (pureSheaf X.ring M N))
  have hf : pureSheaf X.ring M N ≫ U.map (s.modules.inv.app T ≫ v) =
      pureSheaf X.ring M N ≫
        U.map (s.modules.inv.app T ≫ s.modules.hom.app T) := by
    apply (cancel_epi (s.sets.hom.app P)).mp
    have ht := factor (pureSheaf X.ring M N)
    have hh := hv.trans ht.symm
    change h.inverse.map (pureSheaf X.ring M N) ≫ h.insertion T ≫ U.map v =
      h.inverse.map (pureSheaf X.ring M N) ≫ h.insertion T ≫
        U.map (s.modules.hom.app T) at hh
    rw [reassoc_of% hi, reassoc_of% hi] at hh
    simpa only [Functor.map_comp, Category.assoc] using hh
  have hm : s.modules.inv.app T ≫ v =
      s.modules.inv.app T ≫ s.modules.hom.app T := by
    apply pure_hom_ext X.ring M N T
    intro W m n
    exact congrArg (fun t ↦ t.hom.app W (m, n)) hf
  exact (cancel_epi (s.modules.inv.app T)).mp hm

private noncomputable abbrev tensorTotal (X : RingedTensorCorner.{u, w}) :=
  Functor.uncurry.obj ((@MonoidalCategory.curriedTensor X.mateModules _
    (monoidalCategory X.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))

private theorem total_map_eq {A : Type*} [Category A] [Abelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [CategoryTheory.Limits.HasCoproducts.{0} A]
    {P P' Q Q' : CochainComplex A ℤ} (a : P ⟶ P') (b : Q ⟶ Q') :
    (Functor.uncurry.obj ((MonoidalCategory.curriedTensor A).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))).map
          (Prod.mkHom a b) =
      HomologicalComplex.mapBifunctorMap a b (MonoidalCategory.curriedTensor A) (.up ℤ) := by
  simp [Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
    HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

set_option maxHeartbeats 800000 in
-- Elaborate the ordinary tensor comparison on all total-complex summands.
/-- The ordinary total tensor comparison respects a ringed identity datum.

Proof: on ordinary modules the insertion equation identifies the images of generalized
sections under the identity comparison. The pure-tensor formula for the canonical
comparison, followed by naturality of the pure pairing, gives equality on pure tensors.
The tensor universal property gives equality of module morphisms. In each degree of the
cochain total tensor, test on every coproduct summand. Its comparison component is the
inverse module tensor comparison followed by the pullback of the summand inclusion.
Naturality of the module identity comparison and the module equation just proved give
the required equality on that summand. No flatness is needed and no degrees are exchanged.
Source: Stacks Project, Tags 03EL, 07A4 and 0FPI.
(blueprint: lem-sfb-ringed-projection-identity-total-tensor) -/
theorem ringedProjectionIdentityTotalTensor {X : RingedTensorCorner.{u, w}}
    (h : RingedTensorEdge X X) (s : Identity h)
    (P Q : CochainComplex X.mateModules ℤ) :
    (h.ordinaryTensor.totalIso X.ring X.ring h.inverseRing h.inverse h.algebraic
      h.ringMap h.pullback h.object_eq h.pushforward h.moduleAdjunction P Q).inv ≫
        (Functor.uncurry.obj ((@MonoidalCategory.curriedTensor X.mateModules _
          (monoidalCategory X.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))).map
          (Prod.mkHom
          ((NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom.app P)
          ((NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom.app Q)) =
      (NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom.app
        ((Functor.uncurry.obj ((@MonoidalCategory.curriedTensor X.mateModules _
          (monoidalCategory X.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))).obj
          (P, Q)) := by
  let e := h.ordinaryTensor.totalIso X.ring X.ring h.inverseRing h.inverse h.algebraic
    h.ringMap h.pullback h.object_eq h.pushforward h.moduleAdjunction P Q
  apply (cancel_epi e.hom).mp
  change e.hom ≫ (e.inv ≫ _) = e.hom ≫ _
  rw [Iso.hom_inv_id_assoc]
  let := monoidalCategory X.ring
  let := ringedTensorPreadditive X.ring
  rw [total_map_eq]
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap]
  change (s.modules.hom.app (P.X i) ▷ _) ≫ (_ ◁ s.modules.hom.app (Q.X j)) ≫
      CochainComplex.ιMapBifunctor P Q (curriedTensor _) i j n hij =
    CochainComplex.ιMapBifunctor
      ((h.pullback.mapHomologicalComplex (.up ℤ)).obj P)
      ((h.pullback.mapHomologicalComplex (.up ℤ)).obj Q)
      (curriedTensor _) i j n hij ≫ e.hom.f n ≫
      s.modules.hom.app (((tensorTotal X).obj (P, Q)).X n)
  rw [← tensorHom_def_assoc]
  rw [reassoc_of% (ringedTensorTotalComponent h P Q i j n hij)]
  erw [s.modules.hom.naturality]
  have hm := module_identity h s (P.X i) (Q.X j)
  have hm' : (h.ordinaryTensor.mu (P.X i) (Q.X j)).inv ≫
      s.modules.hom.app ((P.X i) ⊗ (Q.X j)) =
      s.modules.hom.app (P.X i) ⊗ₘ s.modules.hom.app (Q.X j) := by
    erw [← hm]
    simp only [Iso.inv_hom_id_assoc]
  erw [← Category.assoc, hm']
  rfl

end SheafOfModules.ProjectionCoherence
