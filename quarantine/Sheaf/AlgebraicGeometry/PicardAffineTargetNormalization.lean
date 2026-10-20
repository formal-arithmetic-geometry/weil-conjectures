/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

import Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveModel
import Sheaf.Algebra.Homology.UniversalH0ProjectiveNormalization
import WeilConjectures.AlgebraicGeometry.AffineLocalizedDerivedSheafification
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Fixed-affine models used in the Picard comparison

Source: Stacks Project, Tag 0BF2.
(blueprint: lem-sc-picard-affine-target-normalization)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- A universally trivial structure H-zero gives a normalized target on the entire affine.
Source: Stacks Project, Tag 0BF2, target complexes; Tags 08CR, 08EB and 0B91.
(blueprint: lem-sc-picard-affine-target-normalization)

Proof: First obtain an unnormalized bounded finite projective module complex P
on the supplied affine. The trivialization identifies its derived sheafification
with the restricted image of M. Perfect base change and the universal ordinary
structure unit give zero negative homology and free rank-one H0 after every ring
base change. Normalize this ring complex to Q by finite-projective cancellation:
remove negative contractible pairs, split its rank-one H0 summand, and cancel the
complementary degree-zero pair. The resulting Q has no negative terms and d0=0.
Apply the explicitly constructed affinePerfectSheafification functor termwise.
The tilde finite-free comparison, restriction-unit comparison and over-equivalence
unit comparison carry every finite-free module retract to a finite-free sheaf
retract. Functoriality proves their retract equations, finite support and negative
term vanishing; preservation of zero maps proves d0=0. Finally the affine derived
sheafification comparison transports the derived isomorphism P to Q, and its
endpoint isomorphisms compose with the geometric P-model isomorphism. The empty
affine is handled by the same construction over the zero ring. -/
theorem picard_affine_target_normalization
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (M : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    (U : W.Opens) (hU : IsAffineOpen U)
    (htrivial : Nonempty
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf)) :
    ∃ C : CochainComplex
        (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ,
      IsStrictlyPerfect W U C ∧ (∀ j : ℤ, j < 0 → IsZero (C.X j)) ∧
      C.d 0 1 = 0 ∧
      Nonempty ((SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj M))) ≅
          DerivedCategory.Q.obj C) := by
  classical
  obtain ⟨P, hb, hf, hp, hbase, ⟨eP⟩⟩ :=
    picard_affine_structure_projective_model f hO M W k U hU htrivial
  let R := W.presheaf.obj (.op U)
  let : HasDerivedCategory.{v + 1} (ModuleCat.{v} R) :=
    HasDerivedCategory.standard _
  obtain ⟨Q, hQb, hQr, hQneg, hQzero, ⟨ePQ⟩⟩ :=
    CochainComplex.universalH0_projective_normalization R P hb hf hp hbase
  let F := affinePerfectSheafification W U hU
  let C := (F.mapHomologicalComplex (.up ℤ)).obj Q
  -- Transport finite free retracts through the explicit affine sheafification.
  let T := Modules.restrictFunctor hU.isoSpec.hom
  let H := T ⋙ (Modules.overEquiv U).inverse
  have : T.Additive := Functor.additive_of_iso (Modules.restrictFunctorIsoPullback _).symm
  have : HasBinaryBiproducts
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : PreservesBinaryBiproducts (Modules.overEquiv U).inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : (Modules.overEquiv U).inverse.Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have hfree (m : ℕ) : Nonempty (F.obj
      (ModuleCat.of R (ULift.{v} (Fin m) →₀ R)) ≅
      SheafOfModules.free (R := (moduleRings W.toRingedSpace).over U)
        (ULift.{v} (Fin m))) := by
    let unitIso := (Modules.overEquiv U).inverse.mapIso
      ((Modules.restrictUnitIso hU.isoSpec.hom) ≪≫
        Modules.overEquivFunctorObjUnitIso U) ≪≫
        ((Modules.overEquiv U).unitIso.app
          (SheafOfModules.unit ((moduleRings W.toRingedSpace).over U))).symm
    exact ⟨H.mapIso (tildeFinsupp (ULift.{v} (Fin m))) ≪≫
      (SheafOfModules.mapFreeIso H (ULift.{v} (Fin m)) unitIso.symm).symm⟩
  have hC : IsStrictlyPerfect W U C := by
    obtain ⟨a, b, hab⟩ := hQb
    refine ⟨⟨a, b, fun n hn ↦ F.map_isZero (hab n hn)⟩, ?_⟩
    intro n
    obtain ⟨m, ι, π, hιπ⟩ := hQr n
    obtain ⟨e⟩ := hfree m
    refine ⟨m, F.map ι ≫ e.hom, e.inv ≫ F.map π, ?_⟩
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hιπ]
    exact F.map_id (Q.X n)
  have hCneg : ∀ n : ℤ, n < 0 → IsZero (C.X n) :=
    fun n hn ↦ F.map_isZero (hQneg n hn)
  have hCzero : C.d 0 1 = 0 := by
    change F.map (Q.d 0 1) = 0
    rw [hQzero, Functor.map_zero]
  -- The affine comparison sends the module-derived isomorphism to the sheaf model.
  obtain ⟨G, _, ⟨cmp⟩⟩ := affine_localized_derived_sheafification W U hU
  refine ⟨C, hC, hCneg, hCzero, ⟨?_⟩⟩
  exact eP ≪≫ (cmp.app P).symm ≪≫ G.mapIso ePQ ≪≫ cmp.app Q

end AlgebraicGeometry.Scheme
