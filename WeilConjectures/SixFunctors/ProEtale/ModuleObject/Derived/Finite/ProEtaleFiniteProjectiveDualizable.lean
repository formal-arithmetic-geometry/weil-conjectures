/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.ProEtalePullbackInternalHom
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Comparison
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteLocallyProjective

/-!
# Dualizability of finite locally projective coefficient modules

Source: blueprint main-20261015, stratum Hom lemma, proof step 3.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma isDualizable_finite_power
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasFiniteBiproducts A]
    (U : A) (hU : IsDualizable U) (n : ℕ) :
    IsDualizable (∏ᶜ fun _ : Fin n ↦ U) := by
  let : HasBinaryBiproducts A := HasBinaryBiproducts.of_hasBinaryProducts
  induction n with
  | zero =>
    apply IsZero.isDualizable
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro i
    exact Fin.elim0 i
  | succ n hn =>
    let V := ∏ᶜ fun _ : Fin n ↦ U
    let e : U ⊞ V ≅ ∏ᶜ (fun _ : Fin (n + 1) ↦ U) :=
      { hom := Pi.lift (Fin.cases biprod.fst (fun i ↦ biprod.snd ≫ Pi.π _ i))
        inv := biprod.lift (Pi.π _ 0) (Pi.lift fun i : Fin n ↦ Pi.π _ i.succ)
        hom_inv_id := by
          apply biprod.hom_ext
          · simp
          · apply Pi.hom_ext
            intro i
            simp
        inv_hom_id := by
          apply Pi.hom_ext
          intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simp
          · simp }
    exact (hU.biprod hn).of_iso e

private theorem finiteFree_retract_isDualizable
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) (r : ℕ)
    (L : supportModules Λ S) (ι : L ⟶ Mod.finiteFree (condensedRingObj Λ S) r)
    (π : Mod.finiteFree (condensedRingObj Λ S) r ⟶ L) (h : ι ≫ π = 𝟙 _) :
    IsDualizable L := by
  apply IsDualizable.of_retract ⟨ι, π, h⟩
  exact (isDualizable_finite_power _ isDualizable_unit r).of_iso
    (biproduct.isoProduct (fun _ : Fin r ↦ Mod.regular (condensedRingObj Λ S))).symm

/-- A module locally a retract of a finite free module is dualizable.
Source: blueprint stratum Hom lemma, proof step 3; Stacks Project, Tag 08JJ.
(blueprint: lem-proetale-finite-projective-dualizable)

Proof: the internal evaluation from the dual tensor M to Hom(L,M) is invertible
for the regular module by the unitors, and hence for a finite direct sum of regular
modules by the finite-coordinate calculation. Restrict to each member of the covering
in IsFiniteLocallyProjective. The splitting exhibits the evaluation for L as a retract
of this finite-free evaluation; its inverse is obtained by inclusion, finite-free
inverse, and projection. Thus evaluation is locally invertible. The local inverses
agree on overlaps because they invert the same map, and sheaf descent glues them.
In particular evaluation at M=L is invertible. Transposing the identity of L gives
the coevaluation; currying and the inverse evaluation identity prove the two zigzags.
The closed symmetric monoidal duality criterion then supplies a right dual. This also
covers rank zero and the empty site. -/
theorem finiteLocallyProjective_isDualizable
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (S : Scheme.{u}) (L : supportModules Λ S) (hL : IsFiniteLocallyProjective Λ S L) :
    IsDualizable L := by
  have hlocal (W : S.ProEt)
      (h : ∃ (r : ℕ)
        (ι : (supportPullback Λ W.hom).obj L ⟶ Mod.finiteFree (condensedRingObj Λ W.left) r)
        (π : Mod.finiteFree (condensedRingObj Λ W.left) r ⟶
          (supportPullback Λ W.hom).obj L), ι ≫ π = 𝟙 _) :
      IsIso ((supportPullback Λ W.hom).map (MonoidalClosed.ihomUnitTensorToIhom L L)) := by
    obtain ⟨r, ι, π, hip⟩ := h
    obtain ⟨hd⟩ := finiteFree_retract_isDualizable Λ W.left r _ ι π hip
    let M := (supportPullback Λ W.hom).obj L
    let : ExactPairing Mᘁ M := BraidedCategory.exactPairing_swap M Mᘁ
    have : IsIso (MonoidalClosed.ihomUnitTensorToIhom
        ((supportPullback Λ W.hom).obj L) ((supportPullback Λ W.hom).obj L)) :=
      MonoidalClosed.isIso_ihomUnitTensorToIhom Mᘁ M M
    have := supportPullback_ihomComparison_isIso Λ W.hom L
    exact Functor.Monoidal.isIso_map_ihomUnitTensorToIhom_of_ihomComparison _ _ _
  let t := MonoidalClosed.ihomUnitTensorToIhom L L
  have ht : IsIso t.hom := by
    refine Sheaf.isIso_of_isIso_app_of_mem _ t.hom fun V ↦ ?_
    obtain ⟨R, hR, hsplit⟩ := hL V
    refine ⟨R, hR, ?_⟩
    intro W f hf
    have := hlocal W (hsplit W f hf)
    have hmap : IsIso ((ProEtale.upperStar Ab.{u + 1} W.hom).map t.hom) :=
      inferInstanceAs (IsIso ((Mod.forget _).map ((supportPullback Λ W.hom).map t)))
    have hres : IsIso ((ProEtale.localizationRestriction Ab.{u + 1} W.hom W.prop).map
        t.hom) := (NatIso.isIso_map_iff
      (ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} W.hom W.prop) t.hom).mp hmap
    have happ : IsIso (((ProEtale.localizationRestriction Ab.{u + 1} W.hom W.prop).map
        t.hom).hom.app (op (Scheme.ProEt.mk (𝟙 W.left)))) := inferInstance
    rw [ProEtale.localizationRestriction_map_hom_app] at happ
    let e : (MorphismProperty.Over.map ⊤ W.prop).obj
        (Scheme.ProEt.mk (𝟙 W.left)) ≅ W :=
      MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _).symm
    exact @NatTrans.isIso_app_of_iso _ _ _ _ _ _ t.hom.hom _ _ e.op happ
  have : IsIso t := by
    have : IsIso ((Mod.forget _).map t) := ht
    exact isIso_of_reflects_iso t (Mod.forget _)
  let := MonoidalClosed.exactPairingOfIsIso L
  let := BraidedCategory.exactPairing_swap ((ihom L).obj (𝟙_ _)) L
  exact ⟨⟨(ihom L).obj (𝟙_ _)⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
