/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeFiniteEtaleSheetTrace
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap

/-! # Explicit local transposes for the native finite-etale trace pairing -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarComp upperStarLowerStarAdjunction

/-- The sheet projection family has a specified value and is a product comparison.
Source: the canonical product map on a split cover.
(blueprint: new-det-sp-native-finite-etale-trace-pairing-local).
Proof. Take the inverse-image comparison followed by the ordinary counit.
The published split-cover product theorem proves invertibility, and the frozen
sheet comparison equation identifies each component. -/
theorem nativeFiniteEtaleSheetProjection_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (c : FiniteEtaleModuleChart p)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    ∃ r : ∀ j : Fin c.degree,
        (upperStar Λ c.map).obj ((lowerStar Λ p).obj M) ⟶
          (upperStar Λ (c.sheet j)).obj M,
      r = (fun j ↦
        (finiteEtaleTraceSheetComparison Λ p c.map (c.sheet j) (c.over j)).hom.app
          ((lowerStar Λ p).obj M) ≫
        (upperStar Λ (c.sheet j)).map ((upperStarLowerStarAdjunction Λ p).counit.app M)) ∧
      IsIso (Pi.lift r) := by
  refine ⟨fun j ↦
    ((eqToIso (congrArg (upperStar Λ) (c.over j))).symm ≪≫
      upperStarComp Λ (c.sheet j) p).hom.app ((lowerStar Λ p).obj M) ≫
      (upperStar Λ (c.sheet j)).map ((upperStarLowerStarAdjunction Λ p).counit.app M),
    ?_, ?_⟩
  · funext j
    exact congrArg (fun e : upperStar Λ c.map ≅
        upperStar Λ p ⋙ upperStar Λ (c.sheet j) ↦
        e.hom.app ((lowerStar Λ p).obj M) ≫
          (upperStar Λ (c.sheet j)).map ((upperStarLowerStarAdjunction Λ p).counit.app M))
      (finiteEtaleTraceSheetComparison_eq Λ p c.map (c.sheet j) (c.over j)).symm
  · exact splitProEtaleModuleProductMap_isIso Λ p c.map c.degree c.sheet c.over c.splits M

/-- The uniquely specified sheet projection family, kept at its native module type.
Source: finite sheet decomposition in smooth trace clause (3).
(blueprint: new-det-sp-native-finite-etale-trace-pairing-local). -/
@[irreducible]
def nativeFiniteEtaleSheetProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (c : FiniteEtaleModuleChart p)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    ∀ j : Fin c.degree,
      (upperStar Λ c.map).obj ((lowerStar Λ p).obj M) ⟶
        (upperStar Λ (c.sheet j)).obj M :=
  Classical.choose (nativeFiniteEtaleSheetProjection_exists Λ p c M)

/-- The projection agrees with the specified sheet comparison.
Source: finite sheet decomposition in smooth trace clause (3).
(blueprint: new-det-sp-native-finite-etale-trace-pairing-local). -/
theorem nativeFiniteEtaleSheetProjection_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (c : FiniteEtaleModuleChart p)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (j : Fin c.degree) :
    nativeFiniteEtaleSheetProjection Λ p c M j =
      (finiteEtaleTraceSheetComparison Λ p c.map (c.sheet j) (c.over j)).hom.app
        ((lowerStar Λ p).obj M) ≫
      (upperStar Λ (c.sheet j)).map ((upperStarLowerStarAdjunction Λ p).counit.app M) := by
  unfold nativeFiniteEtaleSheetProjection
  exact congrFun (Classical.choose_spec
    (nativeFiniteEtaleSheetProjection_exists Λ p c M)).1 j

/-- Naturality of the canonical sheet projection.
Source: finite sheet decomposition in smooth trace clause (3).
(blueprint: new-det-sp-native-finite-etale-trace-pairing-local). -/
theorem nativeFiniteEtaleSheetProjection_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (c : FiniteEtaleModuleChart p)
    {M N : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)}
    (f : M ⟶ N) (j : Fin c.degree) :
    (upperStar Λ c.map).map ((lowerStar Λ p).map f) ≫ nativeFiniteEtaleSheetProjection Λ p c N j =
      nativeFiniteEtaleSheetProjection Λ p c M j ≫ (upperStar Λ (c.sheet j)).map f := by
  simp only [nativeFiniteEtaleSheetProjection_eq]
  exact (Functor.whiskerLeft (lowerStar Λ p)
      (finiteEtaleTraceSheetComparison Λ p c.map (c.sheet j) (c.over j)).hom ≫
    Functor.whiskerRight (upperStarLowerStarAdjunction Λ p).counit
      (upperStar Λ (c.sheet j))).naturality f

/-- The product of sheet projections is invertible.
Source: finite sheet decomposition in smooth trace clause (3).
(blueprint: new-det-sp-native-finite-etale-trace-pairing-local). -/
theorem nativeFiniteEtaleSheetProjection_product_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (c : FiniteEtaleModuleChart p)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    IsIso (Pi.lift (nativeFiniteEtaleSheetProjection Λ p c M)) := by
  unfold nativeFiniteEtaleSheetProjection
  exact (Classical.choose_spec (nativeFiniteEtaleSheetProjection_exists Λ p c M)).2

/-- On a chart the trace pairing is the row of the sheet maps.
Source: finite sheet decomposition in smooth trace clause (3).
(blueprint: new-det-sp-native-finite-etale-trace-pairing-local). -/
theorem nativeFiniteEtaleTracePairing_chart
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p] (c : FiniteEtaleModuleChart p)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : M ⟶ (upperStar Λ p).obj P) :
    (upperStar Λ c.map).map ((lowerStar Λ p).map f ≫ nativeFiniteEtaleSheetTrace Λ p P) =
      Pi.lift (nativeFiniteEtaleSheetProjection Λ p c M) ≫
        ∑ j, Pi.π (fun j ↦ (upperStar Λ (c.sheet j)).obj M) j ≫
          (upperStar Λ (c.sheet j)).map f ≫
          (finiteEtaleTraceSheetComparison Λ p c.map (c.sheet j) (c.over j)).inv.app P := by
  classical
  rw [Functor.map_comp, nativeFiniteEtaleSheetTrace_formula Λ p P c]
  simp only [finiteEtaleTraceSheetSum, Preadditive.comp_sum, Pi.lift_π_assoc]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [nativeFiniteEtaleSheetProjection_eq, Category.assoc] using
    congrArg (fun z ↦ z ≫
      (finiteEtaleTraceSheetComparison Λ p c.map (c.sheet j) (c.over j)).inv.app P)
      (nativeFiniteEtaleSheetProjection_naturality Λ p c f j)


private theorem product_total
    {C : Type*} [Category C] [Preadditive C] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → C) [HasProduct M] :
    ∑ j, Pi.π M j ≫ Pi.ι M j = 𝟙 (∏ᶜ M) := by
  classical
  apply Pi.hom_ext
  intro k
  simp only [Preadditive.sum_comp, Category.assoc, Category.id_comp]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    rw [Pi.ι_π_of_ne M hj, comp_zero]
  · simp

/-- The explicit transpose of an arrow on one sheet of a finite splitting chart.
Source: finite biproduct inclusions in smooth trace clause (3).
(blueprint: new-det-sp-native-finite-etale-trace-pairing-local). -/
def nativeFiniteEtaleLocalTranspose
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (c : FiniteEtaleModuleChart p)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : (lowerStar Λ p).obj M ⟶ P) (j : Fin c.degree) :
    (upperStar Λ (c.sheet j)).obj M ⟶
      (upperStar Λ (c.sheet j)).obj ((upperStar Λ p).obj P) :=
  let q := Pi.lift (nativeFiniteEtaleSheetProjection Λ p c M)
  letI : IsIso q := nativeFiniteEtaleSheetProjection_product_isIso Λ p c M
  Pi.ι (fun j ↦ (upperStar Λ (c.sheet j)).obj M) j ≫ inv q ≫
    (upperStar Λ c.map).map h ≫
    (finiteEtaleTraceSheetComparison Λ p c.map (c.sheet j) (c.over j)).hom.app P

/-- The row of the constructed local transposes reconstructs the supplied arrow.
Source: the finite product inclusion/projection identities.
(blueprint: new-det-sp-native-finite-etale-trace-pairing-local).
Proof. Cancel each sheet composition isomorphism. The sum of projection followed
by inclusion is the identity on a finite product in a preadditive category. The
product comparison cancels its inverse. This also handles zero sheets. -/
theorem nativeFiniteEtaleLocalTranspose_reconstruct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (c : FiniteEtaleModuleChart p)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : (lowerStar Λ p).obj M ⟶ P) :
    Pi.lift (nativeFiniteEtaleSheetProjection Λ p c M) ≫
      (∑ j, Pi.π (fun j ↦ (upperStar Λ (c.sheet j)).obj M) j ≫
        nativeFiniteEtaleLocalTranspose Λ p c M P h j ≫
        (finiteEtaleTraceSheetComparison Λ p c.map (c.sheet j) (c.over j)).inv.app P) =
      (upperStar Λ c.map).map h := by
  classical
  have : IsIso (Pi.lift (nativeFiniteEtaleSheetProjection Λ p c M)) :=
    nativeFiniteEtaleSheetProjection_product_isIso Λ p c M
  simp only [nativeFiniteEtaleLocalTranspose, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id]
  have hs : (∑ j, Pi.π (fun j ↦ (upperStar Λ (c.sheet j)).obj M) j ≫
        Pi.ι (fun j ↦ (upperStar Λ (c.sheet j)).obj M) j ≫
          inv (Pi.lift (nativeFiniteEtaleSheetProjection Λ p c M)) ≫
            (upperStar Λ c.map).map h) =
      (∑ j, Pi.π (fun j ↦ (upperStar Λ (c.sheet j)).obj M) j ≫
        Pi.ι (fun j ↦ (upperStar Λ (c.sheet j)).obj M) j) ≫
          inv (Pi.lift (nativeFiniteEtaleSheetProjection Λ p c M)) ≫
            (upperStar Λ c.map).map h := by
    simp only [Preadditive.sum_comp, Category.assoc]
  rw [hs, product_total, Category.id_comp]
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

@[reassoc]
private theorem row_entry
    {C : Type*} [Category C] [Preadditive C] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → C) [HasProduct M] {P : C} (v : ∀ i, M i ⟶ P) (i : ι) :
    Pi.ι M i ≫ (∑ j, Pi.π M j ≫ v j) = v i := by
  rw [Preadditive.comp_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [← Category.assoc, Pi.ι_π_of_ne M hj.symm, zero_comp]
  · simp

/-- The local transpose of the trace pairing recovers the original sheet map.
Source: finite product inclusion/projection identities in smooth trace clause (3).
(blueprint: new-det-sp-native-finite-etale-trace-pairing-local).
Proof. Substitute the trace-pairing row formula into the explicit transpose.
Cancel the product comparison and its inverse. Composing the row with the
selected product inclusion gives its selected entry, and the sheet composition
comparison cancels its inverse. -/
theorem nativeFiniteEtaleLocalTranspose_pairing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p] (c : FiniteEtaleModuleChart p)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : M ⟶ (upperStar Λ p).obj P) (j : Fin c.degree) :
    nativeFiniteEtaleLocalTranspose Λ p c M P
        ((lowerStar Λ p).map f ≫ nativeFiniteEtaleSheetTrace Λ p P) j =
      (upperStar Λ (c.sheet j)).map f := by
  classical
  have : IsIso (Pi.lift (nativeFiniteEtaleSheetProjection Λ p c M)) :=
    nativeFiniteEtaleSheetProjection_product_isIso Λ p c M
  dsimp only [nativeFiniteEtaleLocalTranspose]
  rw [nativeFiniteEtaleTracePairing_chart Λ p c M P f]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [row_entry_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  simp

end AlgebraicGeometry.ProEtale.CondensedRing
