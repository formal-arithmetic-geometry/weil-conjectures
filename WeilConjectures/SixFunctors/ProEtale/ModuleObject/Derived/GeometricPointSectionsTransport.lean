/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationOrdinaryUnit
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective

/-! # Transport geometric-point perfectness to actual scalar sections

Source: sk-lem-finite, first proof paragraph, the identification of geometric-point
realization with ordinary sections (blueprint: lem-sf-geometric-point-sections-transport).

The comparison constructions reuse the regular-module and terminal-section proofs from
the archived point-realization implementation. This module imports no archived declaration.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

private instance pointPullback_leftAdjoint (X : Scheme.{u}) :
    (upperStarFromPoint X).IsLeftAdjoint :=
  (pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint

private instance pointPullback_additive (X : Scheme.{u}) :
    (upperStarFromPoint X).Additive :=
  rightExactFunctor_le_additiveFunctor _ _ _ (by
    rw [rightExactFunctor_iff]
    infer_instance)

/-- The actual tensor-unit global sections equal the terminal condensed scalar ring.
This evaluates the regular module at 1, using the terminal-section universal property.
Source: sk-lem-finite, first paragraph (blueprint: lem-sf-geometric-point-sections-transport). -/
private def pointSectionsScalarEquiv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : MonObj.Γ Λ ≃+* condensedScalarRing Λ :=
  RingEquiv.ofBijective (scalarSectionHom Λ)
    ((regularSectionEquiv Λ (Mod.regular Λ)).bijective.comp Mod.regularEndRingHom_bijective)

private def pointCoyonedaIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    pointCoyoneda Λ ≅ Evaluation.sections (coherentTopology Profinite.{u}) Λ
      (⊤_ Profinite.{u}) ⋙
        ModuleCat.restrictScalars.{u + 1} (pointSectionsScalarEquiv Λ).toRingHom := by
  let S := Evaluation.sections (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u})
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply LinearEquiv.toModuleIso (X₁ := (pointCoyoneda Λ).obj M)
      (X₂ := (S ⋙ ModuleCat.restrictScalars.{u + 1}
        (pointSectionsScalarEquiv Λ).toRingHom).obj M)
    refine
      { toEquiv := regularSectionEquiv Λ M
        map_add' := fun f g ↦ by
          change S.map (f + g) (1 : condensedScalarRing Λ) =
            S.map f (1 : condensedScalarRing Λ) + S.map g (1 : condensedScalarRing Λ)
          rw [S.map_add]
          rfl
        map_smul' := fun s f ↦ by
          change S.map (Mod.regularEndRingHom s ≫ f) (1 : condensedScalarRing Λ) =
            scalarSectionHom Λ s • S.map f (1 : condensedScalarRing Λ)
          rw [S.map_comp]
          let lf : condensedScalarRing Λ →ₗ[condensedScalarRing Λ] S.obj M := (S.map f).hom
          change lf (scalarSectionHom Λ s) = scalarSectionHom Λ s • lf 1
          simpa only [smul_eq_mul, _root_.mul_one] using
            lf.map_smul (scalarSectionHom Λ s) 1 }
  · intro M N f
    ext g
    change S.map (g ≫ f) (1 : condensedScalarRing Λ) =
      S.map f (S.map g (1 : condensedScalarRing Λ))
    rw [S.map_comp]
    rfl

private instance ringRestriction_leftAdjoint
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (ModuleCat.restrictScalars.{u + 1} e.toRingHom).IsLeftAdjoint :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1} e).toAdjunction.isLeftAdjoint

private instance ringRestriction_rightAdjoint
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (ModuleCat.restrictScalars.{u + 1} e.toRingHom).IsRightAdjoint :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1} e).symm.toAdjunction.isRightAdjoint

private def actualSectionsHeartIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    condensedRingCoefficientSections Λ (Spec (.of k)) ≅
      CondensedGeometricPoint.heartFiber Λ k ⋙
        ModuleCat.restrictScalars.{u + 1} (pointSectionsScalarEquiv Λ).toRingHom := by
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  let F := condensedRingCoefficientSections Λ (Spec (.of k))
  exact (Functor.leftUnitor F).symm ≪≫
    Functor.isoWhiskerRight e.counitIso.symm F ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft e.inverse (sectionsPullbackIso Λ k).symm ≪≫
    Functor.isoWhiskerLeft e.inverse (pointCoyonedaIso Λ) ≪≫
    (Functor.associator _ _ _).symm

private def actualSectionsDerivedIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    (condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor ≅
      CondensedGeometricPoint.fiber Λ k ⋙
        (ModuleCat.restrictScalars.{u + 1}
          (pointSectionsScalarEquiv Λ).toRingHom).mapDerivedCategory := by
  have := (finite_point_sections_exact Λ k).1
  have := (finite_point_sections_exact Λ k).2
  exact Functor.rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.mapDerivedCategoryNatIso (actualSectionsHeartIso Λ k) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight (CondensedGeometricPoint.heartFiberDerivedIso Λ k) _

/-- Perfectness supplied by the live geometric-point statement is perfectness of the
actual derived scalar-sections complex over the convolution global section ring.

Source: sk-lem-finite, first proof paragraph
(blueprint: lem-sf-geometric-point-sections-transport).

Proof: the regular module represents sections. Evaluation at 1 identifies its endomorphism
ring with the terminal section ring. The point-topos equivalence identifies actual sections
with singleton evaluation followed by restriction along that ring isomorphism. Exactness
lifts this comparison to the unbounded derived categories. Restriction along a ring
isomorphism preserves bounded finite projective representatives. Apply the perfectness
clause of Statement and transport through the displayed derived comparison.
-/
theorem geometricPointStatement_sections_perfect
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (h : CondensedGeometricPoint.Statement Λ k) :
    (IsNoetherianRing (condensedScalarRing Λ) → IsNoetherianRing (MonObj.Γ Λ)) ∧
    ∀ K : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)),
      _root_.DerivedCategory.IsPerfectRingComplex
        ((condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor.obj K.obj) := by
  constructor
  · intro hR
    exact isNoetherianRing_of_ringEquiv (condensedScalarRing Λ)
      (pointSectionsScalarEquiv Λ).symm
  · intro K
    obtain ⟨_, _, _, _, _, _, hF, _⟩ := h
    have hp := perfect_restrictScalars (pointSectionsScalarEquiv Λ) _ (hF K)
    exact (show _root_.DerivedCategory.IsPerfect _ from hp).of_iso
      ((actualSectionsDerivedIso Λ k).app K.obj).symm

end AlgebraicGeometry.ProEtale.CondensedRing
