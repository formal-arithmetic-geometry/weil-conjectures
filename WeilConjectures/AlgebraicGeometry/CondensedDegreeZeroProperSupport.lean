/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.Sections
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import all WeilConjectures.AlgebraicGeometry.CoefficientHeartLisseExtensionConstructible
import WeilConjectures.AlgebraicGeometry.CondensedLisseSourceZeroLocus
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsOfIsIso
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import all WeilConjectures.AlgebraicGeometry.CompactificationCoherenceCocycle
import all WeilConjectures.AlgebraicGeometry.CompactificationRefinementLocalizing
import WeilConjectures.AlgebraicGeometry.LocalizingClosureCtfEqualsBc

/-! # Degree-zero compact support for constructible condensed modules

Source: latest blueprint, sk-l-dl-a1-endpoints.proof.md, first two sentences, and
sk-def-sfb-module-derived-lower-shriek, degree-zero clause
(blueprint: lem-a1-condensed-degree-zero-proper-support).

All cohomology functors use the actual condensed module derived images. Sections are
represented by module maps out of the regular module. The normalization equations pin the
ordinary identification and the chosen compactification identification to the standard
right-derived degree-zero normalization, followed by the pushforward adjunction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Restriction of a section, represented by its map from the regular coefficient module.
Source: latest blueprint, restriction of sections
(blueprint: lem-a1-condensed-degree-zero-proper-support). -/
def condensedSectionRestriction (ℓ : ℕ) [Fact ℓ.Prime]
    {U X : Scheme.{u}} (j : U ⟶ X)
    (G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (s : (condensedCoefficientSections ℓ X).obj G) :
    (condensedCoefficientSections ℓ U).obj ((upperStar (Profinite.padicAlgClRingObj ℓ) j).obj G) :=
  (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) j).inv ≫
    (upperStar (Profinite.padicAlgClRingObj ℓ) j).map s

/-- Ordinary H^0 on the constructible heart.
Source: latest blueprint, H^0(X,G)
(blueprint: lem-a1-condensed-degree-zero-proper-support). -/
def condensedHeartOrdinaryZero (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (a : X ⟶ Y) :=
  ObjectProperty.ι (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) ⋙
    DerivedCategory.singleFunctor _ 0 ⋙ condensedOrdinaryCohomology ℓ a 0

/-- Compact H^0 on the same heart, computed in a specified compactification.
Source: latest blueprint, H_c^0(X,G)
(blueprint: lem-a1-condensed-degree-zero-proper-support). -/
def condensedHeartCompactZero (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a) :=
  ObjectProperty.ι (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) ⋙
    DerivedCategory.singleFunctor _ 0 ⋙ condensedCompactCohomology ℓ c 0

/-- Sections of constructible modules.
Source: latest blueprint, Gamma(X,G)
(blueprint: lem-a1-condensed-degree-zero-proper-support). -/
def condensedHeartSections (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :=
  ObjectProperty.ι (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) ⋙
    condensedCoefficientSections ℓ X

/-- Sections of the actual extension by zero in a compactification.
Source: latest blueprint, Gamma(Xbar,h_!G)
(blueprint: lem-a1-condensed-degree-zero-proper-support). -/
def condensedCompactificationSections (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a) :=
  ObjectProperty.ι (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) ⋙
    openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) c.i ⋙
      condensedCoefficientSections ℓ c.Z

/-- The standard degree-zero comparison before applying the pushforward adjunction.
Source: latest blueprint, degree-zero normalization of Ra_*
(blueprint: lem-a1-condensed-degree-zero-proper-support). -/
def condensedOrdinaryPointZeroIso (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (a : X ⟶ Y)
    (G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) :
    (condensedOrdinaryCohomology ℓ a 0).obj ((DerivedCategory.singleFunctor _ 0).obj G) ≅
      (condensedCoefficientSections ℓ Y).obj
        ((lowerStar (Profinite.padicAlgClRingObj ℓ) a).obj G) :=
  (condensedCoefficientSections ℓ Y).mapIso
    (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
      (lowerStar (Profinite.padicAlgClRingObj ℓ) a) G 0 ≪≫
      (lowerStar (Profinite.padicAlgClRingObj ℓ) a).rightDerivedZeroIsoSelf.app G)

/-- The compact degree-zero comparison before the proper pushforward adjunction.
The first comparison is the termwise single comparison for the exact open extension.
Source: latest blueprint, degree-zero clause of module derived lower shriek
(blueprint: lem-a1-condensed-degree-zero-proper-support). -/
def condensedCompactPointZeroIso (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    (G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) :
    (condensedCompactCohomology ℓ c 0).obj ((DerivedCategory.singleFunctor _ 0).obj G) ≅
      (condensedCoefficientSections ℓ Y).obj
        ((lowerStar (Profinite.padicAlgClRingObj ℓ) c.g).obj
          ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) c.i).obj G)) :=
  (condensedCoefficientSections ℓ Y).mapIso
    ((DerivedCategory.homologyFunctor _ 0).mapIso
      ((lowerStar (Profinite.padicAlgClRingObj ℓ) c.g).rightDerivedFunctor.mapIso
        ((Functor.mapDerivedCategorySingleFunctor
          (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) c.i) 0).app G)) ≪≫
      Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (lowerStar (Profinite.padicAlgClRingObj ℓ) c.g) _ 0 ≪≫
      (lowerStar (Profinite.padicAlgClRingObj ℓ) c.g).rightDerivedZeroIsoSelf.app _)

private theorem monoidal_scalar_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C]
    (P : A ⥤ B) (F : B ⥤ C) (Q : A ⥤ C)
    [P.LaxMonoidal] [F.LaxMonoidal] [Q.LaxMonoidal]
    (τ : P ⋙ F ⟶ Q) [τ.IsMonoidal] {R : A} (s : 𝟙_ A ⟶ R) :
    Functor.LaxMonoidal.ε F ≫ F.map (Functor.LaxMonoidal.ε P ≫ P.map s) ≫ τ.app R =
      Functor.LaxMonoidal.ε Q ≫ Q.map s := by
  simp only [F.map_comp, Category.assoc]
  rw [← Functor.comp_map, τ.naturality]
  rw [← Category.assoc, ← Category.assoc, ← Functor.LaxMonoidal.comp_ε]
  rw [NatTrans.IsMonoidal.unit]

private theorem monoidalScalar_pullback
    {A B C : Type*} [Category A] [Category B] [Category C]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [MonoidalPreadditive A] [MonoidalPreadditive B] [MonoidalPreadditive C]
    (P : A ⥤ B) (F : B ⥤ C) (Q : A ⥤ C)
    [P.LaxMonoidal] [F.LaxMonoidal] [Q.LaxMonoidal]
    [P.Additive] [F.Additive] [Q.Additive]
    (τ : P ⋙ F ⟶ Q) [τ.IsMonoidal] {R : A} [MonObj R] (s : Γ R) :
    Γ.map (Functor.compAlgHom P F τ R) (Γ.mapFunctor F (Γ.mapFunctor P s)) = Γ.mapFunctor Q s := by
  apply Γ.ext
  simp only [Γ.map_hom, Γ.mapFunctor_hom]
  simpa only [Category.assoc, Functor.compAlgHom] using monoidal_scalar_comp P F Q τ s.hom

private theorem condensedScalar_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Γ Λ) :
    Γ.map (condensedPullbackHom Λ f)
        (Γ.mapFunctor (ProEtale.upperStar Ab.{u + 1} f)
          (condensedRingScalarSections Λ Y s)) = condensedRingScalarSections Λ X s := by
  let (T : Scheme.{u}) : (upperStarFromPoint T).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))).isLeftAdjoint
  let (T : Scheme.{u}) : (upperStarFromPoint T).Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  dsimp only [condensedRingScalarSections]
  exact monoidalScalar_pullback (upperStarFromPoint Y) (ProEtale.upperStar Ab.{u + 1} f)
    (upperStarFromPoint X) (upperStarFromPointComp f).hom (R := Λ) s

private theorem scalarSections_pullback (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (r : CohomologyScalar.{u} ℓ) :
    Γ.map (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f)
        (Γ.mapFunctor (ProEtale.upperStar Ab.{u + 1} f) (cohomologyScalarSections ℓ Y r)) =
      cohomologyScalarSections ℓ X r := by
  exact condensedScalar_pullback (Profinite.padicAlgClRingObj ℓ) f
    ((Profinite.PadicAlgCl.constRingHom ℓ) r.down)

private theorem scalarEnd_pullback (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (r : CohomologyScalar.{u} ℓ) :
    (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) f).inv ≫
        (upperStar (Profinite.padicAlgClRingObj ℓ) f).map
          (Mod.regularEndRingHom (cohomologyScalarSections ℓ Y r)) =
      Mod.regularEndRingHom (cohomologyScalarSections ℓ X r) ≫
        (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) f).inv := by
  apply (cancel_mono (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) f).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (restrictEnd_regularEndRingHom (Profinite.padicAlgClRingObj ℓ) f _).trans
    (congrArg Mod.regularEndRingHom (scalarSections_pullback ℓ f r))

private def pushforwardSectionsIso (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    lowerStar (Profinite.padicAlgClRingObj ℓ) f ⋙ condensedCoefficientSections ℓ Y ≅
      condensedCoefficientSections ℓ X :=
  NatIso.ofComponents (fun G ↦ LinearEquiv.toModuleIso
    (show ((lowerStar (Profinite.padicAlgClRingObj ℓ) f ⋙
        condensedCoefficientSections ℓ Y).obj G) ≃ₗ[CohomologyScalar.{u} ℓ]
      ((condensedCoefficientSections ℓ X).obj G) from
    { toFun := fun z ↦ (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) f).inv ≫
        ((upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f).homEquiv _ _).symm z
      invFun := fun z ↦
        ((upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f).homEquiv _ _)
          ((upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) f).hom ≫ z)
      left_inv := by intro z; simp
      right_inv := by intro z; simp
      map_add' := by
        intro z w
        rw [Adjunction.homAddEquiv_symm_add, Preadditive.comp_add]
      map_smul' := by
        intro r z
        change _ ≫ ((upperStarLowerStarAdjunction _ f).homEquiv _ _).symm
          (Mod.regularEndRingHom (cohomologyScalarSections ℓ Y r) ≫ z) =
            Mod.regularEndRingHom (cohomologyScalarSections ℓ X r) ≫ _
        rw [Adjunction.homEquiv_naturality_left_symm, ← Category.assoc,
          scalarEnd_pullback, Category.assoc] }))
    (fun a ↦ by
      ext z
      change _ ≫ ((upperStarLowerStarAdjunction _ f).homEquiv _ _).symm
        (z ≫ (lowerStar _ f).map a) =
          (_ ≫ ((upperStarLowerStarAdjunction _ f).homEquiv _ _).symm z) ≫ a
      rw [Adjunction.homEquiv_naturality_right_symm, Category.assoc])

private def ordinaryZeroSectionsIso (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    condensedHeartOrdinaryZero ℓ f ≅ condensedHeartSections ℓ X :=
  Functor.isoWhiskerLeft (ObjectProperty.ι
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X))
    (Functor.isoWhiskerRight
      (lowerStar (Profinite.padicAlgClRingObj ℓ) f
        |>.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso)
      (condensedCoefficientSections ℓ Y) ≪≫ pushforwardSectionsIso ℓ f)

private theorem ordinaryZeroSectionsIso_eval
    (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
    (z : (condensedHeartOrdinaryZero ℓ f).obj G) :
    ((ordinaryZeroSectionsIso ℓ f).hom.app G) z =
      (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) f).inv ≫
        ((upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f).homEquiv
          _ _).symm ((condensedOrdinaryPointZeroIso ℓ f G.obj).hom z) := by
  simp only [ordinaryZeroSectionsIso, condensedOrdinaryPointZeroIso,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.trans_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapIso_hom, Functor.map_comp,
    Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso,
    NatIso.ofComponents_hom_app]
  rfl

private def compactZeroSectionsIso (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    condensedHeartCompactZero ℓ c ≅ condensedCompactificationSections ℓ c :=
  Functor.isoWhiskerLeft (ObjectProperty.ι
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X))
    (Functor.isoWhiskerRight
      (Functor.mapDerivedCategorySingleFunctor
        (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) c.i) 0)
      ((lowerStar (Profinite.padicAlgClRingObj ℓ) c.g).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ 0 ⋙ condensedCoefficientSections ℓ Y) ≪≫
      Functor.isoWhiskerLeft (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) c.i)
        (Functor.isoWhiskerRight
          (lowerStar (Profinite.padicAlgClRingObj ℓ) c.g
            |>.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso)
          (condensedCoefficientSections ℓ Y) ≪≫ pushforwardSectionsIso ℓ c.g))

private theorem compactZeroSectionsIso_eval
    (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a)
    (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
    (z : (condensedHeartCompactZero ℓ c).obj G) :
    ((compactZeroSectionsIso ℓ c).hom.app G) z =
      (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) c.g).inv ≫
        ((upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) c.g).homEquiv
          _ _).symm ((condensedCompactPointZeroIso ℓ c G.obj).hom z) := by
  simp only [compactZeroSectionsIso, condensedCompactPointZeroIso,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.trans_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapIso_hom, Functor.comp_map, Functor.map_comp,
    Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso,
    NatIso.ofComponents_hom_app]
  rfl

private def openSectionRestriction (ℓ : ℕ) [Fact ℓ.Prime]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [hη : IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) j).unit] :
    openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j ⋙
      condensedCoefficientSections ℓ X ⟶ condensedCoefficientSections ℓ U where
  app G := ModuleCat.ofHom
    (X := (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j ⋙
      condensedCoefficientSections ℓ X).obj G)
    (Y := (condensedCoefficientSections ℓ U).obj G)
    { toFun := fun z ↦ condensedSectionRestriction ℓ j _ z ≫
        inv ((openImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) j).unit.app G)
      map_add' := by
        intro z w
        change ((upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) j).inv ≫
            (upperStar (Profinite.padicAlgClRingObj ℓ) j).map
              ((z : Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) ⟶
                (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj G) + w)) ≫
                inv ((openImmersionLowerShriekUpperStarAdjunction
                  (Profinite.padicAlgClRingObj ℓ) j).unit.app G) = _
        rw [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
        rfl
      map_smul' := by
        intro r z
        change (_ ≫ (upperStar _ j).map
          (Mod.regularEndRingHom (cohomologyScalarSections ℓ X r) ≫ z)) ≫ _ =
            Mod.regularEndRingHom (cohomologyScalarSections ℓ U r) ≫ _
        rw [Functor.map_comp, ← Category.assoc, scalarEnd_pullback]
        simp only [condensedSectionRestriction, Category.assoc] }
  naturality G H t := by
    ext z
    change (_ ≫ (upperStar _ j).map
      (z ≫ (openImmersionLowerShriek _ j).map t)) ≫ _ =
        ((_ ≫ (upperStar _ j).map z) ≫ _) ≫ t
    rw [Functor.map_comp]
    simp only [Category.assoc]
    have h := (asIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) j).unit).inv.naturality t
    simp only [Functor.comp_map, Functor.id_map, asIso_inv, NatIso.isIso_inv_app] at h
    rw [h]

private theorem openSectionRestriction_apply (ℓ : ℕ) [Fact ℓ.Prime]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) j).unit]
    (G : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U))
    (z : (condensedCoefficientSections ℓ X).obj
      ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj G)) :
    ((openSectionRestriction ℓ j).app G).hom z =
      condensedSectionRestriction ℓ j _ z ≫
        inv ((openImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) j).unit.app G) := by
  rfl

private theorem openSectionRestriction_eval (ℓ : ℕ) [Fact ℓ.Prime]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) j).unit]
    (G : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U))
    (z : (condensedCoefficientSections ℓ X).obj
      ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj G)) :
    ((openSectionRestriction ℓ j).app G) z =
      condensedSectionRestriction ℓ j _ z ≫
        inv ((openImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) j).unit.app G) := by
  rfl

private theorem openExtension_map_eq_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (G : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (s : N ⟶ (openImmersionLowerShriek Λ j).obj G)
    (hs : (upperStar Λ j).map s = 0) : s = 0 := by
  have himage {Y : Scheme.{u}} (g : Y ⟶ X)
      (hg : (upperStar Λ g).map s = 0) :
      IsZero ((upperStar Λ g).obj (Abelian.image s)) := by
    apply IsZero.of_iso _ (Abelian.PreservesImage.iso (upperStar Λ g) s)
    rw [hg]
    exact isZero_kernel_of_mono _
  have hz := isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint
    Λ j j.closedComplement (by rw [j.range_closedComplement]; exact disjoint_compl_right) G
  have hI : IsZero (Abelian.image s) :=
    isZero_of_isZero_upperStar_of_isCompl Λ j.closedComplement j
      (by rw [j.range_closedComplement]; exact isCompl_compl.symm) _
      (himage _ (hz.eq_of_tgt _ _)) (himage j hs)
  rw [← Abelian.image.fac s, hI.eq_of_src (Abelian.image.ι s) 0, comp_zero]

private theorem openSectionRestriction_injective (ℓ : ℕ) [Fact ℓ.Prime]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) j).unit]
    (G : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U)) :
    Function.Injective ((openSectionRestriction ℓ j).app G) := by
  apply (injective_iff_map_eq_zero ((openSectionRestriction ℓ j).app G).hom).2
  intro z hz
  apply openExtension_map_eq_zero (Profinite.padicAlgClRingObj ℓ) j G z
  apply (cancel_epi (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) j).inv).1
  apply (cancel_mono (inv ((openImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ℓ) j).unit.app G))).1
  rw [openSectionRestriction_apply] at hz
  simpa only [condensedSectionRestriction, zero_comp, comp_zero] using hz

private theorem pullback_comp_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {M N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)}
    (s : M ⟶ N) :
    (upperStar Λ (f ≫ g)).map s = 0 ↔
      (upperStar Λ f).map ((upperStar Λ g).map s) = 0 := by
  have h := (upperStarComp Λ f g).hom.naturality s
  change (upperStar Λ (f ≫ g)).map s ≫ (upperStarComp Λ f g).hom.app N =
      (upperStarComp Λ f g).hom.app M ≫
        (upperStar Λ f).map ((upperStar Λ g).map s) at h
  constructor
  · intro hs
    rw [hs, zero_comp] at h
    exact (cancel_epi ((upperStarComp Λ f g).hom.app M)).1
      (by simpa only [comp_zero] using h.symm)
  · intro hs
    change (upperStar Λ (f ≫ g)).map s ≫ (upperStarComp Λ f g).hom.app N =
      (upperStarComp Λ f g).hom.app M ≫
        (upperStar Λ f).map ((upperStar Λ g).map s) at h
    rw [hs] at h
    rw [comp_zero] at h
    exact (cancel_mono ((upperStarComp Λ f g).hom.app N)).1
      (by simpa only [zero_comp] using h)

private theorem openUnit_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit := by
  let ff := (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.comp
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).fullyFaithfulMapModLeft
  have : (openImmersionLowerShriek Λ j).Full := ff.full
  have : (openImmersionLowerShriek Λ j).Faithful := ff.faithful
  exact (openImmersionLowerShriekUpperStarAdjunction Λ j).unit_isIso_of_L_fully_faithful

private theorem regularIso_eq_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} (f : U ⟶ X) :
    (upperStarObjRegularIso Λ f).hom = (Functor.Monoidal.εIso (upperStar Λ f)).inv := by
  apply Mod.hom_ext_of_extendUnitHom (condensedPullbackHom Λ f)
  rw [Functor.Monoidal.εIso_inv]
  have hu := extendUnitHom_η_upperStar Λ f
  change Mod.extendUnitHom (condensedPullbackHom Λ f)
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ X)).obj
        (Mod.regular (condensedRingObj Λ X))) ≫
      (Functor.OplaxMonoidal.η (upperStar Λ f)).hom = condensedPullbackHom Λ f at hu
  calc
    _ = condensedPullbackHom Λ f := by
      simp only [upperStarObjRegularIso, Iso.trans_hom, Iso.app_hom, Mod.comp_hom',
        ← Category.assoc, Mod.extendUnitHom_extendScalarsIsoComapInv_hom_app,
        Category.id_comp]
      rfl
    _ = _ := hu.symm

private theorem regularIso_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStarObjRegularIso Λ f).inv ≫
        (upperStar Λ f).map (upperStarObjRegularIso Λ g).inv ≫
        (upperStarComp Λ f g).inv.app (Mod.regular (condensedRingObj Λ Z)) =
      (upperStarObjRegularIso Λ (f ≫ g)).inv := by
  have he : (upperStarComp Λ f g).app (Mod.regular (condensedRingObj Λ Z)) ≪≫
      (upperStar Λ f).mapIso (upperStarObjRegularIso Λ g) ≪≫ upperStarObjRegularIso Λ f =
        upperStarObjRegularIso Λ (f ≫ g) := by
    apply Iso.ext
    have hu := upperStarComp_hom_app_unit Λ f g
    change (upperStarComp Λ f g).hom.app (Mod.regular (condensedRingObj Λ Z)) ≫
        (upperStar Λ f).map (Functor.Monoidal.εIso (upperStar Λ g)).inv ≫
          (Functor.Monoidal.εIso (upperStar Λ f)).inv =
        (Functor.Monoidal.εIso (upperStar Λ (f ≫ g))).inv at hu
    simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, regularIso_eq_unit] using hu
  exact congrArg Iso.inv he

private theorem regularIso_comp_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    (upperStarObjRegularIso Λ h).inv ≫
        (eqToIso (congrArg (upperStar Λ) w.symm) ≪≫ upperStarComp Λ f g).hom.app
          (Mod.regular (condensedRingObj Λ Z)) =
      (upperStarObjRegularIso Λ f).inv ≫
        (upperStar Λ f).map (upperStarObjRegularIso Λ g).inv := by
  subst h
  simp only [eqToIso_refl, Iso.refl_trans]
  apply (cancel_mono ((upperStarComp Λ f g).inv.app
    (Mod.regular (condensedRingObj Λ Z)))).1
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using
    (regularIso_comp Λ f g).symm

private def restrictionComparison
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : B ⥤ C) (H : C ⥤ B) (adj : F ⊣ H)
    (Rc : B ⥤ A) (Rd : C ⥤ A) (κ : Rc ≅ F ⋙ Rd) : H ⋙ Rc ⟶ Rd where
  app N := κ.hom.app (H.obj N) ≫ Rd.map (adj.counit.app N)
  naturality N N' z := by
    dsimp only [Functor.comp_map]
    rw [← Category.assoc, κ.hom.naturality]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
    exact congrArg (fun t ↦ κ.hom.app (H.obj N) ≫ Rd.map t)
      (by simpa only [Functor.comp_map, Functor.id_map] using adj.counit.naturality z)

private theorem restrictionComparison_eq
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : B ⥤ C) (H : C ⥤ B) (adj : F ⊣ H)
    (Rc : B ⥤ A) (Rd : C ⥤ A) (κ : Rc ≅ F ⋙ Rd) :
    restrictionComparison F H adj Rc Rd κ =
      Functor.whiskerLeft H κ.hom ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight adj.counit Rd ≫ (Functor.leftUnitor _).hom := by
  ext N
  simp only [restrictionComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id]

private def heartRefinementRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c) :
    lowerStar Λ r.hom.hom.hom ⋙ upperStar Λ c.obj.obj.i ⟶ upperStar Λ d.obj.obj.i :=
  restrictionComparison (upperStar Λ r.hom.hom.hom) (lowerStar Λ r.hom.hom.hom)
    (upperStarLowerStarAdjunction Λ r.hom.hom.hom)
    (upperStar Λ c.obj.obj.i) (upperStar Λ d.obj.obj.i)
    (eqToIso (congrArg (upperStar Λ) r.hom.hom.i_hom.symm) ≪≫
      upperStarComp Λ d.obj.obj.i r.hom.hom.hom)

private theorem heartRefinementRestriction_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c) :
    IsIso (heartRefinementRestriction Λ r) := by
  have sq : IsPullback (𝟙 X) d.obj.obj.i c.obj.obj.i r.hom.hom.hom :=
    IsOpenImmersion.isPullback _ _ _ _
      (by simpa only [Category.id_comp] using r.hom.hom.i_hom) r.property
  have := openUnit_isIso Λ c.obj.obj.i
  rw [heartRefinementRestriction, restrictionComparison_eq]
  exact CategoryTheory.restrictionMate_isIso
    (openImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i)
    (upperStarLowerStarAdjunction Λ r.hom.hom.hom)
    (openImmersionLowerShriekUpperStarAdjunction Λ d.obj.obj.i)
    (eqToIso (congrArg (upperStar Λ) r.hom.hom.i_hom.symm) ≪≫
      upperStarComp Λ d.obj.obj.i r.hom.hom.hom)
    (fun G ↦ cartesianModuleCounit Λ sq G)

private theorem adjoint_transpose_unit
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {G : C} {M : D} (z : G ⟶ R.obj M) :
    adj.unit.app G ≫ R.map ((adj.homEquiv _ _).symm z) = z := by
  exact (adj.homEquiv_unit G M ((adj.homEquiv G M).symm z)).symm.trans
    ((adj.homEquiv G M).apply_symm_apply z)

private def adjointFromComparison
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (T : C ⥤ D) (V : C ⥤ C)
    (a : T ⋙ R ≅ V) (b : 𝟭 C ≅ V) : L ⟶ T where
  app G := (adj.homEquiv G (T.obj G)).symm (b.hom.app G ≫ a.inv.app G)
  naturality _ _ t := by
    simpa only [Functor.id_obj, Functor.id_map, NatTrans.comp_app] using
      adjoint_transpose_naturality
      adj (𝟭 C) T (b.hom ≫ a.inv) t

private theorem adjointFromComparison_normalized
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (T : C ⥤ D) (V : C ⥤ C)
    (a : T ⋙ R ≅ V) (b : 𝟭 C ≅ V) (G : C) :
    adj.unit.app G ≫ R.map ((adjointFromComparison adj T V a b).app G) ≫
        a.hom.app G = b.hom.app G := by
  change adj.unit.app G ≫ R.map ((adj.homEquiv G (T.obj G)).symm
    (b.hom.app G ≫ a.inv.app G)) ≫ a.hom.app G = _
  rw [← Category.assoc, adjoint_transpose_unit]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private def heartRefinementMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c) :
    openImmersionLowerShriek Λ c.obj.obj.i ⟶
      openImmersionLowerShriek Λ d.obj.obj.i ⋙ lowerStar Λ r.hom.hom.hom := by
  have := heartRefinementRestriction_isIso Λ r
  have := openUnit_isIso Λ d.obj.obj.i
  exact adjointFromComparison
    (openImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i)
    (openImmersionLowerShriek Λ d.obj.obj.i ⋙ lowerStar Λ r.hom.hom.hom)
    (openImmersionLowerShriek Λ d.obj.obj.i ⋙ upperStar Λ d.obj.obj.i)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft
      (openImmersionLowerShriek Λ d.obj.obj.i) (asIso (heartRefinementRestriction Λ r)))
    (asIso (openImmersionLowerShriekUpperStarAdjunction Λ d.obj.obj.i).unit)

private theorem heartRefinementMap_normalized
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (openImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i).unit.app G ≫
        (upperStar Λ c.obj.obj.i).map ((heartRefinementMap Λ r).app G) ≫
        (heartRefinementRestriction Λ r).app
          ((openImmersionLowerShriek Λ d.obj.obj.i).obj G) =
      (openImmersionLowerShriekUpperStarAdjunction Λ d.obj.obj.i).unit.app G := by
  have := heartRefinementRestriction_isIso Λ r
  have := openUnit_isIso Λ d.obj.obj.i
  have h := adjointFromComparison_normalized
    (openImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i)
    (openImmersionLowerShriek Λ d.obj.obj.i ⋙ lowerStar Λ r.hom.hom.hom)
    (openImmersionLowerShriek Λ d.obj.obj.i ⋙ upperStar Λ d.obj.obj.i)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft
      (openImmersionLowerShriek Λ d.obj.obj.i) (asIso (heartRefinementRestriction Λ r)))
    (asIso (openImmersionLowerShriekUpperStarAdjunction Λ d.obj.obj.i).unit) G
  simpa only [heartRefinementMap, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    asIso_hom, Category.id_comp] using h

private theorem regular_lisse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    IsLisseCoefficientModule Λ (Mod.regular (condensedRingObj Λ X)) := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  exact ⟨1, ⟨upperStarObjRegularIso Λ (𝟙 X) ≪≫ (biproductUniqueIso
    (fun _ : Fin 1 ↦ Mod.regular (condensedRingObj Λ X))).symm⟩⟩

private theorem open_constructible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Z : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Z
      ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj G.obj) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (Z ↘ Spec (.of k))
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (X ↘ Spec (.of k))
      toCompactSpace := inferInstance }
  have hG := G.property
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at hG ⊢
  exact stratified_openExtension (Profinite.padicAlgClRingObj ℓ) j G.obj hG

private theorem closedSupport_proper {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (T : TopologicalSpace.Closeds c.Z)
    (hT : (T : Set c.Z) ⊆ Set.range c.i) :
    IsProper ((Scheme.IdealSheafData.vanishingIdeal
      (⟨c.i ⁻¹' (T : Set c.Z), T.isClosed.preimage c.i.continuous⟩ :
        TopologicalSpace.Closeds X)).subschemeι ≫ f) := by
  classical
  let S : TopologicalSpace.Closeds X :=
    ⟨c.i ⁻¹' (T : Set c.Z), T.isClosed.preimage c.i.continuous⟩
  let q := (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
  have hq : Set.range q = (T : Set c.Z) := by simp [q]
  let l := IsOpenImmersion.lift c.i q (hq.symm ▸ hT)
  have hl : l ≫ c.i = q := IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion (l ≫ c.i) := hl ▸ inferInstance
  have : IsClosedImmersion l := IsClosedImmersion.of_comp l c.i
  have hr : Set.range l = (S : Set X) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      change c.i (l z) ∈ (T : Set c.Z)
      exact hq ▸ (show c.i (l z) ∈ Set.range q from
        ⟨z, (congrArg
        (fun t : (Scheme.IdealSheafData.vanishingIdeal T).subscheme ⟶ c.Z ↦ t z) hl).symm⟩)
    · intro hx
      change c.i x ∈ (T : Set c.Z) at hx
      obtain ⟨z, hz⟩ := hq.symm ▸ hx
      refine ⟨z, ?_⟩
      apply (Scheme.Hom.isOpenEmbedding c.i).injective
      exact (congrArg
        (fun t : (Scheme.IdealSheafData.vanishingIdeal T).subscheme ⟶ c.Z ↦ t z) hl).trans hz
  obtain ⟨e, he, _⟩ :=
    (Scheme.IdealSheafData.reduced_induced_closed_subscheme X S).2.2.2.2.2.2.2
      _ l hr |>.2
  have hlp : IsProper (l ≫ f) := by
    have heq : l ≫ f = q ≫ c.g := by
      calc
        l ≫ f = l ≫ (c.i ≫ c.g) := congrArg (fun t ↦ l ≫ t) c.comm
        _ = q ≫ c.g := by rw [← Category.assoc, hl]
    rw [heq]
    infer_instance
  have h : (Scheme.IdealSheafData.vanishingIdeal S).subschemeι ≫ f =
      e.inv ≫ (l ≫ f) := by
    rw [← he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change IsProper ((Scheme.IdealSheafData.vanishingIdeal S).subschemeι ≫ f)
  rw [h]
  infer_instance

private theorem extensionSection_geometric_boundary_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j]
    (G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (s : Mod.regular (condensedRingObj Λ Z) ⟶ (openImmersionLowerShriek Λ j).obj G)
    (x : Z) (hx : x ∉ Set.range j)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ Z)
    (hb : (Scheme.SpecToEquivOfField Ω Z b).1 = x) : (upperStar Λ b).map s = 0 := by
  have hdisj : Disjoint (Set.range j.base) (Set.range b.base) := by
    apply Set.disjoint_left.2
    rintro y hy ⟨z, rfl⟩
    have hb' : b z = x := by
      change b (IsLocalRing.closedPoint Ω) = x at hb
      exact (congrArg b (Subsingleton.elim z (IsLocalRing.closedPoint Ω))).trans hb
    exact hx (hb' ▸ hy)
  exact (isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint
    Λ j b hdisj G).eq_of_tgt _ _

private theorem support_complement_geometry {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (W : c.Z.Opens)
    (hboundary : ∀ x, x ∉ Set.range c.i → x ∈ W) :
    ∃ S : TopologicalSpace.Closeds X,
      IsProper ((Scheme.IdealSheafData.vanishingIdeal S).subschemeι ≫ f) ∧
      Set.range (Scheme.Opens.ι S.compl ≫ c.i) ⊆ Set.range W.ι := by
  classical
  have hT : (W.compl : Set c.Z) ⊆ Set.range c.i := by
    intro x hx
    by_contra h
    exact hx (hboundary x h)
  let S : TopologicalSpace.Closeds X :=
    ⟨c.i ⁻¹' (W.compl : Set c.Z), W.compl.isClosed.preimage c.i.continuous⟩
  refine ⟨S, closedSupport_proper c W.compl hT, ?_⟩
  rintro x ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  have hy := y.property
  change ¬ c.i (Scheme.Opens.ι S.compl y) ∉ W at hy
  exact not_not.mp hy

private theorem map_section_eq_zero
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {L M N P : C} {Q : D}
    (q : Q ⟶ F.obj L) (a : L ⟶ M) (s : M ⟶ N) (b : N ⟶ P)
    (hs : F.map s = 0) : q ≫ F.map ((a ≫ s) ≫ b) = 0 := by
  simp only [Functor.map_comp, hs, comp_zero, zero_comp]

private theorem pullback_zero_congr
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Z : Scheme.{u}}
    (f g : U ⟶ Z) (h : f = g)
    {M N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)}
    (s : M ⟶ N) : (upperStar Λ f).map s = 0 ↔ (upperStar Λ g).map s = 0 := by
  subst g
  rfl

private theorem pullback_zero_of_open_factorization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Z : Scheme.{u}}
    (f : U ⟶ Z) (W : Z.Opens) (hf : Set.range f ⊆ Set.range W.ι)
    {M N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)}
    (s : M ⟶ N) (hs : (upperStar Λ W.ι).map s = 0) : (upperStar Λ f).map s = 0 := by
  let w := IsOpenImmersion.lift W.ι f hf
  apply (pullback_zero_congr Λ f (w ≫ W.ι)
    (IsOpenImmersion.lift_fac W.ι f hf).symm s).2
  apply (pullback_comp_zero Λ w W.ι s).2
  rw [hs, Functor.map_zero]

private theorem normalized_section_zero
    (ℓ : ℕ) [Fact ℓ.Prime] {X Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j]
    [IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) j).unit]
    (G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (s : (condensedCoefficientSections ℓ Z).obj
      ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj G))
    (S : TopologicalSpace.Closeds X)
    (hs : (upperStar (Profinite.padicAlgClRingObj ℓ) (Scheme.Opens.ι S.compl)).map
      ((upperStar (Profinite.padicAlgClRingObj ℓ) j).map s) = 0) :
    condensedSectionRestriction ℓ (Scheme.Opens.ι S.compl) G
      (((openSectionRestriction ℓ j).app G) s) = 0 := by
  rw [openSectionRestriction_eval]
  exact map_section_eq_zero
    (upperStar (Profinite.padicAlgClRingObj ℓ) (Scheme.Opens.ι S.compl))
    (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) (Scheme.Opens.ι S.compl)).inv
    (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) j).inv
    ((upperStar (Profinite.padicAlgClRingObj ℓ) j).map s)
    (inv ((openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) j).unit.app G)) hs

private theorem pullback_section_support
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    {M N : Mod (Sheaf (Scheme.ProEt.topology c.Z) Ab.{u + 1}) (condensedRingObj Λ c.Z)}
    (s : M ⟶ N) (W : c.Z.Opens)
    (hboundary : ∀ x, x ∉ Set.range c.i → x ∈ W)
    (hWs : (upperStar Λ W.ι).map s = 0) :
    ∃ S : TopologicalSpace.Closeds X,
      IsProper ((Scheme.IdealSheafData.vanishingIdeal S).subschemeι ≫ f) ∧
      (upperStar Λ (Scheme.Opens.ι S.compl)).map ((upperStar Λ c.i).map s) = 0 := by
  obtain ⟨S, hS, hv⟩ := support_complement_geometry c W hboundary
  refine ⟨S, hS, ?_⟩
  apply (pullback_comp_zero Λ (Scheme.Opens.ι S.compl) c.i s).1
  exact pullback_zero_of_open_factorization Λ _ W hv s hWs

private theorem normalized_section_support
    (ℓ : ℕ) [Fact ℓ.Prime] {X Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j]
    [IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) j).unit]
    (G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (s : (condensedCoefficientSections ℓ Z).obj
      ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj G))
    (P : TopologicalSpace.Closeds X → Prop)
    (h : ∃ S, P S ∧
      (upperStar (Profinite.padicAlgClRingObj ℓ) (Scheme.Opens.ι S.compl)).map
        ((upperStar (Profinite.padicAlgClRingObj ℓ) j).map s) = 0) :
    ∃ S, P S ∧ condensedSectionRestriction ℓ (Scheme.Opens.ι S.compl) G
      (((openSectionRestriction ℓ j).app G) s) = 0 := by
  exact h.imp (fun S hs ↦ ⟨hs.1, normalized_section_zero ℓ j G s S hs.2⟩)

private theorem zeroLocus_open_core
    (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    {L M : condensedModuleCategory T (Mon.mk (Profinite.padicAlgClRingObj ℓ))}
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) L)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) T M)
    (f : L ⟶ M) :
    ∃ W : T.Opens,
      (∀ x : T,
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ T),
          (Scheme.SpecToEquivOfField Ω T b).1 = x →
            (upperStar (Profinite.padicAlgClRingObj ℓ) b).map f = 0) → x ∈ W) ∧
      (upperStar (Profinite.padicAlgClRingObj ℓ) W.ι).map f = 0 := by
  obtain ⟨W, hW, _, hWs, _⟩ := condensedLisseSource_zero_locus k (ringChar k) ℓ
    (Ne.symm (Fact.out : ringChar k ≠ ℓ)) T a hL hM f
  refine ⟨W, ?_, hWs⟩
  intro x hx
  exact (Set.ext_iff.mp hW x).2 hx

private theorem generic_compactSection_support
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (s : Mod.regular (condensedRingObj Λ c.Z) ⟶ (openImmersionLowerShriek Λ c.i).obj G)
    (hG : IsConstantModelConstructible Λ c.Z ((openImmersionLowerShriek Λ c.i).obj G))
    (hzero : ∀ {L M : condensedModuleCategory c.Z (Mon.mk Λ)},
      IsLisseCoefficientModule Λ L → IsConstantModelConstructible Λ c.Z M →
      ∀ z : L ⟶ M, ∃ W : c.Z.Opens,
        (∀ x : c.Z,
          (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ c.Z),
            (Scheme.SpecToEquivOfField Ω c.Z b).1 = x →
              (upperStar Λ b).map z = 0) → x ∈ W) ∧
        (upperStar Λ W.ι).map z = 0) :
    ∃ S : TopologicalSpace.Closeds X,
      IsProper ((Scheme.IdealSheafData.vanishingIdeal S).subschemeι ≫ f) ∧
      (upperStar Λ (Scheme.Opens.ι S.compl)).map ((upperStar Λ c.i).map s) = 0 := by
  obtain ⟨W, hW, hWs⟩ := hzero
    (L := Mod.regular (condensedRingObj Λ c.Z))
    (M := (openImmersionLowerShriek Λ c.i).obj G) (regular_lisse Λ c.Z) hG s
  have hboundary (x : c.Z) (hx : x ∉ Set.range c.i) : x ∈ W := by
    apply hW x
    intro Ω _ _ b hb
    exact extensionSection_geometric_boundary_zero Λ c.i G s x hx Ω b hb
  exact pullback_section_support Λ c s W hboundary hWs

set_option backward.defeqAttrib.useBackward true in
private theorem compactSection_proper_support
    (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] (c : Compactification (X ↘ Spec (.of k)))
    [IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) c.i).unit]
    (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
    (s : (condensedCompactificationSections ℓ c).obj G) :
    ∃ S : TopologicalSpace.Closeds X,
      IsProper ((Scheme.IdealSheafData.vanishingIdeal S).subschemeι ≫
        (X ↘ Spec (.of k))) ∧
      condensedSectionRestriction ℓ (Scheme.Opens.ι S.compl) G.obj
        (((openSectionRestriction ℓ c.i).app G.obj) s) = 0 := by
  apply normalized_section_support ℓ c.i G.obj s
    (fun S ↦ IsProper ((Scheme.IdealSheafData.vanishingIdeal S).subschemeι ≫
      (X ↘ Spec (.of k))))
  classical
  let : c.Z.Over (Spec (.of k)) := ⟨c.g⟩
  have : c.i.IsOver (Spec (.of k)) := ⟨c.comm.symm⟩
  -- Explicit instances: searching `QuasiCompact c.g` here took about 18 s.
  have hp : IsProper c.g := c.isProper
  have : UniversallyClosed c.g := hp.toUniversallyClosed
  have hqc : QuasiCompact c.g := ⟨fun _ _ ↦ c.g.isProperMap.isCompact_preimage⟩
  have : LocallyOfFiniteType (c.Z ↘ Spec (.of k)) := hp.toLocallyOfFiniteType
  have : QuasiCompact (c.Z ↘ Spec (.of k)) := hqc
  have : IsSeparated (c.Z ↘ Spec (.of k)) := hp.toIsSeparated
  have hzero := @zeroLocus_open_core k _ _ ℓ _ _ _ c.Z c.g _ _ _
  have hs := generic_compactSection_support (Profinite.padicAlgClRingObj ℓ) c G.obj s
    (open_constructible ℓ k c.i G) hzero
  exact hs

private theorem adjoint_sections_refinement
    {A B C : Type*} [Category A] [Category B] [Category C]
    (Rc : C ⥤ A) (Rd : B ⥤ A) (F : C ⥤ B) (H : B ⥤ C)
    (adj : F ⊣ H) (κ : Rc ≅ F ⋙ Rd)
    (ρ : H ⋙ Rc ⟶ Rd) (hρ : ρ = restrictionComparison F H adj Rc Rd κ)
    {N Lc : C} {M Ld : B} {P G : A}
    (ηc : G ≅ Rc.obj Lc) (ηd : G ≅ Rd.obj Ld) (e : Lc ⟶ H.obj Ld)
    (hn : ηc.hom ≫ Rc.map e ≫ ρ.app Ld = ηd.hom)
    (qc : Rc.obj N ≅ P) (qd : Rd.obj M ≅ P) (qF : F.obj N ≅ M)
    (hq : qc.inv ≫ κ.hom.app N = qd.inv ≫ Rd.map qF.inv) (z : N ⟶ Lc) :
    qd.inv ≫ Rd.map (qF.inv ≫ (adj.homEquiv _ _).symm (z ≫ e)) ≫ ηd.inv =
      qc.inv ≫ Rc.map z ≫ ηc.inv := by
  have hn' : ηc.hom ≫ Rc.map e ≫ κ.hom.app (H.obj Ld) ≫
      Rd.map (adj.counit.app Ld) = ηd.hom := by
    simpa only [hρ, restrictionComparison] using hn
  have hh : Rc.map e ≫ κ.hom.app (H.obj Ld) ≫ Rd.map (adj.counit.app Ld) ≫
      ηd.inv = ηc.inv := by
    apply (cancel_epi ηc.hom).1
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun t ↦ t ≫ ηd.inv) hn'
  calc
    _ = (qd.inv ≫ Rd.map qF.inv) ≫ (F ⋙ Rd).map z ≫
        (F ⋙ Rd).map e ≫ Rd.map (adj.counit.app Ld) ≫ ηd.inv := by
      simp only [Adjunction.homEquiv_counit, Functor.map_comp, Functor.comp_map,
        Category.assoc]
    _ = (qc.inv ≫ κ.hom.app N) ≫ (F ⋙ Rd).map z ≫
        (F ⋙ Rd).map e ≫ Rd.map (adj.counit.app Ld) ≫ ηd.inv := by rw [hq]
    _ = qc.inv ≫ Rc.map z ≫ Rc.map e ≫ κ.hom.app (H.obj Ld) ≫
        Rd.map (adj.counit.app Ld) ≫ ηd.inv := by
      simp only [Category.assoc]
      rw [← κ.hom.naturality_assoc z, ← κ.hom.naturality_assoc e]
    _ = _ := by rw [hh]

private theorem heart_single_ctf (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) :
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X
        ((DerivedCategory.singleFunctor _ 0).obj G.obj) ∧
      DerivedCategory.finiteTorAmplitude _ ((DerivedCategory.singleFunctor _ 0).obj G.obj) := by
  let Λ := Profinite.padicAlgClRingObj ℓ
  refine ⟨single_constructible Λ X G.obj G.property, ?_⟩
  exact ⟨0, 0, (localizingClosure_ctf_equals_bc ℓ X Λ
    (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).2
      (Or.inr (Or.inr ⟨Iso.refl _⟩)) G.obj G.property⟩

private theorem underived_boundary_zero_of_derived
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [EnoughInjectives B] [Abelian.HasKInjectiveResolutions B]
    (J : A ⥤ B) [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (H : B ⥤ C) [H.Additive] [PreservesFiniteLimits H]
    (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (G : A)
    (hz : IsZero (T.mapDerivedCategory.obj
      (H.rightDerivedFunctor.obj
        (J.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj G))))) :
    IsZero (T.obj (H.obj (J.obj G))) := by
  let e := T.mapIso ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso H
      (J.obj G) 0 ≪≫ H.rightDerivedZeroIsoSelf.app _).symm) ≪≫
    (T.mapDerivedCategoryHomologyFunctorIso 0).app _ ≪≫
    (DerivedCategory.homologyFunctor _ 0).mapIso
      (T.mapDerivedCategory.mapIso (H.rightDerivedFunctor.mapIso
        ((Functor.mapDerivedCategorySingleFunctor J 0).app G).symm))
  exact ((DerivedCategory.homologyFunctor _ 0).map_isZero hz).of_iso e

private theorem normalized_map_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasZeroMorphisms D]
    (Jc : A ⥤ B) (Rc : B ⥤ A) (Jd : A ⥤ C) (Rd : C ⥤ A)
    (H : C ⥤ B) (T : B ⥤ D) (e : Jc ⟶ Jd ⋙ H)
    (ηc : 𝟭 A ≅ Jc ⋙ Rc) (ηd : 𝟭 A ≅ Jd ⋙ Rd) (ρ : H ⋙ Rc ≅ Rd)
    (hdet : ∀ ⦃M N : B⦄ (φ : M ⟶ N),
      IsIso (Rc.map φ) → IsIso (T.map φ) → IsIso φ) (G : A)
    (hn : ηc.hom.app G ≫ Rc.map (e.app G) ≫ ρ.hom.app (Jd.obj G) = ηd.hom.app G)
    (hzsrc : IsZero (T.obj (Jc.obj G)))
    (hztgt : IsZero (T.obj (H.obj (Jd.obj G)))) : IsIso (e.app G) := by
  apply hdet (e.app G)
  · have : IsIso (ηc.hom.app G ≫ Rc.map (e.app G) ≫ ρ.hom.app (Jd.obj G)) := by
      rw [hn]
      infer_instance
    have := IsIso.of_isIso_comp_left (ηc.hom.app G)
      (Rc.map (e.app G) ≫ ρ.hom.app (Jd.obj G))
    exact IsIso.of_isIso_comp_right _ (ρ.hom.app (Jd.obj G))
  · exact hzsrc.isIso hztgt _

private theorem heartRefinementMap_isIso_of_boundary
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hz : IsZero ((upperStar Λ c.obj.obj.i.closedComplement).obj
      ((lowerStar Λ r.hom.hom.hom).obj ((openImmersionLowerShriek Λ d.obj.obj.i).obj G)))) :
    IsIso ((heartRefinementMap Λ r).app G) := by
  have : QuasiCompact c.obj.obj.i := c.obj.property
  have hij : IsCompl (Set.range c.obj.obj.i.closedComplement.base)
      (Set.range c.obj.obj.i.base) := by
    rw [Scheme.Hom.range_closedComplement]
    exact isCompl_compl.symm
  have := openUnit_isIso Λ c.obj.obj.i
  have := openUnit_isIso Λ d.obj.obj.i
  have := heartRefinementRestriction_isIso Λ r
  exact normalized_map_isIso
    (openImmersionLowerShriek Λ c.obj.obj.i) (upperStar Λ c.obj.obj.i)
    (openImmersionLowerShriek Λ d.obj.obj.i) (upperStar Λ d.obj.obj.i)
    (lowerStar Λ r.hom.hom.hom) (upperStar Λ c.obj.obj.i.closedComplement)
    (heartRefinementMap Λ r)
    (asIso (openImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i).unit)
    (asIso (openImmersionLowerShriekUpperStarAdjunction Λ d.obj.obj.i).unit)
    (asIso (heartRefinementRestriction Λ r))
    (fun {M N} φ hj hi ↦
      (jointlyReflectIsomorphisms_upperStar_of_isCompl
      Λ c.obj.obj.i.closedComplement c.obj.obj.i hij).isIso_of_pairFunctor φ hj hi) G
    (by simpa only [asIso_hom] using heartRefinementMap_normalized Λ r G)
    (isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint
      Λ c.obj.obj.i c.obj.obj.i.closedComplement
      hij.symm.disjoint G) hz

section CachedRefinement

attribute [local instance 3000] projectionDerivedMonoidal
attribute [local instance 4000] projectionModuleAbelian projectionModuleMonoidal
  projectionModuleHasDerived
attribute [local instance 5000] projectionSheafMonoidal projectionCoefficientMonObj
  projectionModuleCategory
attribute [local instance 2000] CategoryTheory.scalarTensor4 CategoryTheory.scalarTensor12
  CategoryTheory.scalarTensor23 CategoryTheory.scalarTensorColimits
  CategoryTheory.scalarFlipTensorColimits
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct upperStarFromPoint
attribute [local instance 2000] CategoryTheory.Mod.hasFunctorialFlatResolution
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf

set_option backward.defeqAttrib.useBackward true

set_option maxHeartbeats 1000000 in
-- Comparing the derived and underived coefficient-module structures needs extra reduction.
private theorem heartRefinementMap_isIso
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification.BoundaryCompactification f}
    (hd : IsSchemeTheoreticallyDominant d.obj.obj.i) (r : d ⟶ c)
    (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) :
    IsIso ((heartRefinementMap (Profinite.padicAlgClRingObj ℓ) r).app G.obj) := by
  have : QuasiCompact c.obj.obj.i := c.obj.property
  have : QuasiCompact d.obj.obj.i := d.obj.property
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have hK := heart_single_ctf ℓ X G
  have hz := boundaryVanishing_of_dense (Profinite.padicAlgClRingObj ℓ) ℓ k
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))
      (X := X) (Y := Y) f hd r ((DerivedCategory.singleFunctor _ 0).obj G.obj) hK
  have hztgt := underived_boundary_zero_of_derived
    (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) d.obj.obj.i)
    (lowerStar (Profinite.padicAlgClRingObj ℓ) r.hom.hom.hom)
    (upperStar (Profinite.padicAlgClRingObj ℓ) c.obj.obj.i.closedComplement) G.obj hz
  have hi := heartRefinementMap_isIso_of_boundary (Profinite.padicAlgClRingObj ℓ) r G.obj hztgt
  exact hi

end CachedRefinement

private def whiskerSectionsIso
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (I : A ⥤ B) (Jc : B ⥤ C) (Jd : B ⥤ D) (H : D ⥤ C)
    (Sc : C ⥤ E) (Sd : D ⥤ E) (t : Jc ⟶ Jd ⋙ H)
    (ht : ∀ G, IsIso (t.app (I.obj G))) (P : H ⋙ Sc ≅ Sd) :
    I ⋙ Jc ⋙ Sc ≅ I ⋙ Jd ⋙ Sd := by
  let comparison := Functor.whiskerLeft I t
  have (G : A) : IsIso (comparison.app G) := ht G
  have : IsIso comparison := NatIso.isIso_of_isIso_app comparison
  exact Functor.isoWhiskerRight (asIso comparison) Sc ≪≫
    Functor.isoWhiskerLeft (I ⋙ Jd) P

private theorem whiskerSectionsIso_hom_app
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (I : A ⥤ B) (Jc : B ⥤ C) (Jd : B ⥤ D) (H : D ⥤ C)
    (Sc : C ⥤ E) (Sd : D ⥤ E) (t : Jc ⟶ Jd ⋙ H)
    (ht : ∀ G, IsIso (t.app (I.obj G))) (P : H ⋙ Sc ≅ Sd) (G : A) :
    (whiskerSectionsIso I Jc Jd H Sc Sd t ht P).hom.app G =
      Sc.map (t.app (I.obj G)) ≫ P.hom.app (Jd.obj (I.obj G)) := by
  rfl

set_option maxHeartbeats 1000000 in
-- Specializing the section comparison traverses the concrete coefficient-module structures.
set_option backward.defeqAttrib.useBackward true in
private def heartRefinementSectionsIso
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification.BoundaryCompactification f}
    (hd : IsSchemeTheoreticallyDominant d.obj.obj.i) (r : d ⟶ c) :
    condensedCompactificationSections ℓ c.obj.obj ≅
      condensedCompactificationSections ℓ d.obj.obj := by
  exact whiskerSectionsIso
    (ObjectProperty.ι (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X))
    (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) c.obj.obj.i)
    (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) d.obj.obj.i)
    (lowerStar (Profinite.padicAlgClRingObj ℓ) r.hom.hom.hom)
    (condensedCoefficientSections ℓ c.obj.obj.Z) (condensedCoefficientSections ℓ d.obj.obj.Z)
    (heartRefinementMap (Profinite.padicAlgClRingObj ℓ) r)
    (heartRefinementMap_isIso ℓ k f hd r)
    (pushforwardSectionsIso ℓ r.hom.hom.hom)

private theorem heartRefinementSectionsIso_apply
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification.BoundaryCompactification f}
    (hd : IsSchemeTheoreticallyDominant d.obj.obj.i) (r : d ⟶ c)
    (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
    (z : (condensedCompactificationSections ℓ c.obj.obj).obj G) :
    ((heartRefinementSectionsIso ℓ k f hd r).hom.app G) z =
      (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) r.hom.hom.hom).inv ≫
        ((upperStarLowerStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) r.hom.hom.hom).homEquiv _ _).symm
          (z ≫ (heartRefinementMap (Profinite.padicAlgClRingObj ℓ) r).app G.obj) := by
  simp only [heartRefinementSectionsIso, whiskerSectionsIso_hom_app, ModuleCat.comp_apply]
  rfl

private theorem heartRefinementSectionsIso_normalized
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification.BoundaryCompactification f}
    (hd : IsSchemeTheoreticallyDominant d.obj.obj.i) (r : d ⟶ c)
    [IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) c.obj.obj.i).unit]
    [IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) d.obj.obj.i).unit]
    (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
    (z : (condensedCompactificationSections ℓ c.obj.obj).obj G) :
    ((openSectionRestriction ℓ d.obj.obj.i).app G.obj)
        (((heartRefinementSectionsIso ℓ k f hd r).hom.app G) z) =
      ((openSectionRestriction ℓ c.obj.obj.i).app G.obj) z := by
  have h := adjoint_sections_refinement
    (upperStar (Profinite.padicAlgClRingObj ℓ) c.obj.obj.i)
      (upperStar (Profinite.padicAlgClRingObj ℓ) d.obj.obj.i)
    (upperStar (Profinite.padicAlgClRingObj ℓ) r.hom.hom.hom)
      (lowerStar (Profinite.padicAlgClRingObj ℓ) r.hom.hom.hom)
    (upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) r.hom.hom.hom)
    (eqToIso (congrArg (upperStar (Profinite.padicAlgClRingObj ℓ)) r.hom.hom.i_hom.symm) ≪≫
      upperStarComp (Profinite.padicAlgClRingObj ℓ) d.obj.obj.i r.hom.hom.hom)
    (heartRefinementRestriction (Profinite.padicAlgClRingObj ℓ) r) rfl
    (asIso ((openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) c.obj.obj.i).unit.app G.obj))
    (asIso ((openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) d.obj.obj.i).unit.app G.obj))
    ((heartRefinementMap (Profinite.padicAlgClRingObj ℓ) r).app G.obj)
    (by simpa only [asIso_hom] using
      heartRefinementMap_normalized (Profinite.padicAlgClRingObj ℓ) r G.obj)
    (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) c.obj.obj.i)
      (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) d.obj.obj.i)
    (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) r.hom.hom.hom)
    (regularIso_comp_eq (Profinite.padicAlgClRingObj ℓ) d.obj.obj.i r.hom.hom.hom
      c.obj.obj.i r.hom.hom.i_hom) z
  rw [openSectionRestriction_eval, heartRefinementSectionsIso_apply,
    openSectionRestriction_eval]
  simpa only [condensedSectionRestriction, Category.assoc, asIso_inv] using h

private theorem conjugated_transformation_injective
    {C : Type*} [Category C] {R : Type*} [Ring R]
    {F F' H H' : C ⥤ ModuleCat R}
    (β : F ≅ F') (δ : H ≅ H') (t : H' ⟶ F')
    (ht : ∀ G, Function.Injective (t.app G)) (G : C) :
    Function.Injective ((δ.hom ≫ t ≫ β.inv).app G) := by
  exact (ConcreteCategory.bijective_of_isIso (β.inv.app G)).1.comp
    ((ht G).comp (ConcreteCategory.bijective_of_isIso (δ.hom.app G)).1)

private theorem comparison_trans_symm_cancel
    {C : Type*} [Category C] {A B C' D : C}
    (δ : A ≅ B) (E₀ : B ≅ D) (E : C' ≅ D) :
    (δ ≪≫ E₀ ≪≫ E.symm).hom ≫ E.hom = δ.hom ≫ E₀.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem exists_dense_common_boundary
    {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₀ c : Compactification.BoundaryCompactification f) :
    ∃ d : Compactification.BoundaryCompactification f,
      IsSchemeTheoreticallyDominant d.obj.obj.i ∧ Nonempty (d ⟶ c₀) ∧ Nonempty (d ⟶ c) := by
  rcases Compactification.exists_common_dense_refinement.{u, 0} f c₀.obj.obj c.obj.obj with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hfamily⟩
  let family : Bool → Compactification f
    | false => c₀.obj.obj
    | true => c.obj.obj
  obtain ⟨e, hd, he⟩ := hfamily Bool family
  obtain ⟨p₀, hj₀, hS₀, hb₀⟩ := he false
  obtain ⟨p, hj, hS, hb⟩ := he true
  let d : Compactification.BoundaryCompactification f :=
    ⟨⟨e, e.quasiCompact_openImmersion inferInstance⟩⟩
  refine ⟨d, hd, ⟨?_⟩, ⟨?_⟩⟩
  · exact ⟨ObjectProperty.homMk ⟨p₀, hj₀, hS₀⟩, hb₀⟩
  · exact ⟨ObjectProperty.homMk ⟨p, hj, hS⟩, hb⟩

private theorem common_refinement_sections_comparison
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₀ c d : Compactification.BoundaryCompactification f}
    (hd : IsSchemeTheoreticallyDominant d.obj.obj.i) (r₀ : d ⟶ c₀) (r : d ⟶ c)
    [IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) c₀.obj.obj.i).unit]
    [IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) c.obj.obj.i).unit] :
    ∃ e : condensedCompactificationSections ℓ c₀.obj.obj ≅
        condensedCompactificationSections ℓ c.obj.obj,
      ∀ (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        (z : (condensedCompactificationSections ℓ c₀.obj.obj).obj G),
        ((openSectionRestriction ℓ c.obj.obj.i).app G.obj) ((e.hom.app G) z) =
          ((openSectionRestriction ℓ c₀.obj.obj.i).app G.obj) z := by
  let E₀ := heartRefinementSectionsIso ℓ k f hd r₀
  let E := heartRefinementSectionsIso ℓ k f hd r
  let e := E₀ ≪≫ E.symm
  refine ⟨e, ?_⟩
  intro G z
  have := openUnit_isIso (Profinite.padicAlgClRingObj ℓ) d.obj.obj.i
  have hE : (E.hom.app G) ((e.hom.app G) z) = (E₀.hom.app G) z := by
    have h := congrArg (fun τ ↦ (τ.app G) z)
      (comparison_trans_symm_cancel (Iso.refl _) E₀ E)
    simpa only [Iso.refl_trans, Iso.refl_hom, Category.id_comp,
      e, NatTrans.comp_app, ModuleCat.comp_apply] using h
  rw [← heartRefinementSectionsIso_normalized ℓ k f hd r G ((e.hom.app G) z), hE]
  exact heartRefinementSectionsIso_normalized ℓ k f hd r₀ G z

private theorem boundary_pair_elim
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (P : Compactification f → Compactification f → Prop)
    (h : ∀ c₀ c : Compactification.BoundaryCompactification f, P c₀.obj.obj c.obj.obj)
    (c₀ c : Compactification f) : P c₀ c :=
  h ⟨⟨c₀, c₀.quasiCompact_openImmersion inferInstance⟩⟩
    ⟨⟨c, c.quasiCompact_openImmersion inferInstance⟩⟩

private def sectionComparisonProperty
    (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c₀ c : Compactification f) : Prop :=
  ∀ [IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) c₀.i).unit]
    [IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) c.i).unit],
    ∃ e : condensedCompactificationSections ℓ c₀ ≅ condensedCompactificationSections ℓ c,
      ∀ (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        (z : (condensedCompactificationSections ℓ c₀).obj G),
        ((openSectionRestriction ℓ c.i).app G.obj) ((e.hom.app G) z) =
          ((openSectionRestriction ℓ c₀.i).app G.obj) z

private theorem compactification_sections_comparison
    (k : Type u) [Field k]
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (c₀ c : Compactification (X ↘ Spec (.of k)))
    [IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) c₀.i).unit]
    [IsIso (openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) c.i).unit] :
    ∃ e : condensedCompactificationSections ℓ c₀ ≅ condensedCompactificationSections ℓ c,
      ∀ (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        (z : (condensedCompactificationSections ℓ c₀).obj G),
        ((openSectionRestriction ℓ c.i).app G.obj) ((e.hom.app G) z) =
          ((openSectionRestriction ℓ c₀.i).app G.obj) z := by
  have hall : sectionComparisonProperty ℓ c₀ c := by
    refine boundary_pair_elim (X ↘ Spec (.of k)) (sectionComparisonProperty ℓ) ?_ c₀ c
    intro b₀ b
    unfold sectionComparisonProperty
    intro h₀ h
    obtain ⟨d, hd, ⟨r₀⟩, ⟨r⟩⟩ := exists_dense_common_boundary (X ↘ Spec (.of k)) b₀ b
    exact common_refinement_sections_comparison ℓ k (X ↘ Spec (.of k)) hd r₀ r
  exact hall

/-- The compact-support comparison in degree zero is natural, coefficient-linear and
injective, every image section has proper closed support, and every compactification
realizes it as restriction from extension by zero.

Source: latest blueprint, sk-l-dl-a1-endpoints.proof.md, first two sentences
(blueprint: lem-a1-condensed-degree-zero-proper-support).

Proof:
1. For the chosen compactification c₀ with open immersion h, the degree-zero normalization
   H^0(Rf_*(G[0])) ≅ f_*G of the right-derived functor, followed by the pushforward/pullback
   adjunction on maps out of the regular module, identifies ordinary H^0 with Gamma(X,G).
   After the exact single comparison for h_!, the same normalization for the proper map
   identifies H_c^0 with Gamma(Xbar,h_!G). Constant scalars commute with pullback by
   monoidality of the from-point compositor, so both identifications are linear natural
   isomorphisms with exactly the stated component formulae.
2. Restriction of sections pulls back the map from the regular module along h, identifies
   the pulled-back regular module, and applies the inverse of the unit G → h^*h_!G, which is
   invertible because h_! is fully faithful. Conjugating it by the two identifications
   defines alpha; cancellation gives its normalization.
3. Injectivity: if a map s into h_!G restricts to zero on X, the image of s restricts to
   zero on X (pullback is exact) and on the closed boundary (h_!G restricts to zero there,
   by disjoint vanishing), so open/closed detection makes the image, hence s, zero.
4. Proper support: h_!G is constructible (open extension of constructible modules). The
   lisse-source zero-locus theorem, applied to the section map from the rank-one regular
   module, gives an open zero locus W containing the boundary, because every geometric
   point of the boundary kills h_!G. Its closed complement lies in X; the reduced induced
   closed subscheme of its preimage S is identified with the lift of that of the complement,
   so it is proper over k. Pullback composition gives vanishing on X minus S.
5. Every compactification: for a refinement r : d → c, the open-restriction mate of the
   pullback compositor and the proper counit is invertible (Cartesian open-restriction
   counit). Its adjoint j_!G → r_*j'_!G restricts to the identity on X; when d is dense,
   the boundary-vanishing lemma of the cocycle proof, applied to G[0] (bounded constructible
   and of Tor amplitude [0,0] by the field-coefficient theorem), makes its closed restriction
   invertible, so open/closed detection makes it an isomorphism. On sections it preserves
   restriction to X. A common dense refinement of c₀ and an arbitrary c compares their
   section functors compatibly with restriction; composing with step 1 gives the last clause.
-/
theorem condensed_degree_zero_proper_support
    (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] (c₀ : Compactification (X ↘ Spec (.of k))) :
    ∃ β : condensedHeartOrdinaryZero ℓ (X ↘ Spec (.of k)) ≅ condensedHeartSections ℓ X,
      (∀ (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        (z : (condensedHeartOrdinaryZero ℓ (X ↘ Spec (.of k))).obj G),
        (β.hom.app G) z =
          (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) (X ↘ Spec (.of k))).inv ≫
            ((upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
              (X ↘ Spec (.of k))).homEquiv _ _).symm ((condensedOrdinaryPointZeroIso ℓ
                (X ↘ Spec (.of k)) G.obj).hom z)) ∧
      ∃ α : condensedHeartCompactZero ℓ c₀ ⟶ condensedHeartOrdinaryZero ℓ
          (X ↘ Spec (.of k)),
        (∀ G, Function.Injective (α.app G)) ∧
        (∀ (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
          (z : (condensedHeartCompactZero ℓ c₀).obj G),
          condensedSectionRestriction ℓ c₀.i
              ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) c₀.i).obj G.obj)
              ((upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) c₀.g).inv ≫
                ((upperStarLowerStarAdjunction
                  (Profinite.padicAlgClRingObj ℓ) c₀.g).homEquiv _ _).symm
                  ((condensedCompactPointZeroIso ℓ c₀ G.obj).hom z)) =
            (β.hom.app G) ((α.app G) z) ≫
              (openImmersionLowerShriekUpperStarAdjunction
                (Profinite.padicAlgClRingObj ℓ) c₀.i).unit.app G.obj) ∧
        (∀ (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
          (z : (condensedHeartCompactZero ℓ c₀).obj G),
          ∃ S : TopologicalSpace.Closeds X,
            IsProper ((Scheme.IdealSheafData.vanishingIdeal S).subschemeι ≫
              (X ↘ Spec (.of k))) ∧
            condensedSectionRestriction ℓ (Scheme.Opens.ι S.compl) G.obj
              ((β.hom.app G) ((α.app G) z)) = 0) ∧
        (∀ c : Compactification (X ↘ Spec (.of k)),
          ∃ e : condensedHeartCompactZero ℓ c₀ ≅ condensedCompactificationSections ℓ c,
            (∀ (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
              (z : (condensedHeartCompactZero ℓ c₀).obj G),
              condensedSectionRestriction ℓ c.i
                  ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) c.i).obj G.obj)
                  ((e.hom.app G) z) =
                (β.hom.app G) ((α.app G) z) ≫
                  (openImmersionLowerShriekUpperStarAdjunction
                    (Profinite.padicAlgClRingObj ℓ) c.i).unit.app G.obj)) := by
  have : QuasiCompact c₀.i := c₀.quasiCompact_openImmersion inferInstance
  have := openUnit_isIso (Profinite.padicAlgClRingObj ℓ) c₀.i
  let β := ordinaryZeroSectionsIso ℓ (X ↘ Spec (.of k))
  let δ := compactZeroSectionsIso ℓ c₀
  let R := Functor.whiskerLeft
    (ObjectProperty.ι (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X))
    (openSectionRestriction ℓ c₀.i)
  let α := δ.hom ≫ R ≫ β.inv
  have ha (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      (z : (condensedHeartCompactZero ℓ c₀).obj G) :
      (β.hom.app G) ((α.app G) z) =
        ((openSectionRestriction ℓ c₀.i).app G.obj) ((δ.hom.app G) z) := by
    change (β.inv.app G ≫ β.hom.app G) (R.app G ((δ.hom.app G) z)) = _
    simp [R]
  have hδ (G : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      (z : (condensedHeartCompactZero ℓ c₀).obj G) :
      (δ.hom.app G) z =
        (upperStarObjRegularIso (Profinite.padicAlgClRingObj ℓ) c₀.g).inv ≫
          ((upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) c₀.g).homEquiv
            _ _).symm ((condensedCompactPointZeroIso ℓ c₀ G.obj).hom z) := by
    exact compactZeroSectionsIso_eval ℓ c₀ G z
  refine ⟨β, ?_, α, ?_, ?_, ?_, ?_⟩
  · intro G z
    exact ordinaryZeroSectionsIso_eval ℓ (X ↘ Spec (.of k)) G z
  · intro G
    exact conjugated_transformation_injective β δ R
      (fun G ↦ by
        simpa only [R, Functor.whiskerLeft_app, condensedCompactificationSections,
          condensedHeartSections, Functor.comp_obj, ObjectProperty.ι_obj] using
          openSectionRestriction_injective ℓ c₀.i G.obj) G
  · intro G z
    rw [ha, ← hδ G z]
    change condensedSectionRestriction ℓ c₀.i _ ((δ.hom.app G) z) =
      (condensedSectionRestriction ℓ c₀.i _ ((δ.hom.app G) z) ≫
        inv ((openImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) c₀.i).unit.app G.obj)) ≫
        (openImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) c₀.i).unit.app G.obj
    simp
  · intro G z
    rw [ha]
    exact compactSection_proper_support k ℓ X c₀ G ((δ.hom.app G) z)
  · intro c
    have := openUnit_isIso (Profinite.padicAlgClRingObj ℓ) c.i
    obtain ⟨E, hE⟩ := compactification_sections_comparison k ℓ X c₀ c
    refine ⟨δ ≪≫ E, ?_⟩
    intro G z
    rw [ha]
    have hn := hE G ((δ.hom.app G) z)
    rw [openSectionRestriction_eval] at hn
    simpa only [Iso.trans_hom, NatTrans.comp_app, ModuleCat.comp_apply] using
      (IsIso.comp_inv_eq ((openImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) c.i).unit.app G.obj)).mp hn

end AlgebraicGeometry.ProEtale.CondensedRing
