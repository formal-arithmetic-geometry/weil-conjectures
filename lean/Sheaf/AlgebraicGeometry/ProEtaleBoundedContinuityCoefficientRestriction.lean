/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Bounded continuity with the specified coefficient action

Source: Stacks Project, Tags 03EP and 070K; Hemo--Richarz--Scholbach,
Lemma 5.3(1), equation (5.4).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.ProEt

private theorem rightDerivedModelIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive]
    (h : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (s : K ⟶ J), J.IsKInjective ∧ QuasiIso s) :
    Nonempty (F.rightDerivedFunctor ≅ F.rightDerivedFunctorOfQuasiIsoResolutions h) := by
  have := Functor.IsRightDerivedFunctor.isLeftKanExtension F.rightDerivedFunctor
    F.rightDerivedFunctorUnit (HomotopyCategory.quasiIso A (.up ℤ))
  obtain ⟨e, _, _⟩ := F.rightDerivedFunctorOfQuasiIsoResolutions_unique h
    F.rightDerivedFunctor F.rightDerivedFunctorUnit (fun H ↦
      (F.rightDerivedFunctor.homEquivOfIsLeftKanExtension F.rightDerivedFunctorUnit H).bijective)
  exact ⟨e.symm⟩

/-- Bounded continuity is unchanged by restriction along the adjoint coefficient map.
The cocone is arbitrary, and its actual legs induce the displayed comparison.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), equation (5.4); Stacks Tags
03EP and 070K (blueprint: lem-pe-bounded-continuity-coefficient-restriction).
Proof: factor module direct image as direct image with its f_*S-action followed by
restriction along R → f_*S. Restriction leaves the underlying abelian sheaf unchanged,
so it is exact and preserves colimits, by preservation and reflection through the
faithful exact forgetful functor. Uniqueness of right derived functors and commutation
of an exact functor with homology identify the specified higher direct image with
ringHigherDirectImage followed by restriction. Apply boundedContinuityDirectImage to
the canonical colimit cocone, then transport preservation to the given colimit cocone.
Mapping its colimit property through restriction and the natural isomorphism proves
that the canonical desc for the actual legs is an isomorphism. -/
theorem boundedContinuityDirectImage_coefficients
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (R : Sheaf (topology Y) CommRingCat.{u + 1})
    (S : Sheaf (topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex (proEtaleRingModules X S) ℤ)
    (v : Cocone D) (hv : IsColimit v)
    (n : ℤ) (hD : ∀ i : I, ∀ j : ℤ, j < n → IsZero ((D.obj i).X j)) (q : ℤ) :
    IsIso (colimit.desc
      (D ⋙ DerivedCategory.Q ⋙ proEtaleRingDerivedDirectImage f R S c ⋙
        DerivedCategory.homologyFunctor _ q)
      ((DerivedCategory.Q ⋙ proEtaleRingDerivedDirectImage f R S c ⋙
        DerivedCategory.homologyFunctor _ q).mapCocone v)) := by
  let SR := (sheafCompose (topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let TR := (proEtaleSheafDirectImage f RingCat.{u + 1}).obj SR
  let RR := (sheafCompose (topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let phi : RR ⟶ TR :=
    (sheafCompose (topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (proEtaleRingDirectImageMap f R S c)
  let E := SheafOfModules.restrictScalars.{u + 1} phi
  let F := ringModuleDirectImage f SR
  let U := SheafOfModules.toSheaf.{u + 1} RR
  have hRR := moduleSheaves_colimits_forgetful.{u + 1, u, u + 1, u + 1} RR
  have hTR := moduleSheaves_colimits_forgetful.{u + 1, u, u + 1, u + 1} TR
  have : PreservesFiniteLimits U := hRR.2.1
  have : PreservesFiniteColimits U := hRR.2.2.1
  have : PreservesFiniteLimits (SheafOfModules.toSheaf.{u + 1} TR) := hTR.2.1
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} TR) := hTR.2.2.1
  have : PreservesFiniteLimits E := by
    have : PreservesFiniteLimits (E ⋙ U) :=
      inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u + 1} TR))
    have : ReflectsFiniteLimits U := reflectsFiniteLimits_of_reflectsIsomorphisms U
    exact preservesFiniteLimits_of_reflects_of_preserves E U
  have : PreservesFiniteColimits E := by
    have : PreservesFiniteColimits (E ⋙ U) :=
      inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} TR))
    have : ReflectsFiniteColimits U :=
      { reflects := fun J _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
    exact preservesFiniteColimits_of_reflects_of_preserves E U
  have : PreservesColimitsOfShape I E := by
    have : PreservesColimitsOfShape I U :=
      (hRR.2.2.2.2.2 I).2.1
    have : PreservesColimitsOfShape I (E ⋙ U) :=
      (hTR.2.2.2.2.2 I).2.1
    have : ReflectsColimitsOfShape I U := reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves E U
  let ordinary : proEtaleRingModuleDirectImage f R S c ≅ F ⋙ E :=
    NatIso.ofComponents (fun M ↦
      (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by intros; rfl)))
      (by intros; rfl)
  obtain ⟨z⟩ := rightDerivedModelIso F (ringModuleDirectImage_hasKInjectiveResolutions SR)
  let e : proEtaleRingDerivedDirectImage f R S c ⋙ DerivedCategory.homologyFunctor _ q ≅
      ringHigherDirectImage f SR q ⋙ E :=
    Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorNatIso ordinary ≪≫
        Functor.rightDerivedFunctorCompMapDerivedCategoryIso F E ≪≫
        Functor.isoWhiskerRight z E.mapDerivedCategory)
      (DerivedCategory.homologyFunctor _ q) ≪≫
    Functor.isoWhiskerLeft (ringDerivedDirectImage f SR)
      (E.mapDerivedCategoryHomologyFunctorIso q).symm
  let H := DerivedCategory.Q ⋙ ringHigherDirectImage f SR q
  have hcont := boundedContinuityDirectImage f SR D n hD q
  have : IsIso ((colimit.isColimit (D ⋙ H)).desc
      (H.mapCocone (colimit.cocone D))) := by
    change IsIso (colimit.desc (D ⋙ H) (H.mapCocone (colimit.cocone D)))
    exact hcont
  have hc : IsColimit (H.mapCocone (colimit.cocone D)) :=
    (colimit.isColimit (D ⋙ H)).ofPointIso
  have : PreservesColimit D H :=
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D) hc
  have he : IsColimit ((H ⋙ E).mapCocone v) :=
    isColimitOfPreserves E (isColimitOfPreserves H hv)
  have ht : IsColimit ((DerivedCategory.Q ⋙
      proEtaleRingDerivedDirectImage f R S c ⋙
      DerivedCategory.homologyFunctor _ q).mapCocone v) :=
    IsColimit.mapCoconeEquiv (Functor.isoWhiskerLeft DerivedCategory.Q e.symm) he
  exact ht.coconePointUniqueUpToIso (colimit.isColimit _) |>.isIso_inv

end AlgebraicGeometry.Scheme.ProEt
