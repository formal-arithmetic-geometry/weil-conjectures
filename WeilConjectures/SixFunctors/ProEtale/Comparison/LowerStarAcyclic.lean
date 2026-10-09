/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!
# Acyclicity for pro-étale direct images on the affine pro-étale basis

Let `f : U ⟶ V` be a morphism of schemes. A pro-étale sheaf `G` on `U` is acyclic for the
direct image `f_*` as soon as its higher derived sections over the pro-étale `U`-schemes
`U ×_V W` vanish, for `W` running over the affine pro-étale site of `V`
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isZero_rightDerived`): the higher
direct images are computed by `f_*` of an injective resolution, whose complex of sections over
`W` is the complex of sections over `U ×_V W` of the resolution, and exactness of a complex of
sheaves can be tested on the presheaves underlying its restriction to the affine pro-étale site.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Evaluation of pro-étale sheaves at an object of the pro-étale site. -/
noncomputable abbrev sectionsFunctor {X : Scheme.{u}} (Y : X.ProEt) :
    Sheaf (ProEt.topology X) A ⥤ A :=
  sheafToPresheaf (ProEt.topology X) A ⋙ (evaluation _ A).obj (op Y)

/-- A short complex of pro-étale sheaves is exact if the short complexes of sections over all
objects of the affine pro-étale site are exact. -/
lemma ShortComplex.exact_of_exact_sectionsFunctor {X : Scheme.{u}}
    (S : ShortComplex (Sheaf (ProEt.topology X) A))
    (h : ∀ W : X.AffineProEt,
      (S.map (sectionsFunctor A ((AffineProEt.toProEt X).obj W))).Exact) : S.Exact := by
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  let Φ := (AffineProEt.toProEt X).sheafPushforwardContinuous A (AffineProEt.topology X)
    (ProEt.topology X)
  have : Φ.Additive := ⟨rfl⟩
  have : Φ.PreservesHomology := {}
  rw [← S.exact_map_iff_of_faithful Φ]
  -- the presheaves underlying the restriction to the affine site form an exact short complex
  let T := (S.map Φ).map (sheafToPresheaf (AffineProEt.topology X) A)
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_evaluation]
    exact fun W ↦ h W.unop
  -- sheafifying it gives back the restriction, sheafification being exact
  have : (presheafToSheaf (AffineProEt.topology X) A).PreservesHomology := {}
  have hT' := hT.map (presheafToSheaf (AffineProEt.topology X) A)
  refine (ShortComplex.exact_iff_of_iso ?_).1 hT'
  exact (ShortComplex.mapNatIso (S.map Φ) (sheafificationNatIso _ _)).symm

/-- A pro-étale sheaf `G` on `U` is acyclic for the direct image along `f : U ⟶ V` if its higher
derived sections over `U ×_V W` vanish for every object `W` of the affine pro-étale site of
`V`. -/
theorem rightAcyclic_lowerStar_of_isZero_rightDerived {U V : Scheme.{u}} (f : U ⟶ V)
    (G : Sheaf (ProEt.topology U) A)
    (h : ∀ (W : V.AffineProEt) (q : ℕ), IsZero (((sectionsFunctor A
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
        ((AffineProEt.toProEt V).obj W))).rightDerived (q + 1)).obj G)) :
    (ProEtale.lowerStar A f).rightAcyclic G := by
  intro q
  let R : InjectiveResolution G := injectiveResolution G
  refine IsZero.of_iso ?_ (R.isoRightDerivedObj _ (q + 1))
  rw [HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology]
  refine ShortComplex.exact_of_exact_sectionsFunctor A _ fun W ↦ ?_
  have h' := (h W q).of_iso (R.isoRightDerivedObj _ (q + 1)).symm
  rw [HomologicalComplex.homologyFunctor_obj,
    ← HomologicalComplex.exactAt_iff_isZero_homology] at h'
  exact h'

/-- **Acyclicity of pulled-back injectives over quasi-compact quasi-separated objects.** Let
`f : U ⟶ V` be quasi-compact and quasi-separated, `I` an injective étale sheaf on `U` and `W` an
object of the affine pro-étale site of `V`. Then the higher derived sections of `ν_U^* I` over
the quasi-compact quasi-separated pro-étale `U`-scheme `U ×_V W` vanish. -/
theorem isZero_rightDerived_sectionsFunctor_comparisonUpperStar_obj {U V : Scheme.{u}}
    (f : U ⟶ V) [QuasiCompact f] [QuasiSeparated f] (I : Sheaf U.smallEtaleTopology A)
    [Injective I] (W : V.AffineProEt) (q : ℕ) :
    IsZero (((sectionsFunctor A ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
      ((AffineProEt.toProEt V).obj W))).rightDerived (q + 1)).obj
        ((comparisonUpperStar A U).obj I)) :=
  sorry

/-- For `f` quasi-compact and quasi-separated, the comparison pullback `ν_U^* I` of an injective
étale sheaf is acyclic for the pro-étale direct image `f_*`. -/
theorem rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective {U V : Scheme.{u}}
    (f : U ⟶ V) [QuasiCompact f] [QuasiSeparated f] (I : Sheaf U.smallEtaleTopology A)
    [Injective I] :
    (ProEtale.lowerStar A f).rightAcyclic ((comparisonUpperStar A U).obj I) :=
  rightAcyclic_lowerStar_of_isZero_rightDerived A f _
    (isZero_rightDerived_sectionsFunctor_comparisonUpperStar_obj A f I)

end AlgebraicGeometry.ProEtale
