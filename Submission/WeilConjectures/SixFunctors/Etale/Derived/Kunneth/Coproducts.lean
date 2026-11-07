/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleCoyoneda
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Preadditive.LiftToFinset
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimensionDefs
public import Submission.WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Submission.WeilConjectures.ConstructibleSheaf.GenericConstancy
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.Support
public import Submission.WeilConjectures.AlgebraicGeometry.FundamentalGroup.GeometricFiber
public import Submission.WeilConjectures.PointCount
public import Submission.WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import Submission.WeilConjectures.AlgebraicGeometry.AffineSpace.Line
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Submission.WeilConjectures.Blowup.Proper
public import Submission.WeilConjectures.Compactification.Affine
public import Submission.WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Submission.WeilConjectures.CategoryTheory.Sites.ModuleCohomologyExt
public import Submission.WeilConjectures.SixFunctors.OpenClosed.Supported
public import Submission.WeilConjectures.SixFunctors.OpenClosed.Exact
public import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import Submission.WeilConjectures.AlgebraicGeometry.Regular
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Stalk
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Submission.WeilConjectures.AlgebraicGeometry.BaseChangeDimension
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveResolution
public import Submission.WeilConjectures.AlgebraicGeometry.GroupScheme.Separated
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Submission.WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
public import Submission.WeilConjectures.Compactification.BaseChange
public import Submission.WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteOverField
public import Submission.WeilConjectures.Blowup.Complement
public import Submission.WeilConjectures.Blowup.Principalization
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import Submission.WeilConjectures.ConstructibleSheaf.OpenClosed
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDelta
public import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SymmetricProduct
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
public import Submission.WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Submission.WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Direct sums and finite cohomological dimension

For a quasi-compact quasi-separated morphism `f` of finite cohomological dimension, the derived
pushforward `Rf_*` on unbounded derived categories of étale sheaves of `Λ`-modules commutes with
direct sums, and similarly for `RΓ(X, -)` (blueprint `lem-kun-0f11`, Stacks 0F11).

The proof follows the blueprint. The higher direct images `R^q f_*` of sheaves commute with
filtered colimits (`AlgebraicGeometry.Etale.preservesFilteredColimitsOfSize_higherDirectImage`),
hence with direct sums, which are filtered colimits of finite direct sums. Then the unbounded
statement follows from the finiteness of the cohomological dimension: the coproduct of
K-injective complexes with injective components is a complex of `f_*`-acyclic objects, which
computes `Rf_*` (`CategoryTheory.Functor.preservesColimitsOfShape_rightDerivedFunctor`); this
replaces the hypercohomology spectral sequence of the blueprint.

For `RΓ(X, -)`, the classical derived functors `R^q Γ(X, -)` are identified with
`N ↦ Hom(Λ_X[0], N[0]⟦q⟧)` (`AlgebraicGeometry.Etale.shiftedHomFunctorFreeSheafFinalObjectIso`),
using the derived adjunction between the constant sheaf functor and `R⁺Γ(X, -)`; this functor
commutes with filtered colimits on a quasi-compact quasi-separated scheme
(`AlgebraicGeometry.Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject`).

## Main definitions

- `AlgebraicGeometry.Etale.constantSheafIsoFreeSheafFinalObject`: `Λ_X ≅ Λ[X]`.
- `AlgebraicGeometry.Etale.shiftedHomFunctorFreeSheafFinalObjectIso`:
  `Hom(Λ_X[0], -[0]⟦q⟧) ≅ R^q Γ(X, -)`.

## Main statements

- `AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedLowerStar` and
  `AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedGlobalSections` (`lem-kun-0f11`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The higher direct images `R^q f_*` along a quasi-compact quasi-separated morphism commute
with direct sums of étale sheaves of `Λ`-modules: direct sums are filtered colimits of finite
direct sums. -/
instance preservesColimitsOfShape_rightDerived_lowerStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (ι : Type (u + 1)) (q : ℕ) :
    PreservesColimitsOfShape (Discrete ι) (((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q) :=
  have := Etale.preservesFilteredColimitsOfSize_higherDirectImage Λ f q
  have : PreservesColimitsOfShape (Finset (Discrete ι))
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q) :=
    preservesColimitsOfShape_of_natIso
      (((f)_*[ModuleCat.{u + 1} Λ]).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
        q)
  preservesColimitsOfShape_discrete_of_preservesColimitsOfShape_finset ι _

/-- Blueprint `lem-kun-0f11`: direct sums and finite cohomological dimension.

For a quasi-compact quasi-separated morphism `f` of finite cohomological dimension,
`Rf_* : D(X_ét, Λ) ⥤ D(Y_ét, Λ)` commutes with direct sums. -/
theorem preservesCoproducts_rightDerivedLowerStar {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hf : HasFiniteCohomologicalDimensionMorphism Λ f) (ι : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete ι) (R((f)_*[ModuleCat.{u + 1} Λ])) := by
  obtain ⟨d, hd⟩ := hf
  exact ((f)_*[ModuleCat.{u + 1} Λ]).preservesColimitsOfShape_rightDerivedFunctor_of_rightDerived
    ι d.toNat (fun F q hq ↦ Functor.isZero_rightDerived_of_isZero_homology _ F q (hd F q (by lia)))
    fun n ↦ inferInstance

/-- Morphisms out of the constant sheaf `Λ` on the small étale site of `X` are morphisms out of
the free sheaf `Λ[X]` on the final object: both are the global sections of the target. -/
noncomputable def constantSheafHomEquivFreeSheafFinalObject (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) ⟶ G) ≃
      ((Etale.freeSheaf Λ X).obj (Etale.finalObject X) ⟶ G) :=
  ((constantSheafAdj _ _ (isTerminalFinalObject X)).homEquiv _ G).trans
    ((ModuleCat.selfHomAddEquiv Λ _).toEquiv.trans
      (Etale.freeSheafHomEquiv Λ (Etale.finalObject X) G).symm)

/-- `AlgebraicGeometry.Etale.constantSheafHomEquivFreeSheafFinalObject` is natural in the target. -/
lemma constantSheafHomEquivFreeSheafFinalObject_comp (X : Scheme.{u})
    {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) ⟶ G)
    (g : G ⟶ G') :
    constantSheafHomEquivFreeSheafFinalObject Λ X G' (f ≫ g) =
      constantSheafHomEquivFreeSheafFinalObject Λ X G f ≫ g := by
  refine (Etale.freeSheafHomEquiv Λ (Etale.finalObject X) G').injective ?_
  simp only [constantSheafHomEquivFreeSheafFinalObject, Equiv.trans_apply,
    Etale.freeSheafHomEquiv_comp, Adjunction.homEquiv_naturality_right]
  exact (Equiv.apply_symm_apply _ _).trans
    (congrArg (fun y ↦ (g.hom.app (Opposite.op (Etale.finalObject X))).hom y)
      (Equiv.apply_symm_apply (Etale.freeSheafHomEquiv Λ (Etale.finalObject X) G) _).symm)

/-- The constant sheaf `Λ` on the small étale site of `X` is the free sheaf `Λ[X]` on the final
object: both corepresent the global sections. -/
noncomputable def constantSheafIsoFreeSheafFinalObject (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) ≅
      (Etale.freeSheaf Λ X).obj (Etale.finalObject X) :=
  (Coyoneda.fullyFaithful.preimageIso (NatIso.ofComponents
    (fun G ↦ (constantSheafHomEquivFreeSheafFinalObject Λ X G).toIso)
    (fun g ↦ by
      ext f
      exact constantSheafHomEquivFreeSheafFinalObject_comp Λ X f g))).unop.symm

/-- Étale cohomology as shifted maps out of `Λ_X[0]`: the functor `N ↦ Hom(Λ_X[0], N[0]⟦q⟧)` is
the `q`-th right derived functor `R^q Γ(X, -)` of the global sections, followed by the forgetful
functor to abelian groups. This follows from the derived adjunction between the constant sheaf
functor and `R⁺Γ(X, -)`, and the identification `Hom(Λ[0], K⟦q⟧) ≅ H^q(K)` in `D⁺(Λ)`. -/
noncomputable def shiftedHomFunctorFreeSheafFinalObjectIso (X : Scheme.{u}) (q : ℕ) :
    Etale.shiftedHomFunctor Λ ((Etale.freeSheaf Λ X).obj (Etale.finalObject X)) q ≅
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerived q ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat :=
  have : Projective (ModuleCat.of Λ Λ) :=
    ModuleCat.projective_of_free (Module.Basis.singleton Unit Λ)
  Etale.shiftedHomFunctorMapIso Λ (constantSheafIsoFreeSheafFinalObject Λ X).symm q ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ (q : ℤ))
      (preadditiveCoyoneda.mapIso ((Functor.mapDerivedCategoryPlusSingleFunctor
          (F := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).app
            (ModuleCat.of Λ Λ)).op ≪≫
        (constantSheafΓAdj _ _).derivedPlus.preadditiveCoyonedaObjIso _) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.commShiftIso
          (F := (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorPlus)
            (q : ℤ)) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (DerivedCategory.Plus.shiftFunctorCompPreadditiveCoyonedaObjSingleFunctorZeroIso
            (ModuleCat.of Λ Λ) q)) ≪≫
    Functor.isoWhiskerRight (Functor.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
        (F := Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q)
      (preadditiveCoyoneda.obj (Opposite.op (ModuleCat.of Λ Λ))) ≪≫
    Functor.isoWhiskerLeft _ (ModuleCat.preadditiveCoyonedaObjSelfIso Λ)

/-- The higher derived functors `R^q Γ(X, -)` of the global sections on a quasi-compact
quasi-separated scheme commute with direct sums of étale sheaves of `Λ`-modules: étale cohomology
commutes with filtered colimits, and direct sums are filtered colimits of finite direct sums. -/
instance preservesColimitsOfShape_rightDerived_globalSections (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (ι : Type (u + 1)) (q : ℕ) :
    PreservesColimitsOfShape (Discrete ι)
      ((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerived q) :=
  have := Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject Λ X q
    (Finset (Discrete ι))
  have : PreservesColimitsOfShape (Finset (Discrete ι))
      ((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerived q ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat) :=
    preservesColimitsOfShape_of_natIso (shiftedHomFunctorFreeSheafFinalObjectIso Λ X q)
  have : PreservesColimitsOfShape (Finset (Discrete ι))
      ((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerived q) :=
    preservesColimitsOfShape_of_reflects_of_preserves _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat)
  preservesColimitsOfShape_discrete_of_preservesColimitsOfShape_finset ι _

/-- Blueprint `lem-kun-0f11`, part (2): for a quasi-compact quasi-separated scheme `X` of finite
cohomological dimension, `RΓ(X, -)` commutes with direct sums. -/
theorem preservesCoproducts_rightDerivedGlobalSections (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (hX : HasFiniteCohomologicalDimension Λ X)
    (ι : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete ι) (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X) := by
  obtain ⟨d, hd⟩ := hX
  exact (Sheaf.Γ X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).preservesColimitsOfShape_rightDerivedFunctor_of_rightDerived ι d.toNat
    (fun F q hq ↦ Functor.isZero_rightDerived_of_isZero_homology _ F q (hd F q (by lia)))
    fun n ↦ inferInstance

end Etale

end AlgebraicGeometry
