/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackTensorComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionSuccessive
public import WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
/-- Open localization part of the general-field tools: `j_!` and `j^*` preserve bounded
constant-model constructibles and the localizing closures, and `j_! ⊣ j^*` restricts to them.
(Triangulatedness of `D(j_!)` is an instance and is not part of this statement.)
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/
sk-thm-purity-transport.proof.md, Steps 1, 6 and 7

Proof plan: apply the exact derived open calculus (lem-pod-condensed-open-derived-calculus)
for exactness, coproducts and the ambient adjunction. Transport finite constant-model stratifications across the open immersion by
adding the closed complement with zero model, and restrict stratifications from the ambient
scheme to the open. Closure under shifts, triangles and coproducts then gives the two
localizing-closure inclusions by minimality; fullness restricts the ambient adjunction.
(blueprint: lem-dla1-general-field-open-localizing-tools). -/
theorem openLocalizingTools (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [PerfectField k] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k))]
    [IsSeparated (T ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k))]
    {U : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j] :
    (∀ K, constantModelBoundedConstructible Λ U K →
        constantModelBoundedConstructible Λ T
          (D(openImmersionLowerShriek Λ j).obj K)) ∧
      (∀ K, localizingClosureProEtale Λ U K →
        localizingClosureProEtale Λ T
          (D(openImmersionLowerShriek Λ j).obj K)) ∧
      (∀ K, constantModelBoundedConstructible Λ T K →
        constantModelBoundedConstructible Λ U
          (D(upperStar Λ j).obj K)) ∧
      (∀ K, localizingClosureProEtale Λ T K →
        localizingClosureProEtale Λ U (D(upperStar Λ j).obj K)) ∧
      ∃ (hshriek : ∀ K, localizingClosureProEtale Λ T
          (((localizingClosureProEtale Λ U).ι ⋙ D(openImmersionLowerShriek Λ j)).obj K))
        (hstar : ∀ K, localizingClosureProEtale Λ U
          (((localizingClosureProEtale Λ T).ι ⋙ D(upperStar Λ j)).obj K)),
        Nonempty
          ((localizingClosureProEtale Λ T).lift
              ((localizingClosureProEtale Λ U).ι ⋙
                D(openImmersionLowerShriek Λ j)) hshriek ⊣
            (localizingClosureProEtale Λ U).lift
              ((localizingClosureProEtale Λ T).ι ⋙ D(upperStar Λ j)) hstar) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
