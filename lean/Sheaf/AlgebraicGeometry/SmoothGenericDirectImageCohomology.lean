module
public import Sheaf.AlgebraicGeometry.SmoothLisseRelativeDualBounded
public import Sheaf.AlgebraicGeometry.FiniteLisseFieldDual
public import Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.ULift
@[expose] public section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
/-- The bounded and lisse cohomology part of smooth generic direct image. Source:
lem-asd-smooth-generic-direct-image, construction through compact duality
(blueprint: lem-asd-smooth-generic-direct-image-cohomology). -/
theorem smooth_generic_directImage_cohomology
    (k : Type u) [Field k] (S : Scheme.{u}) [IsIntegral S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k)
    (X : Scheme.{u}) (f : X ⟶ S) [IsSeparated f] [Smooth f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (hL : Scheme.IsFiniteLocallyConstantSheaf L) :
    ∃ U : S.Opens, Nonempty U ∧
      ∀ (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme),
        IsPullback p fU f U.ι →
        (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
            ((R((fU)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
              ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj L))))) ∧
        ∀ i : ℤ, Scheme.IsFiniteLocallyConstantSheaf
          ((_root_.DerivedCategory.homologyFunctor _ i).obj
            ((R((fU)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
              ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj L)))) := by sorry
end AlgebraicGeometry.Etale
