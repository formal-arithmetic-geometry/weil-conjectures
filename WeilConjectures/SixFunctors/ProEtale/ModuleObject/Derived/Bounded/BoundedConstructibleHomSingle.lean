/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleShiftSingle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!
# Internal Hom of constructible sheaves in degree zero

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Remark 6.8.15 and
  Propositions 6.6.11 and 6.8.11(3)
* SGA 4½, Th. finitude 1.6
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

/-- Internal Hom of two constructible sheaves in degree zero is bounded constructible as soon as
the bounded constructible complexes are stable under the derived hom. -/
private theorem boundedConstructible_hom_single_of_isMonoidalClosed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [(boundedConstructible (condensedRingObj Λ X)).IsMonoidalClosed]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : IsConstructibleModuleObject (condensedRingObj Λ X) F)
    (hG : IsConstructibleModuleObject (condensedRingObj Λ X) G) :
    boundedConstructible (condensedRingObj Λ X)
      (((derivedHom Λ X).obj (op ((DerivedCategory.singleFunctor _ 0).obj F))).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)) := by
  have hsingle : ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      IsConstructibleModuleObject (condensedRingObj Λ X) M →
      boundedConstructible (condensedRingObj Λ X) ((DerivedCategory.singleFunctor _ 0).obj M) :=
    fun M hM ↦ (boundedConstructible _).prop_of_iso ((shiftFunctorZero _ ℤ).app _)
      (boundedConstructible_shift_single _ M hM 0)
  exact (boundedConstructible _).prop_ihom (hsingle F hF) (hsingle G hG)

/-- Internal Hom of two constructible `ℚ̄_ℓ`-sheaves is bounded constructible. -/
theorem boundedConstructible_hom_single
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [Fact (ringChar k ≠ ℓ)]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) F)
    (hG : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) G) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)
      (((derivedHom (Profinite.padicAlgClRingObj ℓ) X.left).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj F))).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)) :=
  boundedConstructible_hom_single_of_isMonoidalClosed _ _ F G hF hG

namespace ContinuousMapRingObj

/-- Internal Hom of two constructible `E`-sheaves is bounded constructible, for a finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
theorem boundedConstructible_hom_single
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {k : Type u} [Field k]
    [Fact (ringChar k).Prime]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [Fact (ringChar k ≠ ℓ)]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left) F)
    (hG : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left) G) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X.left)
      (((derivedHom (Profinite.continuousMapRingObj E) X.left).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj F))).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)) :=
  boundedConstructible_hom_single_of_isMonoidalClosed _ _ F G hF hG

end ContinuousMapRingObj

namespace PadicIntegersRingObj

/-- Internal Hom of two constructible `𝒪_E`-sheaves is bounded constructible, for a finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
theorem boundedConstructible_hom_single
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {k : Type u} [Field k] [Fact (ringChar k).Prime]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [Fact (ringChar k ≠ ℓ)]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) F)
    (hG : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) G) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)
      (((derivedHom (Profinite.padicIntegersRingObj ℓ E) X.left).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj F))).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)) :=
  boundedConstructible_hom_single_of_isMonoidalClosed _ _ F G hF hG

end PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
