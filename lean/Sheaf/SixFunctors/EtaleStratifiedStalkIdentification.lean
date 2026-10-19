module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.SixFunctors.ConnectedEtalePerfectConstant
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# Derived geometric stalk of a constant local model

Source: `literature/stacks-project/etale-cohomology.tex`, Tag 09BI
(blueprint: lem-sf-etale-stratified-stalk-identification).

The statement records that an étale-local constant complex model identifies the derived
geometric stalk with the original coefficient complex, using exact inverse image and stalk
functors.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/--
Source: Stacks Project, `etale-cohomology.tex`, Tag 09BI
(blueprint: lem-sf-etale-stratified-stalk-identification).

If the inverse image of a derived étale module complex is isomorphic to the termwise
constant sheaf complex associated to `E`, then every algebraically closed geometric stalk
identifies the derived stalk with `E`.  The isomorphism is obtained by applying the exact
stalk functor to the given isomorphism, using inverse-image/stalk composition, and then
using the canonical constant-sheaf stalk identifications degree by degree.  The argument
is unbounded and imposes no finiteness, constructibility, boundedness, or Tor-amplitude
hypothesis.
-/
theorem derivedGeometricStalkIso
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (f : U ⟶ X)
    (K : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (E : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (α : Nonempty (((Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory).obj K ≅
      _root_.DerivedCategory.Q.obj
        (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (ubar : Spec (.of Ω) ⟶ U) :
    Nonempty ((geometricStalk A (ubar ≫ f)).obj K ≅
      _root_.DerivedCategory.Q.obj E) := by
  obtain ⟨α⟩ := α
  let F := (pointSmallEtale ubar).sheafFiber (A := ModuleCat.{u + 1} A)
  have : F.Additive := (pointSmallEtale ubar).sheafFiber_additive
  let G := (pointSmallEtale (ubar ≫ f)).sheafFiber (A := ModuleCat.{u + 1} A)
  have : G.Additive := (pointSmallEtale (ubar ≫ f)).sheafFiber_additive
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget (ModuleCat.{u + 1} A)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let c := constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)
  let e : c ⋙ F ≅ 𝟭 (ModuleCat.{u + 1} A) :=
    (pointSmallEtale ubar).constantSheafCompSheafFiberIso _ _
  change Nonempty (G.mapDerivedCategory.obj K ≅ _)
  exact ⟨((Functor.mapDerivedCategoryNatIso
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f ubar)).app K).symm ≪≫
    (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} A) f) F).app K ≪≫
    F.mapDerivedCategory.mapIso α ≪≫ F.mapDerivedCategoryFactors.app _ ≪≫
    _root_.DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).app E ≪≫
        (Functor.mapHomologicalComplexIdIso (ModuleCat.{u + 1} A)
          (ComplexShape.up ℤ)).app E)⟩

end AlgebraicGeometry.Etale
