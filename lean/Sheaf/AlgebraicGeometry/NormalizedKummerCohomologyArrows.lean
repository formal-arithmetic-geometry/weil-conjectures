module

public import Sheaf.AlgebraicGeometry.NormalizedKummerGlobalArrows
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase

/-! # The actual global Kummer classes and their generator maps
Source: Stacks Project, Tags 03PL and 072W; blueprint relative Kummer computation,
Step 2 (blueprint: def-pur-normalized-kummer-cohomology-arrows).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The unique module-derived realization of the ordinary scalar-extended boundary.
Source: Stacks Tag 03PL (blueprint: def-pur-normalized-kummer-cohomology-arrows). -/
@[irreducible]
def normalizedKummerDerivedClass (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤)))
    (w : Γ(T, ⊤)ˣ) :
    (DerivedCategory.singleFunctor _ 0).obj (kummerExchangeConstant A T) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateLine T m A hA))⟦(1 : ℤ)⟧ :=
  (Equiv.ofBijective (ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T m A hA) 1)
    (ordinaryFiniteClass_bijective_arbitraryBase A T
      (Scheme.finiteEtaleTateLine T m A hA) 1)).symm
        (relativeKummerClass A m hA T hT w)

/-- The constant-sheaf derived adjunction realizes a global module class in RΓ.
Source: Stacks Tag 072W (blueprint: def-pur-normalized-kummer-cohomology-arrows). -/
@[irreducible]
def normalizedKummerClassToGlobal (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ)
    (x : (DerivedCategory.singleFunctor _ 0).obj (kummerExchangeConstant A T) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of A A) ⟶
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} A) T).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))⟦(q : ℤ)⟧ :=
  ((constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)).derivedAdjunction.homEquiv
    ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of A A)) _)
      ((constantSheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} A)).leftDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫
        ((constantSheaf T.smallEtaleTopology
          (ModuleCat.{u + 1} A)).mapDerivedCategorySingleFunctor 0).hom.app _ ≫ x) ≫
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} A) T).commShiftIso (q : ℤ)).hom.app _

end AlgebraicGeometry.Etale
