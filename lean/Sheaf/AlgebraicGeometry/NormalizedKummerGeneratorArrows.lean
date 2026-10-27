module

public import Sheaf.AlgebraicGeometry.NormalizedKummerCohomologyArrows
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Sheaf.AlgebraicGeometry.KummerLineInclusionOver

/-! # Absolute and relative normalized generator maps
Source: blueprint Step 2 (blueprint: def-pur-normalized-kummer-generator-arrows).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The absolute generator map a -> a kappa(w), computed by H0 of its shifted class.
Source: blueprint Step 2 (blueprint: def-pur-normalized-kummer-generator-arrows). -/
@[irreducible]
def normalizedKummerGeneratorMap (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤)))
    (w : Γ(T, ⊤)ˣ) :
    ModuleCat.of A A ⟶ (cohomology (ModuleCat.{u + 1} A) T 1).obj
      ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateLine T m A hA)) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app (ModuleCat.of A A) ≫
    (DerivedCategory.homologyFunctor _ 0).map
      (normalizedKummerClassToGlobal A T (Scheme.finiteEtaleTateLine T m A hA) 1
        (normalizedKummerDerivedClass A m hA T hT w)) ≫
    ((DerivedCategory.homologyFunctor _ 0).shiftIso
      (1 : ℤ) 0 (1 : ℤ) (add_zero _)).hom.app _

/-- The same normalized Kummer generator in bounded-below derived cohomology,
transported by the canonical compatibility of total and bounded-below RΓ.
Source: blueprint Step 2 (blueprint: def-pur-normalized-kummer-generator-arrows). -/
@[irreducible]
def normalizedKummerGeneratorPlusMap (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤)))
    (w : Γ(T, ⊤)ˣ) :
    ModuleCat.of A A ⟶ (DerivedCategory.Plus.homologyFunctor _ 1).obj
      (normalizedKummerGlobal A m hA T) :=
  normalizedKummerGeneratorMap A m hA T hT w ≫
    (DerivedCategory.homologyFunctor _ 1).map
      ((Sheaf.Γ T.smallEtaleTopology
        (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusCompatibility.inv.app
          (relativeKummerLinePlus A m hA T))

/-- The relative generator is the actual Leray edge section of kappa(t).
Source: blueprint Step 2 (blueprint: def-pur-normalized-kummer-generator-arrows). -/
@[irreducible]
def normalizedKummerRelativeGenerator (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) {k : Type u} [Field k] {B : Scheme.{u}}
    (p : B ⟶ Spec (.of k)) (hT : IsUnit (m : Γ(normalizedKummerFamily p true, ⊤))) :
    kummerExchangeConstant A B ⟶
      (DerivedCategory.homologyFunctor _ 1).obj
        ((kummerExchangeLower A (normalizedKummerProjection p true)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateLine (normalizedKummerFamily p true) m A hA))) :=
  kummerExchangeEdge A (normalizedKummerProjection p true)
    ((DerivedCategory.singleFunctor _ 0).obj
      (Scheme.finiteEtaleTateLine (normalizedKummerFamily p true) m A hA)) 1
    (normalizedKummerDerivedClass A m hA _ hT
      (Units.map (pullback.fst (KummerLine.structureMap k true) p).appTop.hom.toMonoidHom
        (KummerLine.coordinateUnit k)))

/-- The actual open inclusion in the family, induced by k[t] -> k[t,t^-1].
Source: blueprint Step 2 (blueprint: def-pur-normalized-kummer-generator-arrows). -/
def normalizedKummerInclusion {k : Type u} [Field k] {B : Scheme.{u}}
    (p : B ⟶ Spec (.of k)) : normalizedKummerFamily p true ⟶ normalizedKummerFamily p false :=
  pullback.map _ _ _ _ (KummerLine.inclusion k) (𝟙 B) (𝟙 (Spec (.of k)))
    ((Category.comp_id _).trans (normalizedKummerInclusion_over k).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)


end AlgebraicGeometry.Etale
