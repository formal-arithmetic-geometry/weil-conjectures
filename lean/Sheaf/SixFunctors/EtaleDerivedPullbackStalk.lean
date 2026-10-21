module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.CategoryTheory.ExactDerivedComposition
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Derived inverse image and geometric stalks

Source: Stacks Project, `etale-cohomology.tex`, Tag 03Q1, clauses (1) and (3),
extended termwise and localized at quasi-isomorphisms.
(blueprint: lem-sf-etale-derived-pullback-stalk)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

attribute [local instance] CategoryTheory.GrothendieckTopology.Point.sheafFiber_additive

/-- The exact inverse image followed by an exact geometric module stalk is canonically
isomorphic to the stalk at the image geometric point on the unbounded derived categories.
The equation says that on every representing complex the derived isomorphism is the
localization of the degreewise canonical inverse-image stalk comparison. Its components
are morphisms of `A`-modules, hence additive and `A`-linear; the complex isomorphism and
its naturality encode compatibility with differentials and all morphisms of complexes.

Source: Stacks Project, Tag 03Q1, `lemma-stalk-pullback` (1), (3); Tag 015F,
`lemma-right-derived-exact-functor`; Tag 04VG, `lemma-properties-left-localization`.
(blueprint: lem-sf-etale-derived-pullback-stalk)

Proof:
1. The inverse-image module exactness theorem identifies the underlying abelian inverse
image and transports the constant-ring action. The inverse-image stalk-germ comparison
is natural in modules. Apply naturality to multiplication by each scalar: it is therefore
`A`-linear. This is the canonical `upperStarCompSheafFiberIso` for module coefficients.
2. Apply this comparison degreewise. Naturality for each differential makes it a chain
isomorphism; naturality for each component of a chain map gives naturality on complexes.
3. Inverse image and the two stalks are additive and exact. The constant-complex stalk
exactness lemma and exact-functor derived factorization show their termwise functors
preserve quasi-isomorphisms, including for unbounded complexes.
4. Descend the chain isomorphism by `Localization.liftNatIso`, as in the exact-derived
natural-isomorphism lemma, and compose with the inverse of the normalized exact-derived
composition isomorphism. The two localization normalizations give precisely the equation
below. Naturality holds on the entire derived category by localization. No boundedness,
finiteness, flatness, or other condition on the scheme morphism is used. -/
theorem exists_etaleDerivedPullbackStalkIso
    (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}} (f : U ⟶ T)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ U) :
    ∃ α : (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
        (pointSmallEtale v).sheafFiber.mapDerivedCategory ≅
          (pointSmallEtale (v ≫ f)).sheafFiber.mapDerivedCategory,
      ∀ C : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
        α.hom.app (_root_.DerivedCategory.Q.obj C) ≫
            (pointSmallEtale (v ≫ f)).sheafFiber.mapDerivedCategoryFactors.hom.app C =
          (pointSmallEtale v).sheafFiber.mapDerivedCategory.map
              ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactors.hom.app C) ≫
            (pointSmallEtale v).sheafFiber.mapDerivedCategoryFactors.hom.app
              (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj C) ≫
            _root_.DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso
                (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f v)
                (ComplexShape.up ℤ)).hom.app C) := by
  sorry

end AlgebraicGeometry.Etale
