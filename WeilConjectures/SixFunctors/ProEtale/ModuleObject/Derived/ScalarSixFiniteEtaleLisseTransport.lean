/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin

/-! # Pullback of finite scalar realizations on constant charts

Source: blueprint scalar-six-ctf (1), finite projective local models.
(blueprint: lem-sfb-finite-scalar-realization-constant-chart).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]
  {Λ : ScalarSixRing.{u}}
  (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj A))
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
      Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]

/-- On a constant ordinary comparison chart, the pullback of the finite scalar
realization is the single complex of the realized constant module. This comparison
requires no finiteness or projectivity of the constant module.

Source: blueprint scalar-six-ctf (1), constant-model and pullback comparisons;
Stacks 099Y and the exact-functor derived single comparison.
(blueprint: lem-sfb-finite-scalar-realization-constant-chart).

Proof: commute exact inverse image with the degree-zero single functor. The finite
discrete coefficient encoding commutes with scheme pullback; identify the specified
realization with that encoding using its normalized ring isomorphism. Apply the given
constant-chart isomorphism. Restriction along e.hom commutes with inverse image via
the coefficient-pullback comparison. Finally commute both exact coefficient functors
with singles and compose these isomorphisms. Every comparison is an isomorphism on
the whole module category, so empty charts and the zero ring cause no exception. -/
theorem finiteScalarRealizationConstantChart
    (S T : Scheme.{u}) (f : T ⟶ S)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (P : ModuleCat.{u + 1} (ULift.{u + 1} A))
    (i : (AlgebraicGeometry.ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) S).obj L) ≅
      (constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P) :
    Nonempty ((CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj
      ((sfbFiniteScalarRealization A e eR S).obj
        ((DerivedCategory.singleFunctor _ 0).obj L)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((Mod.comap (coefficientMap e.hom.hom T)).obj
          ((finiteComparisonRealization A T eR).obj
            ((constantSheaf (Scheme.ProEt.topology T)
              (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P)))) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
