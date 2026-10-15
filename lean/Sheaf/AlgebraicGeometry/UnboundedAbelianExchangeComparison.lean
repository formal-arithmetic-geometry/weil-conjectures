/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison

/-!
# Unbounded exchange and forgetting module coefficients

Source: Stacks Project, Tags 0D6J(3), 0D6E and 07A7
(blueprint: lem-kun-unbounded-abelian-exchange-comparison).

The inverse-image comparison is descended termwise. Its derived adjunction mate gives
an actual canonical direct-image comparison; the theorem asserts its invertibility and
its normalization by the right-derived units. This normalization identifies it with
0D6J's K-injective replacement construction, without preservation of K-injectives.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The termwise inverse-image coefficient comparison, transported to exact inverse image.
Source: Stacks Project, Tags 03D3 and 07A7
(blueprint: lem-kun-unbounded-abelian-exchange-comparison). -/
noncomputable def moduleAbelianUnboundedUpperStarIso
    (Λ : Type (u + 1)) [CommRing Λ] {A B : Scheme.{u}} (v : A ⟶ B) :
    D((v)^*[ModuleCat.{u + 1} Λ]) ⋙ D(moduleAbelianForget Λ A) ≅
      D(moduleAbelianForget Λ B) ⋙ D((v)^*[AddCommGrpCat.{u + 1}]) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleAbelianUpperStarIso Λ v).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The adjunction mate of the termwise inverse-image comparison. Its right-derived-unit
normalization below identifies it with the map computed by a module K-injective complex
and an abelian K-injective replacement of its underlying complex.
Source: Stacks Project, Tags 0D6J(3) and 07A7
(blueprint: lem-kun-unbounded-abelian-exchange-comparison). -/
noncomputable def moduleAbelianUnboundedLowerStarComparison
    (Λ : Type (u + 1)) [CommRing Λ] {A B : Scheme.{u}} (v : A ⟶ B) :
    R((v)_*[ModuleCat.{u + 1} Λ]) ⋙ D(moduleAbelianForget Λ B) ⟶
      D(moduleAbelianForget Λ A) ⋙ R((v)_*[AddCommGrpCat.{u + 1}]) :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v)
    (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v)
    (TwoSquare.mk _ _ _ _ (moduleAbelianUnboundedUpperStarIso Λ v).inv)).natTrans

/-- Exact conservative coefficient forgetting intertwines canonical unbounded exchange.
The unit equation is stated on every homotopy complex: on a K-injective module complex
`I`, apply it and naturality of the abelian derived unit to a quasi-isomorphism `UI → J`
with `J` abelian K-injective. Both derived units at K-injectives are invertible, so the
equation says exactly that the comparison is the class of `v_* UI → v_* J`.

Source: Stacks Project, Tags 0D6J(3), 0D6E and 07A7
(blueprint: lem-kun-unbounded-abelian-exchange-comparison).

Proof:
1. Forgetting preserves kernels and sheafified cokernels. The inverse of a bijective
module map is linear. Exact-functor localization and its homology comparison imply
exactness and reflection of isomorphisms on unbounded derived categories.
2. Descend the ordinary inverse-image coefficient comparison termwise. Its square
coherence follows degree by degree and survives localization.
3. Factor the ringed-topos morphism through the coefficient-forgetting morphism in
both orders. The derived pushforward composition theorem (0D6E) gives invertibility
of the resolution-normalized comparison (0D6J), and its displayed unit equation.
4. The derived adjoint-square comparison identifies this normalized comparison with
the mate defined above and gives the compatible derived units and counits.
5. Transpose the two sides of the exchange equation under the abelian f'-adjunction.
Expand exchange as the mate of the square comparison followed by g'^* of the counit.
Use step 4 for f and f', naturality of the inverse-image comparisons, and the square
coherence from step 2. Both transposes become the square comparison followed by the
forgotten counit and the source comparison. Injectivity of the adjunction bijection
gives the equality. The two endpoint composites are isomorphisms by steps 2 and 3.
-/
theorem unbounded_abelian_exchange_comparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    (∀ T : Scheme.{u},
      PreservesFiniteLimits (moduleAbelianForget Λ T) ∧
      PreservesFiniteColimits (moduleAbelianForget Λ T) ∧
      (D(moduleAbelianForget Λ T)).IsTriangulated ∧
      (D(moduleAbelianForget Λ T)).ReflectsIsomorphisms ∧
      ∀ i : ℤ, Nonempty
        (D(moduleAbelianForget Λ T) ⋙
            DerivedCategory.homologyFunctor
              (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) i ≅
          DerivedCategory.homologyFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i ⋙
            moduleAbelianForget Λ T)) ∧
    (∀ {A B : Scheme.{u}} (v : A ⟶ B),
      IsIso (moduleAbelianUnboundedLowerStarComparison Λ v) ∧
      ∀ P : HomotopyCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))
          (ComplexShape.up ℤ),
        (moduleAbelianForget Λ B).mapDerivedCategoryFactorsh.inv.app
            (((v)_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (ComplexShape.up ℤ) |>.obj P) ≫
          D(moduleAbelianForget Λ B).map
            (((v)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorUnit.app P) ≫
          (moduleAbelianUnboundedLowerStarComparison Λ v).app
            (DerivedCategory.Qh.obj P) =
        ((v)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorUnit.app
            ((moduleAbelianForget Λ A).mapHomotopyCategory (ComplexShape.up ℤ) |>.obj P) ≫
          R((v)_*[AddCommGrpCat.{u + 1}]).map
            ((moduleAbelianForget Λ A).mapDerivedCategoryFactorsh.inv.app P)) ∧
    ∀ K : DerivedCategoryModule Λ X,
      D(moduleAbelianForget Λ Y').map
          ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) ≫
        (moduleAbelianUnboundedLowerStarComparison Λ f').app
          (D((g')^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R((f')_*[AddCommGrpCat.{u + 1}]).map
          ((moduleAbelianUnboundedUpperStarIso Λ g').hom.app K) =
      (moduleAbelianUnboundedUpperStarIso Λ g).hom.app
          (R((f)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
        D((g)^*[AddCommGrpCat.{u + 1}]).map
          ((moduleAbelianUnboundedLowerStarComparison Λ f).app K) ≫
        (exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
          (D(moduleAbelianForget Λ X).obj K) := by
  sorry

end AlgebraicGeometry.Etale
