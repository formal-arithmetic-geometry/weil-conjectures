/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist

/-!
# The unbounded module exchange on K-injective representatives

Source: Stacks Project, sites-cohomology.tex, Tags 0736 and 07A7; derived.tex,
Tags 070I, 070K and 0DVC. Blueprint main-20261015, sk-def-exchange, final paragraph.
(blueprint: lem-weil-pbc-derived-exchange-module-termwise).

The comparison below is the agent-formulated unbounded representative statement,
using the exact inverse-image mate of `def-kun-unbounded-exchange`.
The three auxiliary definitions spell out its canonical maps, without additional choices.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical direct-image comparison on a specified K-injective representative:
`Q(u_*I) ≅ Ru_*(QI) ≅ Ru_*K`, with the second arrow induced by `s.symm`.
Source: Stacks Project, derived.tex, Tags 070K and 070Y
(blueprint: lem-weil-pbc-derived-exchange-module-termwise). -/
noncomputable def moduleExchangeDirectImageIso
    (Λ : Type (u + 1)) [CommRing Λ] {U V : Scheme.{u}} (f : U ⟶ V)
    {K : DerivedCategoryModule Λ U}
    (I : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    [I.IsKInjective] (s : K ≅ DerivedCategory.Q.obj I) :
    DerivedCategory.Q.obj (((f)_*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex
      (.up ℤ) |>.obj I) ≅ (R((f)_*[ModuleCat.{u + 1} Λ])).obj K :=
  (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorObjQIso I).symm ≪≫
    (R((f)_*[ModuleCat.{u + 1} Λ])).mapIso s.symm

/-- The isomorphism `t = g'⁻¹(s) ≫ φ ≫ Q(j)` associated to the replacement `j`.
Source: Stacks Project, sites-cohomology.tex, Tag 07A7, and derived.tex, Tag 070I
(blueprint: lem-weil-pbc-derived-exchange-module-termwise). -/
noncomputable def moduleExchangeReplacementIso
    (Λ : Type (u + 1)) [CommRing Λ] {X' X : Scheme.{u}} (g' : X' ⟶ X)
    {K : DerivedCategoryModule Λ X}
    {I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    (s : K ≅ DerivedCategory.Q.obj I)
    {J : CochainComplex (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    (j : (((g')^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    (D((g')^*[ModuleCat.{u + 1} Λ])).obj K ≅ DerivedCategory.Q.obj J :=
  (D((g')^*[ModuleCat.{u + 1} Λ])).mapIso s ≪≫
    ((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactors.app I ≪≫
    asIso (DerivedCategory.Q.map j)

/-- The complex map `e = Ex⁰_I ≫ f'_*(j)`, using the termwise module mate.
Naturality of the sheaf mate supplies the chain-map condition in every degree.
Source: Stacks Project, sites-cohomology.tex, Tags 0736 and 07A7
(blueprint: lem-weil-pbc-derived-exchange-module-termwise). -/
noncomputable def moduleExchangeRepresentativeMap
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    {J : CochainComplex (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    (j : (((g')^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (.up ℤ)).obj I ⟶ J) :
    (((f)_*[ModuleCat.{u + 1} Λ] ⋙ (g)^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex
      (.up ℤ)).obj I ⟶
        (((f')_*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (.up ℤ)).obj J :=
  (NatTrans.mapHomologicalComplex
    (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) (.up ℤ)).app I ≫
    (((f')_*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (.up ℤ)).map j

/-- The specified unbounded module exchange is computed on any K-injective representative
and any K-injective replacement of its inverse image. The two sides are respectively
`σsrc ≫ Ex_K` and `Q(e) ≫ χ_(J,t)`, with `χ_(I,s)`, `t`, and `e` explicitly defined above.
Consequently conjugating `Q(e)` by the displayed comparison isomorphisms always yields
this fixed exchange mate. This includes bounded below injective representatives, and
requires no K-injectivity of the inverse image of `I`.

Source: Stacks Project, sites-cohomology.tex, Tags 0736 and 07A7; derived.tex,
Tags 070I, 070K, 08BJ and 0DVC; blueprint main-20261015, sk-def-exchange, final paragraph
(blueprint: lem-weil-pbc-derived-exchange-module-termwise).

Proof plan (the six steps of the node):
1. Naturality of the underived module mate makes its components a chain map. The
   termwise adjunction gives ε_(f',J) f'⁻¹(e) = j g'⁻¹(ε_(f,I)) θ⁰. Use
   prop-weil-pbc-inverse-image-modules-exact,
   lem-weil-pbc-underived-exchange-module-linear and
   lem-weil-pbc-termwise-adjunction-homotopy.
2. Direct image is additive and commutes with cones and shifts. The canonical derived
   comparison is invertible on I and J by lem-weil-pbc-kinjective-total-derived and
   prop-weil-pbc-kinjective-resolutions-exist. Exact inverse image gives φ by
   lem-weil-pbc-exact-functor-derived-functor. Localization inverts j, making t invertible.
3. By lem-weil-pbc-right-adjoint-preserves-kinjective, u_*P is K-injective. The two
   K-injective Hom bijections of lem-weil-pbc-kinjective-hom-derived and the homotopy
   adjunction compute the canonical derived transpose of γ_P Q(a) as Q(ε_P u⁻¹a) φ.
   Naturality in s gives the formula with s⁻¹ in front, with no boundedness assumption.
4. Expand def-kun-unbounded-exchange and transpose the left side. Naturality of θᴰ
   and the derived counit, followed by step 3, gives
   B = g'⁻¹(s⁻¹) (φ_I)⁻¹ Q(g'⁻¹(ε_I) θ⁰) φ_M, where M = g⁻¹f_*I.
   The termwise descent formula is clause (2) of
   lem-weil-pbc-localization-universal-property.
5. By steps 1 and 3, the transpose of the right side is
   t⁻¹ Q(j) Q(g'⁻¹(ε_I) θ⁰) φ_M. Expand t and cancel Q(j), giving B again.
   Injectivity of the adjunction Hom bijection (def-weil-pbc-adjunction-mate) proves
   the equality.
6. Both canonical comparison maps are invertible. Cancel them to obtain independence
   of every choice. Bounded below complexes of injectives are K-injective by
   prop-weil-pbc-kinjective-resolutions-exist, so that special case follows as well. -/
theorem derivedExchangeModuleTermwise
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (K : DerivedCategoryModule Λ X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    [I.IsKInjective] (s : K ≅ DerivedCategory.Q.obj I)
    (J : CochainComplex (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    [J.IsKInjective]
    (j : (((g')^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    ((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactors.inv.app
        ((((f)_*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (D((g)^*[ModuleCat.{u + 1} Λ])).map (moduleExchangeDirectImageIso Λ f I s).hom ≫
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K =
    DerivedCategory.Q.map (moduleExchangeRepresentativeMap Λ sq I j) ≫
      (moduleExchangeDirectImageIso Λ f' J (moduleExchangeReplacementIso Λ g' s j)).hom := by
  sorry

end AlgebraicGeometry.Etale
