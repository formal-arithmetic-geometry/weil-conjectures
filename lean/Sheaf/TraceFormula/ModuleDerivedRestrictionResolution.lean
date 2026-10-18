/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.CategoryTheory.RingedSiteModules

import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Module derived restriction on injective section complexes

Source: Stacks Project, `sites-cohomology.tex`, Tag 08J6 and `cohomology.tex`, Tags
01F8, 01F9 and 01FB (blueprint: lem-trf-module-derived-restriction-resolution).

## Main definitions and statement

* `moduleInjectiveComplex`: the existing category of module-sheaf complexes.
* `moduleInjectiveComplexPlus`: bounded-below complexes of injective objects.
* `moduleInjectiveComplexUnderlying`: forget the injective-object wrapper.
* `moduleDerivedRestrictionResolution`: restriction computed on injective section complexes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Underlying module-sheaf complex over a scheme.
Source: Stacks, sites-cohomology.tex, Tag 08J6
(blueprint: lem-trf-module-derived-restriction-resolution). -/
abbrev moduleInjectiveComplex (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :=
  CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ

/-- Bounded-below complexes whose terms are injective module sheaves.
Source: Stacks, derived.tex, Tag 070J
(blueprint: lem-trf-module-derived-restriction-resolution). -/
abbrev moduleInjectiveComplexPlus (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :=
  CochainComplex.Plus (InjectiveObject
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

/-- Forget the injective-object wrapper to the underlying complex.
Source: Stacks, derived.tex, Tag 070J
(blueprint: lem-trf-module-derived-restriction-resolution). -/
abbrev moduleInjectiveComplexUnderlying {T : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (I : moduleInjectiveComplexPlus T Λ) : moduleInjectiveComplex T Λ :=
  (((InjectiveObject.ι _).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj)

/--
For a morphism of schemes and a commutative coefficient ring, the restriction map on
unbounded derived module sections is represented by the degreewise module adjunction
unit followed by an arbitrary map from the pulled-back injective complex to an injective
complex.  The proof is the five-step K-injective, derived-adjunction and Leray
calculation from Stacks Tags 08J6, 01F8, 01F9, 01FB and 015M.
(blueprint: lem-trf-module-derived-restriction-resolution)

Proof (postponed in stage 2).

1. Work throughout in the constant-coefficient module categories, which have enough
injectives by lem-weil-pbc-module-sheaves-enough-injectives. Exact inverse image and
lem-sp-right-adjoint-preserves-injectives imply that direct image preserves injectives.
Thus I, J and u_*J are bounded-below injective complexes, hence K-injective by
lem-weil-pbc-dplus-injective-representative. The direct-image and sections comparison
units are natural and invertible on them by lem-weil-pbc-right-derived-plus-injective.
These are also the unbounded comparisons of def-kun-rgamma-unbounded: the same
K-injective models compute morphisms by lem-sf-kinjective-derived-map-computation,
using prop-weil-pbc-kinjective-resolutions-exist.

2. Put t = u_*a composed with the ordinary unit I to u_*u-inverse(I).
By lem-weil-pbc-termwise-adjunction-homotopy this is a module-linear chain map and the
homotopy-category transpose of a. By def-weil-pbc-direct-image, evaluation of u_*a at
T is evaluation of a at T'. Thus sections of t are exactly e_(u,I) followed by sections
of a, degree by degree; naturality of the unit gives compatibility with differentials.
The parameter w with hw expresses this exact chain map, rather than a chosen replacement.

3. By lem-weil-pbc-exact-functor-derived-factorization, exact inverse image commutes
with localization. Since J and u_*J are K-injective, the localization Hom bijections of
lem-weil-pbc-kinjective-hom-derived and the homotopy adjunction of
lem-weil-pbc-termwise-adjunction-homotopy send Q(a) to Q(t). Their naturality and the
unit formula of lem-weil-pbc-adjunction-of-natural-bijection identify the derived
transpose: Ru_*(Q(a)) composed with the derived unit equals delta_J composed with Q(t),
where delta_J is the direct-image resolution comparison. No inverse to a is used.

4. Normalize Leray on the same models. Choose an injective representative of any
bounded-below derived object by lem-weil-pbc-dplus-injective-representative. Its direct
image is again bounded-below injective, so the equality of module section complexes
Gamma(T,u_*J) = Gamma(T',J) computes Leray without a second replacement. Naturality and
independence follow by lifting derived maps to homotopy classes with
lem-weil-pbc-kinjective-hom-derived; direct image followed by sections gives literally
the same chain map as sections on T'. The uniqueness of
lem-weil-pbc-right-derived-plus-injective identifies this with the canonical 08J6/015M
comparison. Consequently Leray composed with Rsections(delta_J) and the sections
comparison for u_*J is the sections comparison for J.

5. The definition of restriction, naturality of Leray at Q(a), and step 3 rewrite the
left side of the node's equation as Leray followed after Rsections(delta_J) and
Rsections(Q(t)). Naturality of the sections comparison at t and step 4 reduce this to
alpha_J composed with Q(Gamma(T,t)) and alpha_I inverse. Step 2 identifies Gamma(T,t)
with w. In the displayed Lean equation, rightDerivedFunctorObjQIso.hom is alpha_I
inverse and rightDerivedFunctorObjQIso.inv is alpha_J. This proves exactly the claimed
formula, with no quasi-isomorphism assumption on a and no finiteness assumptions.
-/
theorem moduleDerivedRestrictionResolution
    {T T' : Scheme.{u}} (u : T' ⟶ T) (Λ : Type (u + 1)) [CommRing Λ]
    (I : moduleInjectiveComplexPlus T Λ) (J : moduleInjectiveComplexPlus T' Λ)
    (a : ((upperStar (ModuleCat.{u + 1} Λ) u).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (moduleInjectiveComplexUnderlying I) ⟶
      moduleInjectiveComplexUnderlying J)
    (w : ((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (moduleInjectiveComplexUnderlying I) ⟶
      ((Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (moduleInjectiveComplexUnderlying J))
    (hw : ∀ i : ℤ, w.f i =
      globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) u
          ((moduleInjectiveComplexUnderlying I).X i) ≫
        (Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map (a.f i)) :
    ((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorObjQIso
        (moduleInjectiveComplexUnderlying I)).hom ≫
      DerivedCategory.Q.map w ≫
      ((Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorObjQIso
        (moduleInjectiveComplexUnderlying J)).inv =
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).map
          ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) u).unit.app
            (DerivedCategory.Q.obj (moduleInjectiveComplexUnderlying I))) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} Λ) u).hom.app
            ((upperStar (ModuleCat.{u + 1} Λ) u).mapDerivedCategory.obj
              (DerivedCategory.Q.obj (moduleInjectiveComplexUnderlying I))) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T').map
          ((upperStar (ModuleCat.{u + 1} Λ) u).mapDerivedCategoryFactors.hom.app
              (moduleInjectiveComplexUnderlying I) ≫
            DerivedCategory.Q.map a) := by
  sorry

end AlgebraicGeometry.Etale
