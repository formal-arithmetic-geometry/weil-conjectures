/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.CategoryTheory.ConstantLeftModuleTransport
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
public import Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.ProjectionMateExact
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Total-limit comparison and transposes of augmented tower arrows

Source: Stacks Project, Cohomology on Sites, Tags 0A07, 07A6 and 0940;
Derived Categories, Tags 08BJ, 070I and 09T5. The combined normalization is
an agent auxiliary (blueprint: lem-pur-tower-limit-transpose-normalization).

Positive level `n + 1` is encoded by `n : ℕ`. All categories are ordinary
unbounded module derived categories. The comparison is specified by its
common-underived-composite equation, rather than just its projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w a v x y

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantLeftModuleInverseImage

namespace CategoryTheory.TowerLimitTransposeNormalization

section Limits

variable (T : Type a) [Category.{v} T] [Abelian T] [HasLimitsOfShape ℕᵒᵖ T]

/-- The ordinary strict tower limit, with its existing Mathlib construction.
Source: Stacks 0940 (blueprint: lem-pur-tower-limit-transpose-normalization). -/
abbrev towerLimit : (ℕᵒᵖ ⥤ T) ⥤ T := lim

/-- Additivity of the existing limit functor, from preservation of binary products.
Source: Stacks 0940 (blueprint: lem-pur-tower-limit-transpose-normalization). -/
instance towerLimitAdditive : (towerLimit T).Additive :=
  Functor.additive_of_preserves_binary_products (towerLimit T)

variable [HasDerivedCategory.{w} T] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ T)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ T)]

/-- The actual derived constant/limit adjunction, derived from `constLimAdj`.
Its unit supplies the specified identification with a constant tower's total limit.
Source: Stacks 0940 and 09T5
(blueprint: lem-pur-tower-limit-transpose-normalization). -/
abbrev limitAdjunction :
    (Functor.const ℕᵒᵖ : T ⥤ (ℕᵒᵖ ⥤ T)).mapDerivedCategory ⊣
      (towerLimit T).rightDerivedFunctor :=
  (constLimAdj : (Functor.const ℕᵒᵖ : T ⥤ (ℕᵒᵖ ⥤ T)) ⊣
    towerLimit T).mapDerivedCategoryRightDerivedAdjunction


/-- On representatives the derived constant/limit unit is induced by the ordinary
cone of identity maps. On a diagonal K-injective representative all comparisons
are isomorphisms, so this is precisely the identity normalization.
Source: Stacks 0940, 08BJ, 09T5
(blueprint: lem-pur-tower-limit-transpose-normalization). -/
def ConstantUnitNormalization : Prop :=
  ∀ H : CochainComplex T ℤ, H.IsKInjective →
    (limitAdjunction T).unit.app (DerivedCategory.Q.obj H) ≫
        (towerLimit T).rightDerivedFunctor.map
          ((Functor.const ℕᵒᵖ : T ⥤ _).mapDerivedCategoryFactors.hom.app H) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (constLimAdj : (Functor.const ℕᵒᵖ : T ⥤ _) ⊣ towerLimit T).unit (.up ℤ)).app H) ≫
        UnboundedExactTower.cochainUnit (towerLimit T)
          (((Functor.const ℕᵒᵖ : T ⥤ _).mapHomologicalComplex (.up ℤ)).obj H)

end Limits

section Coefficients

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type u} [CommRing A]
  [HasWeakSheafify J RingCat.{u}] [HasWeakSheafify K RingCat.{u}]
  {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
  {U : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
  {adj : L ⊣ U} {hL : PreservesFiniteLimits L}
  (d : ConstantLeftModuleInverseImageLift J K A L U adj hL)

/-- Reuse the supplied constant-module inverse image's additive structure.
Source: Stacks 00YV (blueprint: lem-pur-tower-limit-transpose-normalization). -/
instance inverseAdditive : d.moduleFunctor.Additive := d.additive

/-- Reuse exactness of the canonical constant-module inverse image.
Source: Stacks 00YV (blueprint: lem-pur-tower-limit-transpose-normalization). -/
instance inverseFiniteLimits : PreservesFiniteLimits d.moduleFunctor := d.preservesFiniteLimits

/-- Reuse exactness of the canonical constant-module inverse image.
Source: Stacks 00YV (blueprint: lem-pur-tower-limit-transpose-normalization). -/
instance inverseFiniteColimits : PreservesFiniteColimits d.moduleFunctor :=
  d.preservesFiniteColimits

/-- The supplied module direct image preserves limits by its actual module adjunction.
Source: Stacks 03D7 (blueprint: lem-pur-tower-limit-transpose-normalization). -/
instance directLimits : PreservesLimitsOfSize.{x, y} d.moduleDirect :=
  d.moduleAdj.rightAdjoint_preservesLimits

/-- Additivity of module direct image, using its preservation of binary products.
Source: Stacks 03D7 (blueprint: lem-pur-tower-limit-transpose-normalization). -/
instance directAdditive : d.moduleDirect.Additive :=
  Functor.additive_of_preserves_binary_products d.moduleDirect

variable [HasDerivedCategory.{w} (Modules J A)] [HasDerivedCategory.{w} (Modules K A)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules J A)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules K A)]

/-- Termwise direct image on strict towers, before deriving.
Source: Stacks 0A07 (blueprint: lem-pur-tower-limit-transpose-normalization). -/
abbrev towerDirect : (ℕᵒᵖ ⥤ Modules K A) ⥤ (ℕᵒᵖ ⥤ Modules J A) :=
  (Functor.whiskeringRight ℕᵒᵖ (Modules K A) (Modules J A)).obj d.moduleDirect

/-- Exact termwise inverse image on strict towers, before localization.
Source: Stacks 00YV and 015F
(blueprint: lem-pur-tower-limit-transpose-normalization). -/
abbrev towerInverse : (ℕᵒᵖ ⥤ Modules J A) ⥤ (ℕᵒᵖ ⥤ Modules K A) :=
  (Functor.whiskeringRight ℕᵒᵖ (Modules J A) (Modules K A)).obj d.moduleFunctor

/-- The canonical ordinary module derived adjunction, with its actual counit.
Source: Stacks 07A6, 09T5
(blueprint: lem-pur-tower-limit-transpose-normalization). -/
abbrev moduleAdjunction : d.moduleFunctor.mapDerivedCategory ⊣
    d.moduleDirect.rightDerivedFunctor := d.moduleAdj.mapDerivedCategoryRightDerivedAdjunction

/-- The canonical tower derived adjunction, derived from the termwise module adjunction.
Source: Stacks 07A6, 09T5
(blueprint: lem-pur-tower-limit-transpose-normalization). -/
abbrev towerAdjunction : (towerInverse d).mapDerivedCategory ⊣
    (towerDirect d).rightDerivedFunctor :=
  (d.moduleAdj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction

/-- The fixed direct-image/total-limit comparison identifies the composite Hom bijection
and every augmented-arrow transpose, including the actual derived counits.

Source: Stacks Project, Cohomology on Sites, 0A07 (first proof), 07A6 and 0940;
Derived Categories, 08BJ, 070I and 09T5
(blueprint: lem-pur-tower-limit-transpose-normalization).

`d` is any presentation of the canonical constant-coefficient module lift of the
geometric adjunction, not an arbitrary pair of module functors. `J` is the target
site and `K` the source site. The ideal `_I` is unrestricted; its quotients do not
enter this constant-A assertion. The first equation uniquely normalizes `a` as the
comparison of the common underived composite in
lem-weil-ringed-tower-pushforward-limit-comparison. The next two clauses say that
the actual units of the derived constant/limit adjunctions are isomorphisms. Their
inverses are the diagonal K-injective normalization `Rlim Δ ≅ 1`; thus a unit still
visible in the final formula is precisely the suppressed source identification.
The Hom equalities are universally quantified, so include zero objects, identity
morphisms, constant towers and the counit specialization. All operations in these
equalities are natural Hom equivalences or natural transformations.

Proof (the seven steps of the node):
1. Use lem-pe-constant-left-module-inverse-image and
   lem-weil-pbc-ringed-topoi-module-adjunction for the exact module adjunction.
   By lem-weil-tower-category-levelwise-abelian it extends termwise to towers;
   lem-weil-pbc-exact-functor-derived-factorization descends its exact left functors
   and the constant/inverse-image identity.
2. The ordinary constant/limit Hom bijection is `constLimAdj`. Since level 1 is
   terminal in the tower index, evaluation there is left adjoint to constants.
   It is exact, so lem-weil-pbc-right-adjoint-preserves-kinjective makes constants
   preserve K-injectives. The same criterion makes limit preserve K-injectives.
   Compute Rlim of a diagonal K-injective as that same complex, with identity unit,
   by lem-weil-pbc-ringed-strict-tower-homotopy-limit.
3. Use lem-weil-pbc-diagram-site-realization and prop-pur-kinjective-resolutions-exist
   for a K-injective tower H representing V. Direct image, tower direct image and
   limit preserve K-injectives, hence lem-weil-pbc-kinjective-total-derived computes
   both composites on H. The fixed comparison from
   lem-weil-ringed-tower-pushforward-limit-comparison is the ordinary limit.post
   comparison on H, giving exactly the first equation below.
4. By lem-weil-pbc-kinjective-hom-derived the displayed Hom sets are homotopy Hom
   sets into these representatives. By lem-weil-pbc-termwise-adjunction-homotopy
   their adjunction bijections are the ordinary termwise ones. The counit equation
   in lem-sc-derived-adjunction-from-underived identifies these with the actual
   canonical derived adjunctions, and identifies the constant/limit unit as in step 2.
5. For a chain map c:B -> lim U^J H, the first two transposes have component
   eps_(H_n) F(pi_n c). The last transpose is the unique chain map with these
   components. Naturality of the ordinary counit and pi_n a = U(pi_n) show that
   transposing c followed by a inverse has these very components. Equality is
   checked in complexes, then localized; no detection by derived projections is used.
6. Put k = j followed by the tower adjunct of b. Its tower transpose is G(j) followed
   by b. Apply step 5 and both constant/limit adjunctions; their units give exactly
   the last formula below and their inverses give the source identifications.
7. Naturality of each Hom bijection and of the fixed comparison proves naturality
   in M,V,Z,b,j. Only exact constant pullback and K-injective resolutions were used:
   neither perfectness, completeness, boundedness nor exact products is needed. -/
theorem tower_limit_transpose_normalization
    [IsNoetherianRing A] (_I : Ideal A) :
    ∃ a : (towerLimit (Modules K A)).rightDerivedFunctor ⋙
        d.moduleDirect.rightDerivedFunctor ≅
      (towerDirect d).rightDerivedFunctor ⋙ (towerLimit (Modules J A)).rightDerivedFunctor,
      (∀ H : CochainComplex (ℕᵒᵖ ⥤ Modules K A) ℤ,
        UnboundedExactTower.cochainUnit d.moduleDirect
            (((towerLimit (Modules K A)).mapHomologicalComplex (.up ℤ)).obj H) ≫
          d.moduleDirect.rightDerivedFunctor.map
            (UnboundedExactTower.cochainUnit (towerLimit (Modules K A)) H) ≫
          a.hom.app (DerivedCategory.Q.obj H) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (preservesLimitNatIso d.moduleDirect (J := ℕᵒᵖ)).hom (.up ℤ)).app H) ≫
          UnboundedExactTower.cochainUnit (towerLimit (Modules J A))
            (((towerDirect d).mapHomologicalComplex (.up ℤ)).obj H) ≫
          (towerLimit (Modules J A)).rightDerivedFunctor.map
            (UnboundedExactTower.cochainUnit (towerDirect d) H)) ∧
      IsIso (limitAdjunction (Modules J A)).unit ∧
      IsIso (limitAdjunction (Modules K A)).unit ∧
      ConstantUnitNormalization (Modules J A) ∧
      ConstantUnitNormalization (Modules K A) ∧
      (∀ (M : DerivedCategory.{w} (Modules J A))
          (V : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules K A))
          (c : M ⟶ (towerLimit (Modules J A)).rightDerivedFunctor.obj
            ((towerDirect d).rightDerivedFunctor.obj V)),
        (limitAdjunction (Modules K A)).homEquiv
            (d.moduleFunctor.mapDerivedCategory.obj M) V
            ((UnboundedExactTower.constantInterchange d.moduleFunctor).inv.app M ≫
              ((towerAdjunction d).homEquiv
                ((Functor.const ℕᵒᵖ : Modules J A ⥤ _).mapDerivedCategory.obj M) V).symm
                (((limitAdjunction (Modules J A)).homEquiv M
                  ((towerDirect d).rightDerivedFunctor.obj V)).symm c)) =
          ((moduleAdjunction d).homEquiv M
            ((towerLimit (Modules K A)).rightDerivedFunctor.obj V)).symm (c ≫ a.inv.app V)) ∧
      (∀ (M : DerivedCategory.{w} (Modules J A))
          (Z : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules J A))
          (V : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules K A))
          (b : (towerInverse d).mapDerivedCategory.obj Z ⟶ V)
          (j : (Functor.const ℕᵒᵖ : Modules J A ⥤ _).mapDerivedCategory.obj M ⟶ Z),
        (moduleAdjunction d).homEquiv M
            ((towerLimit (Modules K A)).rightDerivedFunctor.obj V)
            ((limitAdjunction (Modules K A)).homEquiv
              (d.moduleFunctor.mapDerivedCategory.obj M) V
              ((UnboundedExactTower.constantInterchange d.moduleFunctor).inv.app M ≫
                (towerInverse d).mapDerivedCategory.map j ≫ b)) =
          (limitAdjunction (Modules J A)).unit.app M ≫
            (towerLimit (Modules J A)).rightDerivedFunctor.map j ≫
            (towerLimit (Modules J A)).rightDerivedFunctor.map
              ((towerAdjunction d).homEquiv Z V b) ≫ a.inv.app V) := by
  sorry

end Coefficients

end CategoryTheory.TowerLimitTransposeNormalization
