/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KunnethGlobalSections
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProperTorsionProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula

/-!
# Ordinary étale Künneth and the proper projection formula

Source: Stacks Project, Étale Cohomology, Tags 0F1P and 0F0G; blueprint
sec-smooth-purity/sk-prop-sf-kunneth-ordinary, with the accepted finite-type correction
(blueprint: sk-prop-sf-kunneth-ordinary).

Both conclusions concern the specified canonical morphisms on unbounded derived categories.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Ordinary étale Künneth over a separably closed field, and the proper projection formula,
for finite commutative coefficients with invertible exponent. The proper morphism is between
arbitrary schemes, independently of the field and the finite-type schemes in the first clause.

Source: Stacks Project, Tags 0F1P (`lemma-kunneth`) and 0F0G
(`lemma-projection-formula-proper-mod-n`), and the blueprint's finite-ring version
(blueprint: sk-prop-sf-kunneth-ordinary).

Proof plan:
1. The cartesian square `pullback.fst aX aY`, `pullback.snd aX aY` over `Spec k` satisfies the
   hypotheses of lem-sf-finite-ring-native-kunneth (`isIso_kunnethMap_of_isSepClosed`): the
   native counit-defined Künneth map `Ra_{X*}E ⊗ᴸ Ra_{Y*}K ⟶ Rc_*(p₁^*E ⊗ᴸ p₂^*K)` in
   `D((Spec k)_ét, Λ)` is an isomorphism. That theorem follows the unit's ordinary
   tensor-base-change route (lem-sf-finite-ring-tensor-base-change, lem-kun-0f10, lem-kun-0f12).
2. By def-kun-kunneth-map, `kunnethGlobalSectionsMap` is the composite of the tensor of the
   inverse Leray isomorphisms, `pointGlobalSectionsTensorIso`, derived point global sections
   applied to the native map of step 1, and the final Leray isomorphism. Functors preserve
   isomorphisms and composites of isomorphisms are isomorphisms, so the map is invertible.
3. A finite ring is additively torsion (`isAddTorsion_of_finite`, also for the zero ring).
   For any proper f : U → V, lem-kun-0f0g gives invertibility of def-kun-projection-formula-map
   itself for arbitrary unbounded E, L. This step requires neither finite type over k nor
   boundedness, and does not use the exponent-invertibility hypotheses of the second clause.
-/
theorem ordinaryEtaleKunneth_and_properProjectionFormula
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    (∀ (k : Type u) [Field k] [IsSepClosed k]
      [HasInvertibleExponent Λ (Spec (.of k))]
      (X Y : Scheme.{u}) (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
      [LocallyOfFiniteType aX] [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (E : DerivedCategoryModule Λ X) (K : DerivedCategoryModule Λ Y),
      IsIso (kunnethGlobalSectionsMap Λ (pullback.fst aX aY) (pullback.snd aX aY)
        aX aY (pullback.condition.symm) E K)) ∧
    (∀ (U V : Scheme.{u}) (f : U ⟶ V) [IsProper f]
      [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ V]
      (E : DerivedCategoryModule Λ U) (L : DerivedCategoryModule Λ V),
      IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app L)) := by
  constructor
  · intro k _ _ _ X Y aX aY _ _ _ _ E K
    have := isIso_kunnethMap_of_isSepClosed Λ aX aY
      (pullback.fst aX aY) (pullback.snd aX aY) (IsPullback.of_hasPullback aX aY) E K
    unfold kunnethGlobalSectionsMap
    infer_instance
  · intro U V f _ _ _ E L
    exact isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
      Λ isAddTorsion_of_finite f E L

end AlgebraicGeometry.Etale
