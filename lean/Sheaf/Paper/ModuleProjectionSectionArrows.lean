/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.Paper.IntegralResidueDerivedMonoidal
public import Sheaf.Paper.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Canonical module projection and section comparisons

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-int-restriction/sk-thm-int-restriction-line.proof.md, clause (1), and Stacks 0B56
(blueprint: def-sfb-module-projection-section-arrows).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A typed alias of the existing total left derived pullback, keeping its inferred
K-flat structure fixed when using the tensor comparison. There is no new functor.
Source: blueprint derived pullback convention; Stacks 07A4
(blueprint: def-sfb-module-projection-section-arrows). -/
abbrev moduleDerivedPullback :
    DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ⥤
        DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  (CondensedRing.upperStar Λ f).leftDerivedFunctor

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A typed alias of the existing total right derived direct image, retaining its
canonical K-injective construction. There is no new functor.
Source: blueprint derived direct-image convention; Stacks 0B56
(blueprint: def-sfb-module-projection-section-arrows). -/
abbrev moduleDerivedPushforward :
    DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
        DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :=
  (CondensedRing.lowerStar Λ f).rightDerivedFunctor

namespace ProjectionSection

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The left-ordered projection map is the adjunct of the canonical tensor comparison
followed by identity tensor the counit. Source: blueprint displayed definition of pi
(blueprint: def-sfb-module-projection-section-arrows). -/
def projection {Z B : Scheme.{u}} (f : Z ⟶ B)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B)))
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    M ⊗ (moduleDerivedPushforward Λ f).obj N ⟶
      (moduleDerivedPushforward Λ f).obj
        ((moduleDerivedPullback Λ f).obj M ⊗ N) :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _
    (((CondensedRing.leftDerivedUpperStarTensor Λ f).app M).app
      ((moduleDerivedPushforward Λ f).obj N) ≫
        (𝟙 ((moduleDerivedPullback Λ f).obj M) ⊗ₘ
          (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).counit.app N))

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The canonical section pullback comparison, using the published composition and
identity comparisons. Source: blueprint identification i^* r^* = id
(blueprint: def-sfb-module-projection-section-arrows). -/
def pullbackSection {X V : Scheme.{u}} (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X) :
    (moduleDerivedPullback Λ r) ⋙
      (moduleDerivedPullback Λ i) ≅ 𝟭 _ :=
  (CondensedRing.leftDerivedUpperStarComp Λ i r).symm ≪≫
    Functor.leftDerivedFunctorNatIso _ (eqToIso (congrArg (CondensedRing.upperStar Λ) h)) ≪≫
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (𝟙 X) ≪≫
    profinitePointModuleDerivedIdentity Λ X

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The direct-image section comparison is the adjunction conjugate of pullbackSection.
Source: blueprint composition identifications, uniqueness of adjoints
(blueprint: def-sfb-module-projection-section-arrows). -/
def pushforwardSection {X V : Scheme.{u}} (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X) :
    (moduleDerivedPushforward Λ i) ⋙
      (moduleDerivedPushforward Λ r) ≅ 𝟭 _ :=
  conjugateIsoEquiv
    ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ r).comp
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ i))
    Adjunction.id (pullbackSection Λ r i h).symm


end ProjectionSection

end AlgebraicGeometry.ProEtale
