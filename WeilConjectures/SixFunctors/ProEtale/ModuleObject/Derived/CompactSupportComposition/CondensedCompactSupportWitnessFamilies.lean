/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.Compactification.BaseChange

/-! # Shared types of the six compact-support comparison witnesses

These are type aliases for the six binder domains of `CompactSupportComposition.Coherent`.
Naming them once lets the existential predicate and its record interface use identical types.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.CompactSupportComposition

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The `preserves` witness family in compact-support composition and base change.
Source: latest blueprint sk-thm-sf-comp-composition, clauses (1)--(2).
(blueprint: def-sfb-compact-support-witness-families). -/
def PreservationFamily (k : Type u) [Field k] :=
  ∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left),
    (∀ K, localizingClosureProEtale Λ X.obj.left K →
      localizingClosureProEtale Λ Y.obj.left
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) ∧
    (∀ K, (constantModelBoundedConstructible Λ X.obj.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible Λ Y.obj.left
          ((rightDerivedLowerShriekOfCompactification Λ c).obj K) ∧
        DerivedCategory.finiteTorAmplitude _
          ((rightDerivedLowerShriekOfCompactification Λ c).obj K))

/-- The `comparison` witness family in compact-support composition and base change.
Source: latest blueprint sk-thm-sf-comp-composition, clauses (1)--(2).
(blueprint: def-sfb-compact-support-witness-families). -/
def RefinementComparisonFamily (k : Type u) [Field k] :=
  ∀ {X Y : SepFinType k} (f : X ⟶ Y) (c d : Compactification f.hom.left),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ c ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ d

/-- The `comp` witness family in compact-support composition and base change.
Source: latest blueprint sk-thm-sf-comp-composition, clauses (1)--(2).
(blueprint: def-sfb-compact-support-witness-families). -/
def CompositionComparisonFamily (k : Type u) [Field k] :=
  ∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (c : Compactification f.hom.left) (d : Compactification g.hom.left)
      (e : Compactification (f.hom.left ≫ g.hom.left)),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ c ⋙
          rightDerivedLowerShriekOfCompactification Λ d) ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ e

/-- The `openIso` witness family in compact-support composition and base change.
Source: latest blueprint sk-thm-sf-comp-composition, clauses (1)--(2).
(blueprint: def-sfb-compact-support-witness-families). -/
def OpenExchangeFamily (k : Type u) [Field k] :=
  ∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
      (sq : IsPullback a f'.hom.left f.hom.left v) (c : Compactification f.hom.left),
    D((c.i)_!open⟦Λ⟧) ⋙ moduleObjectDerivedPullback Λ (pullback.fst c.g v) ≅
      moduleObjectDerivedPullback Λ a ⋙ D(((c.ofIsPullback sq).i)_!open⟦Λ⟧)

/-- The `pullback_preserves` witness family in compact-support composition and base change.
Source: latest blueprint sk-thm-sf-comp-composition, clauses (1)--(2).
(blueprint: def-sfb-compact-support-witness-families). -/
def PullbackPreservationFamily (k : Type u) [Field k] :=
  ∀ (X Y : SepFinType k) (v : X.obj.left ⟶ Y.obj.left),
    (∀ K, localizingClosureProEtale Λ Y.obj.left K →
      localizingClosureProEtale Λ X.obj.left ((moduleObjectDerivedPullback Λ v).obj K)) ∧
    (∀ K, (constantModelBoundedConstructible Λ Y.obj.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible Λ X.obj.left ((moduleObjectDerivedPullback Λ v).obj K) ∧
        DerivedCategory.finiteTorAmplitude _ ((moduleObjectDerivedPullback Λ v).obj K))

/-- The `exchange` witness family in compact-support composition and base change.
Source: latest blueprint sk-thm-sf-comp-composition, clauses (1)--(2).
(blueprint: def-sfb-compact-support-witness-families). -/
def ExchangeFamily (k : Type u) [Field k] :=
  ∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
      (_sq : IsPullback a f'.hom.left f.hom.left v)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ c ⋙ moduleObjectDerivedPullback Λ v) ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (moduleObjectDerivedPullback Λ a ⋙ rightDerivedLowerShriekOfCompactification Λ d)

end AlgebraicGeometry.ProEtale.CondensedRing.CompactSupportComposition
