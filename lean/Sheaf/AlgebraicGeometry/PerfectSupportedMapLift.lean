/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.AlgebraicGeometry.PerfectComplex

/-! # Lifting maps from perfect complexes with support

Source: Stacks Project, Derived Categories of Schemes, Tag 09IM, Lemma 36.13.11
(blueprint: lem-sc-perfect-support-map-lift).
-/

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- A map from a perfect complex on a quasi-compact open extends as a direct summand
of a map from a global perfect complex with the prescribed closed support.
Support is expressed by vanishing of every cohomology stalk off the closed subset.
Restriction uses the canonical equivalence from the localized site to the open subscheme.
Source: Stacks Project, Derived Categories of Schemes, Tag 09IM, Lemma 36.13.11
(blueprint: lem-sc-perfect-support-map-lift).

Proof:
1. Cover X by U and finitely many affine opens. Induction reduces to X = U ∪ V
   with V affine; the intersections remain quasi-compact by quasi-separatedness.
2. Apply lem-sc-affine-perfect-support-extension on V to extend the restriction of P
   to a perfect Q supported on T ∩ V, whose restriction is (P ⊕ P[1])|_(U ∩ V).
3. Compose with projection to P and alpha. By lem-sc-affine-perfect-map-lift, replace
   Q by Q tensor^L I, retaining perfectness and support, to lift this map to E|_V.
   The replacement map is an isomorphism on the overlap.
4. Apply lem-sc-derived-open-gluing to this map on V and alpha composed with the
   projection P ⊕ P[1] → P on U, using the overlap isomorphism and its compatibility.
   The resulting map beta : R → E has R perfect and supported on T, since these
   conditions are local on U ∪ V. Inclusion and projection on P ⊕ P[1] exhibit the
   required compatible direct summand on U. -/
theorem exists_perfect_supported_map_lift
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (E : schemeDerivedQCohCategory X)
    (P : schemeDerivedCategory U.toScheme) (hP : IsPerfect U.toScheme P)
    (hPT : ∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj P).val.presheaf x)))
    (α : P ⟶ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory.obj E.obj) :
    ∃ (R : schemeDerivedCategory X) (β : R ⟶ E.obj),
      IsPerfect X R ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj R).val.presheaf x))) ∧
      ∃ (ι : P ⟶ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R)
        (π : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R ⟶ P),
        ι ≫ π = 𝟙 P ∧ ι ≫ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.map β = α :=
  sorry

end AlgebraicGeometry.Scheme
