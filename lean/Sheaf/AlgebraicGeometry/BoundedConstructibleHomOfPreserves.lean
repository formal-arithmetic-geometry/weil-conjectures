/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# Derived internal Hom restricted by bounded constructibility

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
`sk-def-sfb-dc-restricted-functors/def-sfb-dc-hom.md`
(blueprint: def-sfb-dc-hom).

The preservation condition is an explicit hypothesis for an arbitrary commutative condensed
ring. The bifunctor and its identity-component comparison are restrictions of the recorded
ambient derived internal Hom, using the existing full-subcategory construction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

/-- Restriction of the ambient derived internal Hom in both variables, under exactly its
bounded-constructibility preservation condition.

Source: blueprint `def-sfb-dc-hom`, definition of the restricted bifunctor
(blueprint: def-sfb-dc-hom).

Construction: precompose the ambient uncurried `derivedHom` with the two inclusions
`ι.op` and `ι`. The hypothesis `h` supplies the bounded-constructibility certificate at
every pair. `ObjectProperty.lift` keeps its ambient objects and maps and inherits its
identity and composition laws. Currying gives the displayed two-variable functor.
The coefficient examples use the separate finiteness node `lem-sfb-dc-hom-preserves`;
no finiteness-coefficient instance is required for this definition. -/
noncomputable def boundedConstructibleHomOfPreserves
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (h : ∀ K L : BoundedConstructible (condensedRingObj Λ X.left),
      boundedConstructible (condensedRingObj Λ X.left)
        (((derivedHom Λ X.left).obj (op K.obj)).obj L.obj)) :
    (BoundedConstructible (condensedRingObj Λ X.left))ᵒᵖ ⥤
      BoundedConstructible (condensedRingObj Λ X.left) ⥤
        BoundedConstructible (condensedRingObj Λ X.left) :=
  Functor.curry.obj
    ((boundedConstructible (condensedRingObj Λ X.left)).lift
      (((boundedConstructible (condensedRingObj Λ X.left)).ι.op.prod
        (boundedConstructible (condensedRingObj Λ X.left)).ι) ⋙
        Functor.uncurry.obj (derivedHom Λ X.left))
      (fun KL ↦ h KL.1.unop KL.2))

/-- For fixed `K`, the restricted internal Hom commutes with the ambient inclusion.
Its components and inverse components are identities on the same ambient Hom object.

Source: blueprint `def-sfb-dc-hom`, final sentence and its full-subcategory expansion
(blueprint: def-sfb-dc-hom).

Construction: after forgetting the property certificate, `ObjectProperty.lift` has the
same object and map assignments as its input. Apply `Functor.curryObjProdComp` to the two
inclusions, then the inverse currying unit at the ambient Hom bifunctor. Both canonical
comparisons have identity components. -/
noncomputable def boundedConstructibleHomOfPreservesCompatibility
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (h : ∀ K L : BoundedConstructible (condensedRingObj Λ X.left),
      boundedConstructible (condensedRingObj Λ X.left)
        (((derivedHom Λ X.left).obj (op K.obj)).obj L.obj))
    (K : BoundedConstructible (condensedRingObj Λ X.left)) :
    (boundedConstructibleHomOfPreserves ℓ X Λ h).obj (op K) ⋙
        (boundedConstructible (condensedRingObj Λ X.left)).ι ≅
      (boundedConstructible (condensedRingObj Λ X.left)).ι ⋙
        (derivedHom Λ X.left).obj (op K.obj) :=
  (Functor.curryObjProdComp
    (boundedConstructible (condensedRingObj Λ X.left)).ι.op
    (boundedConstructible (condensedRingObj Λ X.left)).ι
    (Functor.uncurry.obj (derivedHom Λ X.left))).app (op K) ≪≫
    Functor.isoWhiskerLeft (boundedConstructible (condensedRingObj Λ X.left)).ι
      ((Functor.currying.unitIso.symm.app (derivedHom Λ X.left)).app (op K.obj))

end AlgebraicGeometry.ProEtale.CondensedRing
