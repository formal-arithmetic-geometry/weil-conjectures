/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-! # Exceptional inverse image for the chosen compactification

The definition is the restricted pullback along the open leg composed after the chosen right
adjoint of the restricted proper pushforward along the proper leg of `c_f`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The recorded chosen compactification of a morphism in `Over (Spec k)`, expressed as a
compactification of its underlying morphism. This only binds the structure morphism instances;
its value is the chosen compactification `compactificationOverField`. -/
noncomputable def exceptionalInverseImageCompactification
    {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) : Compactification f.left := by
  letI : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  letI : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  letI : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  letI : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  letI : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  exact (AlgebraicGeometry.compactificationOverField k f.left).obj.obj

/-- The chosen compactification's proper pushforward restricted to bounded constructible
complexes, using precisely its preservation hypothesis. -/
noncomputable def exceptionalInverseImageProperPushforward
    {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (hP : ∀ K : ProEtale.BoundedConstructible
        (condensedRingObj Λ (exceptionalInverseImageCompactification f).Z),
      boundedConstructible (condensedRingObj Λ Y.left)
        ((lowerStar Λ (exceptionalInverseImageCompactification f).g).rightDerivedFunctor.obj
          K.obj)) :
    ProEtale.BoundedConstructible
        (condensedRingObj Λ (exceptionalInverseImageCompactification f).Z) ⥤
      ProEtale.BoundedConstructible (condensedRingObj Λ Y.left) :=
  (boundedConstructible (condensedRingObj Λ Y.left)).lift
    ((boundedConstructible
      (condensedRingObj Λ (exceptionalInverseImageCompactification f).Z)).ι ⋙
        (lowerStar Λ (exceptionalInverseImageCompactification f).g).rightDerivedFunctor) hP

/-- The exceptional inverse image is the compactification-dependent composite evaluated at
`c_f`: the chosen right adjoint of its restricted proper pushforward followed by the actual
restricted pullback along its open leg. The right adjoint is chosen by Functor.rightAdjoint
from the displayed existence assumption; no existence theorem is asserted here. -/
noncomputable def boundedConstructibleUpperShriekOfRightAdjoint
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (hP : ∀ K : ProEtale.BoundedConstructible
        (condensedRingObj Λ (exceptionalInverseImageCompactification f).Z),
      boundedConstructible (condensedRingObj Λ Y.left)
        ((lowerStar Λ (exceptionalInverseImageCompactification f).g).rightDerivedFunctor.obj
          K.obj))
    [(exceptionalInverseImageProperPushforward Λ f hP).IsLeftAdjoint] :
    ProEtale.BoundedConstructible (condensedRingObj Λ Y.left) ⥤
      ProEtale.BoundedConstructible (condensedRingObj Λ X.left) :=
  Functor.comp
    (C := ProEtale.BoundedConstructible (condensedRingObj Λ Y.left))
    (D := ProEtale.BoundedConstructible
      (condensedRingObj Λ (exceptionalInverseImageCompactification f).Z))
    (E := ProEtale.BoundedConstructible (condensedRingObj Λ X.left))
    (exceptionalInverseImageProperPushforward Λ f hP).rightAdjoint
    (boundedConstructibleUpperStar Λ ℓ (k := k) (X := X)
      (Y := (exceptionalInverseImageCompactification f).overObj)
      (exceptionalInverseImageCompactification f).overI)

end AlgebraicGeometry.ProEtale.CondensedRing
