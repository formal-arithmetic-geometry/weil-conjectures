/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-! # Exceptional inverse image on bounded constructible complexes

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-existence/det-def-sfb-dc-upper-shriek.md
(blueprint: det-def-sfb-dc-upper-shriek).

For arbitrary coefficients with the stated preservation property, compose a supplied chosen
proper right adjoint with restricted open pullback. The chosen compactification construction
and adjunction are imported from `ExceptionalInverseImage` and `ExceptionalAdjunction`.
The three adic existence cases are imported from `UpperShriek`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (H : PreservesBoundedConstructiblePushforwards Λ k)
  {f : X ⟶ Y} (c : Compactification.BoundaryCompactification f.left)

-- The open pullback carries the large native internal-module derived-category types.
/-- For a chosen right adjoint `Rp^!` of the restricted proper pushforward, the exceptional
inverse image attached to `c` is `Rp^! ⋙ Li^*`. The functor is constructed directly between
bounded constructible categories. The supplied adjunction is used by the following definition;
no right-adjoint existence is asserted for arbitrary condensed coefficients.

Source: latest blueprint, sec-six-functors-basics/sk-thm-existence,
`det-def-sfb-dc-upper-shriek.md`, displayed compactification definition
(blueprint: det-def-sfb-dc-upper-shriek). -/
noncomputable def boundedConstructibleExceptionalOfCompactification
    (Rp : ProEtale.BoundedConstructible (condensedRingObj Λ Y.left) ⥤
      ProEtale.BoundedConstructible (condensedRingObj Λ c.obj.obj.Z)) :
    ProEtale.BoundedConstructible (condensedRingObj Λ Y.left) ⥤
      ProEtale.BoundedConstructible (condensedRingObj Λ X.left) :=
  Functor.comp
    (C := ProEtale.BoundedConstructible (condensedRingObj Λ Y.left))
    (D := ProEtale.BoundedConstructible (condensedRingObj Λ c.obj.obj.Z))
    (E := ProEtale.BoundedConstructible (condensedRingObj Λ X.left)) Rp
    (boundedConstructibleUpperStar Λ ℓ (k := k) (X := X) (Y := c.obj.obj.overObj)
      c.obj.obj.overI)

-- Compose adjunctions on the native internal-module derived categories.
/-- The compactification adjunction is the composite of the restricted open adjunction and
`Rp_* ⊣ Rp^!`. In particular its left and right functors are respectively a left and a right
adjoint. Its unit, counit and Hom bijection are those of `Adjunction.comp`, with the open
adjunction first and the proper adjunction second. A different choice of proper right adjoint
is compared by `Adjunction.rightAdjointUniq`, uniquely when compatible with the counits.

Source: latest blueprint, sec-six-functors-basics/sk-thm-existence,
`det-def-sfb-dc-upper-shriek.md`, composite adjunction paragraph
(blueprint: det-def-sfb-dc-upper-shriek). -/
noncomputable def boundedConstructibleExceptionalOfCompactificationAdjunction
    (Rp : ProEtale.BoundedConstructible (condensedRingObj Λ Y.left) ⥤
      ProEtale.BoundedConstructible (condensedRingObj Λ c.obj.obj.Z))
    (adj : boundedConstructibleLowerStarOfPreserves Λ H c.obj.obj.overG ⊣ Rp) :
    boundedConstructibleLowerShriekOfCompactificationOfPreserves Λ ℓ H c ⊣
      boundedConstructibleExceptionalOfCompactification Λ ℓ c Rp :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ
    (k := k) (U := X) (X := c.obj.obj.overObj) c.obj.obj.overI).comp adj

end AlgebraicGeometry.ProEtale.CondensedRing
