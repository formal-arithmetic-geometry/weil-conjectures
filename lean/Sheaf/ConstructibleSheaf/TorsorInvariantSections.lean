/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.ConstructibleSheaf.TorsorAssociatedModule

/-!
# Invariant sections descend along a finite etale torsor

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-invariant-sections)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.GaloisCover

/-- Invariant locally constant coefficient functions on the torsor are precisely
sections of the constant coefficient sheaf downstairs, before sheafification.
Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-invariant-sections)

Proof: Over an etale object W, trivialize the pulled-back torsor on an etale
cover of W. An invariant function has the same value on all translates of a
local torsor section, so evaluation gives a locally constant function on each
member of this cover. A different section differs locally by a group element;
invariance makes the evaluations identical. They therefore glue uniquely on
W. Conversely pull back a locally constant function on W to the torsor; it is
invariant. Surjectivity of the torsor and its local trivializations show that
these operations are inverse. They commute with restriction and pointwise
module operations, including restriction of scalars. Locally constant functions
on W identify with sections of the constant coefficient sheaf: the constant
presheaf maps to them by constant functions; any locally constant function is
locally in its image on its open fibers, and equality of two such sections is
local. This gives the identification after sheafification of the constant
presheaf. On the empty object both section modules are zero. -/
theorem equivariantModulePresheaf_trivial {V : Scheme.{u}} (ℓ : ℕ)
    {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) :
    Nonempty (
      c.equivariantModulePresheaf ℓ
          (Rep.trivial (ZMod ℓ) P (ULift.{u + 1} (ZMod ℓ))) ⋙
        ModuleCat.restrictScalars.{u + 1}
          (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ) ≅
      ((constantSheaf V.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
          (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))).obj) := by sorry

end AlgebraicGeometry.Scheme.GaloisCover
