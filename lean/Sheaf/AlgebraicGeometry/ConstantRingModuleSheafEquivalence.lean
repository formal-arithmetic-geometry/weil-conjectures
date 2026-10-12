/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Module sheaves and modules over the constant ring sheaf

Source: Stacks Project, Modules on Sites, Section 18.11, Lemma 18.11.1.
(blueprint: new-constant-ring-module-sheaf-equivalence)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The two encodings of sheaves of modules over ZMod r are equivalent, compatibly
with their underlying abelian sheaves.
Source: Stacks Project, Modules on Sites, Section 18.11, Lemma 18.11.1
(https://stacks.math.columbia.edu/tag/03CY), applied to the constant ring presheaf.
(blueprint: new-constant-ring-module-sheaf-equivalence)

Proof: First identify the single and double lifts of ZMod r by the ring isomorphism
sending a lifted element to its twice-lifted value. A module-valued sheaf has an
action of the constant ring presheaf on its underlying abelian sheaf. Extend this
action to the sheafification of that presheaf: locally represent a section of the
constant ring sheaf by constant scalars, act on the restrictions of the module
section, and glue. Independence of representatives, the module laws and linearity
of maps are local assertions and follow from the original action and sheaf
uniqueness. Conversely restrict an action along the sheafification unit and the
ring isomorphism. The two constructions retain the underlying abelian sheaf and
all underlying morphisms. Uniqueness of the extended action gives inverse natural
isomorphisms, hence an equivalence and the displayed natural isomorphism of
forgetful functors. This works for r = 0 and r = 1 as well as for the empty scheme;
no nonzero scalar or nonempty covering assumption is used. -/
theorem constantRing_moduleSheaf_equivalence (X : Scheme.{u}) (r : ℕ) :
    ∃ E : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) ≌
      SheafOfModules.{u + 1}
        ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
          (RingCat.of (ULift.{u + 1, u} (ULift.{u} (ZMod r))))),
      Nonempty
        (sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
              AddCommGrpCat.{u + 1}) ≅
          E.functor ⋙ SheafOfModules.toSheaf _) := by sorry

end AlgebraicGeometry.Etale
