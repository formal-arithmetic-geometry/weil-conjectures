/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # A nonzero morphism into a locally constant sheaf has locally nonzero germs

Source: the first step of blueprint `lem-weil-pbc-lisse-generic-kernel`
(blueprint: lem-weil-pbc-locally-constant-nonzero-germs).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A nonzero morphism into an abelian sheaf whose underlying set sheaf is locally
constant has a section on a nonempty etale neighbourhood whose image has nonzero
geometric germs everywhere on that neighbourhood.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-weil-pbc-lisse-generic-kernel`,
first proof step (blueprint: lem-weil-pbc-locally-constant-nonzero-germs).

Proof:
1. Geometric stalks are jointly faithful, so a nonzero morphism has a nonzero map
   on some geometric stalk. Choose an element with nonzero image and represent it
   by a section of the source on a pointed etale neighbourhood.
2. Lift the point to a member of the etale cover trivializing the underlying set
   sheaf of the target. Refine the pointed neighbourhood by its fibre product with
   this cover member. Pointed neighbourhoods over the cover member are cofinal, so
   the image germ remains nonzero. Identify the target with a constant set sheaf
   on the cover member. The image germ and the zero germ correspond to two distinct
   elements m and z of the constant set.
3. The stalk of a constant set sheaf is its constant set: sheafification does not
   change stalks and the colimit of a constant diagram over the nonempty connected
   category of pointed neighbourhoods is its value. Equality of germs in a filtered
   colimit holds after refinement. Refine twice so that the image section is the
   constant section m and the zero section is the constant section z.
4. The refined neighbourhood is nonempty because it retains its marked geometric
   point. At every geometric point of this neighbourhood, the constant-sheaf stalk
   formula sends these sections to the distinct elements m and z. Thus the image
   germ is nonzero at every such point. This uses local constancy only as a sheaf
   of sets; it does not require the trivialization to respect addition.
-/
theorem exists_section_everywhere_nonzero_germ (X : Scheme.{u})
    (N F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F))
    (ψ : N ⟶ F) (hψ : ψ ≠ 0) :
    ∃ (U : X.Etale) (_ : Nonempty U.left) (s : N.obj.obj (op U)),
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
        (v : (pointSmallEtale t).fiber.obj U),
        (pointSmallEtale t).toPresheafFiber U v F.obj (ψ.hom.app (op U) s) ≠ 0 := by sorry

end AlgebraicGeometry.Scheme
