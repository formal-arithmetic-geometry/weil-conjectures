/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.RationalRepresentationGZero
public import Sheaf.AlgebraicGeometry.TrivialTorusCoherentData

/-! # Character twists on an arbitrary action scheme

Source: the character-action convention in the agent-formulated concentration input
to Milne, Algebraic Groups (2017), Section 22d, Theorem 22.50, p.480;
Stacks Project, Groupoids, Tag 03LF, for linearizations.
(blueprint: def-sfb-torus-character-gzero-action)

The integral group and character ring are the existing constructions. The predicates
below specify the forward character twist and normalize its action on that group.
They neither choose modules nor replace the underlying Grothendieck group.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.EquivariantCoherent

variable {F : Type u} [Field F]
variable {T : Grp (Over (Spec (.of F)))} {Y : Over (Spec (.of F))} [ModObj T.X Y]

/-- A character twist multiplies the forward linearization by the character evaluated
at the universal group coordinate. The underlying module is unchanged up to isomorphism.
This is tensoring with the one-dimensional representation of the character, with the
geometric action from y to ty, rather than its dual.
Source: Stacks 03LF and the character-action convention in the concentration input to
Milne (2017), Section 22d, Theorem 22.50, p.480
(blueprint: def-sfb-torus-character-gzero-action). -/
def IsCharacterTwist {D : ActionGroupoidModel T.X Y}
    (χ : TrivialTorusCoherent.Character T) (M P : Coherent D) : Prop :=
  ∃ e : underlying P ≅ underlying M,
    (linearization P).inv ≫ (Scheme.Modules.tensorPullback (target T.X Y)).map e.hom =
      (Scheme.Modules.tensorPullback (source T.X Y)).map e.hom ≫
        (linearization M).inv ≫
        ((Scheme.Modules.tensorPullback (target T.X Y)).obj (underlying M)).smulHom
          (TrivialTorusCoherent.characterValue T χ (T.X ⊗ Y) (fst T.X Y))

/-- The integral character-ring action on the existing equivariant coherent group,
normalized on every generator by its forward character twist. Existence of twist
representatives is included, so normalization is not a vacuous condition.
Source: the character-action convention in the concentration input to Milne (2017),
Section 22d, Theorem 22.50, p.480, with linearizations as in Stacks 03LF
(blueprint: def-sfb-torus-character-gzero-action). -/
def IsCharacterAction (D : ActionGroupoidModel T.X Y)
    (m : Module (TrivialTorusCoherent.CharacterRing T) (GZero D)) : Prop :=
  (∀ (χ : TrivialTorusCoherent.Character T) (M : Coherent D),
    ∃ P : Coherent D, IsCharacterTwist χ M P) ∧
    ∀ (χ : TrivialTorusCoherent.Character T) (M P : Coherent D),
      IsCharacterTwist χ M P →
        m.smul (AddMonoidAlgebra.single χ 1) (classOf M) = classOf P

end AlgebraicGeometry.EquivariantCoherent
