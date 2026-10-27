/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.AbelianSpacePoincareData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap

/-! # Universal rigidified Picard representations

Source: Stacks Project, quot.tex, Tags 0D28, 0D2B, 0D2C; spaces-perfect.tex, Tag 0E0S;
moduli.tex, Tags 0DNI, 0DNJ (blueprint: def-sfb-rigidified-picard-representation).

The existing pointed-space, axis, and classification constructions apply to arbitrary
pointed families, without requiring a group law or algebraic triviality. Here the
classification includes ALL lines and ALL algebraic-space parameters. SmallModules
is the published equivalent small affine model of the same small etale module category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

open Poincare

variable {S : Scheme.{u}}

/-- The universal rigidified line classifies every line, with arbitrary space parameters.
`Classifies` requires the actual pullback isomorphism to preserve the specified
rigidification, through the canonical pullback compositors. The right axis says that
zero classifies the trivial line, and the intersection equates its two normalizations.
Source: Stacks 0D28, 0D2B, 0D2C; etale descent of line modules over the parameter
(blueprint: def-sfb-rigidified-picard-representation). -/
def RepresentsAllRigidifiedLines {B : AlgebraicSpace S} (A D : Pointed B)
    (U : (product A.p D.p).SmallModules) (rU : Axes A D U) : Prop :=
  IsLine (product A.p D.p) U ∧
    ∀ (T : AlgebraicSpace S) (b : T ⟶ B) (L : (product A.p b).SmallModules),
      IsLine (product A.p b) L →
      ∀ r : (smallModuleTensorPullback (parameterSection A b)).obj L ≅ 𝟙_ T.SmallModules,
        ∃! a : T ⟶ D.X, Classifies A D U rU b L r a

/-- Every automorphism preserving a rigidification is the identity, for space parameters.
Source: Stacks 0D2B; descent on a parameter atlas
(blueprint: def-sfb-rigidified-picard-representation). -/
def AllRigidifiedAutomorphisms {B : AlgebraicSpace S} (A : Pointed B) : Prop :=
  ∀ (T : AlgebraicSpace S) (b : T ⟶ B) (L : (product A.p b).SmallModules),
    IsLine (product A.p b) L →
    ∀ (r : (smallModuleTensorPullback (parameterSection A b)).obj L ≅ 𝟙_ T.SmallModules)
      (v : L ≅ L),
      (smallModuleTensorPullback (parameterSection A b)).map v.hom ≫ r.hom = r.hom →
        v = Iso.refl L

/-- The canonical structure-sheaf map is invertible after every space base change.
In particular this includes every scheme parameter.
Source: Stacks 0E0S (blueprint: def-sfb-rigidified-picard-representation). -/
def UniversalStructureIso {B : AlgebraicSpace S} (A : Pointed B) : Prop :=
  ∀ (T : AlgebraicSpace S) (b : T ⟶ B),
    IsIso (moduleStructureMap (snd A.p b))

/-- Multiplication represents tensor product on rigidified isomorphism classes.
The tensor module is literal. Its rigidification is unique up to rigidified isomorphism:
under UniversalStructureIso, any two rigidifications differ by a unique base unit.
Thus existentially supplying its rigidification specifies the tensor CLASS exactly.
Source: Stacks 0D28 and the group law of 0D2C
(blueprint: def-sfb-rigidified-picard-representation). -/
def PicardTensorLaw (A : Pointed (groupSpaceBase S)) (P : AlgebraicSpace S)
    (G : CommutativeSpaceGroup P)
    (U : (product A.p (groupSpaceProjection P)).SmallModules)
    (rU : Axes A (pointedGroup P G) U) : Prop :=
  ∀ (T : AlgebraicSpace S) (b : T ⟶ groupSpaceBase S)
    (c : T ⟶ product (groupSpaceProjection P) (groupSpaceProjection P))
    (L M : (product A.p b).SmallModules),
    IsLine (product A.p b) L → IsLine (product A.p b) M →
    ∀ (r : (smallModuleTensorPullback (parameterSection A b)).obj L ≅ 𝟙_ T.SmallModules)
      (s : (smallModuleTensorPullback (parameterSection A b)).obj M ≅ 𝟙_ T.SmallModules),
      Classifies A (pointedGroup P G) U rU b L r
          (c ≫ fst (groupSpaceProjection P) (groupSpaceProjection P)) →
      Classifies A (pointedGroup P G) U rU b M s
          (c ≫ snd (groupSpaceProjection P) (groupSpaceProjection P)) →
      ∃ t : (smallModuleTensorPullback (parameterSection A b)).obj (L ⊗ M) ≅
          𝟙_ T.SmallModules,
        Classifies A (pointedGroup P G) U rU b (L ⊗ M) t (c ≫ addition P G)

/-- Arbitrary scheme base change pulls back the universal line and BOTH normalizations.
The pulled-back data again represent all rigidified lines for all space parameters;
comparisons with any other such representation are unique, for spaces and lines.
This includes geometric-point base changes and requires no Noetherianity on T.
Source: Stacks 0D25, 0D28, 0D2B; etale descent of the universal module
(blueprint: def-sfb-rigidified-picard-representation). -/
def AllRigidifiedPicardBaseChange {B : AlgebraicSpace S} (A D : Pointed B)
    (U : (product A.p D.p).SmallModules) (rU : Axes A D U) : Prop :=
  ∀ (T : Over S) (g : schemeSpace T ⟶ B),
    ∃ s : Axes (A.baseChange g) (D.baseChange g)
        ((smallModuleTensorPullback (baseChangeProductMap A D g)).obj U),
      IsBaseChangedAxes A D g U rU s ∧
      RepresentsAllRigidifiedLines (A.baseChange g) (D.baseChange g)
        ((smallModuleTensorPullback (baseChangeProductMap A D g)).obj U) s ∧
      ∀ (E : Pointed (schemeSpace T))
        (V : (product (A.baseChange g).p E.p).SmallModules)
        (rV : Axes (A.baseChange g) E V),
        RepresentsAllRigidifiedLines (A.baseChange g) E V rV →
          Nonempty (DualComparison (A.baseChange g) (D.baseChange g) E
            ((smallModuleTensorPullback (baseChangeProductMap A D g)).obj U) V s rV) ∧
          Subsingleton (DualComparison (A.baseChange g) (D.baseChange g) E
            ((smallModuleTensorPullback (baseChangeProductMap A D g)).obj U) V s rV)

end AlgebraicGeometry.AlgebraicSpace
