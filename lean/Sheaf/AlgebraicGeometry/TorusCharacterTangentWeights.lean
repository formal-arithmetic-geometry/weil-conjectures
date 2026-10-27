/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential

/-! # Character weights on the tangent space of a group scheme

Source: Milne, Algebraic Groups (2017), Section 16i, Proposition 16.64, pp.348--349
(blueprint: def-sfb-torus-character-tangent-weights).

The internal action is Mathlib's `ModObj`. Character weights are tested by the
actual action on dual-number tangent points, rather than by differentiating characters.
For a split torus over an algebraically closed field, its rational points are dense,
so these are the usual character weight spaces. Spans and suprema implement the
subspace underlying the direct sum of weight spaces.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.TorusCharacterTangent

/-- An internal action preserves the group law on every test scheme. Together with
`ModObj` and the inverse in the acting group, this says it acts by group automorphisms.
Source: Milne, Section 16i (blueprint: def-sfb-torus-character-tangent-weights). -/
def ActsByGroupAutomorphisms {F : Type u} [Field F]
    (S H : Grp (Over (Spec (.of F)))) [ModObj S.X H.X] : Prop :=
  ∀ (W : Over (Spec (.of F))) (s : W ⟶ S.X) (x y : W ⟶ H.X),
    s • (x * y) = (s • x) * (s • y)

/-- Stability of a subgroup scheme is stability of its represented subfunctor, on
all test schemes. Source: Milne, Proposition 16.64, p.348
(blueprint: def-sfb-torus-character-tangent-weights). -/
def IsStable {F : Type u} [Field F]
    (S H : Grp (Over (Spec (.of F)))) [ModObj S.X H.X]
    {K : Grp (Over (Spec (.of F)))} (j : K ⟶ H) : Prop :=
  ∀ (W : Over (Spec (.of F))) (s : W ⟶ S.X) (x : W ⟶ K.X),
    ∃ y : W ⟶ K.X, s • (x ≫ j.hom.hom) = y ≫ j.hom.hom

/-- The character eigenspace in the tangent space. A tangent vector is represented
by its actual dual-number point; the character is evaluated at each F-point of S.
For a split torus over algebraically closed F this is precisely its character
weight space. Source: Milne, formula (123), p.348
(blueprint: def-sfb-torus-character-tangent-weights). -/
def weightSpace {F : Type u} [Field F]
    (S H : Grp (Over (Spec (.of F)))) [ModObj S.X H.X]
    (χ : S ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) :
    Submodule F (GrpObj.Lie H.X) :=
  Submodule.span F {v | ∀ s : 𝟙_ (Over (Spec (.of F))) ⟶ S.X,
    (toUnit ((Spec (.of (DualNumber F))).asOver (Spec (.of F))) ≫ s) •
        GrpObj.tangentPoint v =
      GrpObj.tangentPoint
        (((Scheme.ΓSpecIso (.of F)).hom
          ((s ≫ χ.hom.hom).left.appTop
            ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv
              (LaurentPolynomial.T 1)))) • v)}

/-- The positive rational ray of a character, written multiplicatively: positive
integers m,n satisfy χ^m = eta^n. Source: Milne, p.348, definition of (α)
(blueprint: def-sfb-torus-character-tangent-weights). -/
def InPositiveRay {F : Type u} [Field F]
    {S : Grp (Over (Spec (.of F)))}
    (eta χ : S ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) : Prop :=
  ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ χ.hom.hom ^ m = eta.hom.hom ^ n

/-- The subspace underlying the direct sum of the character spaces on the positive
ray. Source: Milne, formula (125), p.348
(blueprint: def-sfb-torus-character-tangent-weights). -/
def positiveRaySpace {F : Type u} [Field F]
    (S H : Grp (Over (Spec (.of F)))) [ModObj S.X H.X]
    (eta : S ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) :
    Submodule F (GrpObj.Lie H.X) :=
  ⨆ (χ : S ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (_ : InPositiveRay eta χ), weightSpace S H χ

end AlgebraicGeometry.TorusCharacterTangent
