/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.PicardCanonicalBaseChange

/-! # Tensor pullback square and conjugation

Source: Stacks Project, Tags 0095, 0096, 0097 and 08HY.
(blueprint: lem-sc-picard-tensor-square-conjugacy)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The inverse conjugate of a pushforward square is the tensor pullback square.
Source: Stacks Project, Tags 0095, 0096 and 0097 (tensor formula, adjunction,
and composition), and
08HY (the pushforward square used to define base change).
(blueprint: lem-sc-picard-tensor-square-conjugacy)

Proof: Transport each tensor pullback to ordinary pullback by
`picardTensorComparison`. The conjugate of each comparison is the identity,
by uniqueness of left adjoints. Whiskering these identities and using
`conjugateEquiv_comp` reduces each composition comparison to
`conjugateEquiv_pullbackComp_inv`. For the middle equality comparison,
substitute equal morphisms; its conjugate is the identity and equals the
pushforward equality comparison, as checked on sections. Therefore the
conjugate of the three-factor pullback square is the three-factor pushforward
square. Apply inverse conjugation and evaluate at A. Naturality of
`picardTensorComparison` identifies its whiskered composition component with
`picardTensorCompIso`. The component of the functor equality transport is the
object equality transport. No cartesian assumption or invertibility of the
base-change map is used, and the calculation applies to zero modules and
empty schemes. -/
theorem picardTensorSquareConjugacy
    {X S T X' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
    (g : T ⟶ S) (v : X' ⟶ X) (e : v ≫ f = f' ≫ g) (A : S.Modules) :
    let adj : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), tensorPullback k ⊣ pushforward k :=
      fun k ↦ Classical.choose (exists_tensorPullbackAdjunction k)
    ((conjugateEquiv ((adj f).comp (adj v)) ((adj g).comp (adj f'))).symm
      ((pushforwardComp v f).hom ≫ (pushforwardCongr e).hom ≫
        (pushforwardComp f' g).inv)).app A =
    (picardTensorCompIso f' g A ≪≫
      eqToIso (congrArg (fun k ↦ (tensorPullback k).obj A) e.symm) ≪≫
      (picardTensorCompIso v f A).symm).hom := by sorry

end AlgebraicGeometry.Scheme.Modules
