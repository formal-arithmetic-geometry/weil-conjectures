/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# The zero sheaf is constructible

A zero sheaf on the small étale site of a scheme `X` is constant, being isomorphic to the
constant sheaf at the zero object; hence it is locally constant. Its stalks are zero, hence
singletons as soon as the forgetful functor of the coefficient category preserves the
terminal object, so it is finite. Being finite locally constant, it is constructible with
respect to the trivial stratification of `X`.

## Main results

- `AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.of_isZero`
- `AlgebraicGeometry.Scheme.IsFiniteSheaf.of_isZero`
- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_isZero`
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_isZero`
  (blueprint: `lemma:constructible-zero`)

-/

@[expose] public section

universe u u'

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}
variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- A zero sheaf is locally constant: it is constant, and a constant sheaf is locally
constant. -/
lemma IsLocallyConstantSheaf.of_isZero {F : Sheaf X.smallEtaleTopology A} (hF : IsZero F) :
    IsLocallyConstantSheaf F :=
  (Sheaf.IsConstant.of_isZero hF).isLocallyConstantSheaf

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [PreservesLimit (Functor.empty.{0} A) (CategoryTheory.forget A)]

/-- A zero sheaf is finite: its stalks are zero, whose underlying types are singletons since
the forgetful functor preserves the terminal object. -/
lemma IsFiniteSheaf.of_isZero {F : Sheaf X.smallEtaleTopology A} (hF : IsZero F) :
    IsFiniteSheaf F where
  finite_sheafFiber Ω _ _ s := by
    have hz : IsZero ((pointSmallEtale s).sheafFiber.obj F) :=
      (pointSmallEtale s).sheafFiber.map_isZero hF
    have hT : IsTerminal ((CategoryTheory.forget A).obj ((pointSmallEtale s).sheafFiber.obj F)) :=
      hz.isTerminal.isTerminalObj (CategoryTheory.forget A)
    have : Unique ((CategoryTheory.forget A).obj ((pointSmallEtale s).sheafFiber.obj F)) :=
      Types.isTerminalEquivUnique _ hT
    exact Finite.of_subsingleton

/-- A zero sheaf is finite locally constant. -/
lemma IsFiniteLocallyConstantSheaf.of_isZero {F : Sheaf X.smallEtaleTopology A}
    (hF : IsZero F) : IsFiniteLocallyConstantSheaf F where
  toIsLocallyConstantSheaf := IsLocallyConstantSheaf.of_isZero hF
  toIsFiniteSheaf := IsFiniteSheaf.of_isZero hF

/-- **A zero sheaf is constructible**, with respect to the trivial stratification of `X`.
(blueprint: `lemma:constructible-zero`) -/
lemma IsConstructibleSheaf.of_isZero {F : Sheaf X.smallEtaleTopology A} (hF : IsZero F) :
    IsConstructibleSheaf F :=
  have := IsFiniteLocallyConstantSheaf.of_isZero hF
  IsFiniteLocallyConstantSheaf.isConstructibleSheaf F

end AlgebraicGeometry.Scheme

end
