/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DensePoints
public import WeilConjectures.ConstructibleSheaf.GenericConstancy

/-!
# Descent of finite locally constant sheaves along surjective étale morphisms

Let `u : U ⟶ T` be surjective and étale. A geometric point of `T` lifts to `U`: its base change
along `u` is a nonempty étale scheme over a separably closed field, which has a rational point
(`AlgebraicGeometry.Scheme.exists_comp_eq_of_etale_of_surjective`). Since `u` is moreover a
one-member étale cover of `T`, a sheaf `G` on `T` is finite locally constant as soon as `u^* G`
is (`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_upperStar_of_etale`).
-/

@[expose] public section

universe u u'

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {U T : Scheme.{u}} (u : U ⟶ T) [Etale u] [Surjective u]

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

end AlgebraicGeometry.Scheme
