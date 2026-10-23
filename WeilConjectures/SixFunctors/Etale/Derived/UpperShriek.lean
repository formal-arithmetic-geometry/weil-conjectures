/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek

/-!

# Derived Upper Shriek

Let `k` be a finite or separably closed field and `Λ` a finite ring whose order is invertible in
`k`. For a morphism `f : X ⟶ Y` of `k`-schemes of finite type admitting a compactification, the
exceptional inverse image `Rf^!` is *constructed* here out of the two halves of the derived lower
shriek `Rf_! = Di_! ⋙ Rg_*` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:

`Rf^! := Rg^! ⋙ Di^*`,

where `Rg^!` is a chosen right adjoint of the derived pushforward `Rg_*` along the *proper*
morphism `g`, and `Di^*` is the levelwise pullback along the open immersion `i`, which is right
adjoint to `Di_!` by `Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction`. The
adjunction `Rf_! ⊣ Rf^!` is then the composite of these two adjunctions.

The only input is that `Rg_*` is a left adjoint for proper `g`. This is the instance
`isLeftAdjoint_rightDerivedLowerStar_of_isProper`, which holds in this setting only. All
categories are unbounded derived categories of étale sheaves of `Λ`-modules.

`Rf^!` is only defined on the unbounded derived categories: it does not preserve bounded
below objects in general, so it does not restrict to `D⁺`.

# Main Results

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isProper` : for `g` proper,
  `Rg_* : D(Z_ét, Λ) ⥤ D(Y_ét, Λ)` is a left adjoint.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactification` : `Rf^!` with respect to
  a compactification `c`, with scoped notation `Rf^!(c)[Λ]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactificationAdjunction` : the
  adjunction `Rf_!(c)[ModuleCat Λ] ⊣ Rf^!(c)[Λ]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriek` : `Rf^! : D(Y_ét, Λ) ⥤ D(X_ét, Λ)` for the
  chosen compactification, with scoped notation `R(f)^![Λ]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` : the adjunction `Rf_! ⊣ Rf^!`.

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` : `Rf_!` is a left adjoint,
  a consequence of the previous item.

## Implementation notes

* `isLeftAdjoint_rightDerivedLowerStar_of_isProper` is `sorry`, but the statement is true. It is
  restricted to finite coefficients over a finite or separably closed field because it is false
  for general coefficients. In the pro-étale setting it fails even for field coefficients: for an
  abelian variety of positive dimension over an algebraically closed field, `Ra_*` does not
  preserve countable coproducts on `D(E_proét, Λ)`.
* `Rg^!` for proper `g` is `Functor.rightAdjoint`, i.e. an arbitrary choice of right adjoint
  extracted from the instance, not a construction. Only the adjunction
  `Adjunction.ofIsLeftAdjoint` should be used about it. The composite `Rf^!` is a construction
  out of it and `Di^*`.
* The derived adjunction `Di_! ⊣ Di^*` goes through the total left derived functor of `i_!`,
  which is why the K-flat hypotheses on `ModuleCat Λ` of
  `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek` are needed for the
  adjunctions of this file, though not for the definition of `Rf^!` itself.
* There is no underived `f^!`, but the notation still carries the `R` of `R(f)_![A]` and
  `R((g)_*[A])`, to mark that it lives on derived categories rather than on sheaves.

## TODO

* The composition `R(f ≫ g)^! ≅ R(g)^! ⋙ R(f)^!`, from the corresponding compatibility
  of `Rf_!`.
* For `f` étale, `Rf^! = f^*`; for `f` proper, `Rf^!` is right adjoint to `Rf_*`.

-/

@[expose] public section

universe u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {k : Type u} [Field k] (Λ : Type (u + 1)) [CommRing Λ]

section Proper

/- The hypotheses are binders of the instance itself, not section variables: an instance proved
by `sorry` does not use them, so as section variables they would be silently dropped. -/

/-- Let `k` be a finite or separably closed field, `Y` a `k`-scheme of finite type, and `Λ` a
finite ring whose order is invertible in `k`. Then for a proper morphism `g : Z ⟶ Y`, the derived
pushforward `Rg_* : D(Z_ét, Λ) ⥤ D(Y_ét, Λ)` on the unbounded derived categories is a left
adjoint. Its right adjoint is the exceptional inverse image `Rg^!` along `g`.

The statement is true; it is `sorry` only because the proof needs more theory. By proper base
change [Stacks, Tag 095T], `Rg_*` has finite cohomological dimension. Over such a field, the
étale sites of `Z` and `Y` have finite `Λ`-cohomological dimension [SGA 4, X, Cor. 4.3 and
Thm. 5.1]. So `Rg_*` preserves coproducts, and Brown representability [Neeman, *Triangulated
categories*, Thm. 8.4.4] gives the right adjoint. -/
instance isLeftAdjoint_rightDerivedLowerStar_of_isProper [Fact (Finite k ∨ IsSepClosed k)]
    [Finite Λ] [Fact (IsUnit (Nat.card Λ : k))] {Z : Scheme.{u}} {Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (g : Z ⟶ Y.left) [IsProper g] :
    ((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor.IsLeftAdjoint :=
  sorry

end Proper

variable [Fact (Finite k ∨ IsSepClosed k)] [Finite Λ] [Fact (IsUnit (Nat.card Λ : k))]

section OfCompactification

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

/-- The exceptional inverse image `Rf^! : D(Y_ét, Λ) ⥤ D(X_ét, Λ)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of a morphism `f` of `k`-schemes of finite type, on the unbounded derived
categories of étale sheaves of `Λ`-modules. It is a chosen right adjoint `Rg^!` of the derived
pushforward `Rg_*` along the proper `g`, followed by the levelwise pullback `Di^*` along the open
immersion `i`. -/
noncomputable def rightDerivedUpperShriekOfCompactification :
    DerivedCategory (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ((c.g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor.rightAdjoint ⋙
    D((c.i)^*[ModuleCat.{u + 1} Λ])

@[inherit_doc rightDerivedUpperShriekOfCompactification]
scoped notation "Rf^!("c")[" Λ "]" =>
  rightDerivedUpperShriekOfCompactification Λ c

end OfCompactification

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  (f : X ⟶ Y) [HasCompactification f.left]

section Unbounded

/-- The exceptional inverse image `Rf^! : D(Y_ét, Λ) ⥤ D(X_ét, Λ)` along a morphism `f` of
`k`-schemes of finite type admitting a compactification, on the unbounded derived categories of
étale sheaves of `Λ`-modules. It is the functor `rightDerivedUpperShriekOfCompactification`
attached to the chosen compactification `HasCompactification.compactification f.left`. -/
noncomputable def rightDerivedUpperShriek :
    DerivedCategory (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  Rf^!(HasCompactification.compactification f.left)[Λ]

@[inherit_doc rightDerivedUpperShriek]
scoped notation "R(" f ")^![" Λ "]" =>
  rightDerivedUpperShriek Λ f

lemma rightDerivedUpperShriek_eq : R(f)^![Λ] =
    Rf^!(HasCompactification.compactification f.left)[Λ] := rfl

end Unbounded

section Adjunction

/- The K-flat resolution package on `ModuleCat Λ`, needed for the derived adjunction
`Di_! ⊣ Di^*` along the open immersion of a compactification, see
`Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction`. -/
variable [MonoidalCategory (ModuleCat.{u + 1} Λ)] [MonoidalPreadditive (ModuleCat.{u + 1} Λ)]
  [SymmetricCategory (ModuleCat.{u + 1} Λ)] [MonoidalClosed (ModuleCat.{u + 1} Λ)]
  [Abelian.HasFunctorialFlatResolution (ModuleCat.{u + 1} Λ)]

/-- The adjunction `Rf_! ⊣ Rf^!` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
the composite of the derived adjunction `Di_! ⊣ Di^*` along the open immersion `i` and of the
adjunction `Rg_* ⊣ Rg^!` along the proper `g`. -/
noncomputable def rightDerivedUpperShriekOfCompactificationAdjunction {f : X ⟶ Y}
    (c : Compactification f.left) :
    Rf_!(c)[ModuleCat.{u + 1} Λ] ⊣ Rf^!(c)[Λ] :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) c.i).comp
    (Adjunction.ofIsLeftAdjoint _)

/-- The adjunction `Rf_! ⊣ Rf^!` on the unbounded derived categories of étale sheaves of
`Λ`-modules. -/
noncomputable def rightDerivedUpperShriekAdjunction :
    R(f.left)_![ModuleCat.{u + 1} Λ] ⊣ R(f)^![Λ] :=
  rightDerivedUpperShriekOfCompactificationAdjunction Λ
    (HasCompactification.compactification f.left)

/-- The derived lower shriek `Rf_! : D(X_ét, Λ) ⥤ D(Y_ét, Λ)` is a left adjoint, its right
adjoint being `R(f)^![Λ]`. -/
instance isLeftAdjoint_rightDerivedLowerShriek :
    (R(f.left)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint :=
  (rightDerivedUpperShriekAdjunction Λ f).isLeftAdjoint

instance : (R(f)^![Λ]).IsRightAdjoint :=
  (rightDerivedUpperShriekAdjunction Λ f).isRightAdjoint

end Adjunction

end Etale

end AlgebraicGeometry
