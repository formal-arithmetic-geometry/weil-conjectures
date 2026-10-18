/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Equivalence

/-!
# Internal-Hom cancellation by an invertible tensor factor

Source: Stacks Project, Categories, Tags 0FFM and 0GWJ; their evaluation-normalized
consequence (blueprint: lem-sf-invertible-factor-hom-cancellation).

## Main definitions

- `CategoryTheory.MonoidalClosed.ihomTensorBoth`: simultaneous tensoring of the two arguments.

## Main statements

- `CategoryTheory.MonoidalClosed.invertibleFactorHomCancellation`: the two canonical
  transposes are isomorphisms, with variable naturality, factor compatibility, and the
  evaluation equations for their forward and inverse maps.

Mathlib places the argument of internal Hom on the left of evaluation. The evaluation
`[X,Y] ⊗ X ⟶ Y` of Tag 0GWJ is therefore `(β_ _ X).hom ≫ (ihom.ev X).app Y`.
The same symmetry transports the chosen adjunction to tensoring on the right. No
additional choice of internal Hom or evaluation is made here.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C]

/-- Simultaneous tensoring `[X,Y] ⟶ [X ⊗ J,Y ⊗ J]`, defined by transposing evaluation
with an identity on `J`. Source: Stacks Project, Tags 0FFM and 0GWJ
(blueprint: lem-sf-invertible-factor-hom-cancellation).
This construction uses no inverse-factor data. The braiding moves `J` past `[X,Y]`,
and the associators put `X` and `[X,Y]` next to one another for evaluation. -/
noncomputable def ihomTensorBoth (X Y J : C) :
    (ihom X).obj Y ⟶ (ihom (X ⊗ J)).obj (Y ⊗ J) :=
  curry ((α_ X J ((ihom X).obj Y)).hom ≫
    X ◁ (β_ J ((ihom X).obj Y)).hom ≫
    (α_ X ((ihom X).obj Y) J).inv ≫ (ihom.ev X).app Y ▷ J)

/-- Internal-Hom cancellation by an invertible tensor factor, with both forward and inverse
maps normalized by evaluation. Source: Stacks Project, Tags 0FFM and 0GWJ
(blueprint: lem-sf-invertible-factor-hom-cancellation).

The witnesses `t` and `s` are uniquely determined by the first conjunct, so these are
specified canonical isomorphisms, not arbitrary representing-object comparisons.
The cancellation isomorphism in the node is `(s X Y).symm`.

Proof plan:
1. Tensoring on the right with `J` and with `I` gives quasi-inverse functors. The composites
   are identified with the identity by the associator, `a` or `b`, and the right unitor.
   Naturality follows from the monoidal axioms; no triangle law on `a` and `b` is needed.
2. Apply `lem-sf-quasi-inverse-hom-bijection`, represented by `Equivalence.mk` and
   `Equivalence.fullyFaithfulFunctor.map_bijective`. Tensoring with `J` is fully faithful,
   and every object is isomorphic to `(Z ⊗ I) ⊗ J`.
3. Define the transposes using the closed adjunction. The first is the existing
   `ihomTensorToIhom`; the second is `ihomTensorBoth`. Uncurrying gives the two evaluation
   equations, with the right evaluation obtained by symmetry as above.
4. Test the first map on `W ⊗ J`. A map into `[X,Y] ⊗ J` uniquely equals `h ▷ J`.
   Transpose `h`, tensor with `J`, then interchange `J` and `X` using the braiding.
   Each operation is bijective, so postcomposition with this particular first map is
   bijective on these test objects.
5. Transport along `(Z ⊗ I) ⊗ J ≅ Z` to get bijectivity for every test object. Taking
   the test object to be the target gives a right inverse; injectivity at the source
   makes it also a left inverse. Thus the first map is an isomorphism.
6. For the second map, postcomposition is the chain of bijections given by transposition,
   tensoring both source and target with `J`, reassociation, and transposition back.
   The same isomorphism test proves it invertible.
7. Uncurry the two variable-naturality identities. Both sides agree by evaluation
   naturality, braiding naturality, and associator naturality. Transposition is injective.
8. For `z : J ≅ J'`, uncurry the factor-compatibility identities. The first follows from
   braiding naturality. The second uses `z.inv` in the contravariant argument and `z.hom`
   in the covariant argument; their composite cancels. The definitions do not use `a,b`.
9. Compose the defining evaluation equations with the inverse maps to obtain the inverse
   evaluation equations. Multiply the variable and factor naturality identities by
   inverses to obtain the corresponding compatibilities for the inverse isomorphisms.
-/
theorem invertibleFactorHomCancellation (J I : C)
    (a : J ⊗ I ≅ 𝟙_ C) (b : I ⊗ J ≅ 𝟙_ C) :
    ∃ (t : ∀ X Y : C, (ihom X).obj Y ⊗ J ≅ (ihom X).obj (Y ⊗ J))
      (s : ∀ X Y : C, (ihom X).obj Y ≅ (ihom (X ⊗ J)).obj (Y ⊗ J)),
      (∀ X Y : C, (t X Y).hom = ihomTensorToIhom X Y J ∧
        (s X Y).hom = ihomTensorBoth X Y J) ∧
      (∀ X Y : C,
        (t X Y).hom ▷ X ≫ (β_ ((ihom X).obj (Y ⊗ J)) X).hom ≫
            (ihom.ev X).app (Y ⊗ J) =
          (α_ ((ihom X).obj Y) J X).hom ≫
            (ihom X).obj Y ◁ (β_ J X).hom ≫ (α_ ((ihom X).obj Y) X J).inv ≫
            ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y) ▷ J ∧
        (s X Y).hom ▷ (X ⊗ J) ≫
            (β_ ((ihom (X ⊗ J)).obj (Y ⊗ J)) (X ⊗ J)).hom ≫
            (ihom.ev (X ⊗ J)).app (Y ⊗ J) =
          (α_ ((ihom X).obj Y) X J).inv ≫
            ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y) ▷ J ∧
        (t X Y).inv ▷ X ≫ (α_ ((ihom X).obj Y) J X).hom ≫
            (ihom X).obj Y ◁ (β_ J X).hom ≫ (α_ ((ihom X).obj Y) X J).inv ≫
            ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y) ▷ J =
          (β_ ((ihom X).obj (Y ⊗ J)) X).hom ≫ (ihom.ev X).app (Y ⊗ J) ∧
        (s X Y).inv ▷ (X ⊗ J) ≫ (α_ ((ihom X).obj Y) X J).inv ≫
            ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y) ▷ J =
          (β_ ((ihom (X ⊗ J)).obj (Y ⊗ J)) (X ⊗ J)).hom ≫
            (ihom.ev (X ⊗ J)).app (Y ⊗ J)) ∧
      (∀ (X X' Y Y' : C) (f : X' ⟶ X) (g : Y ⟶ Y'),
        ((pre f).app Y ≫ (ihom X').map g) ▷ J ≫ (t X' Y').hom =
          (t X Y).hom ≫ (pre f).app (Y ⊗ J) ≫ (ihom X').map (g ▷ J) ∧
        ((pre f).app Y ≫ (ihom X').map g) ≫ (s X' Y').hom =
          (s X Y).hom ≫ (pre (f ▷ J)).app (Y ⊗ J) ≫
            (ihom (X' ⊗ J)).map (g ▷ J) ∧
        ((pre f).app (Y ⊗ J) ≫ (ihom X').map (g ▷ J)) ≫ (t X' Y').inv =
          (t X Y).inv ≫ ((pre f).app Y ≫ (ihom X').map g) ▷ J ∧
        ((pre (f ▷ J)).app (Y ⊗ J) ≫ (ihom (X' ⊗ J)).map (g ▷ J)) ≫
            (s X' Y').inv =
          (s X Y).inv ≫ (pre f).app Y ≫ (ihom X').map g) ∧
      (∀ (X Y J' : C) (z : J ≅ J'),
        (ihom X).obj Y ◁ z.hom ≫ ihomTensorToIhom X Y J' =
          (t X Y).hom ≫ (ihom X).map (Y ◁ z.hom) ∧
        ihomTensorBoth X Y J' =
          (s X Y).hom ≫ (pre (X ◁ z.inv)).app (Y ⊗ J) ≫
            (ihom (X ⊗ J')).map (Y ◁ z.hom)) := by
  sorry

end CategoryTheory.MonoidalClosed
