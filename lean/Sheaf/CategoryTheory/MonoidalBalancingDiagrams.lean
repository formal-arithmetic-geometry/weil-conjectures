/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Strong monoidal transport of balancing and quotient-action diagrams

Source: the current blueprint, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/lem-sfb-extend-to-qlbar-constructible.proof.md,
final clause on restricting extended presentations to strata and pro-étale covers;
Stacks Project, Categories, Tag 0FFL (tensorator naturality and associativity).
(blueprint: lem-sfb-monoidal-balancing-diagrams)
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

/-- A strong monoidal tensorator identifies both balancing arrows for extension along
`φ : R ⟶ S`. It also transports equivariance for multiplication on the first `S` factor
of an arbitrary map `q : S ⊗ M.X ⟶ P.X`. The transported structures are those of
`monObjObj` and `mapMod`; no colimit, braiding or commutativity assumption is needed.
The two comparison isomorphisms are `Monoidal.μIso F S M.X` and the composite of
`whiskerRightIso (Monoidal.μIso F S R) (F.obj M.X)` with
`Monoidal.μIso F (S ⊗ R) M.X`.

Source: the current blueprint, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/lem-sfb-extend-to-qlbar-constructible.proof.md,
final clause on restricting extended presentations; Stacks Project, Categories, Tag 0FFL.
(blueprint: lem-sfb-monoidal-balancing-diagrams)

Proof:
1. The tensorator is an isomorphism by def-sfb-strong-monoidal-functor. Tensor
bifunctoriality (def-sfb-monoidal-category) makes its right whiskering an isomorphism;
the inverse of the displayed composite is the reverse composite of their inverses.
2. Put k = (S tensor φ) followed by multiplication. Naturality at (identity, φ)
and def-sfb-modobj-transport give the transported k as the tensorator followed by F(k).
Naturality at (k, identity) then gives the first balancing-arrow identity.
3. Tensorator associativity at (S, R, M.X), followed by naturality at
(identity, the action of M), gives the second identity using the transported action
of def-sfb-modobj-transport.
4. Write u for (identity tensor the S,M tensorator) followed by the S,(S tensor M)
tensorator, and v for the corresponding left-associated composite at (S, S, M.X).
Associativity gives v followed by F(α) = α followed by u. Cancel the associators
to obtain α inverse followed by v = u followed by F(α inverse).
5. Substitute the transported multiplication and action from def-sfb-modobj-transport.
Tensor bifunctoriality and naturality at (identity, q) turn the left side of the
transported action equation into u followed by F of its original left side.
Naturality at (multiplication, identity) and step 4 turn the right side into u
followed by F of its original right side. The assumed equation for q identifies them.
-/
theorem monoidal_balancing_diagrams
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal]
    {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ]
    (M : Mod C R) :
    ((whiskerRightIso (Monoidal.μIso F S R) (F.obj M.X)) ≪≫
        Monoidal.μIso F (S ⊗ R) M.X).hom ≫
        F.map ((S ◁ φ ≫ μ[S]) ▷ M.X) =
      (F.obj S ◁ F.map φ ≫ μ[F.obj S]) ▷ F.obj M.X ≫
        (Monoidal.μIso F S M.X).hom ∧
    ((whiskerRightIso (Monoidal.μIso F S R) (F.obj M.X)) ≪≫
        Monoidal.μIso F (S ⊗ R) M.X).hom ≫
        F.map ((α_ S R M.X).hom ≫ S ◁ γ[R,M.X]) =
      (α_ (F.obj S) (F.obj R) (F.obj M.X)).hom ≫
        F.obj S ◁ γ[F.obj R,((F.mapMod R).obj M).X] ≫
          (Monoidal.μIso F S M.X).hom ∧
    ∀ (P : Mod C S) (q : S ⊗ M.X ⟶ P.X),
      S ◁ q ≫ γ[S,P.X] = (α_ S S M.X).inv ≫ μ[S] ▷ M.X ≫ q →
      F.obj S ◁ ((Monoidal.μIso F S M.X).hom ≫ F.map q) ≫
          γ[F.obj S,((F.mapMod S).obj P).X] =
        (α_ (F.obj S) (F.obj S) (F.obj M.X)).inv ≫
          μ[F.obj S] ▷ F.obj M.X ≫ (Monoidal.μIso F S M.X).hom ≫ F.map q := by
  sorry

end CategoryTheory.Functor
