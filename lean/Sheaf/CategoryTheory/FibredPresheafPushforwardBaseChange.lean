module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Final

/-! # Presheaf pushforward base change for fibred groupoids

Source: Stacks Project, stacks-sheaves, Tag 075B (lemma-base-change), and
equation-pushforward (blueprint: lem-sfb-fibred-presheaf-pushforward-base-change).

Inverse image is precomposition and direct image is right Kan extension.
Its pointwise limit is the group of compatible families on the test fibre.
The comparison below specifies what it means for the given square to be
2-cartesian, including its specified vertical 2-isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄ t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace CategoryTheory

/-- The comparison to the fibrewise 2-product for a specified square over `Sch/S`.
Its tuple is `(v'(d), a(d), e(d))`; thus being an equivalence expresses precisely
that the specified square is 2-cartesian.
Source: Stacks Project, 075B, lemma-base-change
(blueprint: lem-sfb-fibred-presheaf-pushforward-base-change). -/
def fibredPresheafSquareComparison {S : AlgebraicGeometry.Scheme.{u}}
    {C : BasedCategory.{v₁, w₁} (Over S)} {X : BasedCategory.{v₂, w₂} (Over S)}
    {Y : BasedCategory.{v₃, w₃} (Over S)} {D : BasedCategory.{v₄, w₄} (Over S)}
    (v : BasedFunctor C X) (b : BasedFunctor Y X)
    (a : BasedFunctor D C) (v' : BasedFunctor D Y)
    (e : ModuliTwoIso (v'.comp b) (a.comp v)) :
    D.obj ⥤ (moduliTwoFiberProduct b v).obj where
  obj d := ⟨⟨v'.obj d, a.obj d, e.val.hom.app d⟩,
    ⟨inferInstance, by
      change X.p.IsHomLift (𝟙 (Y.p.obj (v'.toFunctor.obj d))) _
      rw [v'.w_obj]
      exact e.property d⟩⟩
  map f := ObjectProperty.homMk
    { left := v'.map f
      right := a.map f
      w := e.val.hom.naturality f }
  map_id d := by apply ObjectProperty.hom_ext; dsimp; ext <;> simp <;> rfl
  map_comp f g := by apply ObjectProperty.hom_ext; dsimp; ext <;> simp <;> rfl

/-- Canonical underived base change, natural both in the abelian presheaf and
in objects of `Y`, for every specified 2-cartesian square of fibred groupoids.
The equality specifies the canonical map by its compatible-family coordinates.
By `ranObjObjIsoLimit_hom_π`, the counit evaluations below are
exactly the coordinates indexed by `(d, δ : v'(d) → y)`, namely
`(a(d), e(d)⁻¹ ≫ b(δ))` in the test fibre of `v` over `b(y)`.

Source: Stacks Project, 075B, lemma-base-change and equation-pushforward
(blueprint: lem-sfb-fibred-presheaf-pushforward-base-change).

Proof:
1. Present the test fibre over `b(y)` by pairs `(c, α : v(c) → b(y))`.
   The fibred-groupoid cartesian lifting property identifies these with the
   scheme test-fibre triples, with coefficient `N(c)`.
2. For the fibrewise product, its test fibre over `y` consists of tuples
   `(y₀,c,θ,δ)`. Send this to `(c, θ⁻¹ ≫ b(δ))`. Cartesian factorization
   through `δ` gives a unique lift of every arrow between images, hence full
   faithfulness. Lift the base arrow of `α` to `δ`; factor `α` through `b(δ)`.
   Its vertical factor is invertible, giving essential surjectivity.
3. For an arbitrary specified square, compose this test-fibre equivalence with
   the equivalence supplied by its comparison to the fibrewise product.
   Full faithfulness lifts arrows and essential surjectivity transports the
   structural arrow to `y`, so this again is an equivalence of test fibres.
4. Apply lem-weil-pbc-initial-functor-limit to the opposite equivalence.
   Its comma categories have terminal objects by full faithfulness and
   essential surjectivity. Restriction of compatible families is therefore a
   bijection, and it preserves addition since addition is coordinatewise.
5. A coefficient morphism acts coordinatewise and hence commutes with this
   restriction. For `r : y' → y`, the equality
   `θ⁻¹ ≫ b(δ ≫ r) = (θ⁻¹ ≫ b(δ)) ≫ b(r)` proves commutation with all
   presheaf restrictions. The component inverses inherit both naturalities.
6. The right Kan counit evaluates a family at its identity structural arrow;
   precomposing by the displayed structural arrow evaluates at that coordinate.
   Hence the constructed isomorphism satisfies the displayed equation.
   No topology or representability is used. -/
theorem fibredPresheaf_pushforward_baseChange {S : AlgebraicGeometry.Scheme.{u}}
    {C : BasedCategory.{v₁, w₁} (Over S)} {X : BasedCategory.{v₂, w₂} (Over S)}
    {Y : BasedCategory.{v₃, w₃} (Over S)} {D : BasedCategory.{v₄, w₄} (Over S)}
    (v : BasedFunctor C X) (b : BasedFunctor Y X)
    (a : BasedFunctor D C) (v' : BasedFunctor D Y)
    (e : ModuliTwoIso (v'.comp b) (a.comp v))
    (hC : IsFibredInGroupoids C) (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (hD : IsFibredInGroupoids D)
    (hcart : (fibredPresheafSquareComparison v b a v' e).IsEquivalence) :
    ∃ β : v.toFunctor.op.ran ⋙
        (Functor.whiskeringLeft _ _
          AddCommGrpCat.{max v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄ t}).obj b.toFunctor.op ≅
      (Functor.whiskeringLeft _ _
          AddCommGrpCat.{max v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄ t}).obj a.toFunctor.op ⋙
        v'.toFunctor.op.ran,
      ∀ (N : C.objᵒᵖ ⥤ AddCommGrpCat.{max v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄ t})
        (y : Y.obj) (d : D.obj) (δ : v'.obj d ⟶ y),
        (β.hom.app N).app (op y) ≫
            (v'.toFunctor.op.ran.obj (a.toFunctor.op ⋙ N)).map δ.op ≫
            (v'.toFunctor.op.ranCounit.app (a.toFunctor.op ⋙ N)).app (op d) =
          (v.toFunctor.op.ran.obj N).map (e.val.inv.app d ≫ b.map δ).op ≫
            (v.toFunctor.op.ranCounit.app N).app (op (a.obj d)) := by
  sorry

end CategoryTheory
