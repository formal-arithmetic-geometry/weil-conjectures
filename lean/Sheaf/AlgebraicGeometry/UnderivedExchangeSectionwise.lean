/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The section formula for underived étale exchange

Source: blueprint, sec-proper-base-change, sk-def-exchange,
lem-weil-pbc-underived-exchange-sectionwise; Stacks Project, Tags 03Q0, 00VE,
00WH, and 03CB (blueprint: lem-weil-pbc-underived-exchange-sectionwise).

The representative is a left Kan extension generator followed by `toSheafify`.
The theorem evaluates the existing exchange morphism on it, so equality of
sheafified representatives implies equality of their images. It also records
that morphism's prescribed adjunct.
This stage-2 statement is recorded for the sectionwise exchange node.
-/

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
universe u
variable {X' X Y' Y : Scheme.{u}}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
noncomputable section
namespace AlgebraicGeometry
/-- The map `ℓ_a` from `V ×[Y'] X'` to `(W ×[Y] X) ×[X] X'` over `X'`.
Its first coordinate is induced by `a`, its second is the projection to `X'`.
Source: blueprint, sk-def-exchange, lem-weil-pbc-underived-exchange-sectionwise,
second paragraph (blueprint: lem-weil-pbc-underived-exchange-sectionwise). -/
def sectionwiseBaseChangeHom (sq : CommSq g' f' f g) (W : Y.Etale) (V : Y'.Etale)
    (a : V ⟶ g.Etale.obj W) : f'.Etale.obj V ⟶ g'.Etale.obj (f.Etale.obj W) := by
  let p : V.left ⟶ W.left := a.left ≫ pullback.fst W.hom g
  let r : (f'.Etale.obj V).left ⟶ (f.Etale.obj W).left :=
    pullback.lift (pullback.fst V.hom f' ≫ p) (pullback.snd V.hom f' ≫ g') (by
      dsimp [p]
      have ha := a.w
      change a.left ≫ pullback.snd W.hom g = V.hom at ha
      calc
        _ = pullback.fst V.hom f' ≫ (a.left ≫ pullback.snd W.hom g) ≫ g := by
          simp [Category.assoc, pullback.condition]
        _ = pullback.fst V.hom f' ≫ V.hom ≫ g := by rw [ha]
        _ = pullback.snd V.hom f' ≫ f' ≫ g := by simp only [pullback.condition_assoc]
        _ = pullback.snd V.hom f' ≫ g' ≫ f := by rw [sq.w])
  exact MorphismProperty.Over.homMk
    (pullback.lift r (pullback.snd V.hom f') (by
      change r ≫ pullback.snd W.hom f = pullback.snd V.hom f' ≫ g'
      dsimp [r]
      simp))
    (by
      change pullback.lift r (pullback.snd V.hom f') _ ≫
          pullback.snd (f.Etale.obj W).hom g' = pullback.snd V.hom f'
      simp)
/-- The underived exchange map extends the representative rule, with the specified adjunct.
Source: blueprint, sec-proper-base-change, sk-def-exchange,
lem-weil-pbc-underived-exchange-sectionwise; Stacks Project, Tags 03Q0, 00VE, 00WH, 03CB
(blueprint: lem-weil-pbc-underived-exchange-sectionwise).

Proof, following the five steps of the DAG node:
1. Use the finite-limit-preserving étale base-change functor and the presheaf pullback
   of lem-weil-pbc-presheaf-pullback-sets-left-exact. Its value at V is the filtered
   colimit over (W,a); its unit is the coprojection for (W,id). Composing its adjunction
   with def-weil-pbc-sheafification gives exactly the unit after `toSheafify`.
   lem-weil-pbc-etale-inverse-image-algebraic-structures identifies this with the
   abelian inverse-image adjunction, including its underlying unit.
2. Put Q = g'⁻¹ F and B = f'_* Q. For each (W,a), apply the unit at K and restrict
   along ℓ_a. Naturality of the unit says that for h : W₁ → W₂ the value at
   (W₂,a₂,s) equals the value at (W₁,a₁,h* s) when a₂ = b_g(h) a₁, because
   ℓ_a₂ = b_g'(b_f(h)) ℓ_a₁. Thus these group homomorphisms respect the colimit
   relations (def-weil-pbc-category-colimit). Precomposition of a gives naturality
   in V, so they define a presheaf morphism r : P_g(f_*F) → B.
3. B is a sheaf by def-weil-pbc-direct-image. Sheafification gives a unique ψ
   with ψ j = r. This proves independence even for equality only after sheafification.
   At (W,id), the unit description gives the g-adjunct δ of ψ as f_*η_g' followed
   by the canonical identification d : f_*g'_*Q ≅ g_*f'_*Q.
4. Under def-weil-pbc-composite-adjunction the adjunct of ε_f' ∘ f'⁻¹ψ is δ,
   by the triangle identity. The unit-compatible composition isomorphisms of
   lem-weil-pbc-inverse-image-composition identify the adjunct of
   g'⁻¹ε_f ∘ θ with d ∘ f_*g'_*(g'⁻¹ε_f) ∘ f_*η_g' ∘ η_f; their direct-image
   components are the same iterated-fibre-product identification used in step 3.
5. Naturality of η_g' at ε_f changes this last expression to
   d ∘ f_*η_g' ∘ f_*ε_f ∘ η_f = d ∘ f_*η_g' = δ, by the triangle identity.
   Injectivity of the adjunction bijection gives ε_f' ∘ f'⁻¹ψ = g'⁻¹ε_f ∘ θ.
   def-weil-pbc-underived-exchange therefore identifies ψ with `Etale.baseChangeMap`.
   Its generator formula is the first conjunct, and its adjunct is the second. -/
theorem underivedExchangeSectionwise
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (F : Sheaf X.smallEtaleTopology (AddCommGrpCat.{u + 1})) :
    (∀ (V : Y'.Etale) (W : Y.Etale) (a : V ⟶ g.Etale.obj W)
        (s : ((Etale.lowerStar (AddCommGrpCat.{u + 1}) f).obj F).obj.obj (op W)),
      ((Etale.baseChangeMap (AddCommGrpCat.{u + 1}) sq.toCommSq).app F).hom.app (op V)
          ((toSheafify Y'.smallEtaleTopology
            ((MorphismProperty.Over.pullback @Etale ⊤ g).op.leftKanExtension
              (((Etale.lowerStar (AddCommGrpCat.{u + 1}) f).obj F).obj))).app (op V)
            (((MorphismProperty.Over.pullback @Etale ⊤ g).op.leftKanExtension
              (((Etale.lowerStar (AddCommGrpCat.{u + 1}) f).obj F).obj)).map a.op
              (((MorphismProperty.Over.pullback @Etale ⊤ g).op.leftKanExtensionUnit
                (((Etale.lowerStar (AddCommGrpCat.{u + 1}) f).obj F).obj)).app (op W) s))) =
        ((Etale.upperStar (AddCommGrpCat.{u + 1}) g').obj F).obj.map
            (sectionwiseBaseChangeHom sq.toCommSq W V a).op
          (((Etale.upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) g').unit.app F).hom.app
            (op (f.Etale.obj W)) s)) ∧
      (Etale.upperStar (AddCommGrpCat.{u + 1}) f').map
          ((Etale.baseChangeMap (AddCommGrpCat.{u + 1}) sq.toCommSq).app F) ≫
        (Etale.upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) f').counit.app
          ((Etale.upperStar (AddCommGrpCat.{u + 1}) g').obj F) =
      (Etale.squareUpperStarIso (AddCommGrpCat.{u + 1}) sq.toCommSq).hom.app
          ((Etale.lowerStar (AddCommGrpCat.{u + 1}) f).obj F) ≫
        (Etale.upperStar (AddCommGrpCat.{u + 1}) g').map
          ((Etale.upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) f).counit.app F) := by
  sorry
end AlgebraicGeometry
