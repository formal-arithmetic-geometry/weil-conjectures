/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedInverseImageComposition
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

/-!
# Identity and pasting laws of derived square isomorphisms

Source: Stacks Project, Remarks 0E46 and 0E47
(blueprint: lem-weil-pbc-derived-square-iso-pasting).

The node's closing sentence (the same three identities for the sheaf-level square isomorphisms
`AlgebraicGeometry.Etale.squareUpperStarIso`) is stated in the source repository by
`AlgebraicGeometry.Etale.squareUpperStarIso_id`, `squareUpperStarIso_paste_horiz_hom` and
`squareUpperStarIso_paste_vert_hom` (`WeilConjectures.SixFunctors.BaseChange.Pasting`,
`.DerivedPasting`; node lem-weil-pbc-square-iso-pasting) and is not restated here.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Identity, horizontal pasting and vertical pasting of derived square comparisons.
Source: Stacks Project, Remarks 0E46 and 0E47
(blueprint: lem-weil-pbc-derived-square-iso-pasting).

Proof: Step 1 uses lem-weil-pbc-square-iso-pasting for the sheaf identities and applies
these maps termwise. Step 2 uses the localization factorization comparisons of
def-weil-pbc-derived-square-iso and lem-weil-pbc-derived-inverse-image-composition:
lifting respects composition, inverses and both whiskerings by naturality.
Step 3 identifies the two sides on every localized complex with the same termwise map.
Step 4 uses lem-weil-pbc-localization-universal-property to descend equality.
Step 5 restricts to the full bounded-below subcategories. -/
theorem derivedSquareIsoPasting :
    let A := AddCommGrpCat.{u + 1}
    let P := fun {S T : Scheme.{u}} (q : S ⟶ T) => (upperStar A q).mapDerivedCategoryPlus
    let θ := fun {S T S' T' : Scheme.{u}} {a : S' ⟶ S} {b : S' ⟶ T'}
        {c : S ⟶ T} {d : T' ⟶ T} (sq : CommSq a b c d) => pullbackSquareComparison A sq
    let c := fun {R S T : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ R) =>
      (upperStarCompDerivedPlus A a b).symm
    let i := fun S : Scheme.{u} => upperStarIdDerivedPlus A S
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)),
      (θ (IsPullback.id_horiz f).toCommSq).hom.app K =
        (P f).map ((i Y).hom.app K) ≫ (i X).inv.app ((P f).obj K)) ∧
    (∀ {X Y X' Y' X'' Y'' : Scheme.{u}}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
        {f'' : X'' ⟶ Y''} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
        (sq₁ : IsPullback g' f' f g) (sq₂ : IsPullback h' f'' f' h)
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)),
      (P f'').map ((c h g).hom.app K) ≫
          (θ (sq₂.paste_horiz sq₁).toCommSq).hom.app K =
        (θ sq₂.toCommSq).hom.app ((P g).obj K) ≫
          (P h').map ((θ sq₁.toCommSq).hom.app K) ≫
          (c h' g').hom.app ((P f).obj K)) ∧
    (∀ {X Y X' Y' W W' : Scheme.{u}}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
        {e : W ⟶ X} {e' : W' ⟶ X'} {g'' : W' ⟶ W}
        (sq₁ : IsPullback g' f' f g) (sq₃ : IsPullback g'' e' e g')
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)),
      (c e' f').hom.app ((P g).obj K) ≫
          (θ (sq₃.paste_vert sq₁).toCommSq).hom.app K =
        (P e').map ((θ sq₁.toCommSq).hom.app K) ≫
          (θ sq₃.toCommSq).hom.app ((P f).obj K) ≫
          (P g'').map ((c e f).hom.app K)) := by
  sorry

end AlgebraicGeometry.Etale
