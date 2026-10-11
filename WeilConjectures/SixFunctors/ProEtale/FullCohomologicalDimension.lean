/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint

/-!
# The cohomological-dimension bound on the étale-origin class

Let `k` be separably closed, `p : X̄ ⟶ Y` a proper morphism of `k`-schemes locally of finite type
with `dim X̄ ≤ d`, and `Λ` a finite ring. For every base change `p' : X'' ⟶ Y''` of `p` and every
étale sheaf `F` of `Λ`-modules on `X''`, the pro-étale higher direct images
`H^r(Rp'_{proét,*} ν^* F)` vanish for `r > 2d`
(`AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_comparisonUpperStar`,
blueprint `sk-prop-sf-fullcd-etale-origin`). The comparison `ν^* Rp'_{ét,*} ≅ Rp'_{proét,*} ν^*`
reduces this to the étale statement
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isPullback_of_isProper`.

This is the uniform bound `FullCD(p, Λ; 2d)` of blueprint `sk-def-sf-admissible` *restricted to
the sheaves of étale origin*, the essential image `AlgebraicGeometry.ProEtale.etaleOrigin` of the
comparison pullback `ν^*` (blueprint `def-sf-fullcd-used-class`); the unrestricted bound fails
(blueprint `sk-rem-sf-fullcd-scope`).

## Main definitions

- `AlgebraicGeometry.ProEtale.etaleOrigin`: the pro-étale sheaves of étale origin.
- `AlgebraicGeometry.ProEtale.HasCohomologicalDimensionLEOnEtaleOrigin`: the class-restricted
  bound `FullCD_cls(p, A; c)` of blueprint `def-sf-fullcd-class`.

## Main statements

- `AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_comparisonUpperStar`:
  blueprint `sk-prop-sf-fullcd-etale-origin`.
- `AlgebraicGeometry.ProEtale.etaleOrigin_upperStar_obj`: blueprint
  `lem-sf-fullcd-class-restriction`.
- `AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedComparisonLowerStar`: blueprint
  `prop-sf-comparison-bound-zero`.
- `AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_of_etaleOrigin`: blueprint
  `thm-sf-fullcd-etale-origin`.
- `AlgebraicGeometry.ProEtale.hasCohomologicalDimensionLEOnEtaleOrigin`: blueprint
  `thm-sf-fullcd-class`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

/-- Blueprint `sk-prop-sf-fullcd-etale-origin`: `FullCD` on the étale-origin class

**The cohomological-dimension bound on the étale-origin class.** Let `k` be separably closed,
let `p : X' ⟶ Y` be a proper morphism of finite-type `k`-schemes with `dim X' ≤ d`, and let
`Λ` be a finite coefficient ring whose exponent is invertible on `X'` — so that every sheaf of
`Λ`-modules is torsion, which is the first line of the blueprint proof. Then for every étale
sheaf `F` of `Λ`-modules on any base change `X''` of `X'`,

`H^r(Rp'_{proét,*} ν_{X''}^* F) = 0` for `r > 2d`.

Quantifying over the base changes is what turns the statement into the bound
`HasUniformCohomologicalDimensionLE` restricted to the essential image of `ν^*`. This is *not*
clause (1) of `HasAmbientExceptionalRightAdjoint`, which quantifies over all pro-étale sheaves
and fails in general (see `sk-rem-sf-fullcd-scope`); what it supports is the constructible
`Rf^!` on the étale-origin class.

The proof follows the blueprint: the comparison
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso'` identifies
`Rp'_{proét,*} ν^* F` with `ν^* Rp'_{ét,*} F`, `ν^*` is exact, and the étale higher direct
images vanish above `2d` (`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isPullback_of_isProper`).
The invertibility of the exponent of `Λ` is not used. -/
theorem isZero_homology_rightDerivedLowerStar_comparisonUpperStar (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k] {X' Y : Scheme.{u}}
    (p : X' ⟶ Y) [IsProper p] (aX' : X' ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX'] [LocallyOfFiniteType aY] (hp : p ≫ aY = aX')
    [HasInvertibleExponent Λ X'] (d : ℕ) (hd : topologicalKrullDim X' ≤ (d : WithBot ℕ∞))
    {X'' Y'' : Scheme.{u}} (g' : X'' ⟶ X') (p' : X'' ⟶ Y'') (g : Y'' ⟶ Y)
    (sq : IsPullback g' p' p g)
    (F : Sheaf X''.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (r : ℤ) (hr : (2 * d : ℤ) < r) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
      ((R((p')_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X'').obj F)))) := by
  have : IsProper p' := MorphismProperty.of_isPullback sq.flip inferInstance
  have hvan := Etale.isZero_higherDirectImage_of_isPullback_of_isProper Λ p aX' aY hp d hd sq F r hr
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
  refine IsZero.of_iso (Functor.map_isZero (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y'') hvan)
    ((_root_.DerivedCategory.homologyFunctor _ r).mapIso
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p').rightDerivedFunctor.mapIso
        (((comparisonUpperStar (ModuleCat.{u + 1} Λ) X'').mapDerivedCategorySingleFunctor
          0).app F).symm ≪≫
        ((rightDerivedLowerStarComparisonIso' p' (ModuleCat.{u + 1} Λ)).app K).symm) ≪≫
      (((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y'').mapDerivedCategoryHomologyFunctorIso
        r).app _).symm)

section EtaleOrigin

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Blueprint `def-sf-fullcd-used-class`: The coefficient class of the blueprint.

A sheaf on the small pro-étale site of `X` is *of étale origin* if it is isomorphic to `ν^* G` for
a sheaf `G` on the small étale site of `X`: the essential image of the comparison pullback. By
blueprint `lem-sf-proetale-constructible-origin` this class contains the constructible pro-étale
sheaves at a finite coefficient ring. -/
abbrev etaleOrigin (X : Scheme.{u}) : ObjectProperty (Sheaf (Scheme.ProEt.topology X) A) :=
  (comparisonUpperStar A X).essImage

variable {A} in
/-- Blueprint `lem-sf-fullcd-class-restriction`: The coefficient class is stable under
restriction to a pro-étale base change.

The pullback `q^* F` of a sheaf `F` of étale origin along any morphism `q : X' ⟶ X` is again of
étale origin: `q^* ν_X^* G ≅ ν_{X'}^* q^* G`
(`AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso`). The blueprint states this
for the projection `q : X̄ ×_Y V ⟶ X̄` of a base change along an object `V` of `Y_proét`, and
the same argument is the stability under inverse image of blueprint `thm-sf-fullcd-used-class`. -/
lemma etaleOrigin_upperStar_obj {X X' : Scheme.{u}} (q : X' ⟶ X)
    {F : Sheaf (Scheme.ProEt.topology X) A} (hF : etaleOrigin A X F) :
    etaleOrigin A X' ((ProEtale.upperStar A q).obj F) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  exact ⟨(Etale.upperStar A q).obj G,
    ⟨((comparisonUpperStarCompUpperStarIso A q).app G).symm ≪≫ (ProEtale.upperStar A q).mapIso e⟩⟩

/-- Blueprint `def-sf-fullcd-class`: The class-restricted full cohomological-dimension datum.

`FullCD_cls(p, A; c)` holds for `p : X ⟶ Y` if `H^r(Rp_* F) = 0` for every `r > c` and every
pro-étale sheaf `F` of étale origin on `X`, and the same holds after every base change along an
object `V` of `Y_proét`, for the restriction `g'^* F` of `F` to the base-changed source (which is
again of étale origin, `AlgebraicGeometry.ProEtale.etaleOrigin_upperStar_obj`). This is
`AlgebraicGeometry.ProEtale.HasUniformCohomologicalDimensionLE` with the quantifier over all
sheaves restricted to the sheaves of étale origin. -/
def HasCohomologicalDimensionLEOnEtaleOrigin {X Y : Scheme.{u}} (p : X ⟶ Y) (c : ℕ) : Prop :=
  (∀ F : Sheaf (Scheme.ProEt.topology X) A, etaleOrigin A X F → ∀ r : ℤ, (c : ℤ) < r →
    IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
      ((R((p)_*[A])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ∧
  ∀ (V : Y.ProEt) ⦃X' : Scheme.{u}⦄ (g' : X' ⟶ X) (p' : X' ⟶ V.left),
    IsPullback g' p' p V.hom → ∀ F : Sheaf (Scheme.ProEt.topology X) A, etaleOrigin A X F →
      ∀ r : ℤ, (c : ℤ) < r →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
          ((R((p')_*[A])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((ProEtale.upperStar A g').obj F))))

end EtaleOrigin

section Bound

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `prop-sf-comparison-bound-zero`: The comparison bound on coefficients of étale
origin is `M = 0`.

For every étale sheaf `G` of `Λ`-modules on `X` (no constructibility needed),
`R^q ν_* (ν^* G) = 0` for `q > 0`. The first assertion of the blueprint, that the unit
`G ⟶ ν_* ν^* G` is an isomorphism, is
`AlgebraicGeometry.ProEtale.isIso_comparisonAdjunction_unit`; the vanishing is its derived form
`G ≅ Rν_* ν^* G` (Bhatt–Scholze, Corollary 5.1.6,
`AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_unit_app`). -/
theorem isZero_homology_rightDerivedComparisonLowerStar (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (hq : 0 < q) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R(ν_*(X)[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj G)))) := by
  let M := (_root_.DerivedCategory.singleFunctor _ 0).obj G
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) X M ⟨0, inferInstance⟩
  refine IsZero.of_iso (_root_.DerivedCategory.isZero_of_isLE M 0 q hq)
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((R(ν_*(X)[ModuleCat.{u + 1} Λ])).mapIso
        (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app G).symm ≪≫
        (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app M)).symm))

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k] {X Y : Scheme.{u}} (p : X ⟶ Y)
  [IsProper p] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [LocallyOfFiniteType aY] (hp : p ≫ aY = aX) [HasInvertibleExponent Λ X] (d : ℕ)
  (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))

include hp hd in
/-- Blueprint `thm-sf-fullcd-etale-origin`: FullCD for coefficients of étale origin.

Let `k` be separably closed, `p : X ⟶ Y` a proper morphism of finite-type `k`-schemes with
`dim X ≤ d`, and `F` a pro-étale sheaf of `Λ`-modules of étale origin on `X`. Then
`H^r(Rp_* F) = 0` for `r > 2d`, and the same holds for the base change of `p` along every object
`V` of `Y_proét`, applied to the restriction of `F`. The blueprint asks this for the base changes
whose source has dimension at most `d`; it holds for all of them, as
`AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_comparisonUpperStar` allows
base change along an arbitrary morphism. -/
theorem isZero_homology_rightDerivedLowerStar_of_etaleOrigin
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hF : etaleOrigin (ModuleCat.{u + 1} Λ) X F) (r : ℤ) (hr : (2 * d : ℤ) < r) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
      ((R((p)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ∧
    ∀ (V : Y.ProEt) ⦃X' : Scheme.{u}⦄ (g' : X' ⟶ X) (p' : X' ⟶ V.left),
      IsPullback g' p' p V.hom →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
          ((R((p')_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').obj F)))) := by
  have key {X' Y' : Scheme.{u}} (g' : X' ⟶ X) (p' : X' ⟶ Y') (g : Y' ⟶ Y)
      (sq : IsPullback g' p' p g) {F' : Sheaf (Scheme.ProEt.topology X') (ModuleCat.{u + 1} Λ)}
      (hF' : etaleOrigin (ModuleCat.{u + 1} Λ) X' F') :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
        ((R((p')_*[ModuleCat.{u + 1} Λ])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F'))) := by
    obtain ⟨G, ⟨e⟩⟩ := hF'
    exact IsZero.of_iso (isZero_homology_rightDerivedLowerStar_comparisonUpperStar Λ p aX aY hp d
      hd g' p' g sq G r hr)
      ((_root_.DerivedCategory.homologyFunctor _ r).mapIso ((R((p')_*[ModuleCat.{u + 1} Λ])).mapIso
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso e.symm)))
  exact ⟨key (𝟙 X) p (𝟙 Y) (IsPullback.of_id_fst (f := p)) hF,
    fun V X' g' p' sq ↦ key g' p' V.hom sq (etaleOrigin_upperStar_obj g' hF)⟩

include hp hd in
/-- Blueprint `thm-sf-fullcd-class`: The blueprint's coefficient class supplies the restricted
datum, with `c = 2 dim X̄`.

For `p : X ⟶ Y` proper between finite-type `k`-schemes, `k` separably closed and `dim X ≤ d`, the
class-restricted bound `FullCD_cls(p, Λ; 2d)` holds. This is
`AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_of_etaleOrigin`; the
comparison bound on the class is `M = 0`
(`AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedComparisonLowerStar`), so the residual
`2d` is the étale direction. -/
theorem hasCohomologicalDimensionLEOnEtaleOrigin :
    HasCohomologicalDimensionLEOnEtaleOrigin (ModuleCat.{u + 1} Λ) p (2 * d) :=
  ⟨fun F hF r hr ↦ (isZero_homology_rightDerivedLowerStar_of_etaleOrigin Λ p aX aY hp d hd F hF r
      (by exact_mod_cast hr)).1,
    fun V _ g' p' sq F hF r hr ↦ (isZero_homology_rightDerivedLowerStar_of_etaleOrigin Λ p aX aY
      hp d hd F hF r (by exact_mod_cast hr)).2 V g' p' sq⟩

end Bound

end ProEtale

end AlgebraicGeometry
