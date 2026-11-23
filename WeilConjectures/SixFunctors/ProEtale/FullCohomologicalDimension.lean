/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint

/-!
# The cohomological-dimension bound on the étale-origin class

Let `k` be separably closed, `p : X̄ ⟶ Y` a proper morphism of `k`-schemes locally of finite type
with `dim X̄ ≤ d`, and `Λ` a finite ring. For every base change `p' : X'' ⟶ Y''` of `p` and every
étale sheaf `F` of `Λ`-modules on `X''`, the pro-étale higher direct images
`H^r(Rp'_{proét,*} ν^* F)` vanish for `r > 2d`
(`AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_comparisonUpperStar`). The
comparison `ν^* Rp'_{ét,*} ≅ Rp'_{proét,*} ν^*` reduces this to the étale statement
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isPullback_of_isProper`.

This is the uniform bound `FullCD(p, Λ; 2d)` *restricted to the sheaves of étale origin*, the
essential image `AlgebraicGeometry.ProEtale.etaleOrigin` of the comparison pullback `ν^*`; the
unrestricted bound fails.

## Main definitions

- `AlgebraicGeometry.ProEtale.etaleOrigin`: the pro-étale sheaves of étale origin.
- `AlgebraicGeometry.ProEtale.HasCohomologicalDimensionLEOnEtaleOrigin`: the class-restricted
  bound `FullCD_cls(p, A; c)`.

## Main statements

- `AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_comparisonUpperStar`:
  `FullCD` on the étale-origin class.
- `AlgebraicGeometry.ProEtale.etaleOrigin_upperStar_obj`: the étale-origin class is stable under
  pullback.
- `AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedComparisonLowerStar`: the comparison
  bound on coefficients of étale origin.
- `AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_of_etaleOrigin`: the bound
  for coefficients of étale origin.
- `AlgebraicGeometry.ProEtale.hasCohomologicalDimensionLEOnEtaleOrigin`: the class-restricted
  bound.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

/-- **The cohomological-dimension bound on the étale-origin class.** Let `k` be separably closed,
let `p : X' ⟶ Y` be a proper morphism of finite-type `k`-schemes with `dim X' ≤ d`, and let
`Λ` be a finite coefficient ring whose exponent is invertible on `X'`. Then for every étale
sheaf `F` of `Λ`-modules on any base change `X''` of `X'`,
`H^r(Rp'_{proét,*} ν_{X''}^* F) = 0` for `r > 2d`. -/
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
  have : IsProper p' := MorphismProperty.of_isPullback sq inferInstance
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

/-- The coefficient class of étale origin.

A sheaf on the small pro-étale site of `X` is *of étale origin* if it is isomorphic to `ν^* G` for
a sheaf `G` on the small étale site of `X`: the essential image of the comparison pullback. -/
abbrev etaleOrigin (X : Scheme.{u}) : ObjectProperty (Sheaf (Scheme.ProEt.topology X) A) :=
  (comparisonUpperStar A X).essImage

variable {A} in
/-- The coefficient class is stable under restriction to a pro-étale base change.

The pullback `q^* F` of a sheaf `F` of étale origin along any morphism `q : X' ⟶ X` is again of
étale origin: `q^* ν_X^* G ≅ ν_{X'}^* q^* G`
(`AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso`). -/
lemma etaleOrigin_upperStar_obj {X X' : Scheme.{u}} (q : X' ⟶ X)
    {F : Sheaf (Scheme.ProEt.topology X) A} (hF : etaleOrigin A X F) :
    etaleOrigin A X' ((ProEtale.upperStar A q).obj F) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  exact ⟨(Etale.upperStar A q).obj G,
    ⟨((comparisonUpperStarCompUpperStarIso A q).app G).symm ≪≫ (ProEtale.upperStar A q).mapIso e⟩⟩

/-- The class-restricted full cohomological-dimension datum.

`FullCD_cls(p, A; c)` holds for `p : X ⟶ Y` if `H^r(Rp_* F) = 0` for every `r > c` and every
pro-étale sheaf `F` of étale origin on `X`, and the same holds after every base change along an
object `V` of `Y_proét`, for the restriction `g'^* F` of `F` to the base-changed source. -/
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

variable {A} in
/-- The coefficient class is closed under colimits: the comparison pullback `ν^*` is fully
faithful and preserves colimits, so its essential image is closed under the colimits that exist
in pro-étale sheaves. -/
instance etaleOrigin_isClosedUnderColimitsOfShape (X : Scheme.{u}) (J : Type*) [Category J]
    [HasColimitsOfShape J (Sheaf X.smallEtaleTopology A)]
    [HasColimitsOfShape J (Sheaf (Scheme.ProEt.topology X) A)] :
    (etaleOrigin A X).IsClosedUnderColimitsOfShape J :=
  inferInstance

end EtaleOrigin

section Bound

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The comparison bound on coefficients of étale origin is `M = 0`: for every étale sheaf `G` of
`Λ`-modules on `X` (no constructibility needed), `R^q ν_* (ν^* G) = 0` for `q > 0`. -/
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

open MonoidalCategory in
/-- The constant coefficient sheaf is of étale origin: the constant sheaf `Λ`, the monoidal unit
of pro-étale sheaves of `Λ`-modules, is `ν^*` of the constant étale sheaf
(`AlgebraicGeometry.ProEtale.comparisonUpperStarUnitIso`). -/
lemma etaleOrigin_unit (X : Scheme.{u}) :
    etaleOrigin (ModuleCat.{u + 1} Λ) X
      (𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :=
  ⟨𝟙_ _, ⟨comparisonUpperStarUnitIso Λ X⟩⟩

variable {Λ} in
/-- The coefficient class is closed under extensions: for a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of pro-étale sheaves of `Λ`-modules on `X` with `F₁` and `F₃` of étale
origin, `F₂` is of étale origin. -/
theorem etaleOrigin_of_shortExact {X : Scheme.{u}}
    {S : ShortComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    (h₁ : etaleOrigin (ModuleCat.{u + 1} Λ) X S.X₁)
    (h₃ : etaleOrigin (ModuleCat.{u + 1} Λ) X S.X₃) :
    etaleOrigin (ModuleCat.{u + 1} Λ) X S.X₂ := by
  obtain ⟨G₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨G₃, ⟨e₃⟩⟩ := h₃
  let F := comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  let α₁ : F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj G₁) ≅
      (DerivedCategory.singleFunctor _ 0).obj S.X₁ :=
    (F.mapDerivedCategorySingleFunctor 0).app G₁ ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e₁
  let α₃ : F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj G₃) ≅
      (DerivedCategory.singleFunctor _ 0).obj S.X₃ :=
    (F.mapDerivedCategorySingleFunctor 0).app G₃ ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e₃
  have hplus : DerivedCategory.TStructure.t.plus
      (((DerivedCategory.singleFunctor _ 0).obj G₁)⟦(1 : ℤ)⟧) :=
    ⟨-1, DerivedCategory.TStructure.t.isGE_shift _ 0 1 (-1)⟩
  obtain ⟨δ, hδ : F.mapDerivedCategory.map δ = _⟩ :=
    (bijective_comparisonUpperStar_mapDerivedCategory_map _ _ hplus).2
      (α₃.hom ≫ hS.singleTriangle.mor₃ ≫ α₁.inv⟦(1 : ℤ)⟧' ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app _)
  obtain ⟨C, f, g, hT⟩ := Pretriangulated.distinguished_cocone_triangle₂ δ
  have hcomm : (F.mapDerivedCategory.map δ ≫
      (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _) ≫ α₁.hom⟦(1 : ℤ)⟧' =
      α₃.hom ≫ hS.singleTriangle.mor₃ := by
    rw [hδ]
    simp [← Functor.map_comp]
  let e₂ := Pretriangulated.Triangle.π₂.mapIso (Pretriangulated.isoTriangleOfIso₁₃ _ _
    (F.mapDerivedCategory.map_distinguished _ hT) hS.singleTriangle_distinguished α₁ α₃ hcomm)
  have hC (n : ℤ) (hn : IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((DerivedCategory.singleFunctor _ 0).obj S.X₂))) :
      IsZero ((DerivedCategory.homologyFunctor _ n).obj C) :=
    F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (hn.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e₂))
  have : C.IsGE 0 := (DerivedCategory.isGE_iff C 0).2 fun i hi ↦
    hC i (DerivedCategory.isZero_of_isGE _ 0 i hi)
  have : C.IsLE 0 := (DerivedCategory.isLE_iff C 0).2 fun i hi ↦
    hC i (DerivedCategory.isZero_of_isLE _ 0 i hi)
  obtain ⟨E, ⟨eE⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE C 0
  exact ⟨E, ⟨(DerivedCategory.singleFunctor _ 0).preimageIso
    (((F.mapDerivedCategorySingleFunctor 0).app E).symm ≪≫
      F.mapDerivedCategory.mapIso eE.symm ≪≫ e₂)⟩⟩

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k] {X Y : Scheme.{u}} (p : X ⟶ Y)
  [IsProper p] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [LocallyOfFiniteType aY] (hp : p ≫ aY = aX) [HasInvertibleExponent Λ X] (d : ℕ)
  (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))

include hp hd in
/-- FullCD for coefficients of étale origin.

Let `k` be separably closed, `p : X ⟶ Y` a proper morphism of finite-type `k`-schemes with
`dim X ≤ d`, and `F` a pro-étale sheaf of `Λ`-modules of étale origin on `X`. Then
`H^r(Rp_* F) = 0` for `r > 2d`, and the same holds for the base change of `p` along every object
`V` of `Y_proét`, applied to the restriction of `F`. -/
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
/-- For `p : X ⟶ Y` proper between finite-type `k`-schemes, `k` separably closed and `dim X ≤ d`,
the class-restricted bound `FullCD_cls(p, Λ; 2d)` holds. The hypothesis
`[HasInvertibleExponent Λ X]` is not used. -/
theorem hasCohomologicalDimensionLEOnEtaleOrigin :
    HasCohomologicalDimensionLEOnEtaleOrigin (ModuleCat.{u + 1} Λ) p (2 * d) :=
  ⟨fun F hF r hr ↦ (isZero_homology_rightDerivedLowerStar_of_etaleOrigin Λ p aX aY hp d hd F hF r
      (by exact_mod_cast hr)).1,
    fun V _ g' p' sq F hF r hr ↦ (isZero_homology_rightDerivedLowerStar_of_etaleOrigin Λ p aX aY
      hp d hd F hF r (by exact_mod_cast hr)).2 V g' p' sq⟩

end Bound

section WeaklyContractible

open Opposite

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- FullCD tested on affine weakly contractible objects.

`FullCD(p, Λ; c)` holds if and only if, for every base change `p'` of `p` along an object `V` of
`Y_proét`, every pro-étale sheaf `F` of `Λ`-modules on the base-changed source and every `r > c`,
the sections of `H^r(Rp'_* F)` over every affine weakly contractible object of `V_proét` vanish. -/
theorem hasUniformCohomologicalDimensionLE_iff_forall_isWeaklyContractible {X Y : Scheme.{u}}
    (p : X ⟶ Y) (c : ℕ) :
    HasUniformCohomologicalDimensionLE (ModuleCat.{u + 1} Λ) p c ↔
      ∀ (V : Y.ProEt) ⦃X' : Scheme.{u}⦄ (g' : X' ⟶ X) (p' : X' ⟶ V.left),
        IsPullback g' p' p V.hom →
          ∀ (F : Sheaf (Scheme.ProEt.topology X') (ModuleCat.{u + 1} Λ)) (r : ℤ), (c : ℤ) < r →
            ∀ W : V.left.ProEt, IsAffine W.left →
              (Scheme.ProEt.topology V.left).IsWeaklyContractible.{u + 1} W →
                Subsingleton ((((_root_.DerivedCategory.homologyFunctor _ r).obj
                  ((R((p')_*[ModuleCat.{u + 1} Λ])).obj
                    ((_root_.DerivedCategory.singleFunctor _ 0).obj F))).obj.obj (op W))) := by
  refine forall_congr' fun V ↦ forall_congr' fun X' ↦ forall_congr' fun g' ↦
    forall_congr' fun p' ↦ forall_congr' fun _ ↦ forall_congr' fun F ↦ forall_congr' fun r ↦
      forall_congr' fun _ ↦ isZero_iff_forall_isWeaklyContractible _

end WeaklyContractible

end ProEtale

end AlgebraicGeometry
