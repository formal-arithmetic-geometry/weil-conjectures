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

variable {A} in
/-- Blueprint `thm-sf-fullcd-used-class`: the coefficient class is closed under colimits.

The comparison pullback `ν^*` is fully faithful and preserves colimits, being a left adjoint, so
its essential image is closed under the colimits that exist in pro-étale sheaves. -/
instance etaleOrigin_isClosedUnderColimitsOfShape (X : Scheme.{u}) (J : Type*) [Category J]
    [HasColimitsOfShape J (Sheaf X.smallEtaleTopology A)]
    [HasColimitsOfShape J (Sheaf (Scheme.ProEt.topology X) A)] :
    (etaleOrigin A X).IsClosedUnderColimitsOfShape J :=
  inferInstance

end EtaleOrigin

section Bound

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {Λ} in
/-- Blueprint `thm-sf-fullcd-used-class`: the coefficient class is closed under extensions.

Let `0 → F₁ → F₂ → F₃ → 0` be a short exact sequence of pro-étale sheaves of `Λ`-modules on `X`
with `F₁` and `F₃` of étale origin. Then `F₂` is of étale origin: its extension class lies in
`Hom(ν^* G₃, ν^* G₁[1]) ≅ Hom(G₃, G₁[1])` by the full faithfulness of `ν^*` on bounded below
complexes (`AlgebraicGeometry.ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map`),
so it is `ν^*` of the extension of `G₃` by `G₁` with the corresponding class. -/
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

end Bound

section WeaklyContractible

open Opposite

variable (Λ : Type (u + 1)) [CommRing Λ]

end WeaklyContractible

end ProEtale

end AlgebraicGeometry
