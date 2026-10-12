/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # The geometric fibre restriction formula for exchange

Source: Stacks Project, Tag 0EYP, the canonical base change map on germs.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale
open Scheme
set_option backward.isDefEq.respectTransparency false

/-- The pointed neighbourhood section on the geometric fibre, followed by its lift
through the iterated pullback. Both components are specified, so this construction
involves no choice of a geometric lift. -/
noncomputable def geometricFibreSectionLift
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V) :
    Scheme.Etale.mk (𝟙 X') ⟶ g'.Etale.obj (f.Etale.obj V) := by
  let a : X' ⟶ pullback V.hom f := pullback.lift (f' ≫ v.left) g' (by
    have hv : v.left ≫ V.hom = s := v.w
    rw [Category.assoc, hv]
    exact sq.w.symm)
  exact MorphismProperty.Over.homMk
    (pullback.lift a (𝟙 X') (by
      change a ≫ pullback.snd V.hom f = 𝟙 X' ≫ g'
      simp [a])) (pullback.lift_snd _ _ _)

/-- Restrict a neighbourhood section by the inverse-image unit and the specified
pointed lift to the fibre. This definition does not use the exchange map. -/
noncomputable def geometricFibreSectionRestriction
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V) :
    F.obj.obj (op (f.Etale.obj V)) ⟶
      ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X'))) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g').unit.app F).hom.app
      (op (f.Etale.obj V)) ≫
    ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.map
      (geometricFibreSectionLift sq V v).op

/-- The inverse-image comparison at the identity geometric point, with identity
composition normalized. -/
noncomputable def geometricPointSourceStalkIso
    (Λ : Type (u + 1)) [CommRing Λ]
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Y)
    (P : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.obj
        ((s)^*[ModuleCat.{u + 1} Λ].obj P) ≅
      (pointSmallEtale s).sheafFiber.obj P := by
  simpa only [Functor.comp_obj, Category.id_comp] using
    (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) s (𝟙 _)).app P

/-- Any map on direct-image germs having the fibre restriction formula is the
actual exchange after the canonical source comparison and a target section comparison.
This is a compatibility assertion only: it asserts no invertibility of that map or
of exchange, and has no integral or proper hypothesis.

Source: Stacks Project, Tag 0EYP, definition of the base change map, and Tags 03Q1
and 03QO for inverse-image stalks and sections on the spectrum of a closed field.
(blueprint: lem-sbc-geometric-fibre-exchange-germs).

Proof: identify the source by the inverse-image stalk isomorphism. On Spec Omega,
every pointed etale neighbourhood of the identity has a section through its marked
point, so the terminal section germ is bijective. Apply this to the direct image
along f', and identify its terminal sections with those on X' using the unique
isomorphism from the pullback of the terminal object to the terminal object. Its
inverse is the target comparison b. For a neighbourhood (V,v), the pushforward
unit identity for base change expresses the mate as the unit for g' followed by
the pushforward square isomorphism. Restrict along the marked point v: the two
pullback projections are f' followed by v and g', respectively. The iterated
pullback lift is therefore geometricFibreSectionLift. This gives exactly the
displayed formula on every germ. All germs have such representatives, so the
assumed formula for Theta proves the equality on every element. No bijectivity
of Theta is used. -/
theorem geometricFibreExchange_germs
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (Θ : (pointSmallEtale s).sheafFiber.obj ((f)_*[ModuleCat.{u + 1} Λ].obj F) ⟶
      ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X'))))
    (hΘ : ∀ (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V)
      (z : F.obj.obj (op (f.Etale.obj V))),
      Θ.hom ((pointSmallEtale s).toPresheafFiber V v
        ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj z) =
      (geometricFibreSectionRestriction Λ sq.toCommSq F V v).hom z) :
    ∃ b : (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.obj
        ((f')_*[ModuleCat.{u + 1} Λ].obj ((g')^*[ModuleCat.{u + 1} Λ].obj F)) ≅
          ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X'))),
      (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
          ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) ≫ b.hom =
        (geometricPointSourceStalkIso Λ s ((f)_*[ModuleCat.{u + 1} Λ].obj F)).hom ≫ Θ := by
  sorry

end AlgebraicGeometry.Etale
