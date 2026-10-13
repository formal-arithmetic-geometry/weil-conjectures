/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.Integral.StalkOpen

/-!
# Base change along an integral morphism

For a cartesian square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
with `f` integral, the base change map `g^* f_* ⟶ f'_* g'^*` on étale sheaves of `Λ`-modules is
an isomorphism (`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isIntegralHom`). As `f_*` and
`f'_*` are exact, the derived base change map `g^* Rf_* ⟶ Rf'_* g'^*` on `D⁺` is then an
isomorphism as well (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isIntegralHom`).
This extends the finite case `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isIntegralHom`: base change along an
  integral morphism.
- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isIntegralHom`: its derived form.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

open Scheme Scheme.Hom in
/-- **The base change map on restricted germs**: for a geometric point `t` of `X'` over the
geometric point `y'` of `Y'`, the restriction to `t` of the image of a germ `a` of `f_* F` at
`y' ≫ g` under the stalk of the base change map `g^* f_* F ⟶ f'_* g'^* F` at `y'` is, through
`(g'^* F)_t ≅ F_{t ≫ g'}`, the restriction of `a` to `t ≫ g'`. -/
lemma Etale.stalkRestrict_sheafFiber_map_baseChangeMap_app (sq : IsPullback g' f' f g)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y' : Spec (.of Ω) ⟶ Y'}
    (t : f'.GeometricFiber y') (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (a : ToType ((pointSmallEtale (y' ≫ g)).sheafFiber.obj ((f)_*[ModuleCat.{u + 1} Λ].obj F))) :
    (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g' t.1).hom.app F
        (Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f' y' t (((g')^*[ModuleCat.{u + 1} Λ]).obj F)
          ((pointSmallEtale y').sheafFiber.map
            ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F)
            ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g y').inv.app
              ((f)_*[ModuleCat.{u + 1} Λ].obj F) a))) =
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f (y' ≫ g)
        (GeometricFiber.baseChangeEquiv sq y' t)
        F a := by
  obtain ⟨s, rfl⟩ := t
  have h := congrArg (fun φ ↦ (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g
      (s ≫ f')).inv.app ((f)_*[ModuleCat.{u + 1} Λ].obj F) ≫ φ)
    (Etale.sheafFiber_map_baseChangeMap_app_stalkRestrict (ModuleCat.{u + 1} Λ) sq.toCommSq s F)
  simp only [Iso.inv_hom_id_app_assoc] at h
  exact ConcreteCategory.congr_hom h a

variable [IsIntegralHom f]

open Scheme Scheme.Hom in
/-- **The base change map of an integral morphism is an isomorphism on stalks** at geometric
points with algebraically closed residue field. Both stalks embed into the product of the
stalks of `F` at the geometric points of `X` over `y' ≫ g`
(`AlgebraicGeometry.Etale.eq_zero_of_forall_stalkRestrict_eq_zero`), compatibly with the base
change map, which is therefore injective. For surjectivity, a germ `b` of `f'_* g'^* F` at `y'`
agrees at each geometric point `t` of `X'` over `y'` with the image of some germ `a t` of
`f_* F` (`AlgebraicGeometry.Etale.surjective_stalkRestrict_of_isIntegralHom`), and then at all
points near `t` in the fibre topology
(`AlgebraicGeometry.Etale.exists_finset_stalkRestrict_eq_zero`). By quasi-compactness of the
geometric fibre (`AlgebraicGeometry.Scheme.Hom.Nbhd.exists_finset_geometricFiber_cover`)
finitely many `a t` suffice, and they patch to a germ of `f_* F`
(`AlgebraicGeometry.Etale.exists_stalkRestrict_eq_of_finset`) mapping to `b`. -/
lemma Etale.isIso_sheafFiber_map_baseChangeMap_app_of_isIntegralHom (sq : IsPullback g' f' f g)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y' : Spec (.of Ω) ⟶ Y')
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((pointSmallEtale y').sheafFiber.map
      ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F)) := by
  classical
  have : IsIntegralHom f' := MorphismProperty.of_isPullback sq inferInstance
  let e := GeometricFiber.baseChangeEquiv sq y'
  let M := (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g y').inv.app
      ((f)_*[ModuleCat.{u + 1} Λ].obj F) ≫ (pointSmallEtale y').sheafFiber.map
        ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F)
  have key (t : f'.GeometricFiber y') a :
      (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g' t.1).hom.app F
        (Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f' y' t
          (((g')^*[ModuleCat.{u + 1} Λ]).obj F) (M a)) =
        Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f (y' ≫ g) (e t) F a :=
    Etale.stalkRestrict_sheafFiber_map_baseChangeMap_app Λ sq t F a
  have hinj (t : f'.GeometricFiber y') x
      (hx : (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g' t.1).hom.app F x = 0) :
      x = 0 := by
    have := congrArg
      ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g' t.1).inv.app F) hx
    rwa [← ConcreteCategory.comp_apply, Iso.hom_inv_id_app, ConcreteCategory.id_apply,
      map_zero] at this
  have hM : IsIso M := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab ↦ ?_, fun b ↦ ?_⟩
    · -- injectivity: the restrictions of `a - b` to the geometric points over `y' ≫ g` vanish
      rw [← sub_eq_zero]
      refine Etale.eq_zero_of_forall_stalkRestrict_eq_zero Λ f (y' ≫ g) F _ fun t ↦ ?_
      rw [← e.apply_symm_apply t, ← key, map_sub, hab, sub_self, map_zero, map_zero]
    · -- surjectivity: patch finitely many local preimages of `b`
      have hsurj (t : f'.GeometricFiber y') : ∃ a,
          Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f (y' ≫ g) (e t) F a =
            (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g' t.1).hom.app F
              (Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f' y' t
                (((g')^*[ModuleCat.{u + 1} Λ]).obj F) b) :=
        Etale.surjective_stalkRestrict_of_isIntegralHom Λ f (y' ≫ g) (e t) F _
      choose a ha using hsurj
      have hd (t : f'.GeometricFiber y') : Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f' y' t
          (((g')^*[ModuleCat.{u + 1} Λ]).obj F) (M (a t) - b) = 0 :=
        hinj t _ (by rw [map_sub, map_sub, key, ha, sub_self])
      obtain ⟨c₀, hc₀⟩ := Nbhd.exists_isAffine (y' ≫ g)
      choose S hS using fun t ↦ Etale.exists_finset_stalkRestrict_eq_zero Λ sq y' c₀
        (((g')^*[ModuleCat.{u + 1} Λ]).obj F) (M (a t) - b) t (hd t)
      obtain ⟨T, hT⟩ := Nbhd.exists_finset_geometricFiber_cover f c₀ fun t ↦ S (e.symm t)
      let enum : Fin T.card → f.GeometricFiber (y' ≫ g) := fun i ↦ (T.equivFin.symm i).1
      let P (t : f.GeometricFiber (y' ≫ g)) (i : Fin T.card) : Prop :=
        ∀ r ∈ S (e.symm (enum i)),
          (basePt f c₀ t).appTopPoint r = (basePt f c₀ (enum i)).appTopPoint r
      have hPne (t : f.GeometricFiber (y' ≫ g)) : (Finset.univ.filter (P t)).Nonempty := by
        obtain ⟨t₀, ht₀, h⟩ := hT t
        refine ⟨T.equivFin ⟨t₀, ht₀⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
        simpa only [P, enum, Equiv.symm_apply_apply] using h
      let m (t : f.GeometricFiber (y' ≫ g)) : Fin T.card :=
        (Finset.univ.filter (P t)).min' (hPne t)
      have hm (t : f.GeometricFiber (y' ≫ g)) : P t (m t) :=
        (Finset.mem_filter.1 (Finset.min'_mem _ (hPne t))).2
      obtain ⟨a₀, ha₀⟩ := Etale.exists_stalkRestrict_eq_of_finset Λ f c₀ F
        (fun i ↦ a (e.symm (enum i))) m (Finset.univ.biUnion fun i ↦ S (e.symm (enum i)))
        (fun t₁ t₂ h ↦ by
          have hfilt : Finset.univ.filter (P t₁) = Finset.univ.filter (P t₂) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, P]
            refine forall₂_congr fun r hr ↦ ?_
            rw [h r (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hr⟩)]
          simp only [m, hfilt])
      refine ⟨a₀, ?_⟩
      rw [← sub_eq_zero]
      refine Etale.eq_zero_of_forall_stalkRestrict_eq_zero Λ f' y' _ _ fun t ↦ hinj t _ ?_
      have h₁ := hS (e.symm (enum (m (e t)))) t (by
        rw [e.apply_symm_apply]
        exact hm (e t))
      rw [map_sub] at h₁
      rw [map_sub, map_sub, key, ha₀, ← key, ← map_sub, h₁, map_zero]
  have : IsIso ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g y').inv.app
      ((f)_*[ModuleCat.{u + 1} Λ].obj F) ≫ (pointSmallEtale y').sheafFiber.map
        ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F)) := hM
  exact IsIso.of_isIso_comp_left
    ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g y').inv.app
      ((f)_*[ModuleCat.{u + 1} Λ].obj F)) _

/-- **Base change along an integral morphism**: for a cartesian square with `f` integral, the
base change map `g^* f_* ⟶ f'_* g'^*` on étale sheaves of `Λ`-modules is an isomorphism.

It is checked on the stalks at the geometric points of `Y'`. For an integral morphism the
stalk of `f_* F` at a geometric point `y` of `Y` is the module of sections of `F` over
`X ×_Y Spec 𝒪^{sh}_{Y,y}`, the spectrum of an integral algebra over a strictly henselian local
ring, and such sections only depend on the fibre of `X` over `y`, which is the same for `y` and
for a geometric point of `Y'` above it. This is the integral case of the exchange property whose
finite case is `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`. -/
theorem Etale.isIso_baseChangeMap_of_isIntegralHom (sq : IsPullback g' f' f g) :
    IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  have (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      IsIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) := by
    refine Scheme.isIso_of_isIso_sheafFiber_map _ fun s ↦ ?_
    have : IsIso (((Scheme.pointSmallEtale (Y'.algClosurePoint s)).ulift.{u + 1}).sheafFiber.map
        ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F)) := by
      rw [← NatIso.naturality_2
        ((Scheme.pointSmallEtale (Y'.algClosurePoint s)).uliftSheafFiberIso (ModuleCat.{u + 1} Λ))
        ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F)]
      have := Etale.isIso_sheafFiber_map_baseChangeMap_app_of_isIntegralHom Λ sq
        (Y'.algClosurePoint s) F
      infer_instance
    exact this
  exact NatIso.isIso_of_isIso_app _

/-- **Derived base change along an integral morphism**: for a cartesian square with `f`
integral, the derived base change map `g^* Rf_* ⟶ Rf'_* g'^*` on `D⁺` is an isomorphism. The
pushforwards along `f` and along its base change `f'`, which is integral too, are exact
(`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`), so this follows
from the sheaf-level statement
`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isIntegralHom` without resolutions. -/
theorem Etale.isIso_derivedBaseChangeMapPlus_of_isIntegralHom (sq : IsPullback g' f' f g) :
    IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  have : IsIntegralHom f' := MorphismProperty.of_isPullback sq inferInstance
  have := Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom Λ f
  have := Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom Λ f'
  have := Etale.isIso_baseChangeMap_of_isIntegralHom Λ sq
  exact Etale.isIso_derivedBaseChangeMapPlus_of_isIso_baseChangeMap _ sq.toCommSq

end AlgebraicGeometry
