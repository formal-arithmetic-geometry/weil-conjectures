/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCover

/-!
# Functoriality of universal profinite étale covers along morphisms of schemes

Let `f : X ⟶ Y` be a morphism of connected quasi-compact quasi-separated schemes and
`x : Spec K ⟶ X` a geometric point, `K` separably closed. The universal profinite étale covers
`X̃_x = lim A` and `Ỹ_{x ≫ f} = lim B` (over pointed Galois finite étale covers) are related by
a morphism `X̃_x ⟶ Ỹ_{x ≫ f}` over `f`: its component at a pointed Galois cover `(B, b)` of `Y` is
the `X`-morphism `X̃_x ⟶ f^* B` corresponding to the point `(b, x)` of the fibre of `f^* B` at
`x`, followed by the projection `f^* B ⟶ B`. It sends the base point to the base point and is
compatible with the transports along a path `τ : F_x ≅ F_z` of `X` and along the induced path
`F_{x ≫ f} ≅ F_{z ≫ f}` of `Y`. This generalises `AlgebraicGeometry.Scheme.UniversalCover.map`,
which treats endomorphisms.

We also record the universal covers of a connected qcqs scheme as a term
`AlgebraicGeometry.Scheme.universalCovers` of `AlgebraicGeometry.Scheme.UniversalCovers`, so that
the morphisms above can be compared with its data.

## Main definitions

- `AlgebraicGeometry.Scheme.UniversalCover.pullbackMap`: the morphism `X̃_x ⟶ Ỹ_{x ≫ f}`.
- `AlgebraicGeometry.Scheme.universalCovers`: the universal covers of a connected qcqs scheme.

## Main statements

- `AlgebraicGeometry.Scheme.UniversalCover.pullbackMap_proj`,
  `AlgebraicGeometry.Scheme.UniversalCover.pt_pullbackMap`,
  `AlgebraicGeometry.Scheme.UniversalCover.pullbackMap_transport`: the morphism lies over `f`,
  preserves base points and is compatible with transports.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme

namespace UniversalCover

open FiniteEtale

attribute [local instance] FiniteEtale.fiberFunctor

section Pullback

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K] (f : X ⟶ Y)

/-- Base change of morphisms of finite étale `Y`-schemes is compatible with the projections
`f^* P ⟶ P`. -/
@[reassoc]
lemma pullback_map_hom_left_fst {P Q : Y.FiniteEtale} (g : P ⟶ Q) :
    ((FiniteEtale.pullback f).map g).hom.left ≫ Limits.pullback.fst Q.obj.hom f =
      Limits.pullback.fst P.obj.hom f ≫ g.hom.left := by
  simp

/-- The projection `f^* P ⟶ P` lies over `f`. -/
@[reassoc]
lemma pullback_fst_hom (P : Y.FiniteEtale) :
    Limits.pullback.fst P.obj.hom f ≫ P.obj.hom = ((FiniteEtale.pullback f).obj P).obj.hom ≫ f :=
  Limits.pullback.condition

/-- The point `(p, x)` of `f^* P` over `x` corresponding to a point `p` of `P` over `x ≫ f`
projects to `p`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberIso_inv_app_left_fst (x : Spec (.of K) ⟶ X) (P : Y.FiniteEtale)
    (p : (fiber (x ≫ f)).obj P) :
    ((pullbackFiberIso f x).inv.app P p).left ≫ Limits.pullback.fst P.obj.hom f = p.left := by
  rw [pullbackFiberIso_inv_app_left]
  exact Limits.pullback.lift_fst _ _ _

/-- The points `(p, x)` of `f^* P` are natural in `P`. -/
lemma pullbackFiberIso_inv_app_naturality (x : Spec (.of K) ⟶ X) {P Q : Y.FiniteEtale}
    (g : P ⟶ Q) (p : (fiber (x ≫ f)).obj P) :
    (fiber x).map ((FiniteEtale.pullback f).map g) ((pullbackFiberIso f x).inv.app P p) =
      (pullbackFiberIso f x).inv.app Q ((fiber (x ≫ f)).map g p) :=
  (ConcreteCategory.congr_hom ((pullbackFiberIso f x).inv.naturality g) p).symm

variable [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace Y]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- The morphism `X̃_x ⟶ Ỹ_{x ≫ f}` over `f : X ⟶ Y`: its component at a pointed Galois cover
`(B, b)` of `Y` is the `X`-morphism `X̃_x ⟶ f^* B` corresponding to `(b, x)`, followed by
`f^* B ⟶ B`. -/
noncomputable def pullbackMap (x : Spec (.of K) ⟶ X) : cover x ⟶ cover (x ≫ f) :=
  limit.lift (diagram (x ≫ f))
    { pt := cover x
      π :=
        { app j := toObj x _ ((pullbackFiberIso f x).inv.app _ (point (x ≫ f) j)) ≫
            Limits.pullback.fst ((obj (x ≫ f)).obj j).obj.hom f
          naturality j j' g := (Category.id_comp _).trans (by
            change _ = (toObj x ((FiniteEtale.pullback f).obj ((obj (x ≫ f)).obj j)) _ ≫
              Limits.pullback.fst ((obj (x ≫ f)).obj j).obj.hom f) ≫
                ((obj (x ≫ f)).map g).hom.left
            rw [Category.assoc, ← pullback_map_hom_left_fst, toObj_comp_assoc,
              pullbackFiberIso_inv_app_naturality, map_point]) } }

/-- `pullbackMap f x` followed by the `Y`-morphism corresponding to `p ∈ F_{x ≫ f}(P)` is the
`X`-morphism `X̃_x ⟶ f^* P` corresponding to `(p, x)`, followed by `f^* P ⟶ P`. -/
@[reassoc (attr := simp)]
lemma pullbackMap_toObj (x : Spec (.of K) ⟶ X) (P : Y.FiniteEtale) (p : (fiber (x ≫ f)).obj P) :
    pullbackMap f x ≫ toObj (x ≫ f) P p =
      toObj x _ ((pullbackFiberIso f x).inv.app P p) ≫ Limits.pullback.fst _ f := by
  obtain ⟨j, g, rfl⟩ := exists_hom_point (x ≫ f) P p
  rw [← π_comp_eq_toObj (x ≫ f) j g, ← Category.assoc, pullbackMap, limit.lift_π]
  change (toObj x ((FiniteEtale.pullback f).obj ((obj (x ≫ f)).obj j)) _ ≫
    Limits.pullback.fst ((obj (x ≫ f)).obj j).obj.hom f) ≫ g.hom.left = _
  rw [Category.assoc, ← pullback_map_hom_left_fst, toObj_comp_assoc,
    pullbackFiberIso_inv_app_naturality]

omit [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- `pullbackMap f x` lies over `f`. -/
lemma pullbackMap_proj (x : Spec (.of K) ⟶ X) :
    pullbackMap f x ≫ proj (x ≫ f) = proj x ≫ f := by
  rw [proj, ← Category.assoc, pullbackMap, limit.lift_π]
  change (toObj x ((FiniteEtale.pullback f).obj ((obj (x ≫ f)).obj (j₀ (x ≫ f)))) _ ≫
    Limits.pullback.fst ((obj (x ≫ f)).obj (j₀ (x ≫ f))).obj.hom f) ≫ p (x ≫ f) _ = _
  rw [Category.assoc, pullback_fst_hom, toObj_hom_assoc]

/-- `pullbackMap f x` sends the base point over `x` to the base point over `x ≫ f`. -/
lemma pt_pullbackMap (x : Spec (.of K) ⟶ X) : pt x ≫ pullbackMap f x = pt (x ≫ f) :=
  hom_ext (x ≫ f) fun P p ↦ by
    rw [Category.assoc, pullbackMap_toObj, pt_toObj_assoc, pullbackFiberIso_inv_app_left_fst,
      pt_toObj]

/-- `pullbackMap f` is compatible with the transports along a path `τ` of `X` and along the
induced path of `Y`. -/
lemma pullbackMap_transport {x z : Spec (.of K) ⟶ X} (τ : fiber x ≅ fiber z) :
    pullbackMap f x ≫ (transport (pullbackPathIso f τ)).hom =
      (transport τ).hom ≫ pullbackMap f z :=
  hom_ext (z ≫ f) fun P p ↦ by
    rw [Category.assoc, transport_hom, transportHom_toObj, pullbackMap_toObj, Category.assoc,
      transport_hom, pullbackMap_toObj, transportHom_toObj_assoc]
    congr 2
    simp only [pullbackPathIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, FintypeCat.comp_apply]
    exact ConcreteCategory.congr_hom ((pullbackFiberIso f x).hom_inv_id_app P) _

end Pullback

end UniversalCover

variable (Y : Scheme.{u}) (Ω : Type u) [Field Ω]

/-- The universal profinite étale covers of a connected quasi-compact quasi-separated scheme
(`AlgebraicGeometry.Scheme.UniversalCover.cover`), as a term of
`AlgebraicGeometry.Scheme.UniversalCovers` (compare
`AlgebraicGeometry.Scheme.nonempty_universalCovers`). -/
noncomputable def universalCovers [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    UniversalCovers Y Ω where
  cover := UniversalCover.cover
  proj := UniversalCover.proj
  weaklyEtale_proj := UniversalCover.weaklyEtale_proj
  pt := UniversalCover.pt
  pt_proj := UniversalCover.pt_proj
  connectedSpace y := UniversalCover.connectedSpace_cover y
  surjective_proj := UniversalCover.surjective_proj
  quasiCompact_proj := UniversalCover.quasiCompact_proj
  bijective_fiber y P := UniversalCover.bijective_fiber y P
  transport := UniversalCover.transport
  transport_proj τ := UniversalCover.transportHom_proj τ
  transport_refl := UniversalCover.transport_refl
  transport_trans := UniversalCover.transport_trans
  pt_transport_reparam := UniversalCover.pt_transport_reparam
  map := UniversalCover.map
  map_proj := UniversalCover.map_proj
  pt_map := UniversalCover.pt_map
  map_transport := UniversalCover.map_transport
  exists_graph y q := UniversalCover.exists_graph y q
  continuous_graph y x := UniversalCover.continuous_graph y x
  loop y := UniversalCover.loop y
  continuous_loop y := UniversalCover.continuous_loop y
  loop_graph y g x := by exact UniversalCover.loop_loopGraph y g x

variable {X Y : Scheme.{u}} {Ω} [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
  [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **Universal covers along a morphism of schemes.** For `f : X ⟶ Y` there are morphisms
`X̃_x ⟶ Ỹ_{x ≫ f}` over `f` between the universal covers, sending base points to base points and
compatible with the transports along paths `τ` of `X` and the induced paths of `Y`. -/
theorem exists_universalCovers_map (f : X ⟶ Y) :
    ∃ φ : ∀ x : Spec (.of (AlgebraicClosure Ω)) ⟶ X,
        (universalCovers X Ω).cover x ⟶ (universalCovers Y Ω).cover (x ≫ f),
      (∀ x, φ x ≫ (universalCovers Y Ω).proj (x ≫ f) = (universalCovers X Ω).proj x ≫ f) ∧
      (∀ x, (universalCovers X Ω).pt x ≫ φ x = (universalCovers Y Ω).pt (x ≫ f)) ∧
      ∀ {x z : Spec (.of (AlgebraicClosure Ω)) ⟶ X} (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber z),
        φ x ≫ ((universalCovers Y Ω).transport (FiniteEtale.pullbackPathIso f τ)).hom =
          ((universalCovers X Ω).transport τ).hom ≫ φ z :=
  ⟨UniversalCover.pullbackMap f, UniversalCover.pullbackMap_proj f,
    UniversalCover.pt_pullbackMap f, UniversalCover.pullbackMap_transport f⟩

end AlgebraicGeometry.Scheme
