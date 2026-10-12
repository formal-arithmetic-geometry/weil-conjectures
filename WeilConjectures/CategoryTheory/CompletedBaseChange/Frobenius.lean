/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.CompletedBaseChange.Rectangle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp

/-!
# Frobenius-equivariant base change squares

Let `𝔗` be a base change square (`CategoryTheory.BaseChangeSquare`). A *Frobenius datum* on
`𝔗` (`def-weil-pbc-frobenius-tower-datum`, abstract form) consists of endofunctors
`Φ_Z` of the four corners (the pullbacks `L Fr_Z^*` along the Frobenius automorphisms) with
commutation isomorphisms with the four pullbacks of the square

```
  κ_f : f^* Φ_Y ≅ Φ_X f^*,   κ_{f'},   κ_g : g^* Φ_Y ≅ Φ_{Y'} g^*,   κ_{g'},
```

(written `upperF ⋙ Φ_X ≅ Φ_Y ⋙ upperF` etc.) such that the resulting cube of left adjoints
commutes with the Cartesian identification. The direct images then commute with the `Φ_Z`
through the mates `β_f : Φ_Y f_* ⟶ f_* Φ_X` of `κ_f`, assumed invertible (for automorphisms
`Fr_Z` they are).

A *Weil structure* on an object `M` is an isomorphism `Φ M ≅ M`, i.e. an object of
`CategoryTheory.Endofunctor.IsoAlgebra Φ`; a *Weil morphism* is a morphism of `IsoAlgebra`s.
The commutation isomorphisms lift the four pullbacks and the two direct images to functors of
Weil objects (`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso`). In particular a Weil
structure `ϑ` on `K` induces the Weil structures
`Θ_B = g^* β_f ∘ κ_g` on `B = g^* f_* K` and `Θ_D = f'_* κ_{g'} ∘ β_{f'}` on `D = f'_* g'^* K`
(`def-weil-pbc-frobenius-corner-structures`), and the exchange map `ξ : B ⟶ D` is a Weil
morphism (`CategoryTheory.BaseChangeSquare.FrobeniusDatum.weilExchange`): this is the
pasting coherence of exchange maps for the Frobenius cube, proved by the mate calculus.

## Main definitions

- `CategoryTheory.BaseChangeSquare.FrobeniusDatum`.
- `CategoryTheory.BaseChangeSquare.FrobeniusDatum.weilB`, `weilD`, `weilExchange`.
- `CategoryTheory.Endofunctor.IsoAlgebra.transport`: transport of a Weil structure along an
  isomorphism (the structures `Θ_A = h⁻¹ Θ_B Φ(h)` and `Θ_C`).

## Main results

- `CategoryTheory.BaseChangeSquare.FrobeniusDatum.exchange_comm`: the exchange map commutes
  with the Frobenius structures.
- `CategoryTheory.Endofunctor.IsoAlgebra.comm_of_rectangle`: in a commutative rectangle in which
  three edges are Weil morphisms and the edge `h'` is a monomorphism, the fourth edge is a Weil
  morphism (`lemma-weil-pbc-frobenius-level-rectangle`, the step "cancel `h'_n`").
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Functor CategoryTheory.TwoSquare

namespace CategoryTheory

namespace Endofunctor.IsoAlgebra

variable {C : Type u₁} [Category.{v₁} C] {F : C ⥤ C}

/-- Transport of a Weil structure along an isomorphism `e : X ≅ K.carrier`: the object `X`
with the structure `Φ X ≅ Φ K ≅ K ≅ X`, i.e. `e⁻¹ ∘ Θ_K ∘ Φ(e)`. -/
noncomputable def transport (K : IsoAlgebra F) {X : C} (e : X ≅ K.carrier) : IsoAlgebra F :=
  mk X (F.mapIso e ≪≫ K.str ≪≫ e.symm)

@[simp]
lemma transport_carrier (K : IsoAlgebra F) {X : C} (e : X ≅ K.carrier) :
    (K.transport e).carrier = X := rfl

@[simp]
lemma transport_str (K : IsoAlgebra F) {X : C} (e : X ≅ K.carrier) :
    (K.transport e).str = F.mapIso e ≪≫ K.str ≪≫ e.symm := mk_str _ _

/-- The transported Weil object is isomorphic to the original one through `e`, which is
therefore a Weil morphism. -/
noncomputable def transportIso (K : IsoAlgebra F) {X : C} (e : X ≅ K.carrier) :
    K.transport e ≅ K :=
  ObjectProperty.isoMk _ (Algebra.isoMk e (by
    change F.map e.hom ≫ K.obj.str = (F.map e.hom ≫ K.str.hom ≫ e.inv) ≫ e.hom
    simp [str_hom]))

@[simp]
lemma transportIso_hom_hom_f (K : IsoAlgebra F) {X : C} (e : X ≅ K.carrier) :
    (K.transportIso e).hom.hom.f = e.hom := rfl

/-- **Cancellation in a rectangle of Weil maps.** Let `h ≫ v' = v ≫ h'` be a commutative
rectangle `A ⟶ D` in which `h`, `v'` and `h'` commute with given structures
`Θ_Z : Φ Z ⟶ Z` and `h'` is a monomorphism. Then `v` commutes with the structures too.
(Blueprint `lemma-weil-pbc-frobenius-level-rectangle`: the equation for the remaining vertical
edge.) -/
lemma comm_of_rectangle {A B C' D : C} {ΘA : F.obj A ⟶ A} {ΘB : F.obj B ⟶ B}
    {ΘC : F.obj C' ⟶ C'} {ΘD : F.obj D ⟶ D} {h : A ⟶ B} {v : A ⟶ C'} {h' : C' ⟶ D}
    {v' : B ⟶ D} (w : h ≫ v' = v ≫ h') [Mono h'] (hh : F.map h ≫ ΘB = ΘA ≫ h)
    (hv' : F.map v' ≫ ΘD = ΘB ≫ v') (hh' : F.map h' ≫ ΘD = ΘC ≫ h') :
    F.map v ≫ ΘC = ΘA ≫ v := by
  rw [← cancel_mono h', Category.assoc, ← hh', ← Category.assoc, ← F.map_comp, ← w,
    Category.assoc, ← w, F.map_comp, Category.assoc, hv', ← Category.assoc, hh,
    Category.assoc]

end Endofunctor.IsoAlgebra

namespace BaseChangeSquare

variable {𝒯 : Type u₁} {𝒰 : Type u₂} {𝒯' : Type u₃} {𝒰' : Type u₄}
  [Category.{v₁} 𝒯] [Category.{v₂} 𝒰] [Category.{v₃} 𝒯'] [Category.{v₄} 𝒰']

/-- A **Frobenius datum** on a base change square `𝔗` (Blueprint
`def-weil-pbc-frobenius-tower-datum`, abstract form): Frobenius pullbacks `Φ_Z` on the four
corners with commutation isomorphisms `κ` with the four pullbacks of the square, such that the
cube of left adjoints commutes, and such that the induced exchange maps `β_f`, `β_{f'}` of the
proper Frobenius faces (the mates of `κ_f`, `κ_{f'}`) are isomorphisms. -/
structure FrobeniusDatum (𝔗 : BaseChangeSquare 𝒯 𝒰 𝒯' 𝒰') where
  /-- The Frobenius pullback on `X`. -/
  ΦX : 𝒯 ⥤ 𝒯
  /-- The Frobenius pullback on `Y`. -/
  ΦY : 𝒰 ⥤ 𝒰
  /-- The Frobenius pullback on `X'`. -/
  ΦX' : 𝒯' ⥤ 𝒯'
  /-- The Frobenius pullback on `Y'`. -/
  ΦY' : 𝒰' ⥤ 𝒰'
  /-- The Frobenius face of `f`: `f^* Φ_Y ≅ Φ_X f^*`. -/
  κF : 𝔗.upperF ⋙ ΦX ≅ ΦY ⋙ 𝔗.upperF
  /-- The Frobenius face of `f'`. -/
  κF' : 𝔗.upperF' ⋙ ΦX' ≅ ΦY' ⋙ 𝔗.upperF'
  /-- The Frobenius face of `g`: `Φ_{Y'} g^* ≅ g^* Φ_Y`. -/
  κG : 𝔗.upperG ⋙ ΦY' ≅ ΦY ⋙ 𝔗.upperG
  /-- The Frobenius face of `g'`. -/
  κG' : 𝔗.upperG' ⋙ ΦX' ≅ ΦX ⋙ 𝔗.upperG'
  /-- The exchange map `β_f` of the proper Frobenius face of `f` is invertible. -/
  isIso_βF : IsIso (mateEquiv 𝔗.adjF 𝔗.adjF (TwoSquare.mk _ _ _ _ κF.inv)).natTrans
  /-- The exchange map `β_{f'}` of the proper Frobenius face of `f'` is invertible. -/
  isIso_βF' : IsIso (mateEquiv 𝔗.adjF' 𝔗.adjF' (TwoSquare.mk _ _ _ _ κF'.inv)).natTrans
  /-- The Frobenius cube commutes with the Cartesian identification. -/
  cube : ((TwoSquare.mk _ _ _ _ κF.inv ≫ₕ 𝔗.isoSquare).whiskerTop κG.hom) =
    ((𝔗.isoSquare ≫ₕ TwoSquare.mk _ _ _ _ κF'.inv).whiskerBottom κG'.hom)

namespace FrobeniusDatum

open Endofunctor

variable {𝔗 : BaseChangeSquare 𝒯 𝒰 𝒯' 𝒰'} (𝔉 : FrobeniusDatum 𝔗)

/-- The exchange isomorphism `β_f : Φ_Y f_* ≅ f_* Φ_X` of the proper Frobenius face of `f`,
written `f_* ⋙ Φ_Y ≅ Φ_X ⋙ f_*`. -/
noncomputable def βF : 𝔗.lowerF ⋙ 𝔉.ΦY ≅ 𝔉.ΦX ⋙ 𝔗.lowerF :=
  haveI := 𝔉.isIso_βF
  asIso (mateEquiv 𝔗.adjF 𝔗.adjF (TwoSquare.mk _ _ _ _ 𝔉.κF.inv)).natTrans

/-- The exchange isomorphism `β_{f'}` of the proper Frobenius face of `f'`. -/
noncomputable def βF' : 𝔗.lowerF' ⋙ 𝔉.ΦY' ≅ 𝔉.ΦX' ⋙ 𝔗.lowerF' :=
  haveI := 𝔉.isIso_βF'
  asIso (mateEquiv 𝔗.adjF' 𝔗.adjF' (TwoSquare.mk _ _ _ _ 𝔉.κF'.inv)).natTrans

/-- The Weil structure `Θ_B = g^*(β_f) ∘ κ_g` on `B = g^* f_* K` induced by a Weil structure on
`K` (Blueprint `def-weil-pbc-frobenius-corner-structures`). -/
noncomputable def weilB : IsoAlgebra 𝔉.ΦX ⥤ IsoAlgebra 𝔉.ΦY' :=
  IsoAlgebra.mapOfNatIso (IsoAlgebra.compCommIso 𝔉.βF 𝔉.κG)

/-- The Weil structure `Θ_D = f'_*(κ_{g'}) ∘ β_{f'}` on `D = f'_* g'^* K` induced by a Weil
structure on `K` (Blueprint `def-weil-pbc-frobenius-corner-structures`). -/
noncomputable def weilD : IsoAlgebra 𝔉.ΦX ⥤ IsoAlgebra 𝔉.ΦY' :=
  IsoAlgebra.mapOfNatIso (IsoAlgebra.compCommIso 𝔉.κG' 𝔉.βF')

/-- **The exchange map commutes with the Frobenius structures**: the pasting coherence of the
exchange maps of the Frobenius cube, as an identity of natural transformations
`g^* f_* Φ_X ⟶ Φ_{Y'} f'_* g'^*` … written `(f_* ⋙ g^*) ⋙ Φ_{Y'} ⟶ Φ_X ⋙ (g'^* ⋙ f'_*)`.
Both sides are mates of the two halves of the commutative Frobenius cube. -/
lemma exchange_comm :
    whiskerRight 𝔗.exchange.natTrans 𝔉.ΦY' ≫ (IsoAlgebra.compCommIso 𝔉.κG' 𝔉.βF').hom =
      (IsoAlgebra.compCommIso 𝔉.βF 𝔉.κG).hom ≫ whiskerLeft 𝔉.ΦX 𝔗.exchange.natTrans := by
  have h := congr_arg (fun α ↦ (mateEquiv 𝔗.adjF 𝔗.adjF' α).natTrans) 𝔉.cube
  rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_whiskerTop_whiskerBottom,
    mateEquiv_vcomp 𝔗.adjF 𝔗.adjF 𝔗.adjF', mateEquiv_vcomp 𝔗.adjF 𝔗.adjF' 𝔗.adjF'] at h
  ext K
  have hK := congr_app h K
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app] at hK
  simp only [NatTrans.comp_app, whiskerRight_app, IsoAlgebra.compCommIso_hom_app,
    whiskerLeft_app]
  simpa [βF, βF', exchange] using hK.symm

/-- **The exchange map is a Weil morphism** `ξ : (B, Θ_B) ⟶ (D, Θ_D)` (Blueprint
`lemma-weil-pbc-frobenius-level-rectangle`, the equation for `v'`). -/
noncomputable def weilExchange : 𝔉.weilB ⟶ 𝔉.weilD :=
  IsoAlgebra.mapOfNatIsoHom 𝔗.exchange.natTrans 𝔉.exchange_comm

@[simp]
lemma weilExchange_app_hom_f (K : IsoAlgebra 𝔉.ΦX) :
    (𝔉.weilExchange.app K).hom.f = 𝔗.exchange.natTrans.app K.carrier := rfl

end FrobeniusDatum

end BaseChangeSquare

end CategoryTheory
