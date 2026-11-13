/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.RingTheory.SelfTorConormalComparison
public import Mathlib.AlgebraicGeometry.Modules.Tilde

import WeilConjectures.AlgebraicGeometry.SelfTorNestedAffineCoordinates
import WeilConjectures.AlgebraicGeometry.Modules.AffineHom

/-! # Compatible affine self-Tor comparison maps

## References

* [Stacks Project, Tag 09PQ](https://stacks.math.columbia.edu/tag/09PQ)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 06YH](https://stacks.math.columbia.edu/tag/06YH)
* [Stacks Project, Tag 01I6](https://stacks.math.columbia.edu/tag/01I6)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- An affine coordinate square for a local comparison, before duality.
The coordinate maps themselves need not be invertible comparisons; only the changes
of coordinates are isomorphisms. No regularity hypothesis is imposed. -/
def IsAffineSelfTorChartMap {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    (U : Y.affineOpens) (n : ℕ) (E Q : Z.Modules)
    (φ : E.over (i ⁻¹ᵁ U.1) ⟶ Q.over (i ⁻¹ᵁ U.1)) : Prop :=
  let T := tilde.functor Γ(Y, U.1) ⋙
    Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
    Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
  let c := selfTorConormalComparison (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
  ∃ (s : E.over (i ⁻¹ᵁ U.1) ≅ (T.obj _).over (i ⁻¹ᵁ U.1))
    (t : (T.obj _).over (i ⁻¹ᵁ U.1) ≅ Q.over (i ⁻¹ᵁ U.1)),
    φ = s.hom ≫ (T.map c).over (i ⁻¹ᵁ U.1) ≫ t.hom

/-- A local affine model is quasi-coherent on the inverse-image chart, so maps from
any isomorphic source are determined by the component on the whole chart. -/
private theorem affine_model_hom_ext
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (U : Y.affineOpens) (M : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (E Q : Z.Modules)
    (s : E.over (i ⁻¹ᵁ U.1) ≅
      (((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
        Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i).obj M).over
          (i ⁻¹ᵁ U.1)))
    (f g : E.over (i ⁻¹ᵁ U.1) ⟶ Q.over (i ⁻¹ᵁ U.1))
    (h : f.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1)))) =
      g.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1))))) : f = g := by
  let V := i ⁻¹ᵁ U.1
  let B := (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj
    ((tilde.functor Γ(Y, U.1)).obj M)
  let C := (Scheme.Modules.pushforward U.1.ι).obj B
  let D := (Scheme.Modules.tensorPullback i).obj C
  let r := i ∣_ U.1
  let a := (Scheme.Modules.nonempty_tensorPullbackAdjunction i).some.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction i)
  let e₀ : (Scheme.Modules.restrictFunctor V.ι).obj D ≅
      (Scheme.Modules.pullback r).obj B :=
    (Scheme.Modules.restrictFunctor V.ι).mapIso (a.app C) ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).app
        ((Scheme.Modules.pullback i).obj C) ≪≫
      (Scheme.Modules.pullbackComp V.ι i).app C ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι i U.1).symm).app C ≪≫
      ((Scheme.Modules.pullbackComp r U.1.ι).symm).app C ≪≫
      (Scheme.Modules.pullback r).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app C).symm ≪≫
      (Scheme.Modules.pullback r).mapIso
        ((Scheme.Modules.restrictFunctorAdjCounitIso U.1.ι).app B)
  have : ((tilde.functor Γ(Y, U.1)).obj M).IsQuasicoherent := by
    change (tilde M).IsQuasicoherent
    infer_instance
  have : B.IsQuasicoherent := by
    dsimp only [B]
    infer_instance
  have : ((Scheme.Modules.pullback r).obj B).IsQuasicoherent := by infer_instance
  have : ((Scheme.Modules.restrictFunctor V.ι).obj D).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso e₀.symm
      (by infer_instance)
  have hV : IsAffineOpen V := U.2.preimage i
  let : IsAffine V.toScheme := hV
  let F := (Scheme.Modules.overEquiv V).functor
  let e := F.mapIso s ≪≫ (Scheme.Modules.overFunctorEquiv V).app D
  have : (F.obj (E.over V)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso e.symm
      (by infer_instance)
  apply F.map_injective
  apply Scheme.Modules.hom_ext_of_isAffine
  intro x
  change f.val.app (op (V.overEquivalence.inverse.obj (⊤ : V.toScheme.Opens))) x =
    g.val.app (op (V.overEquivalence.inverse.obj (⊤ : V.toScheme.Opens))) x
  let W := V.overEquivalence.inverse.obj (⊤ : V.toScheme.Opens)
  have hw : W.left = V := by
    ext z
    change z ∈ Subtype.val '' (Set.univ : Set V) ↔ z ∈ V
    simp
  let δ : W ≅ Over.mk (𝟙 V) := Over.isoMk (eqToIso hw)
  have hs := (ConcreteCategory.bijective_of_isIso
    ((E.over V).val.presheaf.map δ.hom.op)).2
  obtain ⟨y, hy⟩ := hs x
  change (E.over V).val.map δ.hom.op y = x at hy
  rw [← hy]
  have hf := PresheafOfModules.naturality_apply f.val δ.hom.op y
  have hg := PresheafOfModules.naturality_apply g.val δ.hom.op y
  exact hf.trans ((congrArg (fun k ↦ (Q.over V).val.map δ.hom.op (k y)) h).trans hg.symm)


private theorem affine_chart_maps_compatible_of_nested
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) (E Q : Z.Modules)
    (φ : ∀ U : Y.affineOpens, E.over (i ⁻¹ᵁ U.1) ⟶ Q.over (i ⁻¹ᵁ U.1))
    (hlocal : ∀ (V : Y.affineOpens) (f g : E.over (i ⁻¹ᵁ V.1) ⟶
        Q.over (i ⁻¹ᵁ V.1)),
      f.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1)))) =
        g.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1)))) → f = g)
    (hnested : ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1),
      (φ U).val.app (op (Over.mk (homOfLE ((TopologicalSpace.Opens.map i.base).monotone h)))) =
        (φ V).val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1)))))
    (U U' : Y.affineOpens) (W : Z.Opens)
    (a : W ⟶ i ⁻¹ᵁ U.1) (b : W ⟶ i ⁻¹ᵁ U'.1) :
    (φ U).val.app (op (Over.mk a)) = (φ U').val.app (op (Over.mk b)) := by
  have hrestrict (V U : Y.affineOpens) (h : V.1 ≤ U.1)
      (L : Z.Opens) (g : L ⟶ i ⁻¹ᵁ V.1) :
      (φ U).val.app (op (Over.mk
        (g ≫ homOfLE ((TopologicalSpace.Opens.map i.base).monotone h)))) =
        (φ V).val.app (op (Over.mk g)) := by
    let a := homOfLE ((TopologicalSpace.Opens.map i.base).monotone h)
    let ψ : E.over (i ⁻¹ᵁ V.1) ⟶ Q.over (i ⁻¹ᵁ V.1) :=
      { val :=
        { app := fun W ↦ (φ U).val.app (op (Over.mk (W.unop.hom ≫ a)))
          naturality := by
            intro W W' k
            exact (φ U).val.naturality
              (Over.homMk k.unop.left
                (by
                  change k.unop.left ≫ (W.unop.hom ≫ a) = W'.unop.hom ≫ a
                  rw [← Category.assoc, Over.w]) :
                Over.mk (W'.unop.hom ≫ a) ⟶ Over.mk (W.unop.hom ≫ a)).op } }
    have hψ : ψ = φ V := hlocal V ψ (φ V) (by
      change (φ U).val.app (op (Over.mk ((𝟙 _) ≫ a))) = _
      rw [Category.id_comp]
      exact hnested V U h)
    exact congrArg (fun f ↦ f.val.app (op (Over.mk g))) hψ
  apply ModuleCat.hom_ext
  ext x
  let R : Sieve W :=
    { arrows := fun L g ↦ ∃ V : Y.affineOpens, V.1 ≤ U.1 ∧ V.1 ≤ U'.1 ∧ L ≤ i ⁻¹ᵁ V.1
      downward_closed := by
        rintro L L' g ⟨V, hVU, hVU', hL⟩ f
        exact ⟨V, hVU, hVU', (leOfHom f).trans hL⟩ }
  have hR : R ∈ Opens.grothendieckTopology Z W := by
    intro z hz
    obtain ⟨V, hV, hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset
      (show i z ∈ U.1 ⊓ U'.1 from ⟨leOfHom a hz, leOfHom b hz⟩)
    exact ⟨W ⊓ i ⁻¹ᵁ V, homOfLE inf_le_left,
      ⟨⟨V, hV⟩, (show V ≤ U.1 ⊓ U'.1 from hVU).trans inf_le_left,
        (show V ≤ U.1 ⊓ U'.1 from hVU).trans inf_le_right, inf_le_right⟩,
      ⟨hz, hzV⟩⟩
  have hQ := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf (Opens.grothendieckTopology Z) _
      (forget _) Q.isSheaf)
  refine (hQ R hR).isSeparatedFor.ext fun L g hg ↦ ?_
  obtain ⟨V, hVU, hVU', hLV⟩ := hg
  have hU := PresheafOfModules.naturality_apply (φ U).val
    (Over.homMk g : Over.mk (g ≫ a) ⟶ Over.mk a).op x
  have hU' := PresheafOfModules.naturality_apply (φ U').val
    (Over.homMk g : Over.mk (g ≫ b) ⟶ Over.mk b).op x
  have heq : (φ U).val.app (op (Over.mk (g ≫ a))) =
      (φ U').val.app (op (Over.mk (g ≫ b))) := by
    have h₁ := hrestrict V U hVU L (homOfLE hLV)
    have h₂ := hrestrict V U' hVU' L (homOfLE hLV)
    have ha : g ≫ a = homOfLE hLV ≫
        homOfLE ((TopologicalSpace.Opens.map i.base).monotone hVU) :=
      Subsingleton.elim _ _
    have hb : g ≫ b = homOfLE hLV ≫
        homOfLE ((TopologicalSpace.Opens.map i.base).monotone hVU') :=
      Subsingleton.elim _ _
    rw [ha, hb]
    exact h₁.trans h₂.symm
  exact hU.symm.trans ((congrArg (fun f ↦ f (E.val.map g.op x)) heq).trans hU')

/-- Affine normalized comparisons exist locally and agree on overlaps. -/
theorem exists_compatible_affine_selfTor_maps
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    let E := Scheme.Modules.exteriorPower
      ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n
    ∃ φ : ∀ U : Y.affineOpens, E.over (i ⁻¹ᵁ U.1) ⟶ Q.over (i ⁻¹ᵁ U.1),
      (∀ U, IsAffineSelfTorChartMap i U n E Q (φ U)) ∧
      ∀ (U U' : Y.affineOpens) (W : Z.Opens)
        (a : W ⟶ i ⁻¹ᵁ U.1) (b : W ⟶ i ⁻¹ᵁ U'.1),
        (φ U).val.app (op (Over.mk a)) =
          (φ U').val.app (op (Over.mk b)) := by
  obtain ⟨s, t, hnested⟩ := exists_nested_affine_selfTor_coordinates i n
  let T := fun U : Y.affineOpens ↦
    tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
  let c := fun U : Y.affineOpens ↦
    selfTorConormalComparison (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
  let φ := fun U ↦ (s U).hom ≫ ((T U).map (c U)).over (i ⁻¹ᵁ U.1) ≫ (t U).hom
  refine ⟨φ, ?_, ?_⟩
  · intro U
    exact ⟨s U, t U, rfl⟩
  · exact affine_chart_maps_compatible_of_nested i _ _ φ
      (fun V f g h ↦ affine_model_hom_ext i V _ _ _ (s V) f g h) hnested

end AlgebraicGeometry
