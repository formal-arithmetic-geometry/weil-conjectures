/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheafSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Sections of a pro-étale sheaf trivialized along a weakly étale morphism

Let `F` be a sheaf of `Λ`-modules on the small pro-étale site of `Y`, `g : W ⟶ Y` weakly étale
and `ε : g^* F ≅ M_W` a trivialization by the constant sheaf at a discrete `Λ`-module `M`. For a
weakly étale `Y`-scheme `T` together with a `Y`-morphism `h : T ⟶ W`, the sections of `F` over
`T` are the locally constant functions `T → M`
(`AlgebraicGeometry.ProEtale.trivSections`), naturally in `(T, h)`
(`AlgebraicGeometry.ProEtale.trivSections_map`): the pullback `g^*` is the restriction along
the localization functor, and the constant sheaf is the sheaf of locally constant functions.

Two trivializations of `F` over the same `T` differ, at every point `z` of `T`, by a linear
bijection of the values (`AlgebraicGeometry.ProEtale.trivTransition`,
`AlgebraicGeometry.ProEtale.trivSections_apply_eq_trivTransition`): a section `s` is constant
near `z` for the first trivialization, hence equal near `z` to the section with constant value
`s(z)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Scheme.continuousConstSMul_of_discreteTopology

variable {Λ : Type (u + 1)} [CommRing Λ] {Y W : Scheme.{u}}
  (F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))
  (g : W ⟶ Y) [WeaklyEtale g] (M : Type (u + 1)) [AddCommGroup M] [Module Λ M]
  [TopologicalSpace M] [DiscreteTopology M]

/-- A trivialization of `g^* F` by a constant sheaf, as an isomorphism between the restriction
of `F` along the localization functor and the sheaf of locally constant functions. -/
noncomputable def trivIso
    (ε : (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).obj F ≅
      (constantSheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ M)) :
    (ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) g inferInstance).obj F ≅
      ProEt.continuousMapSheafModule W Λ M :=
  ((ProEtale.upperStarIsoLocalizationRestriction _ g inferInstance).app F).symm ≪≫ ε ≪≫
    ProEt.constantSheafIsoContinuousMapSheafModule W Λ M

variable {g} in
/-- A `Y`-morphism from a weakly étale `Y`-scheme to `W` is weakly étale. -/
lemma weaklyEtale_of_comp_eq {T : Y.ProEt} (h : T.left ⟶ W) (hh : h ≫ g = T.hom) :
    WeaklyEtale h :=
  MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) h g ‹_›
    (hh ▸ T.prop)

/-- The object `(T, h)` of the small pro-étale site of `W`. -/
noncomputable def trivObj {T : Y.ProEt} (h : T.left ⟶ W) (hh : h ≫ g = T.hom) : W.ProEt :=
  have := weaklyEtale_of_comp_eq h hh
  Scheme.ProEt.mk h

/-- The object `(T, h)` of the small pro-étale site of `W`, viewed over `Y`, is `T`. -/
noncomputable def trivObjIso {T : Y.ProEt} (h : T.left ⟶ W) (hh : h ≫ g = T.hom) :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).obj (trivObj g h hh) ≅ T :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by simp [trivObj, hh])

variable {F g M}

/-- **Sections of a trivialized sheaf.** For a `Y`-morphism `h : T ⟶ W`, the sections of `F`
over `T` are the locally constant functions `T → M`. -/
noncomputable def trivSections
    (ε : (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).obj F ≅
      (constantSheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ M))
    (T : Y.ProEt) (h : T.left ⟶ W) (hh : h ≫ g = T.hom) :
    F.obj.obj (op T) ≃ₗ[Λ] C(T.left, M) :=
  (F.obj.mapIso (trivObjIso g h hh).op ≪≫
    ((sheafToPresheaf _ _).mapIso (trivIso F g M ε)).app (op (trivObj g h hh))).toLinearEquiv

variable (ε : (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).obj F ≅
  (constantSheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ M))

/-- The identification of sections of a trivialized sheaf is natural. -/
lemma trivSections_map {T T' : Y.ProEt} (f : T' ⟶ T) (h : T.left ⟶ W) (hh : h ≫ g = T.hom)
    (h' : T'.left ⟶ W) (hh' : h' ≫ g = T'.hom) (hf : f.left ≫ h = h')
    (s : F.obj.obj (op T)) :
    trivSections ε T' h' hh' (F.obj.map f.op s) =
      (trivSections ε T h hh s).comp f.left.base.hom := by
  have := weaklyEtale_of_comp_eq h hh
  have := weaklyEtale_of_comp_eq h' hh'
  let φ : trivObj g h' hh' ⟶ trivObj g h hh := MorphismProperty.Over.homMk f.left hf
  have key : (trivObjIso g h' hh').hom ≫ f =
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).map φ ≫
        (trivObjIso g h hh).hom := by
    ext
    simp [trivObjIso, φ]
  have nat := ConcreteCategory.congr_hom ((trivIso F g M ε).hom.hom.naturality φ.op)
    (F.obj.map (trivObjIso g h hh).hom.op s)
  have h1 : F.obj.map (trivObjIso g h' hh').hom.op (F.obj.map f.op s) =
      F.obj.map ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).map φ).op
        (F.obj.map (trivObjIso g h hh).hom.op s) := by
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← F.obj.map_comp, ← F.obj.map_comp,
      ← op_comp, ← op_comp, key]
  change (trivIso F g M ε).hom.hom.app (op (trivObj g h' hh'))
      (F.obj.map (trivObjIso g h' hh').hom.op (F.obj.map f.op s)) =
    ((trivIso F g M ε).hom.hom.app (op (trivObj g h hh))
      (F.obj.map (trivObjIso g h hh).hom.op s)).comp f.left.base.hom
  rw [h1]
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at nat
  erw [nat]
  rfl

section Transition

variable {M' : Type (u + 1)} [AddCommGroup M'] [Module Λ M'] [TopologicalSpace M']
  [DiscreteTopology M'] {W' : Scheme.{u}} {g' : W' ⟶ Y} [WeaklyEtale g']
  (ε' : (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').obj F ≅
    (constantSheaf (Scheme.ProEt.topology W') (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ M'))

omit [WeaklyEtale g] in
/-- The sections over the open subscheme `T_Q` of `T` defined by an open `Q`, with its
morphism to `W`. -/
lemma ofOpenImmersion_hom_eq {T : Y.ProEt} (Q : T.left.Opens) (h : T.left ⟶ W)
    (hh : h ≫ g = T.hom) : (Q.ι ≫ h) ≫ g = (ProEt.ofOpenImmersion T Q.ι).hom := by
  simp [ProEt.ofOpenImmersion, hh]

/-- The transition between two trivializations at a point `z` of `T`: the value at `z` for the
second trivialization of the section with constant value `n` for the first. -/
noncomputable def trivTransition (T : Y.ProEt) (h : T.left ⟶ W) (hh : h ≫ g = T.hom)
    (h' : T.left ⟶ W') (hh' : h' ≫ g' = T.hom) (z : T.left) : M →ₗ[Λ] M' where
  toFun n := trivSections ε' T h' hh' ((trivSections ε T h hh).symm (ContinuousMap.const _ n)) z
  map_add' n n' := by
    change _ = (trivSections ε' T h' hh' _ + trivSections ε' T h' hh' _) z
    rw [← map_add, ← map_add]
    rfl
  map_smul' r n := by
    change _ = (r • trivSections ε' T h' hh' _) z
    rw [← map_smul, ← map_smul]
    rfl

lemma trivTransition_apply (T : Y.ProEt) (h : T.left ⟶ W) (hh : h ≫ g = T.hom)
    (h' : T.left ⟶ W') (hh' : h' ≫ g' = T.hom) (z : T.left) (n : M) :
    trivTransition ε ε' T h hh h' hh' z n =
      trivSections ε' T h' hh' ((trivSections ε T h hh).symm (ContinuousMap.const _ n)) z :=
  rfl

/-- **Two trivializations differ pointwise by the transition.** -/
lemma trivSections_apply_eq_trivTransition (T : Y.ProEt) (h : T.left ⟶ W)
    (hh : h ≫ g = T.hom) (h' : T.left ⟶ W') (hh' : h' ≫ g' = T.hom) (s : F.obj.obj (op T))
    (z : T.left) :
    trivSections ε' T h' hh' s z =
      trivTransition ε ε' T h hh h' hh' z (trivSections ε T h hh s z) := by
  set n := trivSections ε T h hh s z
  let Q := T.left.fiberOpens (trivSections ε T h hh s) n
  let r := ProEt.ofOpenImmersionHom T Q.ι
  let s' := (trivSections ε T h hh).symm (ContinuousMap.const _ n)
  have hr : F.obj.map r.op s = F.obj.map r.op s' := by
    apply (trivSections ε (ProEt.ofOpenImmersion T Q.ι) (Q.ι ≫ h)
      (ofOpenImmersion_hom_eq Q h hh)).injective
    rw [trivSections_map ε r h hh (Q.ι ≫ h) (ofOpenImmersion_hom_eq Q h hh) rfl,
      trivSections_map ε r h hh (Q.ι ≫ h) (ofOpenImmersion_hom_eq Q h hh) rfl]
    ext x
    simp only [ContinuousMap.comp_apply, s', LinearEquiv.apply_symm_apply,
      ContinuousMap.const_apply]
    exact (T.left.mem_fiberOpens _ _ _).1 x.2
  have key := congr_arg (fun t ↦ trivSections ε' (ProEt.ofOpenImmersion T Q.ι) (Q.ι ≫ h')
    (ofOpenImmersion_hom_eq Q h' hh') t ⟨z, (T.left.mem_fiberOpens _ _ _).2 rfl⟩) hr
  rw [trivSections_map ε' r h' hh' (Q.ι ≫ h') (ofOpenImmersion_hom_eq Q h' hh') rfl,
    trivSections_map ε' r h' hh' (Q.ι ≫ h') (ofOpenImmersion_hom_eq Q h' hh') rfl] at key
  exact key

/-- The transition between two trivializations at a point is bijective. -/
lemma bijective_trivTransition (T : Y.ProEt) (h : T.left ⟶ W) (hh : h ≫ g = T.hom)
    (h' : T.left ⟶ W') (hh' : h' ≫ g' = T.hom) (z : T.left) :
    Function.Bijective (trivTransition ε ε' T h hh h' hh' z) := by
  refine Function.bijective_iff_has_inverse.2 ⟨trivTransition ε' ε T h' hh' h hh z, ?_, ?_⟩
  · intro n
    have h1 := trivSections_apply_eq_trivTransition ε' ε T h' hh' h hh
      ((trivSections ε T h hh).symm (ContinuousMap.const _ n)) z
    rw [trivTransition_apply, trivTransition_apply]
    rw [LinearEquiv.apply_symm_apply, ContinuousMap.const_apply] at h1
    rw [trivTransition_apply] at h1
    exact h1.symm
  · intro n
    have h1 := trivSections_apply_eq_trivTransition ε ε' T h hh h' hh'
      ((trivSections ε' T h' hh').symm (ContinuousMap.const _ n)) z
    rw [trivTransition_apply, trivTransition_apply]
    rw [LinearEquiv.apply_symm_apply, ContinuousMap.const_apply] at h1
    rw [trivTransition_apply] at h1
    exact h1.symm

end Transition

end AlgebraicGeometry.ProEtale
