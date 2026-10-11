/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExtFlatBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Vanishing
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechModuleBaseChange

/-!
# Cohomology and flat base change

Consider a cartesian square of schemes
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` and `T = Spec B` affine, `g` flat and `f` quasi-compact and quasi-separated,
and let `ℱ` be a quasi-coherent `𝒪_X`-module. Then `H^q(X, ℱ) ⊗_A B ≅ H^q(Y, g'^* ℱ)`
(Stacks 02KH).

## Strategy

Everything happens on `X`. The morphism `g'` is affine, so `H^q(Y, g'^* ℱ) = H^q(X, ℱ'')` for the
quasi-coherent module `ℱ'' = g'_* g'^* ℱ`, on which `B` acts by sheaf endomorphisms. For every
open `W` of `X` there is a base change map `B ⊗_A H^q(W, ℱ) ⟶ H^q(W, ℱ'')`, `b ⊗ x ↦ b • η_* x`
for the unit `η : ℱ ⟶ ℱ''`, and we show that it is bijective
* on affine opens: in positive degrees both sides vanish, and in degree `0` this is the base
  change of sections `B ⊗_A Γ(W, ℱ) ≅ Γ(g'⁻¹ W, g'^* ℱ)`;
* on `U ∪ V` if it is so on `U`, `V` and `U ∩ V`, by the Mayer–Vietoris sequences and the five
  lemma, `B` being flat over `A` (`CategoryTheory.Abelian.Ext.WithAction`);
* hence on finite unions of affine opens contained in an affine open (intersections of affine
  opens in an affine scheme are affine), then on all quasi-compact opens of the quasi-separated
  scheme `X`, in particular on `X` itself.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace TensorProduct Opposite

namespace TopCat.Sheaf

open CategoryTheory.Abelian

variable {X : TopCat.{u}}

lemma homFreeSheafEquiv_eq (U : Opens X)
    {G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (φ : freeSheaf U ⟶ G) :
    homFreeSheafEquiv U G φ =
      φ.hom.app (op U) (homFreeSheafEquiv U (freeSheaf U) (𝟙 (freeSheaf U))) := by
  rw [← homFreeSheafEquiv_comp, Category.id_comp]

/-- The cohomology in degree `0` of an abelian sheaf `G` on an open `U` is `G(U)`:
`Ext⁰(ℤ_U, G) ≅ Hom(ℤ_U, G) ≅ G(U)`. -/
noncomputable def extFreeSheafZeroAddEquiv (U : Opens X)
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Ext (freeSheaf U) G 0 ≃+ G.obj.obj (op U) where
  toEquiv := Ext.addEquiv₀.toEquiv.trans (homFreeSheafEquiv U G)
  map_add' x y := by
    change homFreeSheafEquiv U G (Ext.addEquiv₀ (x + y)) =
      homFreeSheafEquiv U G (Ext.addEquiv₀ x) + homFreeSheafEquiv U G (Ext.addEquiv₀ y)
    rw [map_add]
    rw [homFreeSheafEquiv_eq, homFreeSheafEquiv_eq U (Ext.addEquiv₀ x),
      homFreeSheafEquiv_eq U (Ext.addEquiv₀ y)]
    rfl

lemma extFreeSheafZeroAddEquiv_comp_mk₀ (U : Opens X)
    {G G' : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (x : Ext (freeSheaf U) G 0)
    (φ : G ⟶ G') :
    extFreeSheafZeroAddEquiv U G' (x.comp (Ext.mk₀ φ) (add_zero 0)) =
      φ.hom.app (op U) (extFreeSheafZeroAddEquiv U G x) := by
  change homFreeSheafEquiv U G' (Ext.addEquiv₀ _) = _
  rw [Ext.addEquiv₀_comp_mk₀, homFreeSheafEquiv_comp]
  rfl

end TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian.Ext

variable {X : Scheme.{u}}

/-- Multiplication by global functions on the underlying abelian sheaf of a sheaf of modules, as
a ring homomorphism to its endomorphisms. -/
noncomputable def smulRingHom (M : X.Modules) :
    Γ(X, ⊤) →+* End ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) where
  toFun a := (SheafOfModules.toSheaf X.ringCatSheaf).map (M.smulHom a)
  map_one' := by rw [smulHom_one, CategoryTheory.Functor.map_id]; rfl
  map_mul' a b := by rw [smulHom_mul, CategoryTheory.Functor.map_comp, End.mul_def]
  map_zero' := by rw [smulHom_zero, CategoryTheory.Functor.map_zero]
  map_add' a b := by rw [smulHom_add, CategoryTheory.Functor.map_add]

/-- Multiplication by global functions of `Y` on the underlying abelian sheaf of the pushforward
`g_* N` of a sheaf of modules along `g : Y ⟶ X`, as a ring homomorphism to its endomorphisms. -/
noncomputable def pushforwardSmulRingHom {Y : Scheme.{u}} (g : Y ⟶ X) (N : Y.Modules) :
    Γ(Y, ⊤) →+* End ((SheafOfModules.toSheaf X.ringCatSheaf).obj ((pushforward g).obj N)) where
  toFun b := (SheafOfModules.toSheaf X.ringCatSheaf).map ((pushforward g).map (N.smulHom b))
  map_one' := by
    rw [smulHom_one, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]; rfl
  map_mul' a b := by
    rw [smulHom_mul, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, End.mul_def]
  map_zero' := by
    rw [smulHom_zero, CategoryTheory.Functor.map_zero, CategoryTheory.Functor.map_zero]
  map_add' a b := by
    rw [smulHom_add, CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_add]

section BaseChange

variable {Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules)
  [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)

variable (f) in
/-- The action of `A = Γ(S, ⊤)` on the underlying abelian sheaf of `ℱ`, through `f^♯`. -/
noncomputable abbrev baseAction : Γ(S, ⊤) →+* End ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ) :=
  (smulRingHom ℱ).comp f.appTop.hom

variable (f' g') in
/-- The action of `B = Γ(T, ⊤)` on the underlying abelian sheaf of `g'_* g'^* ℱ`, through
`f'^♯`. -/
noncomputable abbrev pushforwardPullbackAction :
    Γ(T, ⊤) →+* End ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      ((pushforward g').obj ((pullback g').obj ℱ))) :=
  (pushforwardSmulRingHom g' ((pullback g').obj ℱ)).comp f'.appTop.hom

variable (g') in
/-- The unit `ℱ ⟶ g'_* g'^* ℱ`, on the underlying abelian sheaves. -/
noncomputable abbrev toSheafUnit :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj ((pushforward g').obj ((pullback g').obj ℱ)) :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map ((pullbackPushforwardAdjunction g').unit.app ℱ)

include H in
omit [Algebra Γ(S, ⊤) Γ(T, ⊤)] in
lemma appTop_appTop_of_isPullback (a : Γ(S, ⊤)) :
    g'.appTop (f.appTop a) = f'.appTop (g.appTop a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, H.w]

include H hg in
/-- The unit `ℱ ⟶ g'_* g'^* ℱ` intertwines the actions of `A` and `B`. -/
lemma baseAction_comp_toSheafUnit (a : Γ(S, ⊤)) :
    baseAction f ℱ a ≫ toSheafUnit g' ℱ =
      toSheafUnit g' ℱ ≫ pushforwardPullbackAction f' g' ℱ (algebraMap Γ(S, ⊤) Γ(T, ⊤) a) := by
  have key : ℱ.smulHom (f.appTop a) ≫ (pullbackPushforwardAdjunction g').unit.app ℱ =
      (pullbackPushforwardAdjunction g').unit.app ℱ ≫
        (pushforward g').map (((pullback g').obj ℱ).smulHom (f'.appTop (algebraMap _ _ a))) := by
    rw [smulHom_naturality, hg, ← appTop_appTop_of_isPullback H, pushforward_map_smulHom]
    rfl
  have h := congrArg (SheafOfModules.toSheaf X.ringCatSheaf).map key
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  exact h

/-- The base change map `B ⊗_A H^n(W, ℱ) ⟶ H^n(W, g'_* g'^* ℱ)`, `b ⊗ x ↦ b • η_* x`, for an open
`W` of `X` (with `H^n(W, -) = Ext^n(ℤ_W, -)`), or more generally with `ℤ_W` replaced by any
abelian sheaf `P`. -/
noncomputable abbrev cohomologyBaseChange (P : Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) (n : ℕ) :=
  WithAction.baseChange (baseAction f ℱ) (pushforwardPullbackAction f' g' ℱ) (toSheafUnit g' ℱ)
    (baseAction_comp_toSheafUnit H ℱ hg) P n

section Affine

variable [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

/-- `H⁰(W, ℱ) ≅ Γ(W, ℱ)` as `Γ(S, ⊤)`-modules. -/
noncomputable def sectionsLinearEquiv (W : X.Opens) :
    WithAction (baseAction f ℱ) (TopCat.Sheaf.freeSheaf W) 0 ≃ₗ[Γ(S, ⊤)]
      sectionsModule f ℱ W where
  __ := (WithAction.toExt _).trans (TopCat.Sheaf.extFreeSheafZeroAddEquiv W _)
  map_smul' a x := by
    change TopCat.Sheaf.extFreeSheafZeroAddEquiv W _
      ((WithAction.toExt _ x).comp (mk₀ (baseAction f ℱ a)) (add_zero 0)) = _
    rw [TopCat.Sheaf.extFreeSheafZeroAddEquiv_comp_mk₀]
    rfl


variable (f' g') in
/-- `H⁰(W, g'_* g'^* ℱ) ≅ Γ(g'⁻¹ W, g'^* ℱ)`. -/
noncomputable def pushforwardSectionsAddEquiv (W : X.Opens) :
    WithAction (pushforwardPullbackAction f' g' ℱ) (TopCat.Sheaf.freeSheaf W) 0 ≃+
      sectionsModule f' ((pullback g').obj ℱ) (g' ⁻¹ᵁ W) :=
  (WithAction.toExt _).trans (TopCat.Sheaf.extFreeSheafZeroAddEquiv W _)

include H hg in
/-- In degree `0` the base change map on an affine open `W` is the base change of sections
`B ⊗_A Γ(W, ℱ) ≅ Γ(g'⁻¹ W, g'^* ℱ)`, hence bijective. -/
lemma bijective_cohomologyBaseChange_zero_of_isAffineOpen {W : X.Opens} (hW : IsAffineOpen W) :
    Function.Bijective (cohomologyBaseChange H ℱ hg (TopCat.Sheaf.freeSheaf W) 0) := by
  have key : ⇑(pushforwardSectionsAddEquiv f' g' ℱ W) ∘
      ⇑(cohomologyBaseChange H ℱ hg (TopCat.Sheaf.freeSheaf W) 0) =
      ⇑(sectionsModuleBaseChange H ℱ hg W) ∘ ⇑((sectionsLinearEquiv ℱ W).lTensor Γ(T, ⊤)) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp only [Function.comp_apply, map_zero]
    | add z z' hz hz' =>
      simp only [Function.comp_apply, map_add] at hz hz' ⊢
      rw [hz, hz']
    | tmul b x =>
      change TopCat.Sheaf.extFreeSheafZeroAddEquiv W _ ((WithAction.toExt _ x).comp
          (mk₀ (toSheafUnit g' ℱ ≫ pushforwardPullbackAction f' g' ℱ b)) (add_zero 0)) =
        sectionsModuleBaseChange H ℱ hg W (b ⊗ₜ sectionsLinearEquiv ℱ W x)
      rw [TopCat.Sheaf.extFreeSheafZeroAddEquiv_comp_mk₀, sectionsModuleBaseChange_tmul]
      rfl
  refine (Function.Bijective.of_comp_iff' (pushforwardSectionsAddEquiv f' g' ℱ W).bijective
    _).mp ?_
  rw [key]
  exact (bijective_sectionsModuleBaseChange H ℱ hg hW).comp (LinearEquiv.bijective _)
end Affine

end BaseChange

end AlgebraicGeometry.Scheme.Modules
