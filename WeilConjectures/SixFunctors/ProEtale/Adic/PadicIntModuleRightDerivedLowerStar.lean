/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetAbRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar

/-!
# Derived pushforward of `ℤ_ℓ`-modules and of `ℓ`-adic sheaves

For an arbitrary morphism of schemes `f : X ⟶ Y`, pulling back continuous functions along the
projections `V ×_Y X ⟶ V` is a morphism of ring objects `ℤ_ℓ,Y ⟶ f_* ℤ_ℓ,X`
(`AlgebraicGeometry.ProEtale.padicIntAbSheafToPushforward`), which defines the pushforward of
`ℤ_ℓ`-modules `AlgebraicGeometry.ProEtale.padicIntModPushforward` (the weakly étale case is
`AlgebraicGeometry.ProEtale.padicIntModLowerStar`). We compare its derived functor with the
derived pushforwards of abelian sheaves and of `ℓ`-adic sheaves:

* `Hᵠ(Rf_* M[0])_ab ≅ Hᵠ(Rf_* M_ab[0])` for a `ℤ_ℓ,X`-module `M`
  (`AlgebraicGeometry.ProEtale.forgetHomologyRightDerivedPadicIntModPushforwardIso`): the
  sections of `ℤ_ℓ,X` being torsion-free, `ℤ_ℓ,X` is a flat abelian sheaf
  (`CategoryTheory.Sheaf.preservesMonomorphisms_tensorLeft_of_flat`), so that underlying abelian
  sheaves of injective `ℤ_ℓ`-modules are injective;
* `res Hᵠ(Rf_* F[0]) ≅ Hᵠ(Rf_* (res F)[0])` for an `ℓ`-adic sheaf `F`, where `res` is the
  restriction of scalars `AlgebraicGeometry.ProEtale.AdicSheaf.restrictPadicInt` to
  `ℤ_ℓ`-modules (`AlgebraicGeometry.ProEtale.restrictPadicIntHomologyRightDerivedAdicLowerStarIso`):
  restriction of scalars commutes with the pushforwards
  (`AlgebraicGeometry.ProEtale.adicLowerStarRestrictPadicIntPushforwardIso`), and sends injective
  `ℓ`-adic sheaves to `f_*`-acyclic `ℤ_ℓ`-modules, their underlying abelian sheaves being
  injective (`WeilConjectures.SixFunctors.ProEtale.Adic.ForgetAbRightDerivedLowerStar`).

For a `ℤ_ℓ,X`-module `M` (for instance the limit of an `ℓ`-adic tower), this gives the
comparison `ℚ̄_ℓ ⊗ Hᵠ(Rf_* M[0]) ⟶ Hᵠ(Rf_* (ℚ̄_ℓ ⊗ M)[0])`
(`AlgebraicGeometry.ProEtale.adicSheafExtendScalarsHomologyRightDerivedComparison`), and the
target is lisse as soon as the source is and the comparison is an isomorphism of underlying
abelian sheaves
(`isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_adicSheafExtendScalars`).
That the comparison is an isomorphism (extension of scalars `ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} -` commuting with
`Rf_*` for quasi-compact quasi-separated `f`) is not proved here.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

section ContinuousMap

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Type) [TopologicalSpace T] [Ring T]
  [IsTopologicalRing T]

/-- The comparison `C(-, T)_Y ⟶ f_* C(-, T)_X` of sheaves of rings on `Y_proét`: precomposition
with the projections `V ×_Y X ⟶ V`. -/
noncomputable def continuousMapRingSheafToPushforward :
    continuousMapRingSheaf Y T ⟶
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj (continuousMapRingSheaf X T) :=
  ⟨{ app V := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        (((ContinuousMap.compRightAlgHom ℤ T (pullback.fst V.unop.hom f).base.hom).toRingHom).comp
          ULift.ringEquiv.toRingHom))
     naturality V₁ V₂ a := by
       ext x
       refine ULift.ext _ _ (ContinuousMap.ext fun y ↦ ?_)
       change x.down (a.unop.left (pullback.fst _ f y)) =
         x.down (pullback.fst _ f (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map
           a.unop).left y))
       have key : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map a.unop).left ≫
           pullback.fst _ f = pullback.fst _ f ≫ a.unop.left :=
         pullback.lift_fst _ _ _
       rw [← Scheme.Hom.comp_apply, ← key]
       rfl }⟩

end ContinuousMap

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Continuous `ℓ`-adic functions form a torsion-free abelian group. -/
instance (T : Type*) [TopologicalSpace T] : IsAddTorsionFree (ULift.{u + 1} C(T, ℤ_[l])) :=
  Function.Injective.isAddTorsionFree
    ((ContinuousMap.coeFnAddMonoidHom).comp (AddEquiv.ulift (α := C(T, ℤ_[l]))).toAddMonoidHom)
    (DFunLike.coe_injective.comp ULift.down_injective)

end AlgebraicGeometry.ProEtale

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

/-- **Tensoring with an abelian sheaf with flat sections preserves monomorphisms**: up to
isomorphism it is the sheafification of the sectionwise tensor product, which preserves
injections. -/
lemma preservesMonomorphisms_tensorLeft_of_flat (S : Sheaf J Ab.{u + 1})
    (hS : ∀ U, Module.Flat ℤ (S.obj.obj U)) : (tensorLeft S).PreservesMonomorphisms := by
  let P := S.obj
  have hP : (tensorLeft ((presheafToSheaf J Ab.{u + 1}).obj P)).PreservesMonomorphisms := by
    refine ⟨fun {M N} g _ ↦ ?_⟩
    have : Mono g.hom := (sheafToPresheaf J _).map_mono g
    have (U : Cᵒᵖ) : Mono ((P ◁ g.hom).app U) := by
      have hU : Mono (g.hom.app U) := inferInstance
      rw [AddCommGrpCat.mono_iff_injective] at hU ⊢
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := P.obj U)
        (g.hom.app U).hom.toIntLinearMap hU
    have : Mono (P ◁ g.hom) := NatTrans.mono_of_mono_app _
    let e := Sheaf.presheafToSheafCompTensorLeftIso (J := J) (A := Ab.{u + 1}) P
    have h₁ : (presheafToSheaf J _).obj P ◁ (presheafToSheaf J _).map g.hom =
        e.hom.app _ ≫ (presheafToSheaf J _).map (P ◁ g.hom) ≫ e.inv.app _ := by
      have hn := e.hom.naturality g.hom
      change _ ◁ _ ≫ _ = _ ≫ (presheafToSheaf J _).map (P ◁ g.hom) at hn
      rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id _).symm
    let ε := (sheafificationAdjunction J Ab.{u + 1}).counit
    have h₂ : g = inv (ε.app M) ≫ (presheafToSheaf J _).map g.hom ≫ ε.app N := by
      rw [IsIso.eq_inv_comp]
      exact (ε.naturality g).symm
    change Mono ((presheafToSheaf J _).obj P ◁ g)
    rw [h₂, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp, h₁]
    infer_instance
  exact Functor.PreservesMonomorphisms.of_iso (F := tensorLeft ((presheafToSheaf J _).obj P))
    ((tensoringLeft _).mapIso (asIso ((sheafificationAdjunction J _).counit.app S)))

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### Restriction of scalars from `ℓ`-adic sheaves to `ℤ_ℓ`-modules -/

/-! ### Extension of scalars and the derived pushforward -/

end AlgebraicGeometry.ProEtale
