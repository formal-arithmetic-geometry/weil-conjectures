/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCohomologyPresentation
import all Sheaf.CategoryTheory.DerivedExtEvaluation

/-! # Coefficient naturality of the fixed Ext evaluation -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor
namespace CategoryTheory
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] derivedExtEvaluation

private theorem derivedExtEvaluation_map {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] [HasExt.{u + 1} C] [EnoughInjectives C]
    [HasKInjectiveResolutions C]
    (P : C ⥤ AddCommGrpCat.{u + 1}) [P.Additive] [PreservesFiniteLimits P]
    (A B B' : C) (φ : B ⟶ B') (q : ℕ) (g : P.obj A) (x : Ext A B q) :
    derivedExtEvaluation P A B' q g (x.comp (Ext.mk₀ φ) (add_zero q)) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
        (P.rightDerivedFunctor.map
          (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map φ)))
            (derivedExtEvaluation P A B q g x) := by
  let R := P.rightDerivedFunctor
  let S := DerivedCategory.singleFunctor C 0
  let H₀ := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
  let Hq := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)
  let τ : shiftFunctor _ (q : ℤ) ⋙ R ⋙ H₀ ≅ R ⋙ Hq :=
    Functor.isoWhiskerRight (R.commShiftIso (q : ℤ)) H₀ ≪≫
      Functor.isoWhiskerLeft R (H₀.shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _))
  let e := Functor.isoWhiskerLeft S τ ≪≫
    Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ C 0) (R ⋙ Hq)
  have hn := e.hom.naturality φ
  dsimp only [e, τ, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom, NatTrans.comp_app,
    Functor.comp_map, Functor.map_comp] at hn
  have hx : Ext.homEquiv (x.comp (Ext.mk₀ φ) (add_zero q)) =
      Ext.homEquiv x ≫ (shiftFunctor _ (q : ℤ)).map (S.map φ) := by
    simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀]
    rfl
  unfold derivedExtEvaluation
  rw [hx]
  simp only [Functor.map_comp]
  have h := ConcreteCategory.congr_hom hn
    ((H₀.map (R.map (Ext.homEquiv x)))
      ((P.homologyRightDerivedFunctorObjSingleFunctorIso A 0 ≪≫
        P.rightDerivedZeroIsoSelf.app A).inv g))
  simp only [R, S, H₀, Hq, Functor.comp_obj,
    AddCommGrpCat.comp_apply] at h ⊢
  convert h using 1 <;> rfl

end
end CategoryTheory

namespace AlgebraicGeometry.Etale
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The fixed Ext evaluation commutes with a map of coefficients.
Source: Stacks Project, Tags 03FD and 01FT.
(blueprint: new-sheaf-h-derived-naturality).
Proof: Ext postcomposition represents postcomposition with the shifted single map.
Naturality of the derived shift, homology shift and single-complex comparisons
moves this map through evaluation at the fixed integer generator. This also works
in degree zero and on the empty scheme. -/
theorem sheafHToDerived_map {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) (q : ℕ)
    (x : Sheaf.H F q) :
    sheafHToDerived G q (Sheaf.H.map φ q x) =
      (cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map φ))
          (sheafHToDerived F q x) := by
  unfold sheafHToDerived
  exact derivedExtEvaluation_map _ _ _ _ φ q _ x

end
end AlgebraicGeometry.Etale
