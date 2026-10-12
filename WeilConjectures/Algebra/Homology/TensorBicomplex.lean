/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# The tensor bicomplex of two chain complexes of modules

For chain complexes `P, Q` of `R`-modules we form the (unsigned) double complex
`A(p, q) = P_p ⊗[R] Q_q` with horizontal differential `d_P ⊗ 1` and vertical differential
`1 ⊗ d_Q`, functorially in `P` and `Q`; and the chain map `P ⊗ N → P' ⊗ N'` attached to a chain
map `a : P → P'` and a linear map `g : N → N'`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace HomologicalComplex₂

variable {R : Type u} [CommRing R]

/-- The bifunctor `(P, Q) ↦ A(P, Q)`, `A(p, q) = P_p ⊗ Q_q`, with differentials `d_P ⊗ 1` and
`1 ⊗ d_Q`; on morphisms `A(a, b)_{p,q} = a_p ⊗ b_q`.
(blueprint: `def-weil-pbc-tensor-bicomplex`) -/
noncomputable abbrev tensorBicomplexFunctor :
    ChainComplex (ModuleCat.{u} R) ℕ ⥤ ChainComplex (ModuleCat.{u} R) ℕ ⥤
      HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex _ _

/-- The tensor bicomplex `A(P, Q)` of two chain complexes of `R`-modules.
(blueprint: `def-weil-pbc-tensor-bicomplex`) -/
noncomputable abbrev tensorBicomplex (P Q : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (tensorBicomplexFunctor.obj P).obj Q

lemma tensorBicomplex_X_X (P Q : ChainComplex (ModuleCat.{u} R) ℕ) (p q : ℕ) :
    ((tensorBicomplex P Q).X p).X q = P.X p ⊗ Q.X q := rfl

/-- The chain map `P ⊗ N → P' ⊗ N'` with components `a_p ⊗ g` attached to a chain map
`a : P ⟶ P'` and a linear map `g : N ⟶ N'`. (blueprint: `def-weil-pbc-tensor-bicomplex`) -/
noncomputable def chainTensorMap {P P' : ChainComplex (ModuleCat.{u} R) ℕ} (a : P ⟶ P')
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ)).obj P ⟶
      ((tensorRight N').mapHomologicalComplex (ComplexShape.down ℕ)).obj P' where
  f p := a.f p ⊗ₘ g
  comm' i j _ := by
    change (a.f i ⊗ₘ g) ≫ (P'.d i j ⊗ₘ 𝟙 N') = (P.d i j ⊗ₘ 𝟙 N) ≫ (a.f j ⊗ₘ g)
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, a.comm, Category.comp_id,
      Category.id_comp]

end HomologicalComplex₂
