/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Scheme presentations of stack diagonals

Source: Stacks Project, spaces-groupoids.tex, Tag 04M9; algebraic.tex, Tag 04WZ
(blueprint: def-sfb-scheme-stack-diagonal-presentation).

Both projections of the representing equivalence are retained over the base.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory.Limits

namespace CategoryTheory

/-- A scheme presents the actual two-fibre product, with both specified projections.
Source: Stacks 04M9 (blueprint: def-sfb-scheme-stack-diagonal-presentation). -/
def IsSchemeStackDiagonalPresentation {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {T U R : Over S}
    (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F) (p : R ⟶ T) (q : R ⟶ U) : Prop :=
  ∃ e : BasedFunctor (discreteModuli (yoneda.obj R)) (moduliTwoFiberProduct a b),
    e.toFunctor.IsEquivalence ∧
    Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst a b))
      (discreteModuliMap (yoneda.map p))) ∧
    ∃ η : e.toFunctor ⋙ ObjectProperty.ι _ ⋙ Comma.snd a.toFunctor b.toFunctor ≅
        (discreteModuliMap (yoneda.map q)).toFunctor,
      ∀ x : (discreteModuli (yoneda.obj R)).obj,
        (discreteModuli (yoneda.obj U)).p.IsHomLift
          (𝟙 ((discreteModuli (yoneda.obj R)).p.obj x)) (η.hom.app x)

/-- Scheme representability and a property of the diagonal on all pairs of scheme tests.
Source: Stacks 04WZ and scheme-test diagonal criterion
(blueprint: def-sfb-scheme-stack-diagonal-presentation). -/
def HasSchemeStackDiagonalWith {S : AlgebraicGeometry.Scheme.{u}}
    (P : MorphismProperty AlgebraicGeometry.Scheme.{u})
    (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ∀ (T U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
      (b : BasedFunctor (discreteModuli (yoneda.obj U)) F),
    ∃ (R : Over S) (p : R ⟶ T) (q : R ⟶ U),
      IsSchemeStackDiagonalPresentation a b p q ∧ P (prod.lift p q).left

end CategoryTheory
