/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.ChangeCoefficients

/-! # Independent coefficient/pullback infrastructure: FreeCoefficientPull -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Pullback of a free module followed by extension of scalars agrees with extension
of scalars followed by pullback, through the canonical free-module comparisons. -/
lemma pullIso_hom_app_free_comp (M : Sheaf (ProEt.topology Y) Ab.{u + 1}) :
    (Mod.extendScalars (coefficientMap a X)).map
          ((freeFunctorCompUpperStarIso Λ g).hom.app M) ≫
        (Mod.freeFunctorCompExtendScalarsIso (coefficientMap a X)).hom.app
          ((g)^*[Ab.{u + 1}].obj M) =
      (pullIso a g).hom.app ((Mod.freeFunctor (condensedRingObj Λ Y)).obj M) ≫
        (Strategy3.upperStar Λ' (g)).map ((Mod.freeFunctorCompExtendScalarsIso (coefficientMap a Y)).hom.app M) ≫
        (freeFunctorCompUpperStarIso Λ' g).hom.app M := by
  apply purity_free_pullback_cube
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g)
    (Mod.freeForgetAdjunction _) (Mod.freeForgetAdjunction _)
    (upperStarLowerStarAdjunction Λ g)
    (Mod.extendRestrictAdjunction (coefficientMap a Y))
    (Mod.extendRestrictAdjunction (coefficientMap a X))
    (Mod.freeForgetAdjunction _) (Mod.freeForgetAdjunction _)
    (upperStarLowerStarAdjunction Λ' g)
  intro N
  rw [Mod.purity_conjugate_freeFunctorCompExtendScalarsIso,
    Mod.purity_conjugate_freeFunctorCompExtendScalarsIso]
  simp only [freeFunctorCompUpperStarIso, pullIso, Adjunction.pullIsoOfComapIso,
    Equiv.apply_symm_apply, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  change 𝟙 _ = ((comapLowerStarIso a g).hom.app N).hom
  symm
  exact Mod.comapMapModComapIso_hom_app_hom _ _ _ _ _ _ N


end AlgebraicGeometry.ProEtale.Strategy3
