/-
Copyright (c) 2026 Claude and The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarComparison
public import WeilConjectures.WeilSheaf.SmoothPurityInverseSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullCoherence

/-! # Coefficient extension and a pullback factorization -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- The (Pull) isomorphisms are compatible with the transport of pullbacks along an equation of
morphisms of schemes. -/
lemma purity_pullIso_hom_app_comp_upperStarCongr_hom_app {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (pullIso a f).hom.app M ≫
        (upperStarCongr Λ' h).hom.app ((Mod.extendScalars (coefficientMap a Y)).obj M) =
      (Mod.extendScalars (coefficientMap a X)).map ((upperStarCongr Λ h).hom.app M) ≫
        (pullIso a g).hom.app M := by
  subst h
  simp only [upperStarCongr_self, Iso.refl_hom, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

variable {X U : Scheme.{u}} (p : U ⟶ X) (s : U ⟶ U) (hs : s ≫ p = p)

/-- The coefficient pullback comparison preserves the datum attached to a factorization. -/
lemma purity_extendScalars_map_factor_hom_comp_pullIso
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (Mod.extendScalars (coefficientMap a U)).map
          ((purityModuleFactorIso Λ p s hs).hom.app M) ≫
        (pullIso a p).hom.app M =
      (pullIso a s).hom.app ((p)^*⟦Λ⟧.obj M) ≫
        (s)^*⟦Λ'⟧.map ((pullIso a p).hom.app M) ≫
          (purityModuleFactorIso Λ' p s hs).hom.app
            ((Mod.extendScalars (coefficientMap a X)).obj M) := by
  have key : (Mod.extendScalars (coefficientMap a U)).map
        ((upperStarComp Λ s p).inv.app M) ≫
        (pullIso a (s ≫ p)).hom.app M =
      (pullIso a s).hom.app ((p)^*⟦Λ⟧.obj M) ≫
        (s)^*⟦Λ'⟧.map ((pullIso a p).hom.app M) ≫
          (upperStarComp Λ' s p).inv.app
            ((Mod.extendScalars (coefficientMap a X)).obj M) := by
    simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] using
      purity_inverse_square
        ((Mod.extendScalars (coefficientMap a U)).mapIso ((upperStarComp Λ s p).app M))
        ((upperStarComp Λ' s p).app ((Mod.extendScalars (coefficientMap a X)).obj M))
        ((pullIso a (s ≫ p)).hom.app M)
        ((pullIso a s).hom.app ((p)^*⟦Λ⟧.obj M) ≫
          (s)^*⟦Λ'⟧.map ((pullIso a p).hom.app M))
        (pullIso_hom_app_comp a s p M)
  simp only [purityModuleFactorIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← purity_pullIso_hom_app_comp_upperStarCongr_hom_app a
    hs M, reassoc_of% key]


end AlgebraicGeometry.ProEtale.CondensedRing
