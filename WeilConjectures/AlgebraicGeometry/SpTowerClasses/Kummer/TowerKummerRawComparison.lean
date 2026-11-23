/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerCanonicalKummerExact

/-! # The existing Kummer composite in named complex coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Naming the actual Kummer complex does not change its Kummer composite. -/
theorem towerKummerComposite_eq_raw (l : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (k : Kummer l T)
    (f : (DerivedCategory.singleFunctor (Ab T) 0).obj (integers T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧) :
    kummerComposite (C := Ab T) (towerKummerComplex l k) (towerKummerShortExact l k) f =
      kummerComposite (C := Ab T)
        (ShortComplex.mk k.inclusion k.power k.zero) k.exact f := by
  exact congrArg
    (fun h : (towerKummerComplex l k).ShortExact ↦
      kummerComposite (C := Ab T) (towerKummerComplex l k) h f)
    (Subsingleton.elim (towerKummerShortExact l k) k.exact)

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
