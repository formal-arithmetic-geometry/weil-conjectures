/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.KoszulSelfExtYonedaSurjection
import WeilConjectures.AlgebraicGeometry.KoszulSelfExtStalkBases
import Mathlib.RingTheory.FiniteType

/-! # Self-coefficient Koszul Ext and exterior powers

## References

* Stacks Project, Tag 0BQZ.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Self-coefficient Ext on the Koszul-regular locus is the full exterior algebra
of the conormal dual, in every nonnegative degree, without a rank hypothesis
(Stacks, Tags 0BQW, 0BQY, 0BQZ). -/
theorem koszulRegularImmersion_self_ext_exterior
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (hregular : ∀ z : Z, z ∈ V → ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G) ≅
      Scheme.Modules.exteriorPower
        ((Scheme.Modules.restrictFunctor V.ι).obj
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf))) n) := by
  classical
  dsimp only
  obtain ⟨φ, hφ⟩ := koszulRegularImmersion_self_ext_yoneda_surjection i V n hregular
  have : IsIso φ := by
    apply Scheme.Modules.isIso_of_bijective_stalkLinearMap
    intro z
    obtain ⟨U, hzU, m, f, hf, hreg⟩ := hregular z.1 z.2
    obtain ⟨⟨bT⟩, ⟨bE⟩⟩ :=
      koszulRegularImmersion_self_ext_stalk_bases i V n z U hzU m f hf hreg
    let := Module.Finite.of_basis bT
    let e := bE.equiv bT (Equiv.refl _)
    exact OrzechProperty.bijective_of_surjective_of_injective
      e.toLinearMap (φ.stalkLinearMap z) e.injective (hφ z)
  exact ⟨(asIso φ).symm⟩

end AlgebraicGeometry
