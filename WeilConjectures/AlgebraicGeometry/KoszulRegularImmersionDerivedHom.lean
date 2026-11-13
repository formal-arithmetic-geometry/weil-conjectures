/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.Dimension.Finrank

import WeilConjectures.AlgebraicGeometry.KoszulRegularImmersionExtSheaf
import WeilConjectures.AlgebraicGeometry.ClosedImmersionRankStrataScalarFormality

/-!
# Derived Hom for a Koszul-regular closed immersion

## References

* Stacks Project, Duality for Schemes, Tag 0BQZ.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The derived internal Hom of the pushed-forward structure sheaf of a
Koszul-regular closed immersion is the pushforward of the shifted top exterior
power of the dual conormal sheaf (Stacks, Tag 0BQZ). -/
theorem koszulRegularImmersion_derivedInternalHom
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules))) :
    Nonempty
      ((derivedInternalHom (Opens.grothendieckTopology Y)
          Y.toRingedSpace.sheaf).obj
        (op ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            ((Scheme.Modules.pushforward i).obj
              (SheafOfModules.unit Z.ringCatSheaf))),
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf)) ≅
        (DerivedCategory.Q.obj
          (((Scheme.Modules.pushforward i).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (Scheme.Modules.locallyRankedExteriorComplex
              (SheafOfModules.homObj (R := Z.sheaf)
                ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
                (SheafOfModules.unit Z.ringCatSheaf)) r)))) := by
  let N := SheafOfModules.homObj (R := Z.sheaf)
    ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
    (SheafOfModules.unit Z.ringCatSheaf)
  let E (n : ℕ) := Scheme.Modules.exteriorPower
    ((Scheme.Modules.restrictFunctor (Scheme.Modules.exteriorRankOpen r n).ι).obj N) n
  apply closedImmersion_rankStrata_scalar_formality i r E
    (Scheme.Modules.locallyRankedExteriorTerm N r) (fun _ => rfl)
  intro q
  exact koszulRegularImmersion_extSheaf i hregular r hr q

end AlgebraicGeometry
