/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.RingTheory.KoszulRegularSequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence
import Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom
import Sheaf.AlgebraicGeometry.KoszulRegularImmersionDerivedHom

/-! # Dualizing object of a Koszul-regular closed immersion

Source: Stacks Project, Duality for Schemes, Tag 0BR0, with Tag 0BQZ
(blueprint: lem-sc-smooth-proper-diagonal-koszul-dual).
-/

@[expose] public section

universe u wZ wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The right adjoint applied to the structure sheaf is the shifted top exterior power
of the normal sheaf, with the shift allowed to vary on the clopen rank strata.
The object `OY` is the structure sheaf in the quasi-coherent full subcategory; `hOY`
identifies its underlying derived object. The preservation witness `hpres` defines the
restriction of derived direct image, and `adj` says precisely that `a` is its right adjoint.
An isomorphism of underlying objects is an isomorphism in the full subcategory.

Source: Stacks, Tag 0BR0 (blueprint: lem-sc-smooth-proper-diagonal-koszul-dual).
Proof, following the node:
1. A closed immersion is finite (lem-weil-pbc-closed-immersion-finite), and Z is
Noetherian since Y is. Finite duality (lem-sc-finite-duality-derived-hom, Tags 035C,
0AX2) identifies Ri_* a(OY) with RHom(i_* OZ, OY).
2. The local Koszul Ext calculation (lem-sc-koszul-regular-immersion-derived-hom,
Tag 0BQZ) identifies this with Ri_* of the shifted normal determinant. The local
comparison is compatible with changes of generators and the i_* OZ-module action.
3. The affine derived equivalence (lem-sc-finite-affine-derived-equivalence, Tag 0AVW)
descends this module-compatible comparison to Z. Apply on every clopen rank stratum;
the canonical local comparisons glue to the displayed isomorphism. -/
theorem koszulRegularImmersion_dualizing {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsNoetherian Y] [IsClosedImmersion i]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)))
    (hpres : ∀ E : schemeDerivedCategory Z, schemeDerivedQCohProperty Z E →
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage i).obj E))
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage i)
      (fun E => hpres E.obj E.property) ⊣ a)
    (OY : schemeDerivedQCohCategory Y)
    (hOY : OY.obj = (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        (SheafOfModules.unit Y.ringCatSheaf)) :
    ∃ hdet : schemeDerivedQCohProperty Z ((DerivedCategory.Q (C :=
      SheafOfModules.{u} (moduleRings Z.toRingedSpace))).obj
        (Scheme.Modules.locallyRankedExteriorComplex
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf)) r)),
      Nonempty ((⟨(DerivedCategory.Q (C :=
      SheafOfModules.{u} (moduleRings Z.toRingedSpace))).obj
        (Scheme.Modules.locallyRankedExteriorComplex
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf)) r), hdet⟩ :
        schemeDerivedQCohCategory Z) ≅ a.obj OY) := by
  sorry

end AlgebraicGeometry
