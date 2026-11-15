/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.AlgebraicGeometry.KoszulRegularImmersionAlgebraDualHomology
import WeilConjectures.AlgebraicGeometry.ClosedImmersionRankedCohomologyReconstruction
/-! # Algebra-linear Koszul duality

## References

* Stacks Project, Tags 0BQZ, 0AX3 and 0AVW.
-/

@[expose] public section

universe u wZ wY wA

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Koszul duality before forgetting the direct-image-algebra action. This
statement concerns the ambient scalar right adjoint, not a geometric right adjoint
on quasi-coherent complexes. -/
theorem koszulRegularImmersion_algebraDual {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsNoetherian Y] [IsClosedImmersion i]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)))
    (H : schemeDerivedCategory Y ⥤ DerivedCategory (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i))))
    (adjH : (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace i))
      ⟨Functor.whiskerRight i.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ H) :
    Nonempty ((RingedSpace.derivedModuleDirectImage
      (toDirectImageAlgebraSpace i)).obj ((DerivedCategory.Q (C :=
        SheafOfModules.{u} (moduleRings Z.toRingedSpace))).obj
          (Scheme.Modules.locallyRankedExteriorComplex
            (SheafOfModules.homObj (R := Z.sheaf)
              ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
              (SheafOfModules.unit Z.ringCatSheaf)) r)) ≅
        H.obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf))) := by
  have : CompactSpace Z := i.isClosedEmbedding.compactSpace
  have hfinite : (Set.range r).Finite := r.range_finite
  let M := SheafOfModules.homObj (R := Z.sheaf)
    ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
    (SheafOfModules.unit Z.ringCatSheaf)
  let K := H.obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
      (SheafOfModules.unit Y.ringCatSheaf))
  have hK : ∀ n : ℤ, Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj K ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj
          (Scheme.Modules.locallyRankedExteriorTerm M r n)) := by
    intro n
    exact koszulRegularImmersion_algebraDual_homology i hregular r hr H adjH n
  exact closedImmersion_rankedCohomology_reconstruction i M r hfinite K hK

end AlgebraicGeometry
