/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherent
import WeilConjectures.AlgebraicGeometry.DerivedLocallyBoundedBelowGlobal
import WeilConjectures.AlgebraicGeometry.DerivedAlgebraQCohOfUnderlying
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Derived internal Hom from a pseudo-coherent algebra

## References

* [Stacks, Tag 0A6H], [Stacks, Tag 0BV0], [Stacks, Tag 0BV1], [Stacks, Tag 0AX2]
-/

@[expose] public section

universe u w wA

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- On a Noetherian scheme, derived internal Hom from a quasi-coherent algebra that is
pseudo-coherent as an underlying module takes bounded-below quasi-coherent objects to
bounded-below quasi-coherent algebra-module objects. Forgetting the algebra action gives
an object of the bounded-below quasi-coherent derived category of the scheme.
(Stacks, Tags 0A6H, 0BV0, 0BV1, 0AX2) -/
theorem pseudoCoherentRHomQuasiCoherent
    (Y : Scheme.{u}) [IsNoetherian Y]
    (A : Y.CommAlgebraSheaf) (hA : A.toModule.IsQuasicoherent)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj A.right))]
    (hpc : Scheme.IsPseudoCoherent Y (DerivedCategory.Q.obj
      ((HomologicalComplex.single (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
        (ComplexShape.up ℤ) 0).obj A.toModule)))
    (K : schemeDerivedCategory Y)
    (hK : schemeDerivedQCohProperty Y K) (hbounded : ∃ a : ℤ, K.IsGE a) :
    sheafAlgebraDerivedQCohProperty Y A hA ((derivedRHomAlgebraModule Y A hA).obj K) ∧
    schemeDerivedQCohProperty Y
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat RingCat)).map A.hom)).mapDerivedCategory.obj
            ((derivedRHomAlgebraModule Y A hA).obj K)) ∧
    ∃ a : ℤ,
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat RingCat)).map A.hom)).mapDerivedCategory.obj
            ((derivedRHomAlgebraModule Y A hA).obj K)).IsGE a := by
  let S := DerivedCategory.Q.obj
    ((HomologicalComplex.single (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
      (ComplexShape.up ℤ) 0).obj A.toModule)
  obtain ⟨hq, hlocal⟩ := (rhom_supported_quasiCoherent Y S K hK).1 hpc hbounded
  obtain ⟨e⟩ := derivedRHomAlgebraModule_underlying Y A hA
  let eK := e.app K
  have hq' : schemeDerivedQCohProperty Y
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat RingCat)).map A.hom)).mapDerivedCategory.obj
            ((derivedRHomAlgebraModule Y A hA).obj K)) := by
    intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso eK.symm) (hq n)
  obtain ⟨a, ha⟩ := derivedLocallyBoundedBelowGlobal Y _ hlocal
  have hb : ∃ a : ℤ,
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat RingCat)).map A.hom)).mapDerivedCategory.obj
            ((derivedRHomAlgebraModule Y A hA).obj K)).IsGE a := by
    refine ⟨a, (DerivedCategory.isGE_iff _ a).mpr ?_⟩
    intro n hn
    exact ((DerivedCategory.isGE_iff _ a).mp ha n hn).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso eK)
  exact ⟨derivedAlgebraQCohOfUnderlying Y A hA _ hq' hb, hq', hb⟩

end AlgebraicGeometry
