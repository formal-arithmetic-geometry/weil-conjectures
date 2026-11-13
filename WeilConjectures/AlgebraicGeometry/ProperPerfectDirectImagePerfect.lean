/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.BoundedCoherentFiniteTorDirectImagePerfect
import WeilConjectures.AlgebraicGeometry.PerfectNoetherianCohomology
import WeilConjectures.AlgebraicGeometry.PerfectRelativeFiniteTor
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Perfect direct image along a proper perfect morphism

## References

* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G) (Lemma 37.61.13)
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- Derived direct image along a proper perfect morphism over a Noetherian base
preserves perfect objects. Perfectness of the morphism is expressed by the equivalent
stalkwise finite Tor criterion (Stacks, Lemma 37.61.11; Tag 0B6G). -/
theorem proper_perfect_directImage_perfect
    {X Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [IsNoetherian Y] (f : X ⟶ Y) [IsProper f] (hperfect : HasStalkwiseFiniteTorDimension f)
    (P : schemeDerivedCategory X) (hP : Scheme.IsPerfect X P) :
    Scheme.IsPerfect Y ((schemeDerivedDirectImage f).obj P) := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨hbounded, hcoherent⟩ := Scheme.perfect_bounded_coherent_cohomology X P hP
  have hsupport : ∀ i : ℤ, Scheme.Modules.HasSupportProperOver f
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj P) := by
    intro i
    let F : X.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj P
    obtain ⟨hq, ht⟩ :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp (hcoherent i)
    have : F.IsQuasicoherent := hq
    have : F.IsFiniteType := ht
    let Z : TopologicalSpace.Closeds X :=
      ⟨{x : X | ¬ Subsingleton (F.presheaf.stalk x)},
        (Scheme.Modules.finite_type_module_support_closed X F).2.2.2⟩
    refine ⟨Z, rfl, ?_⟩
    change IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f)
    infer_instance
  exact Scheme.isPerfect_schemeDerivedDirectImage_of_bounded_coherent_finiteTor
    f P hbounded hcoherent hsupport (Scheme.perfect_hasFiniteTorDimensionOver f hperfect P hP)

end AlgebraicGeometry
