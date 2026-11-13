/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparison
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomAdjunction

/-! # PerfectPart of derived internal Hom

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Internal Hom from a perfect source preserves quasi-coherence. -/
theorem rhom_supported_quasiCoherent_perfect_part
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (hL : schemeDerivedQCohProperty X L)
    (hK : Scheme.IsPerfect X K) :
    schemeDerivedQCohProperty X
      ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op K, L)) := by
  classical
  obtain ⟨adj, s, adj', hadj, hs, hadj_sym, hadj'⟩ :=
    scheme_derivedInternalHom_adjunction X
  let N : schemeDerivedQCohCategory X := ⟨L, hL⟩
  obtain ⟨D, hD, ev, hev, hDperfect, comparison, hcomp, hcompM, hcompK,
      bidual, hbidual, hbidual_iso, η, hη, hηuniq, hp, hbase⟩ :=
    perfect_rhom_tensor_comparison X
      ⟨K, schemeDerivedQCohProperty_of_isPerfect X K hK⟩ N hK adj hadj adj' hadj'
  let := schemeDerivedTensorMonoidal X
  have htensor : schemeDerivedQCohProperty X (N.obj ⊗ D.obj) :=
    canonical_derivedTensor_preserve_QCoh X N.obj D.obj N.property D.property
  let c := comparison N
  have hc : IsIso c := hcompM
  intro n
  apply (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).mapIso (asIso c))
  exact htensor n

end AlgebraicGeometry
