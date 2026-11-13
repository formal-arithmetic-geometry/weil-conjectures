/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.ConstructibleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite

/-!
# Finite étale strata of a separated étale morphism

## References

* Stacks Project, Tags 07RZ and 03S9
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact separated étale morphism into a quasi-compact quasi-separated scheme is
finite étale after base change to each member of a finite constructible locally closed
stratification of its target (Stacks, Tags 07RZ and 03S9). -/
theorem exists_etale_separated_stratified_finite {X U : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [QuasiCompact j] :
    ∃ S : Stratification X,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      (∀ i : Fin S.n,
        IsFinite (pullback.snd j (S.immersion i)) ∧
        Etale (pullback.snd j (S.immersion i))) := by
  let hj : Hom.IsQuasiFinite j :=
    (Hom.isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact j).mpr
      ⟨Hom.isLocallyQuasiFinite_of_unramified j ⟨inferInstance, inferInstance⟩, inferInstance⟩
  obtain ⟨S, hScon, hSfin⟩ := exists_constructible_stratified_finite j hj
  refine ⟨S, hScon, fun i ↦ ⟨hSfin i, inferInstance⟩⟩

end AlgebraicGeometry.Scheme
