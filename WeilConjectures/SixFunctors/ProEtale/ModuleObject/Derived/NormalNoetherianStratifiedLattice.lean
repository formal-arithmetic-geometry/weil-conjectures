/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.StratifiedLattice
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalStratifiedLatticeData

/-! # Integral lattices on finite strata of normal Noetherian schemes.

A lisse rational module on a normal Noetherian scheme admits an embedded lisse integral lattice
on each stratum of a finite locally closed stratification, with no base field, characteristic
or separatedness assumption.

## References

* [Stacks, Tag 07RY](https://stacks.math.columbia.edu/tag/07RY)
* [Stacks, Tag 07RZ](https://stacks.math.columbia.edu/tag/07RZ)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A lisse rational module on a normal Noetherian scheme admits an embedded
lisse integral lattice on each stratum of a finite locally closed stratification.
There is no base field, characteristic restriction, separatedness assumption,
connectedness assumption, or assumption that `l` is invertible on the scheme. -/
theorem exists_stratified_lisse_integral_lattice_of_normal
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (_hnormal : ∀ z : X, IsDomain (X.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.presheaf.stalk z)) :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let A := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers l E)
    let B := Profinite.continuousMapRingObj.{u} E
    let a : A ⟶ B :=
      (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap
            (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)
    ∀ L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X),
      LocallyFree (condensedRingObj B X) L →
      ∃ S : Scheme.FiniteLocallyClosedStratification X, ∀ i : Fin S.n,
        let T := S.domain i
        let aT := (upperStarFromPoint T).map a
        let LT := (CondensedRing.upperStar B (S.immersion i)).obj L
        ∃ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj A T),
          LocallyFree (condensedRingObj A T) M ∧
          ∃ ι : M ⟶ (Mod.comap aT).obj LT,
            Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction aT).homEquiv M LT).symm ι) := by
  have : IsNoetherian X := ⟨⟩
  exact exists_stratified_lisse_integral_lattice_of_isNoetherian l E X

end AlgebraicGeometry.ProEtale.CondensedRing
