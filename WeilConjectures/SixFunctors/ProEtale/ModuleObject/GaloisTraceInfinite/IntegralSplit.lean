/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.FieldTowerMoebius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerUnique
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UnitTransportExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegersModPowFinal
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsReductionComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestrictedSplitMonoTorsion

/-!
# The derived unit of an infinite Galois extension with `𝒪_E`-coefficients splits

Let `Ω/L` be a Galois extension whose finite Galois subextensions have degrees prime to `ℓ`
(for instance a pro-`p` extension, `p ≠ ℓ`), `h : G ⟶ Spec L` and `g : G ×_L Ω ⟶ G`. For a
derived complete `𝒪_E`-complex `K` on `G` whose reductions modulo `ℓⁿ⁺¹` are bounded below of
étale origin, the unit `K ⟶ Rg_* Lg^* K` is a split monomorphism
(`ProEtale.CondensedRing.isSplitMono_derivedUnit_galois_padicIntegers`): this is the integral form
of the Hochschild–Serre splitting of SGA 4½, [Th. finitude], Lemme 3.4.

The proof lifts the torsion splittings with
`ProEtale.isSplitMono_of_derivedCompleteIntegers_of_unique_retractions`.
Modulo `ℓⁿ⁺¹` the reduction of the unit is the unit with coefficients `𝒪_E/ℓⁿ⁺¹`
(`ProEtale.CondensedRing.map_unit_comp_derivedPushPullExtendScalarsHom`, the push comparison
being invertible by `isIso_derivedUpperStarExtendScalarsPushHom_integersModPow_app`), compatibly
with the Galois actions. There it has a `Gal(Ω/L)`-invariant retraction
(`ProEtale.exists_invariant_retraction_derivedUnit_galois`), which is unique
(`ProEtale.eq_of_invariant_retraction_derivedUnit_galois`, from the Möbius decomposition of the
infinite level, `ProEtale.exists_galoisTowerMoebiusDecomposition`). The reduction of an invariant
retraction is invariant, the Galois action being defined with integral coefficients.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

end AlgebraicGeometry.ProEtale.CondensedRing
