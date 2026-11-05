/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitChangeGaloisLayer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.IntegralSplit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicAlgCl
public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange

/-!
# The change of geometric generic fibre over a change of trait splits, `𝒪_E`-coefficients

Let `φ : M ⟶ N` be a morphism of models over a change of strictly henselian traits
`Spec R ⟶ Spec R₁` such that `Spec(Ω₁ ⊗_{R₁} R)` is a single point. The change of geometric generic
fibres factors as `g = r₁ ≫ q ≫ r₂` with `r₁`, `r₂` universal homeomorphisms and `q` the base
change of the pro-Galois `Spec L^sep ⟶ Spec L`
(`NearbyCyclesModel.Hom.traitChangeInsepMap_comp_traitChangeGaloisMap_comp`). If the degrees of
the finite Galois subextensions of `L^sep/L` are prime to `ℓ`, the unit of `Lg^* ⊣ Rg_*` with
`𝒪_E`-coefficients is a split monomorphism at the restriction of every derived complete complex
`C` on `Y` whose reductions modulo `ℓⁿ⁺¹` are bounded below of étale origin
(`NearbyCyclesModel.Hom.isSplitMono_unit_toCartesian_generic_of_traitChange_padicIntegers`), by
`ProEtale.CondensedRing.isSplitMono_derivedUnit_galois_padicIntegers`. Consequently the base
change morphism of `Rj_*` restricted to the special fibre is a split monomorphism
(`NearbyCyclesModel.Hom.isSplitMono_map_exchangeRight_app_toCartesian_of_isSplitMono_unit`):
this is the integral form of SGA 4½, [Th. finitude], Lemme 3.4.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped TensorProduct CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom

open Scheme

section Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')

end Abstract

section Integral

variable {R₁ R Ω₁ Ω : Type u} [CommRing R₁] [CommRing R] [Algebra R₁ R] [Field Ω₁]
  [Algebra R₁ Ω₁] [Field Ω] [Algebra R Ω] [Algebra Ω₁ Ω] [Algebra R₁ Ω]
  [IsScalarTower R₁ R Ω] [IsScalarTower R₁ Ω₁ Ω]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {φ : M.Hom N f f'}
  {q : M.total ⟶ Spec (.of R)} {g : M.generic ⟶ Spec (.of Ω)}
  {q₁ : N.total ⟶ Spec (.of R₁)} {g₁ : N.generic ⟶ Spec (.of Ω₁)}
  {ℓ : ℕ} [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

end Integral

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom
