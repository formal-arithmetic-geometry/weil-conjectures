/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedFiniteCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedGeometricFrobeniusTransport
public import WeilConjectures.PoincareDuality.CondensedFrobeniusOperators.FiniteStrictWeilComplex.TraceFormulaFiniteStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.TraceFormulaSchemeGaloisComparison
public import WeilConjectures.TraceFormula.FrobeniusIterate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedFrobeniusGeometry

/-!
# Iterated finite Weil isomorphisms

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-trace-formula/sec-frobenius-correspondences/sk-d-weil/def-trf-iterated-weil-map.md`
(blueprint: def-trf-iterated-weil-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

-- Fix the native site size before synthesizing derived module instances.
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace WeilConjectures.CondensedFrobeniusOperators
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

/-- Iteration of a specified Weil isomorphism at any commutative condensed coefficient
ring. The finite-quotient declaration below is its specialization, with identical
pullback compositors. Source: def-trf-iterated-weil-map
(blueprint: def-trf-iterated-weil-map). -/
noncomputable def iteratedWeilMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (K : D Λ (F.geometricFiber Y₀).left)
    (φ : (L Λ (condensedFrobeniusGeometry F Y₀).h.hom).obj K ≅ K) (m : ℕ) :
    (L Λ ((condensedFrobeniusGeometry F Y₀).h.pow m).hom).obj K ≅ K :=
  CategoryTheory.Iso.powStr (condensedFrobeniusGeometry F Y₀).h
    (fun f => L Λ f) (leftDerivedUpperStarId Λ (F.geometricFiber Y₀).left)
    (fun f g => leftDerivedUpperStarComp Λ f g) φ m

/-- The canonical iterated Weil isomorphism `φ^[m]`, with all pullback compositors
retained by the generic `Iso.powStr` construction.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-trace-formula/sec-frobenius-correspondences/sk-d-weil/def-trf-iterated-weil-map.md`
(blueprint: def-trf-iterated-weil-map).
-/
noncomputable def iteratedWeil
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n) (K : FiniteStrictWeilComplex F Y₀ ell E n hn) (m : ℕ) :
    (L (finiteCoefficient ell E n)
      ((condensedFrobeniusGeometry F Y₀).h.pow m).hom).obj K.carrier.obj ≅ K.carrier.obj :=
  iteratedWeilMap (finiteCoefficient ell E n) F Y₀ K.carrier.obj K.φ m

/-- The scheme-Frobenius map u_m = kappa_m followed by phi^[m].
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-trace-formula/sec-frobenius-correspondences/sk-d-weil/def-trf-iterated-weil-map.md`
(blueprint: def-trf-iterated-weil-map). -/
noncomputable def iteratedWeilSchemeFrobenius
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ F.p) (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n) (K : FiniteStrictWeilComplex F Y₀ ell E n hn)
    (m : ℕ) (hm : 1 ≤ m) :
    (L (finiteCoefficient ell E n) (F.coefficientFreeSchemeFrobeniusIterate Y₀ m)).obj
        K.carrier.obj ≅
      K.carrier.obj :=
  finiteSchemeGaloisComparison F Y₀ ell hEll E n hn K m hm ≪≫
    iteratedWeil F Y₀ ell E n hn K m

end WeilConjectures.CondensedFrobeniusOperators
