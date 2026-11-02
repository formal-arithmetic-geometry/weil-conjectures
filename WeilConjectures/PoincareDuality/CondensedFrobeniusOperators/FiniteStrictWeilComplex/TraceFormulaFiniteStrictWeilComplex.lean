/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedFiniteCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedGeometricFrobeniusTransport
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobenius
public import WeilConjectures.TraceFormula.FrobeniusIterate
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude

/-!
# Finite strict Weil complexes

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/sk-def-sf-weil-complexes/def-trf-strict-weil-complex.md`
(blueprint: def-trf-strict-weil-complex).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

-- These imported instances leave the coefficient-size universe undetermined.
-- Use the native pro-étale site's fixed small model, as in the Tor-amplitude API.
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
/-- A finite strict Weil pair on the recorded bounded-constructible finite-Tor model.
The finite Tor witness is part of the carrier data, while the Weil structure is the
recorded geometric-Frobenius pullback isomorphism.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/sk-def-sf-weil-complexes/def-trf-strict-weil-complex.md`
(blueprint: def-trf-strict-weil-complex). -/
structure FiniteStrictWeilComplex (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ)
    (_hn : 1 ≤ n) where
  carrier : (boundedConstructible (condensedRingObj
    (finiteCoefficient ell E n) (F.geometricFiber Y₀).left)).FullSubcategory
  finiteTor : DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2}
    (Mod (Sheaf (Scheme.ProEt.topology (F.geometricFiber Y₀).left) Ab.{u + 1})
      (condensedRingObj (finiteCoefficient ell E n) (F.geometricFiber Y₀).left)) carrier.obj
  φ : (L (finiteCoefficient ell E n)
    (geometricFrobeniusGeometry F Y₀).h.hom).obj carrier.obj ≅ carrier.obj

namespace FiniteStrictWeilComplex

variable {F : WeilConjectures.FiniteFieldDatum.{u}}
  {Y₀ : Over (Spec (CommRingCat.of F.k₀))} [IsSeparated Y₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  {ell : ℕ} [Fact ell.Prime] {E : Type u} [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] {n : ℕ} {hn : 1 ≤ n}

/-- Morphisms are exactly the underlying arrows commuting with the Weil structure.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/sk-def-sf-weil-complexes/def-trf-strict-weil-complex.md`
(blueprint: def-trf-strict-weil-complex). -/
@[ext] structure Hom (K J : FiniteStrictWeilComplex F Y₀ ell E n hn) where
  hom : K.carrier.obj ⟶ J.carrier.obj
  comm : (L (finiteCoefficient ell E n) (geometricFrobeniusGeometry F Y₀).h.hom).map hom ≫
    J.φ.hom = K.φ.hom ≫ hom

/-- The category of finite strict pairs, with the usual identities and composition.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/sk-def-sf-weil-complexes/def-trf-strict-weil-complex.md`
(blueprint: def-trf-strict-weil-complex). -/
instance : Category (FiniteStrictWeilComplex F Y₀ ell E n hn) where
  Hom := Hom
  id K := ⟨𝟙 K.carrier.obj, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    simp only [Functor.map_comp, Category.assoc]
    rw [g.comm, ← Category.assoc, f.comm, Category.assoc]⟩
  id_comp := by intros; apply Hom.ext; simp
  comp_id := by intros; apply Hom.ext; simp
  assoc := by intros; apply Hom.ext; simp [Category.assoc]

/-- The forgetful functor to the ambient derived category, with finite-Tor carrier.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/sk-def-sf-weil-complexes/def-trf-strict-weil-complex.md`
(blueprint: def-trf-strict-weil-complex). -/
def forget : FiniteStrictWeilComplex F Y₀ ell E n hn ⥤
    D (finiteCoefficient ell E n) (F.geometricFiber Y₀).left where
  obj K := K.carrier.obj
  map f := f.hom

end FiniteStrictWeilComplex

end WeilConjectures.CondensedFrobeniusOperators
