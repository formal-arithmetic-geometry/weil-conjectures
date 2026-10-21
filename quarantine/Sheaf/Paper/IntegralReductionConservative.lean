/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
import Sheaf.Paper.IntegralConstructibleSerre
import Sheaf.Paper.IntegralConstructibleNakayama
import Sheaf.Paper.IntegralReductionScalar
import Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! # Conservativity of integral reduction

Source: Bhatt--Scholze, Sections 6.7--6.8 (blueprint: lem-weil-pbc-integral-reduction-conservative).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- Derived reduction modulo ℓ detects isomorphisms between bounded constructible
integral complexes. Source: Bhatt--Scholze, Proposition 6.8.11(3) and derived Nakayama
(blueprint: lem-weil-pbc-integral-reduction-conservative).

Proof in words. The valuation ring of a finite normed extension is a complete discrete
valuation ring, and ℓ is a positive power of a uniformizer times a unit. On a finite
stratification the cohomology modules are locally finitely presented. The kernel, cokernel
and extension closure of these modules makes the cone of φ bounded constructible.
The integral realization identifies the locally finitely presented internal modules
with the continuous integral sheaves in Proposition 6.8.11(3); this identification and
the coefficient-dependent closure assertions must be established, rather than inferred
from noetherianity alone. Derived reduction carries the cone to zero when the reduced
map is invertible. The two-term coefficient resolution identifies its restricted
reduction with the cone of multiplication by ℓ, so multiplication by ℓ is invertible
on the cone and hence on every cohomology module. Constructible Nakayama makes each
of those modules zero. The cone is therefore zero,
so φ is invertible. This argument includes torsion modules, zero complexes, and empty X;
it uses no properness or exchange hypothesis. -/
theorem integralReduction_reflects_isIso (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    {M N : ProEtale.BoundedConstructible (condensedRingObj (integralCoeff ℓ E) X)}
    (φ : M ⟶ N)
    (hφ : IsIso ((integralReduction ℓ E X).map φ.hom)) : IsIso φ := by
  let := (integralConstructible_serre ℓ E X).1
  let := (integralConstructible_serre ℓ E X).2.1
  let := (integralConstructible_serre ℓ E X).2.2
  let : (boundedConstructible (condensedRingObj (integralCoeff ℓ E) X)).IsTriangulated :=
    isTriangulated_boundedConstructible_of_serre _
  obtain ⟨C, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle φ.hom
  obtain ⟨C', hC', ⟨e⟩⟩ := ObjectProperty.ext_of_isTriangulatedClosed₃'
    (boundedConstructible (condensedRingObj (integralCoeff ℓ E) X))
      _ hT M.property N.property
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (integralReductionMap ℓ E) X)
  let : (L(Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) X))).CommShift ℤ :=
    adj.leftAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  have : (L(Mod.extendScalars
      (coefficientMap (integralReductionMap ℓ E) X))).IsTriangulated :=
    adj.isTriangulated_leftAdjoint
  have hred : IsZero ((integralReduction ℓ E X).obj C) := by
    exact Pretriangulated.Triangle.isZero₃_of_isIso₁ _
      ((L(Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) X))).map_distinguished
        _ hT) hφ
  have hred' : IsZero ((integralReduction ℓ E X).obj C') :=
    hred.of_iso ((integralReduction ℓ E X).mapIso e).symm
  have hℓ : IsIso (ℓ • 𝟙 C') := integralReduction_isIso_nsmul_of_isZero ℓ E X C' hred'
  have hzero : IsZero C' := by
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro n
    let H := DerivedCategory.homologyFunctor
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) n
    have hℓH : IsIso (ℓ • 𝟙 (H.obj C')) := by
      have : IsIso (H.map (ℓ • 𝟙 C')) := inferInstance
      rw [H.map_nsmul, H.map_id] at this
      exact this
    exact integralConstructible_isZero_of_isIso_nsmul ℓ E X _ (hC'.2 n) hℓH
  exact (ObjectProperty.isIso_hom_iff _).mp
    ((Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).mp (hzero.of_iso e))

end AlgebraicGeometry.ProEtale.CondensedRing
