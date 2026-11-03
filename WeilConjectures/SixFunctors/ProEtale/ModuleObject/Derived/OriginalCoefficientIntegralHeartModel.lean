/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization

/-! # Integral models on qcqs schemes

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes,
Proposition 5.5, Theorem 6.12, Corollary 6.13, and Theorem 7.7.
(blueprint: lem-sp-original-coefficient-integral-heart-model)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A constructible rational coefficient module on a qcqs scheme has an integral model.
Source: Hemo--Richarz--Scholbach, Proposition 5.5 and Theorem 7.7.
(blueprint: lem-sp-original-coefficient-integral-heart-model)

Proof: refine the finite-presentation covers of the given strata by w-contractible
affines. Sections of the coefficient rings there are continuous functions on
extremally disconnected profinite sets; these rings are semi-hereditary by HRS
Theorem 6.12. A finitely presented module therefore has a finite projective
resolution. Consequently M[0] is constructible in the derived sense. The qcqs
integral-to-rational comparison of HRS Theorem 7.7 supplies an integral
constructible derived model K for M[0], along the actual coefficient inclusion.
Take N = H^0(K). On a finite constructible stratification, K is locally represented
by bounded complexes of finite projective modules over these coherent section
rings. Their degree-zero cohomology is finitely presented. Exact inverse image
identifies these modules with the local restrictions of N, proving precisely the
raw finite-presentation constructibility required here. Finally flat coefficient
localization commutes with H^0 and identifies its value with H^0(M[0]) = M.
This does not require truncation to preserve derived constructibility, nor a
globally lisse integral lattice. Empty strata and the zero module use zero models. -/
theorem originalCoefficientIntegralHeartModel
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ell E))
    (hM : IsConstructibleModuleObject (padicSubfieldRingObj X ell E) M) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ell E.1) X),
      IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicIntegersRingObj ell E.1) X) N ∧
      Nonempty ((Mod.extendScalars (padicIntegersToPadicSubfield X ell E)).obj N ≅ M) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
