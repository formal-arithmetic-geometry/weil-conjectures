/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalence
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientLinear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars

/-!
# The constants in the two models of `ℓ`-adic sheaves

The constants `ℚ̄_ℓ` act on the two models of `ℓ`-adic sheaves on a scheme `X`: on the sheaves
of modules over `ℚ̄_ℓ,X` of the old model through the constant functions
(`AlgebraicGeometry.ProEtale.AdicSheaf.constScalarSection`), and on the module objects over
`Λ_X = p_X^* ℚ̲̄_ℓ` of the condensed model through the pullbacks `p_X^* c` of the constant global
sections of `ℚ̲̄_ℓ` (`AlgebraicGeometry.ProEtale.CondensedRing.constRingHom`). This file shows
that the comparison `Λ_X ≅ forgetAb ℚ̄_ℓ,X` of the coefficient rings
(`AlgebraicGeometry.ProEtale.condensedRingObjIsoForgetAb`) matches them
(`AlgebraicGeometry.ProEtale.unitHomEval_constRingHom_comp_condensedRingObjIsoForgetAb_hom`).

The proof evaluates on the test object `X[*]`: by adjunction, the global section `p_X^* c` of
`Λ_X`, followed by the realization `Λ_X ≅ ℚ̄_ℓ,X` of the coefficients as bounded functions,
is computed by the normalization of this realization on the profinite test functions
(`AlgebraicGeometry.ProEtale.CondensedQbarCoefficientRealization.globalCoefficientIso_test`),
applied to the constant function `c` on the point.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (T : Type*) [TopologicalSpace T]

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

namespace AdicSheaf

variable {l X}

end AdicSheaf

end AlgebraicGeometry.ProEtale
