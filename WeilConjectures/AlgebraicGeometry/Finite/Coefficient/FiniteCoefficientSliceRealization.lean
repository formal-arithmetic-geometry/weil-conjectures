/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Homology.AcyclicTensorTestEquivalence
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat

/-! # Constant-ring realization on a pro-etale slice

Let `U` be an object of the small pro-etale site of `X` and `B` a commutative ring. Sheaves of
`B`-modules on `U.left` are identified with sheaves of modules over the restriction to the
slice `Over U` of the constant ring sheaf `B`: transport along the slice equivalence
`Over U ≌ U.left.ProEt`, keep the fixed-scalar module presheaf and sheafify it along the
constant-scalar unit. This realization is an additive equivalence compatible with the
sheafified tensor products, and it recovers slice restriction of modules from the fixed-scalar
chart coordinates `finiteCoefficientSliceRestriction`.

Source: Stacks Project, Tags 00YV, 03CY, 03EK and 0GMW
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w v' u' u t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

namespace SheafOfModules

end SheafOfModules

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{t}) (B : Type t) [CommRing B] (U : X.ProEt)

-- The tensor product of module presheaves over the constant ring presheaf.

variable (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}) (φ : adicConstantRing X B ⟶ R)
  (V : X.Etale)

end AlgebraicGeometry.Scheme
