/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement

/-!
# Specified etale-origin witnesses for constant pro-etale coefficients

Source: blueprint, proper base change, etale-origin witness; Stacks Project Tag 099R
(blueprint: def-weil-pbc-etale-origin-witness).

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleOriginWitness`:
  the recorded construction or statement of this node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]

end AlgebraicGeometry.Scheme

@[expose] public noncomputable section
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
