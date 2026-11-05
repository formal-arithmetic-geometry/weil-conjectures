/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.StrictlyHenselianBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ProperBaseChange

/-!
# Base change between strictly henselian local rings, module objects with finite coefficients

Let `T` be a finite discrete commutative ring and `T̲ = C(-, T)` its condensed ring. For a local
homomorphism `ι : R₁ ⟶ R₂` of strictly henselian local rings, morphisms `tᵢ : Spec Ωᵢ ⟶ Spec Rᵢ`
from spectra of separably closed fields, `c : Spec Ω₂ ⟶ Spec Ω₁` with `c ≫ t₁ = t₂ ≫ Spec ι`, and
`b : R₂ ⟶ κ` a map to a field with kernel the maximal ideal, the pullback along `Spec b` of the
base change morphism `L(Spec ι)^* Rt₁_* ⟶ Rt₂_* Lc^*` of module objects over `T̲` is invertible at
every complex bounded below of étale origin
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_of_isStrictlyHenselianLocalRing`). This is
`ProEtale.isIso_leftDerivedUpperStar_map_derivedBaseChangeMap_app_of_isStrictlyHenselianLocalRing`
read through the comparison `Φ` of module objects over `T̲` with pro-étale sheaves of
`T`-modules (`ProEtale.nonempty_arrowIso_map_baseChangeMap_finiteCoefficient`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

end AlgebraicGeometry.ProEtale.CondensedRing
