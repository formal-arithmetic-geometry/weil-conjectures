/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.LocalTerm

/-!

# The counit of an open and closed immersion

Let `j : B ⟶ F` be an open and closed immersion and `e : j_! ℚ̄_ℓ ⟶ ℚ̄_ℓ` the adjoint, for
`Rj_! ⊣ Rj^!`, of the purity isomorphism `ℚ̄_ℓ ≅ Rj^! ℚ̄_ℓ`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitIso_padicAlgCl`). On the summand `B`,
`e` is the inclusion of `Rj_! ℚ̄_ℓ ≅ Rj_* ℚ̄_ℓ` into `ℚ̄_ℓ`, and the unit `ℚ̄_ℓ ⟶ Rj_* Lj^* ℚ̄_ℓ` is
the projection onto it: `e` followed by the unit of `Lj^* ⊣ Rj_*` (read through
`Lj^* ℚ̄_ℓ ≅ ℚ̄_ℓ`) is `Rj_! ℚ̄_ℓ ≅ Rj_* ℚ̄_ℓ`
(`ProEtale.CondensedRing.homEquiv_symm_unitIso_inv_comp_unit`). The abstract form,
`CategoryTheory.Adjunction.homEquiv_symm_comp_conjugate_comp_unit`, holds for any transposed map
`M ⟶ j^* N ≅ j^! N`, given the comparison of `j_!° ≅ j_! ≅ j_*` with the canonical map
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_clopen`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {U : D ⥤ C} {L : C ⥤ D} (a : U ⊣ L)
  {O : C ⥤ D} (ao : O ⊣ U) {S : C ⥤ D} {R : D ⥤ C} (b : S ⊣ R)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {B F : Over (Spec (.of k))} [LocallyOfFiniteType B.hom]
  [QuasiCompact B.hom] [IsSeparated B.hom] [LocallyOfFiniteType F.hom] [QuasiCompact F.hom]
  [IsSeparated F.hom]

end AlgebraicGeometry.ProEtale.CondensedRing
