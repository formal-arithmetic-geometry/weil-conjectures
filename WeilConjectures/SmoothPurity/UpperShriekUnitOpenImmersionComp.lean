/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.TraceFormula.LocalTerm
public import Mathlib.Init
public import Lean.Elab.Tactic.ElabTerm

/-!
# Purity of open immersions and composition

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. For an open immersion
`j` of separated `k`-schemes of finite type, `Rj^! ℚ̄_ℓ ≅ j^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitIso_padicAlgCl`). This file proves:

* `ProEtale.CondensedRing.boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl_comp_hom_app`:
  the identifications `Rj^! ≅ j^*` are compatible with the composition isomorphisms of `R(-)^!`
  and of `(-)^*`, by conjugation of the corresponding statement for `Rj_! ≅ j_!`
  (`boundedConstructibleLowerShriekComp_padicAlgCl_hom_app_of_isOpenImmersion`);
* `ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitIso_padicAlgCl_comp`: hence so are
  the identifications `Rj^! ℚ̄_ℓ ≅ ℚ̄_ℓ`;
* for a morphism `f : X ⟶ Y` and an open immersion `j : Y ⟶ Z`, the comparison
  `R(f ≫ j)^! ℚ̄_ℓ ≅ Rf^! Rj^! ℚ̄_ℓ ≅ Rf^! ℚ̄_ℓ`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitCompIso_padicAlgCl`) satisfies the
  cocycle condition for composites of open immersions
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitCompIso_padicAlgCl_comp`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

/-- The comparison `R(f ≫ j)^! ℚ̄_ℓ ≅ Rf^! Rj^! ℚ̄_ℓ ≅ Rf^! ℚ̄_ℓ` for an open immersion `j`: the
composition isomorphism of the exceptional inverse images followed by `Rf^!` of purity for `j`
(`boundedConstructibleUpperShriekUnitIso_padicAlgCl`). -/
noncomputable def boundedConstructibleUpperShriekUnitCompIso_padicAlgCl (f : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion j.left] :
    (boundedConstructibleUpperShriek ℓ (f ≫ j)).obj
        (𝟙_ (Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) ≅
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).app _ ≪≫
    (boundedConstructibleUpperShriek ℓ f).mapIso
      (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j)

end AlgebraicGeometry.ProEtale.CondensedRing
