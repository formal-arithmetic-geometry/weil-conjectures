/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarComparison

/-! # The descent Frobenius factor in the abstract factorization notation -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Identify the factor isomorphisms before taking their components. -/
lemma purity_geometricFiberProjUpperStarFrobeniusIso_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) :
    geometricFiberProjUpperStarFrobeniusIso Λ a =
      purityModuleFactorIso Λ a.geometricFiberProj a.geometricGaloisFrobenius.hom
        a.geometricGaloisFrobenius_hom_comp_geometricFiberProj := rfl

end AlgebraicGeometry.ProEtale.CondensedRing
