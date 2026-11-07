/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence

/-!
# Finite étale covers as finite locally constant sheaves

Source: Stacks Project, Tags 03RV, 03Q1, 00Y6 and 09ZB
(blueprint: thm-galois-lc-etale).
These are `AlgebraicGeometry.Scheme.exists_finiteEtale_flc_equivalence` and
`AlgebraicGeometry.Scheme.finiteEtale_flc_preserves_torsors`, stated for the category
`Scheme.FLC`, which is `Scheme.FiniteLocallyConstant`.
-/

@[expose] public section

universe v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The Yoneda equivalence, with base change and stalk compatibility. This is
`AlgebraicGeometry.Scheme.exists_finiteEtale_flc_equivalence`.
Source: Stacks Project, Tags 03RV, 03Q1, 00Y6 and 09ZB
(blueprint: thm-galois-lc-etale). -/
theorem exists_finiteEtale_flc_equivalence_sheaf (Y : Scheme.{v}) :
    ∃ Φ : Y.FiniteEtale ≌ Y.FLC,
      Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ≅
        ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{v + 1}) ∧
      (∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ⋙
            (pointSmallEtale s).sheafFiber (A := Type (v + 1)) ≅
          FiniteEtale.fiber s ⋙ CategoryTheory.forget FintypeCat.{v} ⋙ uliftFunctor.{v + 1, v})) ∧
      (∀ (X : Scheme.{v}) (f : X ⟶ Y), ∃ Ψ : X.FiniteEtale ≌ X.FLC,
        Nonempty (Ψ.functor ⋙ ObjectProperty.ι _ ≅
          ObjectProperty.ι _ ⋙ X.smallEtaleTopology.uliftYoneda.{v + 1}) ∧
        Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ⋙ etaleSetPullback f ≅
          FiniteEtale.pullback f ⋙ Ψ.functor ⋙ ObjectProperty.ι _)) :=
  exists_finiteEtale_flc_equivalence Y


end AlgebraicGeometry.Scheme
