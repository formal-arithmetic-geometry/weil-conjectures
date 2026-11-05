/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralCoefficientLimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.TowerIsoLifting

/-!
# Lattices of `ℓ`-adic towers of locally constant sheaves are locally `ℤ_ℓ,X`

The sheaf of abelian groups underlying `ℤ_ℓ,X` is the limit of the tower `n ↦ (ℤ/ℓⁿ)_X` of
abelian sheaves (`AlgebraicGeometry.ProEtale.isLimitPadicIntAbSheafCone`), the forgetful functor
from sheaves of rings to abelian sheaves preserving limits.

Consequently, for a tower `(Gₙ)` of pro-étale abelian sheaves with `Gₙ₊₁/ℓⁿ ≅ Gₙ` (locally, as
cokernels) and `Gₙ` locally isomorphic to `(ℤ/ℓⁿ)_X`, the limit `lim Gₙ` is pro-étale locally
isomorphic to `ℤ_ℓ,X` (`AlgebraicGeometry.ProEtale.exists_cover_nonempty_iso_padicIntAbSheaf`),
provided the constant tower `(ℤ/ℓⁿ)_X` itself satisfies the two hypotheses of
`ProEtale.exists_cover_nonempty_iso_overPullback_limit_of_isColimit_cokernelCofork`:
its transitions are locally cokernels of `ℓⁿ`, and its automorphisms (multiplication by units
of `C(-, ℤ/ℓⁿ)`) lift locally. These two facts about the constant tower are stated as
hypotheses here; the first is proved in
`WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowAbSheafCokernel`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {D E : Type*} [Category* D]
  [Category* E] (F : D ⥤ E) [J.HasSheafCompose F]

/-- Postcomposition of sheaves with a functor preserving limits of shape `K` preserves limits of
shape `K`: limits of sheaves are computed on sections. -/
instance preservesLimitsOfShape_sheafCompose {K : Type*} [Category* K] [HasLimitsOfShape K D]
    [HasLimitsOfShape K E] [PreservesLimitsOfShape K F] :
    PreservesLimitsOfShape K (sheafCompose J F) := by
  have : PreservesLimitsOfShape K (sheafCompose J F ⋙ sheafToPresheaf J E) :=
    preservesLimitsOfShape_of_natIso
      (Iso.refl (sheafToPresheaf J D ⋙ (Functor.whiskeringRight _ _ _).obj F))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J E)

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The tower `n ↦ (ℤ/ℓⁿ)_X` of abelian sheaves on `X_proét`. -/
noncomputable abbrev zmodPowAbSheafDiagram : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  zmodPowSheafDiagram X l ⋙ sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})

/-- **`ℤ_ℓ,X = lim_n (ℤ/ℓⁿ)_X` as abelian sheaves**: the forgetful functor from sheaves of rings
to abelian sheaves preserves limits. -/
noncomputable def isLimitPadicIntAbSheafCone :
    IsLimit ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapCone
      (padicIntSheafCone X l)) :=
  isLimitOfPreserves _ (isLimitPadicIntSheafCone X l)

end AlgebraicGeometry.ProEtale
