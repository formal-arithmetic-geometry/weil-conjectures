/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Cohomological dimension of fibres and the amplitude of compactly supported direct images

Over an algebraically closed field `k'`, a `k'`-scheme `X` of finite type and dimension at most
`d` has no cohomology above `2d` with coefficients in a sheaf of modules over a finite ring
(`AlgebraicGeometry.Etale.subsingleton_H_forget₂_of_two_mul_lt`, blueprint
`fin4-lem-fibrewise-cohomological-dimension`). Consequently, for a separated morphism of finite
type `f : X ⟶ Y` between schemes of finite type over a field whose geometric fibres have
dimension at most `d`, `Rᵠf_! F = 0` for `q > 2d`
(`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerShriek_singleFunctor_of_two_mul_lt`,
blueprint `lem-dg-compact-support-amplitude`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `fin4-lem-fibrewise-cohomological-dimension`: Cohomological dimension over an
algebraically closed field.

Let `k'` be an algebraically closed field, `X` a `k'`-scheme of finite type of dimension at most
`d`, and `F` an étale sheaf of `Λ`-modules over a finite ring `Λ`. Then `Hᵠ(X_ét, F) = 0` for
`q > 2d`, cohomology being that of the underlying abelian sheaf. The blueprint assumes `F`
constructible; this is not needed, since `F` is torsion as `Λ` is finite, and the bound
`cd_tor(X) ≤ 2d` (`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed`) applies
to all torsion sheaves. -/
theorem subsingleton_H_forget₂_of_two_mul_lt {k' : Type u} [Field k'] [IsAlgClosed k']
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k')) [LocallyOfFiniteType a] [QuasiCompact a] (d : ℕ)
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (hq : 2 * d < q) :
    Subsingleton (Sheaf.H ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) := by
  refine Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed d a hX _ ?_ q hq
  refine Sheaf.IsTorsion.of_forall_isAddTorsion fun U x ↦ ?_
  have := Fintype.ofFinite Λ
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨Fintype.card Λ, Fintype.card_pos, ?_⟩
  let y : F.obj.obj U := x
  change Fintype.card Λ • y = 0
  rw [← one_smul Λ y, ← smul_assoc, card_nsmul_eq_zero, zero_smul]

/-- Blueprint `lem-dg-compact-support-amplitude`: The compact-support bound uses the original
fibres.

Let `f : X ⟶ Y` be a separated morphism of finite type (here: one admitting a compactification)
between schemes of finite type over a field `k`, whose geometric fibres have dimension at most
`d`, and let `Λ` be a finite ring. Then for every étale sheaf `F` of `Λ`-modules on `X`,
`Rᵠf_! F = 0` for `q > 2d`. The blueprint also assumes the exponent of `Λ` invertible on `Y`;
this is not needed, proper base change holding for all torsion coefficients. -/
theorem isZero_homology_rightDerivedLowerShriek_singleFunctor_of_two_mul_lt {k : Type u}
    [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX) (d : ℕ)
    (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (hq : (2 * d : ℤ) < q) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) :=
  sorry

end Etale

end AlgebraicGeometry
