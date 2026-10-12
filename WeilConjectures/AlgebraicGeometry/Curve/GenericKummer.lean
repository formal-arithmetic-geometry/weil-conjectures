/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Connecting
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# The generic Kummer residue sheaf

Let `C` be a smooth integral curve over an algebraically closed field `k`, let `n` be invertible
in `k` and let `η : Spec k(C) ⟶ C` be the generic point. Then the valuations at the closed points
induce an isomorphism of étale sheaves

```
  R¹η_* μₙ ≅ ⨁_{x ∈ C closed} i_{x*} ℤ/n.
```

We do not use the stalk formula for strict henselisations. Instead:

1. `R¹η_* 𝔾ₘ = 0` (`AlgebraicGeometry.Scheme.epi_lowerStar_map_cokernelπ_upperStar_gmSheaf`,
   Hilbert 90 on the generic fibres), so the long exact sequence of right derived functors of
   `η_*` applied to the Kummer sequence of `Spec k(C)` identifies `R¹η_* μₙ` with the cokernel of
   `n` on `η_* 𝔾ₘ`;
2. the divisor sequence `0 → 𝔾ₘ → η_* 𝔾ₘ → ⨁_x i_{x*} ℤ → 0` and the surjectivity of `n` on
   `𝔾ₘ` of `C` (Kummer) identify this with the cokernel of `n` on `⨁_x i_{x*} ℤ`, the identification
   being induced by the divisor map;
3. finally the cokernel of `n` on `i_{x*} ℤ` is `i_{x*} ℤ/n`, since `i_{x*}` is exact for a closed
   point `x`.

Here `R¹η_*` is the first right derived functor `Functor.rightDerived` of
`η_* = Etale.lowerStar AddCommGrpCat η`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

section Generic

variable (X : Scheme.{u}) [IsIntegral X]

/-- `η_*` along the generic point, on abelian étale sheaves. -/
noncomputable abbrev genericLowerStar :
    Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField

/-- **`R¹η_* 𝔾ₘ = 0`** along the generic point `η` of an integral regular noetherian scheme, for
the first right derived functor of `η_*`. -/
theorem isZero_rightDerived_one_genericLowerStar_upperStar_gmSheaf [IsNoetherian X]
    [IsRegular X] :
    IsZero ((X.genericLowerStar.rightDerived 1).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj X.gmSheaf)) := by
  let := HasDerivedCategory.standard (Sheaf (Spec X.functionField).smallEtaleTopology
    AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  set F := X.genericLowerStar
  set A := (Etale.upperStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj X.gmSheaf
  let ι := Injective.ι A
  have hS : (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel ι) inferInstance inferInstance
  have hepi : Epi (F.map (cokernel.π ι)) := X.epi_lowerStar_map_cokernelπ_upperStar_gmSheaf ι
  have hepi0 : Epi ((F.rightDerived 0).map (cokernel.π ι)) := by
    have h : (F.rightDerived 0).map (cokernel.π ι) = F.rightDerivedZeroIsoSelf.hom.app _ ≫
        F.map (cokernel.π ι) ≫ F.rightDerivedZeroIsoSelf.inv.app _ := by
      simp
    rw [h]
    infer_instance
  have h0 : hS.rightDerivedδ F 0 = 0 :=
    (cancel_epi ((F.rightDerived 0).map (cokernel.π ι))).1 (by
      rw [hS.comp_rightDerivedδ F 0, comp_zero])
  have hI : IsZero ((F.rightDerived (0 + 1)).obj (Injective.under A)) :=
    F.isZero_rightDerived_obj_injective_succ 0 _
  have hδ : Epi (hS.rightDerivedδ F 0) := (hS.rightDerivedδ_exact₃ F 0).epi_f (hI.eq_of_tgt _ _)
  rw [h0] at hδ
  exact IsZero.of_epi_zero ((F.rightDerived 0).obj (cokernel ι)) _

end Generic

end AlgebraicGeometry.Scheme
