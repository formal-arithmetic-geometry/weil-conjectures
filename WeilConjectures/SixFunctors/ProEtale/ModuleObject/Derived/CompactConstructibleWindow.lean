/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomTruncationWindow
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible

/-!
# Morphisms out of a constructible sheaf only see finitely many degrees

Let `R` be a commutative ring object of sheaves on `X_proét` such that countable products of
`R`-modules are exact, and `C` a constructible sheaf of `R`-modules such that
`Ext^q(C, N) = 0` for `q > d` and all constructible `N`, and such that morphisms out of `C` factor
through filtered colimits. For `K` with ind-constructible cohomology sheaves and `m : ℤ`, the
truncation maps induce bijections

`Hom(C, K[m]) ⟵ Hom(C, (τ_{≤ m} K)[m]) ⟶ Hom(C, (τ_{≥ m - d} τ_{≤ m} K)[m])`

(`AlgebraicGeometry.ProEtale.bijective_comp_truncLEι_shift_and_truncGEπ_shift`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open DerivedCategory.TStructure (t)

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}} {R : Sheaf (Scheme.ProEt.topology X) A} [MonObj R]

/-- Let `C` be a constructible sheaf of `R`-modules with `Ext^q(C, N) = 0` for `q > d` and all
constructible `N`, such that morphisms out of `C` factor through filtered colimits, and assume
countable products of `R`-modules are exact. For `K` with ind-constructible cohomology sheaves and
`m : ℤ`, the truncation maps `K ⟵ τ_{≤ m} K ⟶ τ_{≥ m - d} τ_{≤ m} K` induce bijections
`Hom(C, K[m]) ⟵ Hom(C, (τ_{≤ m} K)[m]) ⟶ Hom(C, (τ_{≥ m - d} τ_{≤ m} K)[m])`. -/
theorem bijective_comp_truncLEι_shift_and_truncGEπ_shift
    [HasExactLimitsOfShape (Discrete ℕ) (Mod (Sheaf (Scheme.ProEt.topology X) A) R)]
    (hR : HasConstructibleExtContinuity R)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) (hM : IsConstructibleModuleObject R M)
    (d : ℤ) (hd : ∀ B, IsConstructibleModuleObject R B → ∀ n < -d,
      ∀ f : (DerivedCategory.singleFunctor _ 0).obj M ⟶
        (DerivedCategory.singleFunctor _ n).obj B, f = 0)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R))
    (hK : DerivedCategory.homologyProperty (IsIndConstructibleModuleObject R) K) (m : ℤ) :
    Function.Bijective (fun f : (DerivedCategory.singleFunctor _ 0).obj M ⟶
          ((t.truncLE m).obj K)⟦m⟧ ↦ f ≫ ((t.truncLEι m).app K)⟦m⟧') ∧
      Function.Bijective (fun f : (DerivedCategory.singleFunctor _ 0).obj M ⟶
          ((t.truncLE m).obj K)⟦m⟧ ↦
        f ≫ ((t.truncGEπ (m - d)).app ((t.truncLE m).obj K))⟦m⟧') :=
  DerivedCategory.bijective_comp_truncLEι_shift_and_truncGEπ_shift d
    (fun B hB n hn ↦ DerivedCategory.eq_zero_of_ind _ (hR M hM) (-d - 1)
      (fun B hB n hn ↦ hd B hB n (by lia)) B hB n (by lia)) K hK m

end AlgebraicGeometry.ProEtale
