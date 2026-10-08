/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible

/-!
# Finiteness for the pushforward of constructible `ℓ`-adic sheaves

Let `K` be an algebraically closed field of characteristic different from `ℓ`, `Y` a scheme
locally of finite type over `K` and `f : X ⟶ Y` a quasi-compact, quasi-separated morphism
locally of finite type. The *finiteness theorem* (SGA 4½, *Th. finitude*, Th. 1.1, with
`ℓ`-adic coefficients as in Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8, and the
blueprint `sk-prop-sf-finiteness`) asserts that for a constructible `ℓ`-adic sheaf `F` on
`X_proét`:

- the pushforward `f_* F` is constructible
  (`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.lowerStar`);
- every higher direct image `Rⁿf_* F`, the `n`-th cohomology sheaf of the total derived
  pushforward `Rf_*(F[0])`, is constructible
  (`AlgebraicGeometry.ProEtale.isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar`);
- if moreover `Y` is quasi-compact, then `Rf_*(F[0])` is bounded: the cohomological dimension of
  `f_*` is at most twice the dimension of the fibres, which is bounded on a quasi-compact `Y`
  (`AlgebraicGeometry.ProEtale.bounded_rightDerivedFunctor_lowerStar`).

These are the inputs for the finiteness of the pushforward of Weil sheaves and Weil complexes
(`WeilConjectures.WeilSheaf.LowerStar`), and are stated here with `sorry`. Their proof
(blueprint `sk-prop-sf-finiteness`) proceeds by generic constructibility for open immersions
(Deligne's dévissage), the proper case, and a Čech argument for a finite affine cover of `X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
  (s : Y ⟶ Spec (.of K)) (f : X ⟶ Y)

/-- **Finiteness for the pushforward of a constructible `ℓ`-adic sheaf** (SGA 4½,
*Th. finitude*): over an algebraically closed field of characteristic `≠ ℓ`, the pushforward
of a constructible `ℓ`-adic sheaf along a quasi-compact quasi-separated morphism locally of
finite type, with target locally of finite type, is constructible. -/
theorem IsAdicConstructibleSheaf.lowerStar (hK : ringChar K ≠ l) [LocallyOfFiniteType s]
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)}
    (hF : IsAdicConstructibleSheaf F) :
    IsAdicConstructibleSheaf ((f)_*[WeilCoefficients.{u} l].obj F) :=
  sorry

/-- **Finiteness for the higher direct images of a constructible `ℓ`-adic sheaf** (SGA 4½,
*Th. finitude*): over an algebraically closed field of characteristic `≠ ℓ`, the higher direct
images `Rⁿf_* F` of a constructible `ℓ`-adic sheaf along a quasi-compact quasi-separated
morphism locally of finite type, with target locally of finite type, are constructible. -/
theorem isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar (hK : ringChar K ≠ l)
    [LocallyOfFiniteType s] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)}
    (hF : IsAdicConstructibleSheaf F) (n : ℤ) :
    IsAdicConstructibleSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((f)_*[WeilCoefficients.{u} l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) :=
  sorry

/-- **Boundedness of the derived pushforward of a constructible `ℓ`-adic sheaf** (SGA 4½,
*Th. finitude*): over an algebraically closed field of characteristic `≠ ℓ`, the derived
pushforward of a constructible `ℓ`-adic sheaf along a quasi-compact quasi-separated morphism
locally of finite type, with target quasi-compact and locally of finite type, is bounded. -/
theorem bounded_rightDerivedFunctor_lowerStar (hK : ringChar K ≠ l) [LocallyOfFiniteType s]
    [QuasiCompact s] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)}
    (hF : IsAdicConstructibleSheaf F) :
    DerivedCategory.TStructure.t.bounded
      ((f)_*[WeilCoefficients.{u} l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  sorry

end AlgebraicGeometry.ProEtale
