/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.ClassicalDefinition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import WeilConjectures.CategoryTheory.KInjectiveBridge

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.Algebra.Homology.KInjectiveProducts
import Sheaf.AlgebraicGeometry.ProEtaleLeftComplete
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.Triangulated.MilnorSequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.TruncationTriangle

/-!
# Fixed-degree truncation for pro-etale sections

Source: the Weil conjectures blueprint, `sk-prop-pe-unbounded-classical`, node
`det-pe-unbounded-classical-truncation` (blueprint: det-pe-unbounded-classical-truncation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated Opposite

namespace AlgebraicGeometry.ProEtale

/-- The constant (possibly noncommutative) coefficient ring sheaf on the small pro-etale site.
Source: blueprint `det-pe-unbounded-classical-truncation`
(blueprint: det-pe-unbounded-classical-truncation). -/
noncomputable def coefficientRingSheaf (X : Scheme.{u}) (A : Type u) [Ring A] :
    Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
  (constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
    (RingCat.of (ULift.{u + 1, u} A))

/-- The category of sheaves of left modules over the coefficient ring sheaf.
Source: blueprint `det-pe-unbounded-classical-truncation`
(blueprint: det-pe-unbounded-classical-truncation). -/
abbrev coefficientModules (X : Scheme.{u}) (A : Type u) [Ring A] :=
  SheafOfModules.{u + 1} (coefficientRingSheaf X A)

/-- Evaluation of coefficient-module sheaves at a pro-etale object, with scalars forgotten.
Source: blueprint `det-pe-unbounded-classical-truncation`
(blueprint: det-pe-unbounded-classical-truncation). -/
noncomputable abbrev evaluationAb (X : Scheme.{u}) (A : Type u) [Ring A]
    (W : X.ProEt) : coefficientModules X A ⥤ AddCommGrpCat.{u + 1} :=
  SheafOfModules.forget (coefficientRingSheaf X A) ⋙
    PresheafOfModules.evaluation (coefficientRingSheaf X A).obj (op W) ⋙
    forget₂ (ModuleCat.{u + 1}
      ((coefficientRingSheaf X A).obj.obj (op W))) AddCommGrpCat.{u + 1}

/-- The total right derived evaluation functor on the unbounded derived category.
Source: blueprint `det-pe-unbounded-classical-truncation`
(blueprint: det-pe-unbounded-classical-truncation). -/
noncomputable def derivedSections (X : Scheme.{u}) (A : Type u) [Ring A]
    (W : X.ProEt) [HasDerivedCategory (coefficientModules X A)]
    [Abelian.HasKInjectiveResolutions (coefficientModules X A)]
    [HasDerivedCategory AddCommGrpCat.{u + 1}] :
    DerivedCategory (coefficientModules X A) ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  (evaluationAb X A W).rightDerivedFunctor

/-- Cohomology of derived sections at `W`, computed in the derived category of abelian groups.
Source: blueprint `det-pe-unbounded-classical-truncation`
(blueprint: det-pe-unbounded-classical-truncation). -/
noncomputable def sectionCohomology (X : Scheme.{u}) (A : Type u) [Ring A]
    (W : X.ProEt) [HasDerivedCategory (coefficientModules X A)]
    [Abelian.HasKInjectiveResolutions (coefficientModules X A)]
    [HasDerivedCategory AddCommGrpCat.{u + 1}]
    (q : ℤ) (H : coefficientModules X A) : AddCommGrpCat.{u + 1} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
    ((derivedSections X A W).obj
      ((DerivedCategory.singleFunctor (coefficientModules X A) (0 : ℤ)).obj H))

/-- A finite coefficient ring has cohomological dimension `e` on classical module sheaves at
`W`, and then unbounded classical complexes satisfy the stated vanishing and truncation
comparison. Source: blueprint `det-pe-unbounded-classical-truncation`
(blueprint: det-pe-unbounded-classical-truncation).

Proof (blueprint detail, Parts (1) and (2)):

1. Evaluation is additive, left exact, and preserves countable products, by sectionwise
kernels and limits (`lem-weil-pbc-module-sheaves-limits-sectionwise`). The ringed-site module
category and abelian groups are Grothendieck (`lem-weil-pbc-ring-sheaves-grothendieck`,
`lem-weil-pbc-ring-modules-grothendieck-abelian`), so functorial K-injective resolutions exist
(`lem-weil-pbc-kinjective-functorial-existence`). The total derived functor is computed on
K-injectives (`lem-weil-pbc-kinjective-total-derived`), commutes with shifts and preserves
triangles (`lem-pc-right-derived-functor-triangulated`). Bounded-below injective resolutions
identify its value on `H[0]` with ordinary evaluation cohomology
(`lem-sc-bounded-below-injective-resolution`, `def-sp-left-exact-additive`).

2. Set `C_n = τ_{≥-n} L`. Its cohomology lies in `[-n,b]` and is classical, since zero
sheaves are classical (`def-kun-truncations`, `sk-def-pe-classical-definition`). If `b < -n`,
it is acyclic and hence zero in the derived category (`def-weil-abstract-derived-category`).

3. Otherwise put `a = -n`. For fixed `m > b+e`, induct on `r` from `a-1` to `b` using
`τ_{≤r-1} C_n → τ_{≤r} C_n → H^r(C_n)[-r]`
(`lem-weil-pbc-truncation-triangle`). The base truncation is zero; the last term after derived
evaluation has degree-`m` cohomology `H^{m-r}(W,H^r(C_n))`, zero because `m-r > e`.
The long exact sequence (`lem-sf-derived-homology-long-exact`) propagates vanishing. Since
`τ_{≤b} C_n → C_n` is a quasi-isomorphism, every `C_n` has this bound.

4. Choose K-injective resolutions `E_n → J_n`. Their termwise product is K-injective and
represents the derived product (`lem-pc-ringed-space-product-kinjective`). Evaluation commutes
with this product and its projections. Exact products of abelian groups
(`lem-pc-abelian-groups-exact-products`) and `lem-weil-derived-limit-products-core` identify the
evaluated product with the product in `D(Ab)`. Thus derived evaluation preserves these products
with their specified projections, not merely up to an unspecified object isomorphism.

5. Left completeness (`det-pe-left-complete-iso`) and `det-pe-products-derived` identify `L`
with the fibre of `1-T` on the product of the `C_n` (`def-weil-derived-limit`). Apply the
triangulated derived evaluation and Step 4. Projection by projection, the image of `T` is the
shift map induced by the transitions on the evaluated tower. Hence the image triangle is the
specified Roos triangle for `B_n = RΓ(W,C_n)`.

6. The abelian-group Milnor sequence (`lem-pc-derived-limit-milnor-sequence`) has outside
terms `R¹lim H^{m-1}(B_n)` and `lim H^m(B_n)`. For `m > b+e+1`, both towers are zero by
Step 3, so the middle term is zero. This proves clause (1) with its stated bound.

7. For clause (2) take `L = τ_{<N} K` and `b = N-1`. Clause (1) gives vanishing above
`N+e`. The standard truncation triangle (`def-sbc-standard-tstructure-derived-category`) has
canonical middle map `K → τ_{≥N} K`; the quotient-to-truncation map is a quasi-isomorphism
by the truncation cohomology formulas (`def-kun-truncations`). Apply derived evaluation and
its long exact sequence. Since `N < m-e-1` implies `m > N+e+1`, the outside terms in degrees
`m` and `m+1` vanish, and the middle map is an isomorphism. All maps retain the coefficient
action; the inverse of a bijective linear map is linear, so underlying groups suffice. -/
theorem unbounded_classical_truncation
    (X : Scheme.{u}) (A : Type u) [Ring A] [Finite A]
    (W : X.ProEt) [HasDerivedCategory (coefficientModules X A)]
    [Abelian.HasKInjectiveResolutions (coefficientModules X A)]
    [HasDerivedCategory AddCommGrpCat.{u + 1}]
    (e : ℕ)
    (hbound : ∀ (q : ℤ) (H : coefficientModules X A),
      IsClassicalModuleSheaf H → q > e → IsZero (sectionCohomology X A W q H))
    : (∀ (L : DerivedCategory (coefficientModules X A))
      (_hL : IsClassicalModuleComplex L) (b : ℤ),
      (∀ (q : ℤ), b < q → IsZero
        ((DerivedCategory.homologyFunctor (coefficientModules X A) q).obj L)) →
      ∀ (m : ℤ), b + e + 1 < m → IsZero
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} m).obj
          ((derivedSections X A W).obj L))) ∧
    (∀ (K : DerivedCategory (coefficientModules X A))
      (_hK : IsClassicalModuleComplex K) (m N : ℤ),
      N < m - e - 1 → IsIso
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} m).map
          ((derivedSections X A W).map
            ((CategoryTheory.Triangulated.TStructure.truncGEπ
              DerivedCategory.TStructure.t N).app K)))) := by
  sorry

end AlgebraicGeometry.ProEtale
