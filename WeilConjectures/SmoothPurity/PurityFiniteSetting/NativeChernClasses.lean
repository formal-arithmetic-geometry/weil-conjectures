/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeSupportedCup.NativeSupportedCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Admissible.AdmissibleDivisorClass
public import WeilConjectures.SmoothPurity.PurityBaseField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleCondensedCoefficientFamily
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleKummerLimitBoundary
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull

/-!
# Chern classes of vector bundles at every admissible condensed coefficient

Source: Stacks Project, Tag 0FI5, proposition-chern-class and equation-chern-classes;
blueprint localized-top-Chern Step 4 (L4) (blueprint: def-pur-chern-classes).

This module is an ADDITION: the finite-level record `ordinaryFiniteChernClasses`
(Sheaf.Paper.PurityChernClasses) is unchanged. Here the coefficient is a presentation
`c : PurityTransport.Coefficient ell` (any presentation, see below), the ordinary
cohomology group H^a(T, Λ(m)) is the Hom group `Λ_T ⟶ Λ_T(m)[a]` in `c.derived ell T`
(source the degree-zero coefficient unit, target `NativeSupportedCup.target`), pullback is
the derived pullback with the canonical unit and root-normalized line comparisons, and the
full-support cup product is the supported cup composite of def-pur-supported-cup with the
unitor as coefficient multiplication.

Coefficient range (stack decision deliv/COEFF-DECISION.md). Every declaration holds for every
presentation `c : PurityTransport.Coefficient P.coefficients.l`, with no further hypothesis on `c`.
This is exactly the coefficient field `Setting.coefficient` of the current def-pur-conventions Lean
(`WeilConjectures.CurrentPurityConventions.Setting`): the finite constructor accepts every finite
commutative ell-primary ring A, and the other constructors are Z_ell, Q_ell, O_E, E and Qbar_ell.
`nativeChernAdmissible` shows that the ring of every presentation satisfies the current
admissibility predicate `CondensedRing.IsAdmissibleCoefficientFor P.coefficients` used by the
divisor-class interface (Sheaf.Paper.AdmissibleDivisorClass). No declaration of the withdrawn model
module of lem-pur-condensed-cartier-compact-exchange is used or imported.

Choice of first Chern class. The node takes h = c_{1,A}(O_P(1)), the Kummer first Chern
class of lem-pur-kummer-additivity, i.e. the Kummer boundary of the frame-torsor class of
the line bundle. Two native records exist. `NativeProjectiveBundle.chern` needs an
auxiliary `NativeKummerData` D, a structure with data fields (`integral`, `linear`,
`boundary`). The tree only asserts `∃ D : NativeKummerData` (ProEtaleKummerLimitBoundaryStatement),
so making c_i(F) depend on D would make it non-canonical or need a bare-∃ choice
(AGENTS §5). `CondensedRing.Admissible.firstChernOver` is the unique class with `ChernSpecOver`
(Kummer boundary of `picardUnits`, the frame torsor), taken from `chern_existsUniqueOver` (an `∃!`).
That is exactly the node's c_{1,A}, so we use it. Its target line `Admissible.line` is
identified with `c.line ell T 1` by `nativeChernLineIso`.

The class h_F of thm-pur-projective-bundle-formula is the native realization
B_{Λ,P}(α_P(O_P(1))) of lem-pur-proetale-kummer-limit-boundary; its Lean form is
`NativeProjectiveBundle.tautologicalChern`, i.e. `((D.boundary c).B (Ext.homEquiv.symm
(SpTowerClasses.lineBundleEtaleClass P L))).hom` for a `NativeKummerData` D. That module is
not imported here (it still imports the withdrawn model module), so the identification is stated
against the same boundary of Sheaf.Paper.ProEtaleKummerLimitBoundary:
`nativeFirstChern_eq_nativeBoundary` (every Picard class and every D) and
`nativeChernHyperplane_eq_nativeBoundary` (h = h_F on every realization).

Chern classes are then the unique family solving the projective-bundle relation on every
quotient-convention realization (`nativeChernClasses_existsUnique`, an `∃!`), and
`nativeChernClasses` is its `choose`.

Base field (G1 over K, stack g1k RULES). Every declaration that involves a structure morphism
takes `(K : PurityBaseField P.coefficients.l)` right after `P`, and the structure morphism is
`a : T ⟶ Spec (.of K.K)`; `P` is only the source of the coefficients. The residue inverses are
`K.residueInverse` and the first Chern class is `Admissible.firstChernOver`
(Sheaf.Paper.PurityBaseField, Sheaf.Paper.AdmissibleDivisorClassField). The k̄ case is
`K = P.geometricBase`. The declarations without a structure morphism (coefficient bridges,
`NativeChernCohomology`, `nativeChernOne`, `nativeChernReindex`, `nativeChernCup`,
`nativeChernPower`) are base-free and unchanged.

## Main definitions

- `nativeChernAdmissible`, `nativeChernLine_eq`, `nativeChernLineIso`: coefficient bridges.
- `NativeChernCohomology`, `nativeChernOne`, `nativeChernReindex`, `nativeChernPullback`,
  `nativeChernCup`, `nativeChernPower`: ordinary groups and operations at c.
- `nativeFirstChern`: c_1 of a Picard class; `nativeFirstChern_eq_nativeBoundary`,
  `nativeChernHyperplane_eq_nativeBoundary`: identification with the native Kummer boundary h_F.
- `nativeChernProjectiveRelation`, `IsNativeChernClasses`, `nativeChernClasses`,
  `nativeChernClass`, `nativeTopChern`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry.ProEtale.CondensedRing.Admissible
open AlgebraicGeometry.ProEtale.NativeSupportedCup (ring target derivedLineMul)

/-! ### Coefficient bridges -/

/-- Every coefficient presentation gives an admissible condensed coefficient ring, in the sense
of the current predicate `IsAdmissibleCoefficientFor` (all finite commutative ell-primary A, O_E,
E, Qbar_ell). So the coefficient range of this module is all of def-pur-conventions.
Source: def-pur-conventions and def-pur-admissible-condensed-ring
(blueprint: def-pur-chern-classes).
Proof: by cases on `c`, as `PurityCoefficientChange.coefficientAdmissible`. For
`.finite A fin n h` take the first disjunct with A, the discrete topology, r = n + 1 and the
identity isomorphism (`Coefficient.ring` is `continuousMapRingSheaf A`). For `.integral E`,
`.rational E` and `.closure` take the second, third and fourth disjuncts with the identity.
For `.integers` and `.rationals` take E = Q_ell (the bottom intermediate field) and the
canonical isomorphism Z_ell ≅ O_{Q_ell}, Q_ell ≅ Q_ell of condensed rings. -/
theorem nativeChernAdmissible (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) :
    CondensedRing.IsAdmissibleCoefficientFor P.coefficients (ring.{u} P.coefficients.l c) := by
  sorry

/-- The Tate line of the admissible-ring record is the root-tower first line of c.
Source: sk-def-sp-tate-twist (blueprint: def-pur-chern-classes).
Proof: `integralMap_existsUnique` makes the integral map unique. `c.integralMap ell`
together with `Coefficient.integralMap_isMonHom` is such a map, so both maps agree. Both
lines are then `extendScalars (coefficientMap _ X)` of `tateModule X ell`. -/
theorem nativeChernLine_eq (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) (X : Scheme.{u}) :
    line P (ring P.coefficients.l c) (nativeChernAdmissible P c) X =
      c.firstLine P.coefficients.l X := by
  sorry

/-- The admissible-record Tate line as the first positive line `c.line ell X 1 = 𝟙_ ⊗ Λ(1)`.
Source: sk-def-sp-tate-twist (blueprint: def-pur-chern-classes).
Base field: `nativeChernLineIso` is base-free; `_geometric`: the k̄ G1 version is this same
declaration. -/
def nativeChernLineIso (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) (X : Scheme.{u}) :
    line P (ring P.coefficients.l c) (nativeChernAdmissible P c) X ≅
      c.line P.coefficients.l X 1 :=
  eqToIso (nativeChernLine_eq P c X) ≪≫ (λ_ (c.firstLine P.coefficients.l X)).symm

/-! ### Ordinary cohomology, pullback and cup product at c -/

/-- The degree-zero coefficient unit Λ_T in `c.derived ell T`.
Source: def-pur-conventions (blueprint: def-pur-chern-classes).
Base field: `nativeChernUnit` is base-free; `_geometric`: the k̄ G1 version is this same
declaration. -/
abbrev nativeChernUnit (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) (T : Scheme.{u}) :
    c.derived P.coefficients.l T :=
  (DerivedCategory.singleFunctor _ 0).obj (unit (ring P.coefficients.l c) T)

/-- Ordinary cohomology H^a(T, Λ(m)) = Hom(Λ_T, Λ_T(m)[a]) in the native derived category.
Source: def-pur-chern-classes, ordinary Hom groups (blueprint: def-pur-chern-classes).
Base field: `NativeChernCohomology` is base-free; `_geometric`: the k̄ G1 version is this same
declaration. -/
abbrev NativeChernCohomology (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) (T : Scheme.{u}) (a : ℤ) (m : ℕ) :=
  nativeChernUnit P c T ⟶ target P.coefficients.l c T a m

/-- Transport along equal degree and twist indices.
Source: index bookkeeping only (blueprint: def-pur-chern-classes).
Base field: `nativeChernReindex` is base-free; `_geometric`: the k̄ G1 version is this same
declaration. -/
def nativeChernReindex (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) (T : Scheme.{u})
    {a a' : ℤ} {m m' : ℕ} (ha : a = a') (hm : m = m') :
    target P.coefficients.l c T a m ⟶ target P.coefficients.l c T a' m' :=
  eqToHom (by subst ha; subst hm; rfl)

/-- The class 1 ∈ H^0(T, Λ(0)): `c.line ell T 0 = 𝟙_` is the unit, then the zero shift.
Source: def-pur-chern-classes, c_0 = 1 (blueprint: def-pur-chern-classes).
Base field: `nativeChernOne` is base-free; `_geometric`: the k̄ G1 version is this same declaration.
-/
def nativeChernOne (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) (T : Scheme.{u}) :
    NativeChernCohomology P c T 0 0 :=
  (shiftFunctorZero (c.derived P.coefficients.l T) ℤ).inv.app (nativeChernUnit P c T)

/-- The unit multiplication Λ ⊗ Λ → Λ is invertible after derivation (degree zero, flat).
Source: def-pur-supported-cup, coefficient identification (blueprint: def-pur-chern-classes).
Proof: the unit is flat, so `cupSingleTensorMap` is invertible (`cupSingleTensorMap_isIso`
pattern), and the unitor is an isomorphism. -/
theorem nativeChernUnitMul_isIso (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) (T : Scheme.{u}) :
    IsIso (cupDerivedCoefficientMap
      (λ_ (𝟙_ (Modules (ring P.coefficients.l c) T))).hom) := by
  sorry

/-- Full-support cup product: the supported cup composite at support id_T, with unit
multiplication as coefficient identification and multiplication of the twist lines.
Source: def-pur-supported-class-operations and def-pur-supported-cup
(blueprint: def-pur-chern-classes).
Base field: `nativeChernCup` is base-free; `_geometric`: the k̄ G1 version is this same declaration.
-/
def nativeChernCup (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) (T : Scheme.{u})
    (a b : ℤ) (r s : ℕ) (α : NativeChernCohomology P c T a r)
    (β : NativeChernCohomology P c T b s) : NativeChernCohomology P c T (a + b) (r + s) :=
  letI : ∀ K : c.derived P.coefficients.l T,
      ((curriedTensor (c.derived P.coefficients.l T)).obj K).CommShift ℤ :=
    fun K ↦ DerivedCategory.commShiftTensorLeft _ K
  letI : ∀ K : c.derived P.coefficients.l T,
      ((curriedTensor (c.derived P.coefficients.l T)).flip.obj K).CommShift ℤ :=
    fun K ↦ DerivedCategory.commShiftTensorRight _ K
  -- CHECK: α, β have source `nativeChernUnit` = single (Admissible.unit ..) while θ has
  -- source single 𝟙_ ⊗ single 𝟙_; needs `Admissible.unit Λ T` defeq `𝟙_`.
  cupComposite (cupDerivedCoefficientMap
      (λ_ (𝟙_ (Modules (ring P.coefficients.l c) T))).hom)
    (nativeChernUnitMul_isIso P c T) a b α β ≫
    (derivedLineMul P.coefficients.l c T r s)⟦a + b⟧'

/-- The ordered cup power h^j ∈ H^{2j}(T, Λ(j)) with h^0 = 1 and h^{j+1} = h^j ∪ h.
Source: def-pur-chern-classes, ordered cup power (blueprint: def-pur-chern-classes).
Base field: `nativeChernPower` is base-free; `_geometric`: the k̄ G1 version is this same
declaration. -/
def nativeChernPower (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) (T : Scheme.{u})
    (h : NativeChernCohomology P c T 2 1) : (j : ℕ) → NativeChernCohomology P c T (2 * (j : ℤ)) j
  | 0 => nativeChernOne P c T ≫ nativeChernReindex P c T (by simp) rfl
  | j + 1 => nativeChernCup P c T _ 2 j 1 (nativeChernPower P c T h j) h ≫
      nativeChernReindex P c T (by push_cast; ring) rfl

/-! ### First Chern class -/

/-! ### The projective-bundle relation and the Chern family -/

/-! ### Stated properties of the node -/

end WeilConjectures.PurityFiniteSetting
