/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.RelativeCurvePunctual
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import all WeilConjectures.DeligneLaumon.NativeMixedExtensions
import WeilConjectures.DeligneLaumon.NativeMixedSubquotients
import WeilConjectures.DeligneLaumon.NativeShriek.NativeShriekComposition
import WeilConjectures.DeligneLaumon.NativeShriek.NativeLerayFiltration
import WeilConjectures.Compactification.NagataCompactification

import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstructibleTruncations
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SmoothPurity.WeilSheafComplex

/-!
# Composition preserves the direct-image weight bound

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-general/sec-reduction-to-the-relative-affine-line/
sk-thm-dl-general-sheaf/lem-zl-composition-weight-bound.md`, Statement, order 4319, with the
scope of expert Wei Yang, Zulip #1451 item 38: `X₀`, `Z₀`, `Y₀` separated of finite type
over `k₀` (blueprint: lem-zl-composition-weight-bound).

The finite-field datum is represented by `FiniteFieldDatum`.  Weil sheaves are the
native condensed Weil modules of `NativeL2`; compactly supported higher direct images
are the canonical `RelativeCurve.higherShriek` objects, built from the ordinary condensed
compactification functor `Rp_* ∘ D(j_!)` (`rightDerivedLowerShriekOfCompactification`)
and the canonical Frobenius exchange.  The compactification quantifier makes the statement
independent of a chosen presentation.

## Main statements

* `WeilConjectures.DeligneLaumon.compositionWeightBound`: for separated finite-type
  morphisms `h₀ : X₀ ⟶ Z₀`, `g₀ : Z₀ ⟶ Y₀` of separated finite-type `k₀`-schemes, the
  direct-image weight assertion for `h₀` and `g₀` implies it for `h₀ ≫ g₀`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.DeligneLaumon


private theorem mixed_of_iso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {M N : NativeL2.WeilModule D l X₀} (e : M ≅ N)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    (hM : NativeL2.Mixed D l X₀ M iota w) : NativeL2.Mixed D l X₀ N iota w := by
  obtain ⟨m, G, φ, hc, hz, ⟨last⟩, hm, hp⟩ := hM
  exact ⟨m, G, φ, hc, hz, ⟨last ≪≫ e⟩, hm, hp⟩

private theorem single_constructible
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : NativeL2.WeilModule D l X₀)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier) :
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left ((NativeShriek.single D l X₀).obj M).carrier := by
  let P : ObjectProperty (NativeCondensedModule.Modules l (D.geometricFiber X₀).left) :=
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber X₀).left
  let := (constantModelConstructibleFiniteTor_wellDefined
    (Profinite.padicAlgClRingObj l) (D.geometricFiber X₀).left).1
  let R : ObjectProperty (NativeL2.WeilModule D l X₀) := fun M ↦ P M.carrier
  have : R.ContainsZero := (native_constructible_closure D l X₀).1
  obtain ⟨Z, hZ, hcZ⟩ := ObjectProperty.exists_prop_of_containsZero R
  have : P.ContainsZero := ⟨⟨Z.carrier,
    (CategoryTheory.Endofunctor.IsoAlgebra.forget _).map_isZero hZ, hcZ⟩⟩
  change constantModelBoundedConstructible _ _ ((DerivedCategory.singleFunctor _ 0).obj _)
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst n
    exact P.prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M.carrier).symm hM
  · apply P.prop_of_isZero
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ 0 n hn
    · exact DerivedCategory.isZero_of_isLE _ 0 n hn


/-- Let `X₀`, `Z₀`, `Y₀` be separated finite-type `k₀`-schemes and `h₀ : X₀ ⟶ Z₀`,
`g₀ : Z₀ ⟶ Y₀` separated finite-type morphisms.  If `h₀` and `g₀` satisfy the upper-weight
estimate (every mixed Weil sheaf of weights `≤ v` has `i`th compactly supported higher
direct image mixed of weights `≤ v + i`), then so does `h₀ ≫ g₀`.  Here
`RelativeCurve.higherShriek` is the canonical compact-support cohomology Weil module of the
ordinary condensed compactification functor and `NativeL2.Mixed` is the native
finite-filtration notion of mixedness.

Source: latest blueprint, `lem-zl-composition-weight-bound.md`, Statement and proof
paragraphs 1--2; scope corrected by expert Wei Yang, Zulip #1451 item 38
(blueprint: lem-zl-composition-weight-bound).

Proof, following the six DAG steps.
1. Base change to `k` keeps separated finite type [lem-pod-separated-finite-type-base-change].
Work with `Λ = Q̄_ℓ` in ordinary `D^b_c`, equal to `D_ctf` by the field-coefficient clause of
[prop-functor-package]; [prop-constructible-truncations] and [sk-lem-coefficient-heart] give
bounded t-structures with abelian constructible hearts; [sk-thm-sf-ctf-stability] gives
bounded constructible `K = Rh_! F` and `T = Rg_!` on these categories.
2. For either map take a compactification `f = p j` inside separated finite-type schemes
[sk-def-sfb-dc-setting], `Rf_! = Rp_* D(j_!)` [sk-def-sfb-module-derived-lower-shriek,
sk-def-sfb-module-lower-shriek, sk-def-sfb-derived-categories]. Exact `j_!` induces a
triangulated t-exact functor [lem-sf-exact-functor-derived-triangulated]; `Rp_*` is
triangulated [lem-sfb-derived-exchange-exact-normalization]. Exact module pullback
[det-prop-sfb-module-pullback-exact-main] is t-exact
[lem-weil-pbc-exact-functor-complex-cohomology]; for `M ∈ D^{≥0}`, `A ∈ D^{≤-1}`,
`Hom(A, Rp_* M) = Hom(p^* A, M) = 0` [sk-def-sfb-module-derived-pushpull], so
`Rp_* M ∈ D^{≥0}` [lem-pur-tstructure-lower-bound-hom-test]. Thus `T` is exact and left
t-exact, and `K` has cohomology only in `[0, U]` for some `U ≥ 0`.
3. `P = Lg_Z^*`, `Q = Lg_Y^*` are exact t-exact equivalences [def-weil-weil-sheaf-complex].
By [lem-zl-frobenius-shriek-exchange-coherence], `β = e_g : QT ≅ TP` commutes with shifts and
triangle maps, `θ = Rh_!(φ) ∘ e_{h,F} : PK ≅ K`, and the compositor `TK ≅ R(gh)_! F` is
equivariant, as in [lem-zl-shriek-composition].
4. [lem-zl-finite-truncation-spectral-sequence] applied to `(T, K, P, Q, β)` and `PK ≅ K`
gives `E₂^{a,b} = R^a g_! R^b h_! F ⇒ R^{a+b}(gh)_! F`, zero for `a < 0` or `b < 0`, with a
finite abutment filtration; all pages, differentials, subquotients and graded
identifications are equivariant, and step 3 identifies the abutment Weil structure.
5. The hypothesis for `h` bounds `R^b h_! F` by `w + b`; that for `g`, with `v = w + b`,
bounds `E₂^{a,b}` by `w + b + a = w + n` on `a + b = n`.
6. Each next page is a Weil subquotient; [lem-a1-mixed-direct-summand] (1) keeps the bound,
hence on `E∞^{a,b}`. Its clause (2) keeps `w + n` through the finite abutment filtration,
starting from zero (the empty mixed filtration of [def-weil-punctual-weights]). Thus
`R^n(gh)_! F` is mixed of weights `≤ w + n`.
-/
theorem compositionWeightBound
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hℓ : ell ≠ D.p)
    (iota : PadicAlgCl ell →+* ℂ)
    (X₀ Z₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [IsSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    (hh : ∀ (v : ℝ) (F : NativeL2.WeilModule D ell X₀),
      NativeL2.Mixed D ell X₀ F iota v →
        ∀ (c₀ : Compactification h₀.left) (i : ℕ),
          NativeL2.Mixed D ell Z₀
            (RelativeCurve.higherShriek D ell h₀ c₀ F i) iota (v + i))
    (hg : ∀ (v : ℝ) (F : NativeL2.WeilModule D ell Z₀),
      NativeL2.Mixed D ell Z₀ F iota v →
        ∀ (c₀ : Compactification g₀.left) (i : ℕ),
          NativeL2.Mixed D ell Y₀
            (RelativeCurve.higherShriek D ell g₀ c₀ F i) iota (v + i)) :
    ∀ (w : ℝ) (F : NativeL2.WeilModule D ell X₀),
      NativeL2.Mixed D ell X₀ F iota w →
        ∀ (c₀ : Compactification (h₀.left ≫ g₀.left)) (n : ℕ),
          NativeL2.Mixed D ell Y₀
            (RelativeCurve.higherShriek D ell (h₀ ≫ g₀) c₀ F n) iota (w + n) := by
  intro w F hF cgh n
  classical
  have : IsLocallyNoetherian Z₀.left := LocallyOfFiniteType.isLocallyNoetherian Z₀.hom
  have : CompactSpace Z₀.left := QuasiCompact.compactSpace_of_compactSpace Z₀.hom
  have : IsLocallyNoetherian Y₀.left := LocallyOfFiniteType.isLocallyNoetherian Y₀.hom
  have : CompactSpace Y₀.left := QuasiCompact.compactSpace_of_compactSpace Y₀.hom
  obtain ⟨ch⟩ := (NagataCompactification h₀.left).hasCompactification.nonempty_compactification
  obtain ⟨cg⟩ := (NagataCompactification g₀.left).hasCompactification.nonempty_compactification
  have hcF : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
      (D.geometricFiber X₀).left F.carrier := by
    obtain ⟨m, G, φ, hc, hz, ⟨last⟩, hm, hp⟩ := hF
    obtain ⟨_, hi, _⟩ := native_constructible_closure D ell X₀
    let R : ObjectProperty (NativeL2.WeilModule D ell X₀) := fun M ↦
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        (D.geometricFiber X₀).left M.carrier
    have : R.IsClosedUnderIsomorphisms := hi
    exact R.prop_of_iso last (hc _)
  obtain ⟨m, G, φ, hc, hz, ⟨last⟩, hm, hq⟩ :=
    NativeShriek.lerayFiltration D ell hℓ X₀ Z₀ Y₀ h₀ g₀ ch cg F hcF n
  have hquot (j : Fin m) : NativeL2.Mixed D ell Y₀ (cokernel (φ j)) iota (w + n) := by
    obtain ⟨a, b, hab, A, i, p, hi, he, hA, hQ⟩ := hq j
    have : Mono i := hi
    have : Epi p := he
    have hE := hg (w + b) _ (hh w F hF ch b) cg a
    have hw : (w + (b : ℝ)) + (a : ℝ) = w + (n : ℝ) := by
      have hn : (a : ℝ) + (b : ℝ) = (n : ℝ) := by exact_mod_cast hab
      linarith
    rw [hw] at hE
    have hA' := (nativeMixedSubquotients D ell Y₀ iota (w + n) _ A hA hE).1 i
    exact (nativeMixedSubquotients D ell Y₀ iota (w + n) A _ hQ hA').2 p
  obtain ⟨hzero, hex⟩ := nativeMixedExtensions D ell Y₀ iota (w + n)
  let P : ObjectProperty (NativeL2.WeilModule D ell Y₀) := fun M ↦
    NativeL2.Mixed D ell Y₀ M iota (w + n)
  have : P.IsClosedUnderExtensions := hex
  have hG : ∀ (j : ℕ) (hj : j < m + 1), P (G ⟨j, hj⟩) := by
    intro j
    induction j with
    | zero => exact fun _ ↦ hzero _ hz
    | succ j ih =>
      intro hj
      let k : Fin m := ⟨j, by omega⟩
      have : Mono (φ k) := hm k
      exact P.prop_X₂_of_shortExact
        (show (ShortComplex.mk (φ k) (cokernel.π (φ k))
          (cokernel.condition (φ k))).ShortExact from
            ⟨ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)⟩)
        (ih (by omega)) (hquot k)
  have hiter := mixed_of_iso D ell Y₀ last iota (w + n) (hG m (by omega))
  obtain ⟨e⟩ := NativeShriek.composition D ell hℓ Z₀ h₀ g₀ ch cg cgh
    ((NativeShriek.single D ell X₀).obj F) (single_constructible D ell X₀ F hcF)
  have hout := mixed_of_iso D ell Y₀
    ((NativeShriek.cohomology D ell Y₀ n).mapIso e) iota (w + n) hiter
  simpa only [NativeShriek.cohomology, NativeShriek.image, NativeShriek.single,
    RelativeCurve.higherShriek] using hout

end WeilConjectures.DeligneLaumon
