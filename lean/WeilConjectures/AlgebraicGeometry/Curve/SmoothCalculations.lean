/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import Sheaf.AlgebraicGeometry.ArtinSchreier
import Sheaf.AlgebraicGeometry.ArtinSchreierSequence
import Sheaf.AlgebraicGeometry.BaseChangeCurve
import Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo
import Sheaf.AlgebraicGeometry.Curve.ConstantInvariance
import Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension
import Sheaf.AlgebraicGeometry.Curve.ProperCohomology
import Sheaf.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Curve.Affine
import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
import WeilConjectures.AlgebraicGeometry.Sites.Gm
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.LinearAlgebra.SemilinearFrobenius
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension

/-!
# The curve assertions for constant coefficients on smooth curves

Let `k` be an algebraically closed field, `f : C ⟶ Spec k` a smooth separated connected curve
(`[IsCurve f] [Smooth f] [ConnectedSpace C]`) and `n` a prime. The constant sheaf `𝐅_n` is
read over an arbitrary coefficient ring `Λ` as the constant sheaf `Λ/nΛ`
(`AlgebraicGeometry.Etale.constantModSheaf Λ C n`), and `Hᵠ(C, 𝐅_n)` is the cohomology of its
underlying abelian sheaf, as in the eight curve assertions
`AlgebraicGeometry.IsCurve.Assertions`. This file states, for `F = 𝐅_n`, each assertion
`C₁, …, C₈` in the form of the corresponding field of `AlgebraicGeometry.IsCurve.Assertions`,
under the hypotheses of the smooth-curve calculations:

* `C₁`, `C₈` for every prime `n`; `C₂` for affine `C`; `C₅`, `C₇` for proper `C`;
* `C₄`, `C₆` for `n ≠ char k`;
* `C₃` for `n = char k = p > 0`.

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_constantModSheaf_of_two_lt`: `C₁`.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_constantModSheaf_of_one_lt_of_isAffine`: `C₂`.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP`: `C₃`.
- `AlgebraicGeometry.IsCurve.finite_sheafH_constantModSheaf_of_ne_zero`: `C₄`.
- `AlgebraicGeometry.IsCurve.finite_sheafH_constantModSheaf_of_isProper`: `C₅`.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_constantModSheaf_of_ne_zero`: `C₆`.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_constantModSheaf_of_isProper`: `C₇`.
- `AlgebraicGeometry.IsCurve.surjective_cohomologyMap_constantModSheaf_two`: `C₈`.
- `AlgebraicGeometry.IsCurve.constantModSheaf_curveCalculations`: the smooth-curve
  calculations, the conjunction of the above.
- `AlgebraicGeometry.IsCurve.assertions_constantModSheaf_of_ne_zero`: all eight assertions
  for `𝐅_ℓ`, `ℓ ≠ char k`, on a smooth curve (not necessarily connected).
- `AlgebraicGeometry.IsCurve.assertions_constantModSheaf_of_charP`: all eight assertions
  for `𝐅_p`, `p = char k`, on a smooth curve (not necessarily connected).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### Auxiliary lemmas -/

/-- The constant sheaf `Λ/nΛ` is killed by `n`: `n • 𝟙 = 0` on
`AlgebraicGeometry.Etale.constantModSheaf Λ X n`. -/
lemma Etale.nsmul_id_constantModSheaf (X : Scheme.{u}) (n : ℕ) :
    n • 𝟙 (Etale.constantModSheaf Λ X n) = 0 := by
  rw [Etale.constantModSheaf, ← (constantSheaf _ _).map_id, ← Functor.map_nsmul,
    ← (constantSheaf _ _).map_zero]
  congr 1
  ext
  simpa using (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_span_singleton_self (n : Λ))

/-- For `n > 0`, the underlying abelian sheaf of the constant sheaf `Λ/nΛ` is torsion
(`CategoryTheory.Sheaf.IsTorsion`): every section is killed by `n`. -/
lemma Etale.isTorsion_constantModSheaf (X : Scheme.{u}) {n : ℕ} (hn : 0 < n) :
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      (Etale.constantModSheaf Λ X n)).IsTorsion := by
  refine Sheaf.IsTorsion.of_forall_isAddTorsion fun U x ↦ ?_
  have h := congr_arg
    (fun φ => ((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map φ).app U)
    (Etale.nsmul_id_constantModSheaf Λ X n)
  simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero, NatTrans.app_zero] at h
  have hx := congr_arg (fun φ => φ.hom x) h
  simp only [ModuleCat.hom_nsmul, ModuleCat.hom_zero] at hx
  exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, hx⟩

namespace IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))

/-! ### The assertions `C₁, …, C₈` for `𝐅_n` -/

/-- **`C₁` for `𝐅_n`.** Let `C` be a smooth separated connected curve over an algebraically
closed field `k` and `n` a prime. Then `Hᵠ(C, 𝐅_n) = 0` for `q > 2`, where `𝐅_n` is the constant
sheaf `Λ/nΛ` and `Hᵠ` is the cohomology of its underlying abelian sheaf. This is the
cohomological dimension bound `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le`,
the constant sheaf being killed by `n`.
(blueprint: `lem-sc-c1`) -/
theorem subsingleton_sheafH_constantModSheaf_of_two_lt [IsCurve f] [Smooth f] [ConnectedSpace C]
    (n : ℕ) [Fact n.Prime] (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C n)) q) :=
  subsingleton_sheafH_of_three_le f _
    (Etale.isTorsion_constantModSheaf Λ C (Fact.out : n.Prime).pos) q hq

/-- **`C₂` for `𝐅_n`.** Let `C` be a smooth affine connected curve over an algebraically closed
field `k` and `n` a prime. Then `Hᵠ(C, 𝐅_n) = 0` for `q > 1`. This is the cohomological dimension
bound `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine`, the constant sheaf
being killed by `n`.
(blueprint: `lem-sc-c2`) -/
theorem subsingleton_sheafH_constantModSheaf_of_one_lt_of_isAffine [IsCurve f] [Smooth f]
    [ConnectedSpace C] [IsAffine C] (n : ℕ) [Fact n.Prime] (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C n)) q) :=
  subsingleton_sheafH_of_two_le_of_isAffine f _
    (Etale.isTorsion_constantModSheaf Λ C (Fact.out : n.Prime).pos) q hq

/-- **`C₃` for `𝐅_p`.** Let `k` be algebraically closed of characteristic `p > 0` and `C` a
smooth separated connected curve over `k`. Then `Hᵠ(C, 𝐅_p) = 0` for `q > 1`: by the
Artin–Schreier sequence `0 → 𝐅_p → 𝒪_C → 𝒪_C → 0` and the surjectivity of `F - 1`, the
`p`-cohomological dimension of `C` is at most one. The `p`-primary hypothesis of the field
`C₃` of `AlgebraicGeometry.IsCurve.Assertions` holds automatically for `𝐅_p` and is omitted.
(blueprint: `lem-sc-c3`) -/
theorem subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP [IsCurve f] [Smooth f]
    [ConnectedSpace C] (p : ℕ) [Fact p.Prime] [CharP k p] (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C p)) q) :=
  by
    by_cases hq2 : q = 2
    · subst q
      exact subsingleton_sheafH_constantModSheaf_of_charP_two Λ f p
    · have hq' : 2 < q := by omega
      exact subsingleton_sheafH_constantModSheaf_of_two_lt Λ f p q hq'

/-- **`C₄` for `𝐅_r`.** Let `C` be a smooth separated connected curve over an algebraically
closed field `k` and `r` a prime different from `char k`. If `Λ/rΛ` is finite, then
`Hᵠ(C, 𝐅_r)` is finite for every `q`: `C` is proper or affine, and the
groups are computed by the Kummer sequence. The torsion hypothesis of the field `C₄` of
`AlgebraicGeometry.IsCurve.Assertions` is replaced by `(r : k) ≠ 0`.
(blueprint: `lem-sc-c4`) -/
theorem finite_sheafH_constantModSheaf_of_ne_zero [IsCurve f] [Smooth f] [ConnectedSpace C]
    (r : ℕ) [Fact r.Prime] (hr : (r : k) ≠ 0)
    [Finite (Λ ⧸ (Ideal.span {(r : Λ)} : Ideal Λ))] (q : ℕ) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) q) :=
  sorry

/-- **`C₅` for `𝐅_r`.** Let `C` be a smooth proper connected curve over an algebraically closed
field `k` and `r` an arbitrary prime. If `Λ/rΛ` is finite, then `Hᵠ(C, 𝐅_r)` is finite for
every `q`: for `r ≠ char k` by the curve estimates, and for
`r = char k = p` by the Artin–Schreier sequence, which identifies `H¹(C, 𝐅_p)` with the
Frobenius-fixed part of `H¹(C, 𝒪_C)` and kills the higher groups.
(blueprint: `lem-sc-c5`) -/
theorem finite_sheafH_constantModSheaf_of_isProper [IsCurve f] [Smooth f] [ConnectedSpace C]
    [IsProper f] (r : ℕ) [Fact r.Prime] [Finite (Λ ⧸ (Ideal.span {(r : Λ)} : Ideal Λ))]
    (q : ℕ) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) q) :=
  sorry

/-- **`C₆` for `𝐅_r`.** Let `k ⊆ k'` be algebraically closed fields, `C` a smooth separated
connected curve over `k` and `r` a prime different from `char k`. For every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, 𝐅_r) ⟶ Hᵠ(C', ι'^* 𝐅_r)` is bijective for every `q`. For `Λ = ℤ` and
the standard square this is `AlgebraicGeometry.bijective_cohomologyMap_constantZMod`. The
torsion hypothesis of the field `C₆` of `AlgebraicGeometry.IsCurve.Assertions` is replaced by
`(r : k) ≠ 0`.
(blueprint: `lem-sc-c6`) -/
theorem bijective_cohomologyMap_constantModSheaf_of_ne_zero [IsCurve f] [Smooth f]
    [ConnectedSpace C] (r : ℕ) [Fact r.Prime] (hr : (r : k) ≠ 0) (k' : Type u) [Field k']
    [IsAlgClosed k'] {C' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) q) :=
  sorry

/-- **`C₇` for `𝐅_r`.** Let `k ⊆ k'` be algebraically closed fields, `C` a smooth proper
connected curve over `k` and `r` an arbitrary prime. For every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, 𝐅_r) ⟶ Hᵠ(C', ι'^* 𝐅_r)` is bijective for every `q`. For `r = char k`
this is the invariance of the Frobenius-fixed part of `H¹(C, 𝒪_C)` under the extension `k'/k`.
(blueprint: `lem-sc-c7`) -/
theorem bijective_cohomologyMap_constantModSheaf_of_isProper [IsCurve f] [Smooth f]
    [ConnectedSpace C] [IsProper f] (r : ℕ) [Fact r.Prime] (k' : Type u) [Field k']
    [IsAlgClosed k'] {C' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) q) :=
  sorry

/-- **`C₈` for `𝐅_r`.** Let `C` be a smooth separated connected curve over an algebraically
closed field `k`, `a : W ⟶ C` an open immersion and `r` a prime. Then the restriction
`H²(C, 𝐅_r) ⟶ H²(W, a^* 𝐅_r)` is surjective: either `W = C`, or `W` is affine and
`H²(W, 𝐅_r) = 0`.
(blueprint: `lem-sc-c8`) -/
theorem surjective_cohomologyMap_constantModSheaf_two [IsCurve f] [Smooth f] [ConnectedSpace C]
    (r : ℕ) [Fact r.Prime] {W : Scheme.{u}} (a : W ⟶ C) [IsOpenImmersion a] :
    Function.Surjective (Etale.cohomologyMap a
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) 2) :=
  by
    classical
    let F := (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)
    by_cases ha : Function.Surjective a
    · have : Surjective a := ⟨ha⟩
      have : IsIso a := (isIso_iff_isOpenImmersion_and_surjective a).mpr
        ⟨inferInstance, inferInstance⟩
      exact (Etale.cohomologyMap_bijective a F 2).surjective
    · have hW : IsAffine W := by
        have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
        have : IsRegular C := IsRegular.of_smooth f
        have : IrreducibleSpace C := IsRegular.irreducibleSpace C
        by_cases hdim : topologicalKrullDim C = 1
        · have : IsConnectedCurve f :=
            { krullDim_le_one := IsCurve.krullDim_le_one (f := f)
              connectedSpace := inferInstance
              krullDim_eq_one := hdim }
          obtain ⟨c, hc, hs, _hfin, _hcl⟩ :=
            IsConnectedCurve.exists_smooth_properCompactification f
          have := hc
          have := hs
          have := c.isProper
          have := c.isOpenImmersion
          let V := (a ≫ c.i).opensRange
          have hV : V ≠ ⊤ := by
            intro htop
            apply ha
            intro x
            have hx : c.i x ∈ V := by rw [htop]; trivial
            obtain ⟨w, hw⟩ := hx
            exact ⟨w, c.i.isOpenEmbedding.injective hw⟩
          have : IsAffine V := IsConnectedCurve.isAffine_of_ne_top c.g V hV
          let e : W ≅ (V : Scheme.{u}) :=
            IsOpenImmersion.isoOfRangeEq (a ≫ c.i) V.ι
              (by rw [Scheme.Opens.range_ι]; rfl)
          exact IsAffine.of_isIso e.hom
        · have h0 : topologicalKrullDim C ≤ 0 := by
            have h1 : topologicalKrullDim C < ((0 : ℕ) : WithBot ℕ∞) + 1 :=
              lt_of_le_of_ne (IsCurve.krullDim_le_one (f := f)) hdim
            exact ENat.WithBot.lt_add_one_iff.1 h1
          have : Subsingleton C := subsingleton_of_topologicalKrullDim_le_zero h0
          have : Subsingleton W := ⟨fun x y ↦ a.isOpenEmbedding.injective
            (Subsingleton.elim _ _)⟩
          infer_instance
      have : IsAffine W := hW
      have : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
      have : TopologicalSpace.NoetherianSpace W :=
        a.isOpenEmbedding.isInducing.noetherianSpace
      have : QuasiCompact a := ⟨fun U _ _ ↦
        TopologicalSpace.NoetherianSpace.isCompact _⟩
      have : IsCurve (a ≫ f) :=
        { krullDim_le_one := a.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans
            (IsCurve.krullDim_le_one (f := f)) }
      have hF := Etale.isTorsion_constantModSheaf Λ C (Fact.out : r.Prime).pos
      have : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj F) 2) :=
        subsingleton_sheafH_two_of_isAffine (a ≫ f) _ (Etale.isTorsion_upperStar a hF)
      exact fun y ↦ ⟨0, Subsingleton.elim _ _⟩

/-! ### The smooth-curve calculations -/

/-- **The smooth-curve calculations.** Let `C` be a smooth separated connected curve over an
algebraically closed field `k` and `n` a prime. The constant sheaf `𝐅_n` (read over `Λ` as
`Λ/nΛ`) satisfies

* `C₁` and `C₈`;
* `C₂` when `C` is affine, `C₅` and `C₇` when `C` is proper;
* `C₄` and `C₆` when `n ≠ char k` (part (a) of the blueprint statement), the finiteness in
  `C₄` and `C₅` when `Λ/nΛ` is finite;
* `C₃` when `n = char k` (part (b));

each in the form of the corresponding field of `AlgebraicGeometry.IsCurve.Assertions`, with the
coefficient hypotheses specialised to `𝐅_n` as in the lemmas above. The maps in `C₆`, `C₇`,
`C₈` are the pullback maps `AlgebraicGeometry.Etale.cohomologyMap` (part (c)).

Only the assertions are stated here; the explicit groups of part (a) are the curve estimates
`AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_zero_constantZMod`,
`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_one` and
`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_two`, and their invariance
under algebraically closed extension is `AlgebraicGeometry.bijective_cohomologyMap_constantZMod`.
(blueprint: `thm-sc-main`) -/
theorem constantModSheaf_curveCalculations [IsCurve f] [Smooth f] [ConnectedSpace C] (n : ℕ)
    [Fact n.Prime] :
    let F := (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      (Etale.constantModSheaf Λ C n)
    (∀ q, 2 < q → Subsingleton (Sheaf.H F q)) ∧
    (IsAffine C → ∀ q, 1 < q → Subsingleton (Sheaf.H F q)) ∧
    (CharP k n → ∀ q, 1 < q → Subsingleton (Sheaf.H F q)) ∧
    ((n : k) ≠ 0 → Finite (Λ ⧸ (Ideal.span {(n : Λ)} : Ideal Λ)) →
      ∀ q, Finite (Sheaf.H F q)) ∧
    (IsProper f → Finite (Λ ⧸ (Ideal.span {(n : Λ)} : Ideal Λ)) →
      ∀ q, Finite (Sheaf.H F q)) ∧
    ((n : k) ≠ 0 → ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] {C' : Scheme.{u}}
      {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C},
      IsPullback ι' f' f ι → ∀ q, Function.Bijective (Etale.cohomologyMap ι' F q)) ∧
    (IsProper f → ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] {C' : Scheme.{u}}
      {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C},
      IsPullback ι' f' f ι → ∀ q, Function.Bijective (Etale.cohomologyMap ι' F q)) ∧
    (∀ {W : Scheme.{u}} (a : W ⟶ C) [IsOpenImmersion a],
      Function.Surjective (Etale.cohomologyMap a F 2)) :=
  by
    dsimp
    exact ⟨subsingleton_sheafH_constantModSheaf_of_two_lt Λ f n,
    fun _ ↦ subsingleton_sheafH_constantModSheaf_of_one_lt_of_isAffine Λ f n,
    fun _ ↦ subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP Λ f n,
    fun hn _ ↦ finite_sheafH_constantModSheaf_of_ne_zero Λ f n hn,
    fun _ _ ↦ finite_sheafH_constantModSheaf_of_isProper Λ f n,
    fun hn k' _ _ _ _ _ _ h ↦ bijective_cohomologyMap_constantModSheaf_of_ne_zero Λ f n hn k' h,
    fun _ k' _ _ _ _ _ _ h ↦ bijective_cohomologyMap_constantModSheaf_of_isProper Λ f n k' h,
    fun a _ ↦ surjective_cohomologyMap_constantModSheaf_two Λ f n a⟩

/-! ### The eight assertions on smooth curves -/

/-- **The eight assertions for `𝐅_ℓ`, `ℓ ≠ char k`, on a smooth curve.** Let `k` be
algebraically closed, `C` a smooth separated `k`-scheme of finite type of dimension at most
one (not necessarily connected) and `ℓ` a prime different from `char k`. Then the constant sheaf
`𝐅_ℓ` (read over `Λ` as `Λ/ℓΛ`, assumed finite) satisfies all eight assertions
`AlgebraicGeometry.IsCurve.Assertions`; their maps are the pullback maps
`AlgebraicGeometry.Etale.cohomologyMap`. The proof goes through the Kummer sequence, the
compactification of `C` and purity for the boundary points.
(blueprint: `lemma-weil-pbc-smooth-curve-kummer-localization`) -/
theorem assertions_constantModSheaf_of_ne_zero [IsCurve f] [Smooth f] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : k) ≠ 0) [Finite (Λ ⧸ (Ideal.span {(ℓ : Λ)} : Ideal Λ))] :
    IsCurve.Assertions Λ f (Etale.constantModSheaf Λ C ℓ) :=
  sorry

/-- **The eight assertions for `𝐅_p`, `p = char k`, on a smooth curve.** Let `k` be
algebraically closed of characteristic `p > 0` and `C` a smooth separated `k`-scheme of finite
type of dimension at most one (not necessarily connected). Then the constant sheaf `𝐅_p` (read
over `Λ` as `Λ/pΛ`, assumed finite) satisfies all eight assertions
`AlgebraicGeometry.IsCurve.Assertions`
(`C₄` and `C₆` hold since their torsion hypothesis forces the sheaf to vanish). The proof goes
through the Artin–Schreier sequence `0 → 𝐅_p → 𝒪_C → 𝒪_C → 0`; for proper `C` the invariance
`C₇` comes from that of the kernel of `F - 1` on `H¹(C, 𝒪_C)` (this description of the map is
not stated).
(blueprint: `lemma-weil-pbc-smooth-curve-artin-schreier`) -/
theorem assertions_constantModSheaf_of_charP [IsCurve f] [Smooth f] (p : ℕ) [Fact p.Prime]
    [CharP k p] [Finite (Λ ⧸ (Ideal.span {(p : Λ)} : Ideal Λ))] :
    IsCurve.Assertions Λ f (Etale.constantModSheaf Λ C p) :=
  sorry

end IsCurve

end AlgebraicGeometry
