/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.FormalSteps
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.Finiteness
public import WeilConjectures.WeilSheaf.GrothendieckLefschetz
public import WeilConjectures.WeilSheaf.StalkUpperStarCharpoly
public import WeilConjectures.ZetaLinearAlgebra.CharpolyRevExpand
public import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism

/-!
# Upper weight bounds for quasi-finite direct images

Let `f : X ⟶ Y` be a separated quasi-finite morphism of `k₀`-schemes and `F` a Weil sheaf on `X`
whose local Frobenius eigenvalues at every closed point `x` have absolute value at most
`q_x ^ (w / 2)`. Then so do those of `f₀!F` (blueprint: `lem-zl-quasi-finite`, part 3). At a
closed point `y` of `Y` of degree `d`, the Frobenius `F_y` on `(f₀!F)_ȳ` satisfies

`det (1 - T F_y ∣ (f₀!F)_ȳ) = ∏_{x ↦ y} det (1 - T^{e_x} F_x ∣ F_x̄)`, `e_x = [κ(x) : κ(y)]`:

both sides are determined by their traces of powers, which agree by the Grothendieck–Lefschetz
trace formula applied to the point `Spec κ(y)` and to the fibre `X_y = X ×_Y Spec κ(y)`, whose
compactly supported cohomologies in degree zero are identified by compact support base change
and composition. Hence every eigenvalue `β` of `F_y` has a power `β^{e_x}` which is an eigenvalue
of some `F_x`, and `|ι β|^{e_x} ≤ q_x ^ (w / 2) = q_y ^ (e_x w / 2)`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite`: blueprint
  `lem-zl-quasi-finite`, part 3.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section QuasiFiniteCohomology

variable {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (T ↘ Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))] [LocallyQuasiFinite (T ↘ Spec (CommRingCat.of k₀))]

/-- The compactly supported cohomology of a Weil sheaf on a `k₀`-scheme quasi-finite over `k₀`
is concentrated in degree zero. -/
theorem WeilSheaf.subsingleton_compactlySupportedCohomology_of_locallyQuasiFinite
    (G : WeilSheaf k₀ l T) {i : ℤ} (hi : i ≠ 0) :
    Subsingleton (G.compactlySupportedCohomology i).carrier := by
  refine WeilSheaf.subsingleton_globalSections_of_isZero ?_
  rcases lt_or_gt_of_ne hi with h | h
  · exact WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg G h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = n := ⟨i.toNat, (Int.toNat_of_nonneg h.le).symm⟩
    exact isZero_higherLowerShriek_of_quasiFinite (T ↘ Spec (CommRingCat.of k₀)) n
      (by exact_mod_cast h) G

/-- **The trace formula on a scheme quasi-finite over `k₀`**: the trace of `Fᵐ` on
`H_c^0(T ⊗ k̄, G)` is the sum over the closed points `x` of degree dividing `m` of
`deg x · tr (F_x^{m / deg x})`. -/
theorem WeilSheaf.trace_compactlySupportedCohomology_zero_of_locallyQuasiFinite
    (G : WeilSheaf k₀ l T) {m : ℕ} (hm : m ≠ 0) :
    LinearMap.trace (PadicAlgCl l) (G.compactlySupportedCohomology 0).carrier
        ((G.compactlySupportedCohomology 0).frobeniusEnd ^ m) =
      ∑ᶠ x : T.finitePoints, if (T ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ∣ m then
        ((T ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 : PadicAlgCl l) *
          LinearMap.trace (PadicAlgCl l) (G.stalk x).carrier ((G.stalk x).frobeniusEnd ^
            (m / (T ↘ Spec (CommRingCat.of k₀)).degreeOver x.1))
      else 0 := by
  rw [← WeilSheaf.sum_trace_compactlySupportedCohomology G hm, finsum_eq_single _ 0]
  · simp
  · intro i hi
    have := G.subsingleton_compactlySupportedCohomology_of_locallyQuasiFinite hi
    rw [Subsingleton.elim ((G.compactlySupportedCohomology i).frobeniusEnd ^ m) 0, map_zero,
      smul_zero]

end QuasiFiniteCohomology

section Helpers

/-- Equivalent Frobenius modules have the same traces of powers of the Frobenius. -/
theorem _root_.FrobeniusModule.Equiv.trace_frobeniusEnd_pow {K : Type} [Field K]
    {M N : FrobeniusModule.{u + 1, 0} K} (e : M.Equiv N) (m : ℕ) :
    LinearMap.trace K N.carrier (N.frobeniusEnd ^ m) =
      LinearMap.trace K M.carrier (M.frobeniusEnd ^ m) := by
  have hpow : ∀ n : ℕ, (e.toLinearEquiv.conj M.frobeniusEnd) ^ n =
      e.toLinearEquiv.conj (M.frobeniusEnd ^ n) := by
    intro n
    induction n with
    | zero => simp only [pow_zero, Module.End.one_eq_id, LinearEquiv.conj_id]
    | succ n ih => rw [pow_succ, pow_succ, ih, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        LinearEquiv.conj_comp]
  rw [e.frobeniusEnd_eq_conj, hpow, LinearMap.trace_conj']

/-- Over an algebraically closed field, endomorphisms with the same characteristic polynomial
have the same traces of powers. -/
theorem _root_.LinearMap.trace_pow_eq_of_charpoly_eq {K V W : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {A : Module.End K V} {B : Module.End K W}
    (h : A.charpoly = B.charpoly) (m : ℕ) :
    LinearMap.trace K V (A ^ m) = LinearMap.trace K W (B ^ m) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace K (Module.finBasis K V),
    LinearMap.trace_eq_matrix_trace K (Module.finBasis K W), ← LinearMap.toMatrix_pow,
    ← LinearMap.toMatrix_pow, Matrix.trace_pow_eq_sum_pow_roots_charpoly,
    Matrix.trace_pow_eq_sum_pow_roots_charpoly, LinearMap.charpoly_toMatrix,
    LinearMap.charpoly_toMatrix, h]

/-- The trace bookkeeping behind the Frobenius at a point of a quasi-finite direct image: if the
traces of the powers of `H₁ ≃ H₂` are `d tr (A^{m / d})` (for `d ∣ m`) on the one hand and
`∑ₓ dₓ tr (Bₓ^{m / dₓ})` (for `dₓ ∣ m`) on the other, with `dₓ = d eₓ`, then
`tr (Aⁿ) = ∑_{eₓ ∣ n} eₓ tr (Bₓ^{n / eₓ})`. -/
theorem _root_.FrobeniusModule.trace_pow_eq_sum_of_equiv {K : Type} [Field K] [CharZero K]
    {H₁ H₂ A : FrobeniusModule.{u + 1, 0} K} (E : H₁.Equiv H₂) {ι : Type*} [Fintype ι]
    (B : ι → FrobeniusModule.{u + 1, 0} K) {d : ℕ} (hd : d ≠ 0) (e : ι → ℕ)
    (h₁ : ∀ m : ℕ, m ≠ 0 → LinearMap.trace K H₁.carrier (H₁.frobeniusEnd ^ m) =
      if d ∣ m then (d : K) * LinearMap.trace K A.carrier (A.frobeniusEnd ^ (m / d)) else 0)
    (h₂ : ∀ m : ℕ, m ≠ 0 → LinearMap.trace K H₂.carrier (H₂.frobeniusEnd ^ m) =
      ∑ x, if d * e x ∣ m then ((d * e x : ℕ) : K) *
        LinearMap.trace K (B x).carrier ((B x).frobeniusEnd ^ (m / (d * e x))) else 0)
    (n : ℕ) (hn : n ≠ 0) :
    LinearMap.trace K A.carrier (A.frobeniusEnd ^ n) =
      ∑ x, if e x ∣ n then (e x : K) *
        LinearMap.trace K (B x).carrier ((B x).frobeniusEnd ^ (n / e x)) else 0 := by
  have hdn : d * n ≠ 0 := mul_ne_zero hd hn
  have h := E.trace_frobeniusEnd_pow (d * n)
  rw [h₁ _ hdn, h₂ _ hdn, if_pos (dvd_mul_right d n),
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd)] at h
  have hdK : (d : K) ≠ 0 := Nat.cast_ne_zero.2 hd
  refine mul_left_cancel₀ hdK (h.symm.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Nat.mul_div_mul_left _ _ (Nat.pos_of_ne_zero hd)]
  simp only [Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd)]
  split_ifs <;> push_cast <;> ring

end Helpers

section ConcentratedInDegreeZero

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- A Weil complex whose cohomology sheaves vanish outside degree zero is its cohomology sheaf in
degree zero, placed in degree zero. -/
theorem WeilComplex.nonempty_iso_toComplex_homologySheaf_zero (K : WeilComplex k₀ l X)
    (h : ∀ b : ℤ, b ≠ 0 → IsZero ((WeilComplex.homologySheaf b).obj K)) :
    Nonempty (K ≅ WeilSheaf.toComplex.obj ((WeilComplex.homologySheaf 0).obj K)) := by
  have : K.obj.IsGE 0 := (_root_.DerivedCategory.isGE_iff _ 0).2 fun i hi ↦
    (WeilComplex.isZero_homologySheaf_obj_iff i K).1 (h i hi.ne)
  have : K.obj.IsLE 0 := (_root_.DerivedCategory.isLE_iff _ 0).2 fun i hi ↦
    (WeilComplex.isZero_homologySheaf_obj_iff i K).1 (h i hi.ne')
  obtain ⟨Y, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K.obj 0
  let eY : (_root_.DerivedCategory.homologyFunctor _ 0).obj K.obj ≅ Y :=
    (_root_.DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
      (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app Y
  let G' : WeilSheaf k₀ l X := ⟨Y, (WeilSheaf.objectProperty k₀ l X).prop_of_iso eY (K.2.2 0)⟩
  let e' : K ≅ WeilSheaf.toComplex.obj G' := ObjectProperty.isoMk _ e
  exact ⟨e' ≪≫ WeilSheaf.toComplex.mapIso
    ((WeilSheaf.toComplexCompHomologySheafIso.app G').symm ≪≫
      (WeilComplex.homologySheaf 0).mapIso e'.symm)⟩

end ConcentratedInDegreeZero

section Fibre

/-- The direct image with compact support only depends on the morphism, not on the instance
arguments through which it is formed. -/
noncomputable def WeilComplex.derivedLowerShriekCongr {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] {f f' : X ⟶ Y}
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f']
    [LocallyOfFiniteType f'] [QuasiCompact f'] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (h : f = f') :
    WeilComplex.derivedLowerShriek k₀ l f ≅ WeilComplex.derivedLowerShriek k₀ l f' := by
  subst h
  exact Iso.refl _

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [X'.Over (Spec (CommRingCat.of k₀))] [Y'.Over (Spec (CommRingCat.of k₀))]
  {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyQuasiFinite f]
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  {f' : X' ⟶ Y'} [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f'] [LocallyOfFiniteType f']
  [QuasiCompact f'] [IsSeparated (Y' ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X' ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X' ↘ Spec (CommRingCat.of k₀))]
  {g : X' ⟶ X} [g.IsOver (Spec (CommRingCat.of k₀))] {h : Y' ⟶ Y}
  [h.IsOver (Spec (CommRingCat.of k₀))]

/-- **Compact support base change in degree zero for a quasi-finite morphism.** For a cartesian
square `X' = X ×_Y Y'` of `k₀`-schemes with `f : X ⟶ Y` separated and quasi-finite, the
compactly supported cohomology in degree zero of the restriction `h^*(f₀!F)` of the direct image
of a Weil sheaf `F` is that of the restriction `g^*F`: `Rf₀!F = f₀!F` is concentrated in degree
zero, `h^* Rf₀! ≅ Rf'₀! g^*`, and `R(f' ≫ a_{Y'})₀! ≅ R(a_{Y'})₀! ∘ Rf'₀!`. -/
theorem WeilSheaf.nonempty_equiv_compactlySupportedCohomology_upperStar_higherLowerShriek
    (hH : IsPullback g f' f h) (F : WeilSheaf k₀ l X) :
    Nonempty ((((WeilSheaf.upperStar h).obj ((WeilSheaf.higherLowerShriek k₀ l f 0).obj
      F)).compactlySupportedCohomology 0).Equiv
        (((WeilSheaf.upperStar g).obj F).compactlySupportedCohomology 0)) := by
  -- `Rf₀!F` is `f₀!F` placed in degree zero
  obtain ⟨e₂⟩ := WeilComplex.nonempty_iso_toComplex_homologySheaf_zero
    ((WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj F)) fun b hb ↦ by
      rcases lt_or_gt_of_ne hb with hb | hb
      · exact WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg F hb
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = n := ⟨b.toNat, (Int.toNat_of_nonneg hb.le).symm⟩
        exact isZero_higherLowerShriek_of_quasiFinite f n (by exact_mod_cast hb) F
  obtain ⟨e₃⟩ := WeilComplex.nonempty_upperStar_derivedLowerShriek_iso (k₀ := k₀) (l := l) hH
  obtain ⟨e₅⟩ := WeilComplex.nonempty_derivedLowerShriekCompIso (k₀ := k₀) (l := l) f'
    (Y' ↘ Spec (CommRingCat.of k₀))
  -- the identification of the complexes on `Y'`
  let E : WeilSheaf.toComplex.obj ((WeilSheaf.upperStar h).obj
      ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F)) ≅
      (WeilComplex.derivedLowerShriek k₀ l f').obj
        (WeilSheaf.toComplex.obj ((WeilSheaf.upperStar g).obj F)) :=
    (WeilComplex.upperStarToComplexIso h _).symm ≪≫
      (WeilComplex.upperStar h).mapIso e₂.symm ≪≫ e₃.app _ ≪≫
      (WeilComplex.derivedLowerShriek k₀ l f').mapIso (WeilComplex.upperStarToComplexIso g F)
  let E' := (WeilComplex.derivedLowerShriek k₀ l (Y' ↘ Spec (CommRingCat.of k₀))).mapIso E ≪≫
    (e₅.app _).symm ≪≫ (WeilComplex.derivedLowerShriekCongr (comp_over f' _)).app _
  exact ⟨WeilSheaf.globalSectionsEquivOfIso ((WeilComplex.homologySheaf 0).mapIso E')⟩

end Fibre

section Main

variable {ι : PadicAlgCl l →+* ℂ} {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- For a separated quasi-finite morphism `f : X ⟶ Y` of `k₀`-schemes the exact functor `f₀!`
preserves punctual upper weight bounds (blueprint: `sk-l-dl-general-quasifinite`,
`lem-zl-quasi-finite`, part 3): at a closed point `y` the Frobenius permutes the points above
`y`; on an orbit of length `e` an eigenvalue `α` upstairs contributes eigenvalues `β` with
`βᵉ = α` downstairs, whose normalized weights agree because `q_x = q_yᵉ`. -/
theorem WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite {w : ℝ}
    {F : WeilSheaf k₀ l X} (h : F.HasWeightsAtMost ι w) :
    ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).HasWeightsAtMost ι w := by
  intro y β hβ
  -- the closed point `y`, as the spectrum of its residue field, a finite extension of `k₀`
  let Z : Scheme.{u} := Spec (Y.residueField y.1)
  let i : Z ⟶ Y := Y.fromSpecResidueField y.1
  let : Z.Over (Spec (CommRingCat.of k₀)) := ⟨i ≫ Y ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : Finite (Y.residueField y.1) := y.2
  have : IsFinite (Z ↘ Spec (CommRingCat.of k₀)) := by
    change IsFinite (i ≫ Y ↘ Spec (CommRingCat.of k₀))
    rw [← Scheme.Hom.specMap_residueFieldAlgebraMap, IsFinite.SpecMap_iff]
    let := ((Y ↘ Spec (CommRingCat.of k₀)).residueFieldAlgebraMap y.1).toAlgebra
    exact Module.Finite.of_finite
  -- the fibre `X_y = X ×_Y Spec κ(y)`
  obtain ⟨Xy, g, f', hH⟩ : ∃ (Xy : Scheme.{u}) (g : Xy ⟶ X) (f' : Xy ⟶ Z), IsPullback g f' f i :=
    ⟨_, _, _, IsPullback.of_hasPullback f i⟩
  let : Xy.Over (Spec (CommRingCat.of k₀)) := ⟨g ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : g.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : f'.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change f' ≫ i ≫ Y ↘ Spec (CommRingCat.of k₀) = g ≫ X ↘ Spec (CommRingCat.of k₀)
    rw [← Category.assoc, ← hH.w, Category.assoc, comp_over]⟩
  have : IsSeparated f' := MorphismProperty.of_isPullback hH ‹_›
  have : LocallyQuasiFinite f' := MorphismProperty.of_isPullback hH ‹_›
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hH ‹_›
  have : QuasiCompact f' := MorphismProperty.of_isPullback hH ‹_›
  have : IsPreimmersion g :=
    MorphismProperty.of_isPullback hH.flip (inferInstance : IsPreimmersion i)
  have hX' : Xy ↘ Spec (CommRingCat.of k₀) = f' ≫ Z ↘ Spec (CommRingCat.of k₀) :=
    (comp_over f' _).symm
  have : IsSeparated (Xy ↘ Spec (CommRingCat.of k₀)) := by rw [hX']; infer_instance
  have : LocallyOfFiniteType (Xy ↘ Spec (CommRingCat.of k₀)) := by rw [hX']; infer_instance
  have : QuasiCompact (Xy ↘ Spec (CommRingCat.of k₀)) := by rw [hX']; infer_instance
  have : LocallyQuasiFinite (Xy ↘ Spec (CommRingCat.of k₀)) := by rw [hX']; infer_instance
  obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_upperStar_higherLowerShriek
    hH F
  -- the degree `d` of `y` and the unique point `z₀` of `Z`
  set d := (Y ↘ Spec (CommRingCat.of k₀)).degreeOver y.1 with hd_def
  have hd : d ≠ 0 := Scheme.Hom.degreeOver_ne_zero _ y.2
  let z₀ : Z := IsLocalRing.closedPoint (Y.residueField y.1)
  have hiz : ∀ z : Z, i.base z = y.1 := fun z ↦ Scheme.fromSpecResidueField_apply _ _
  have : ∀ z : Z, IsIso (i.residueFieldMap z) := fun z ↦ Scheme.Hom.isIso_residueFieldMap i z
  have hz₀ : z₀ ∈ Z.finitePoints :=
    (Scheme.Hom.mem_finitePoints_iff_of_isIso i z₀).1 ((hiz z₀).symm ▸ y.2)
  have hdegZ : ∀ z : Z, (Z ↘ Spec (CommRingCat.of k₀)).degreeOver z = d := fun z ↦ by
    change (i ≫ Y ↘ Spec (CommRingCat.of k₀)).degreeOver z = d
    rw [Scheme.Hom.degreeOver_comp_of_isIso, hiz]
  -- the traces of the powers of the Frobenius on `H_c^0` of the point
  have hy : (⟨i.base z₀, Scheme.Hom.map_mem_finitePoints i hz₀⟩ : Y.finitePoints) = y :=
    Subtype.ext (hiz z₀)
  have hstalkZ : ∀ k : ℕ, LinearMap.trace (PadicAlgCl l)
      (((WeilSheaf.upperStar i).obj ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F)).stalk ⟨z₀, hz₀⟩).carrier
        ((((WeilSheaf.upperStar i).obj ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F)).stalk ⟨z₀, hz₀⟩).frobeniusEnd ^ k) =
      LinearMap.trace (PadicAlgCl l) (((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).stalk y).carrier ((((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).stalk y).frobeniusEnd ^ k) := by
    intro k
    have hc := WeilSheaf.charpoly_frobeniusEnd_stalk_upperStar i ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F) ⟨z₀, hz₀⟩
    rw [hy, hdegZ, hiz, ← hd_def, Nat.div_self (Nat.pos_of_ne_zero hd), pow_one] at hc
    exact LinearMap.trace_pow_eq_of_charpoly_eq hc k
  have hZtr : ∀ m : ℕ, m ≠ 0 → LinearMap.trace (PadicAlgCl l)
      (((WeilSheaf.upperStar i).obj ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F)).compactlySupportedCohomology 0).carrier
        ((((WeilSheaf.upperStar i).obj ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F)).compactlySupportedCohomology 0).frobeniusEnd ^ m) =
      if d ∣ m then (d : PadicAlgCl l) *
        LinearMap.trace (PadicAlgCl l) (((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).stalk y).carrier ((((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).stalk y).frobeniusEnd ^ (m / d))
      else 0 := by
    intro m hm
    rw [WeilSheaf.trace_compactlySupportedCohomology_zero_of_locallyQuasiFinite _ hm,
      finsum_eq_single _ ⟨z₀, hz₀⟩ fun x hx ↦ absurd (Subtype.ext (Subsingleton.elim _ _)) hx,
      hdegZ, hstalkZ]
  -- the points of the fibre: their degrees and stalks
  have : ∀ x : Xy, IsIso (g.residueFieldMap x) := fun x ↦ Scheme.Hom.isIso_residueFieldMap g x
  have hdegX : ∀ x : Xy, (Xy ↘ Spec (CommRingCat.of k₀)).degreeOver x =
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver (g.base x) := fun x ↦
    Scheme.Hom.degreeOver_comp_of_isIso g (X ↘ Spec (CommRingCat.of k₀)) x
  have hdvd : ∀ x : Xy.finitePoints, d ∣ (Xy ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 :=
    fun x ↦ by
      have := Scheme.Hom.degreeOver_dvd_degreeOver_comp f' (Z ↘ Spec (CommRingCat.of k₀)) x.2
      rwa [← hX', hdegZ] at this
  have hstalkX : ∀ (x : Xy.finitePoints) (k : ℕ), LinearMap.trace (PadicAlgCl l)
      (((WeilSheaf.upperStar g).obj F).stalk x).carrier
        ((((WeilSheaf.upperStar g).obj F).stalk x).frobeniusEnd ^ k) =
      LinearMap.trace (PadicAlgCl l)
        (F.stalk ⟨g.base x.1, Scheme.Hom.map_mem_finitePoints g x.2⟩).carrier
        ((F.stalk ⟨g.base x.1, Scheme.Hom.map_mem_finitePoints g x.2⟩).frobeniusEnd ^ k) := by
    intro x k
    have hc := WeilSheaf.charpoly_frobeniusEnd_stalk_upperStar g F x
    rw [hdegX, Nat.div_self (Nat.pos_of_ne_zero (Scheme.Hom.degreeOver_ne_zero _
      (Scheme.Hom.map_mem_finitePoints g x.2))), pow_one] at hc
    exact LinearMap.trace_pow_eq_of_charpoly_eq hc k
  -- the fibre is finite
  have : Finite Xy := by
    have h1 := (Xy ↘ Spec (CommRingCat.of k₀)).finite_preimage_singleton
      (IsLocalRing.closedPoint k₀)
    have h2 : (Xy ↘ Spec (CommRingCat.of k₀)).base ⁻¹' {IsLocalRing.closedPoint k₀} =
        Set.univ := Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
    rw [h2] at h1
    exact Set.finite_univ_iff.1 h1
  let : Fintype Xy.finitePoints := Fintype.ofFinite _
  -- the traces of the powers of the Frobenius on the stalk of `f₀!F` at `y`
  set e : Xy.finitePoints → ℕ := fun x ↦ (Xy ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 / d
    with he_def
  have hde : ∀ x : Xy.finitePoints,
      (Xy ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 = d * e x := fun x ↦
    (Nat.mul_div_cancel' (hdvd x)).symm
  have he0 : ∀ x : Xy.finitePoints, e x ≠ 0 := fun x h0 ↦ by
    have := hde x
    rw [h0, mul_zero] at this
    exact Scheme.Hom.degreeOver_ne_zero _ x.2 this
  have hXtr : ∀ m : ℕ, m ≠ 0 → LinearMap.trace (PadicAlgCl l)
      (((WeilSheaf.upperStar g).obj F).compactlySupportedCohomology 0).carrier
        ((((WeilSheaf.upperStar g).obj F).compactlySupportedCohomology 0).frobeniusEnd ^ m) =
      ∑ x : Xy.finitePoints, if d * e x ∣ m then ((d * e x : ℕ) : PadicAlgCl l) *
        LinearMap.trace (PadicAlgCl l)
          (F.stalk ⟨g.base x.1, Scheme.Hom.map_mem_finitePoints g x.2⟩).carrier
          ((F.stalk ⟨g.base x.1, Scheme.Hom.map_mem_finitePoints g x.2⟩).frobeniusEnd ^
            (m / (d * e x))) else 0 := by
    intro m hm
    rw [WeilSheaf.trace_compactlySupportedCohomology_zero_of_locallyQuasiFinite _ hm,
      finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [hde x, hstalkX]
  have key := FrobeniusModule.trace_pow_eq_sum_of_equiv E
    (fun x : Xy.finitePoints ↦ F.stalk ⟨g.base x.1, Scheme.Hom.map_mem_finitePoints g x.2⟩) hd e
    hZtr hXtr
  -- the local Frobenius at `y` is the product of the induced Frobenius of the points above `y`
  have hA := LinearMap.charpolyRev_eq_prod_expand_of_trace_pow_eq
    (((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).stalk y).frobeniusEnd Finset.univ
    (fun x : Xy.finitePoints ↦
      (F.stalk ⟨g.base x.1, Scheme.Hom.map_mem_finitePoints g x.2⟩).frobeniusEnd) e he0 key
  have hβ0 : β ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hβ.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, zero_smul] at hv
    exact hv.2 ((((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).stalk y).frobenius.injective
      (hv.1.trans (map_zero _).symm))
  obtain ⟨x, -, hx⟩ := LinearMap.exists_hasEigenvalue_pow_of_charpolyRev_eq _ _ _ e hA hβ hβ0
  have hw := h ⟨g.base x.1, Scheme.Hom.map_mem_finitePoints g x.2⟩ (β ^ e x) hx
  -- the weight bound: `|ι β| ^ e ≤ (q ^ (d e)) ^ (w / 2)`
  have hq : (0 : ℝ) ≤ Nat.card k₀ := Nat.cast_nonneg _
  have hxdeg : (X ↘ Spec (CommRingCat.of k₀)).degreeOver (g.base x.1) = d * e x := by
    rw [← hdegX, hde]
  simp only [Scheme.Hom.residueCard, hxdeg, Nat.cast_pow, map_pow, norm_pow] at hw
  change ‖ι β‖ ≤ ((Nat.card k₀ ^ d : ℕ) : ℝ) ^ (w / 2)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
    (he0 x)).1 ?_
  rw [Nat.cast_pow, ← Real.rpow_pow_comm (by positivity), ← pow_mul]
  rwa [← Real.rpow_pow_comm (by positivity)] at hw

end Main

end AlgebraicGeometry
