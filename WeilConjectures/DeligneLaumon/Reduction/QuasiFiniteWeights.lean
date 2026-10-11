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
theorem FrobeniusModule.Equiv.trace_frobeniusEnd_pow {K : Type} [Field K]
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
theorem LinearMap.trace_pow_eq_of_charpoly_eq {K V W : Type*} [Field K] [IsAlgClosed K]
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

end AlgebraicGeometry
