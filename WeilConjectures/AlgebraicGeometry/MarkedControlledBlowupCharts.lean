/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.Blowup.Gluing

public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateFlag
public import WeilConjectures.AlgebraicGeometry.ControlledTransformIdeal
public import WeilConjectures.AlgebraicGeometry.MarkedIdealOrder
public import WeilConjectures.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Blowup.FlatBaseChange
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Blowup.Affine.StrictTransformChart
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Ideal.Colon

import Mathlib.RingTheory.Flat.Basic

/-! # Smooth marked blowups and their controlled coordinate transforms

Source: Stacks Project, Tags 0804, 0FUE and 0FUT, and the simultaneous-coordinate
calculation (blueprint: lem-trf-marked-controlled-blowup-charts).
The controlled ideal is constructed as an ideal quotient; the support is the existing
scheme-theoretic strict transform, identified with the intrinsic blowup.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Controlled transforms for a smooth closed flag, including empty and deleted components.
The ordered transformed boundary is named by its defining equality `hE'`; unit-ideal
entries record absent old labels. The controlled ideal is on the canonically isomorphic
intrinsic blowup of `N`.
Source: Stacks Project, Tags 0804, 0FUE, 0FUT
(blueprint: lem-trf-marked-controlled-blowup-charts).

Proof:
1. Finite type over Q gives Noetherian schemes; smoothness gives normal local domains.
   Their irreducible components are disjoint open and closed. On a component contained
   in the center, the order hypothesis at its field-valued generic stalk forces J = 0.
2. For I = I(C,N), the regular-immersion theorem for smooth pairs and the associated
   graded polynomial theorem identify I^d/I^(d+1) with a free O_C-module. Induct on
   d < c. A section of J in I^d has zero graded class at the generic point of C, by
   the order hypothesis. A free module over the local domain O_C injects into its
   fraction-field localization, so that class is zero. Outside C the inclusion is
   automatic. Thus J is contained in I^c, also when I is zero.
3. The ambient-closed strict-transform theorem gives Bl_C N isomorphic to N'. The
   blowup complement theorem identifies the unchanged opens. The zero-ideal Rees
   algebra has no positive degrees, so every component contained in C disappears,
   on both N and Z; the unit-ideal blowup is the identity for an empty center.
4. Use the simultaneous étale flag coordinates. A center-coordinate chart has the
   equations a = e(a/e). The regular-sequence blowup presentation eliminates a,
   leaving e, the other ratios, and unchanged coordinates. Flat base change carries
   these polynomial charts to the actual étale neighbourhoods.
5. In a tangent-coordinate chart N' has equations z_l/e = 0. Normal-coordinate charts
   contain no N'. Hence N' and Z' are smooth by étale descent. Blowups of finite-type
   ideals on these Noetherian schemes are proper, so finite type, and composition
   proves the asserted finite type over Q.
6. The strict transform of the denominator hyperplane is absent. Other center
   hyperplanes have equations a/e, and the remaining ones keep their equations.
   Append e = 0. These independent coordinate hyperplanes are SNC and independent
   of the normal ratios defining N'. Descend the regular-intersection criterion.
7. The inclusion J <= I^c permits unique division of each pulled-back generator by
   e^c, since e is a nonzerodivisor. On overlaps e' = h e with h a unit changes the
   divided generators by h^(-c), so the ideals glue. The ideal quotient construction
   is this glued ideal. It is quasi-coherent and finite type, hence coherent on the
   locally Noetherian smooth support. Its affine sections are exactly the colons.
8. Every surviving component of Bl_C N is integral, has a dense unchanged open,
   and has the original function field. At its generic point e is invertible, so
   division preserves nonvanishing of J. No exceptional-only component is added.
9. Over the complement the exceptional ideal is the unit ideal. The support,
   controlled ideal, and each labelled old boundary are therefore unchanged.
The remaining coordinate, monomial and smooth-base-change clauses are stated below.
-/
theorem smooth_marked_controlled_blowup
    {Z N : Scheme.{u}} (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (j : N ⟶ Z)
    [IsClosedImmersion j] [Smooth p] [Smooth (j ≫ p)]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (I J : N.IdealSheafData) [Smooth (I.subschemeι ≫ j ≫ p)]
    (hJ : Scheme.Modules.IsQuasiCoherentFiniteType J.toModules)
    (c : ℕ) (hc : 1 ≤ c) (E : List Z.IdealSheafData)
    (hE : IsStrictNormalCrossingsBoundary E.prod)
    (hflag : HasEtaleCoordinateFlag p j.ker (I.map j) E)
    (horder : ∀ x : N, x ∈ I.support →
      HilbertSamuel.stalkIdeal J x ≤ IsLocalRing.maximalIdeal (N.presheaf.stalk x) ^ c)
    (E' : List (I.map j).blowup.IdealSheafData)
    (hE' : E' = E.map (fun D ↦
      (strictTransformMap D.subschemeι (I.map j).blowupMap (I.map j).support.compl).ker) ++
        [(I.map j).comap (I.map j).blowupMap]) :
    J ≤ I ^ c ∧
    Smooth ((I.map j).blowupMap ≫ p) ∧
    LocallyOfFiniteType ((I.map j).blowupMap ≫ p) ∧
    QuasiCompact ((I.map j).blowupMap ≫ p) ∧
    Smooth (strictTransformToSource j (I.map j).blowupMap (I.map j).support.compl ≫ j ≫ p) ∧
    LocallyOfFiniteType
      (strictTransformToSource j (I.map j).blowupMap (I.map j).support.compl ≫ j ≫ p) ∧
    QuasiCompact
      (strictTransformToSource j (I.map j).blowupMap (I.map j).support.compl ≫ j ≫ p) ∧
    (∃! e : I.blowup ≅ (I.map j).strictTransform j,
      e.hom ≫ strictTransformToSource j (I.map j).blowupMap (I.map j).support.compl =
        I.blowupMap) ∧
    IsStrictNormalCrossingsBoundary E'.prod ∧
    HasEtaleCoordinateFlag ((I.map j).blowupMap ≫ p)
      (strictTransformMap j (I.map j).blowupMap (I.map j).support.compl).ker ⊤ E' ∧
    (I.comap I.blowupMap).IsInvertible ∧
    Scheme.Modules.IsQuasiCoherentFiniteType
      (controlledTransformIdeal I.blowupMap I J c).toModules ∧
    (∀ K : I.blowup.IdealSheafData,
      K * (I.comap I.blowupMap) ^ c = J.comap I.blowupMap ↔
        K = controlledTransformIdeal I.blowupMap I J c) ∧
    (∀ (U : I.blowup.affineOpens) (e : Γ(I.blowup, U.1)),
      (I.comap I.blowupMap).ideal U = Ideal.span {e} →
      (controlledTransformIdeal I.blowupMap I J c).ideal U =
        Submodule.colon ((J.comap I.blowupMap).ideal U) {e ^ c}) ∧
    (∀ D ∈ irreducibleComponents N, D ⊆ (I.support : Set N) →
      I.blowupMap ⁻¹' D = ∅) ∧
    (∀ D ∈ irreducibleComponents Z, D ⊆ ((I.map j).support : Set Z) →
      (I.map j).blowupMap ⁻¹' D = ∅) ∧
    ((∀ D ∈ irreducibleComponents N, ∀ η : N, IsGenericPoint η D →
        HilbertSamuel.stalkIdeal J η ≠ ⊥) →
      ∀ D ∈ irreducibleComponents I.blowup, ∀ η : I.blowup, IsGenericPoint η D →
        HilbertSamuel.stalkIdeal (controlledTransformIdeal I.blowupMap I J c) η ≠ ⊥) ∧
    IsIso (I.blowupMap ∣_ I.support.compl) ∧
    (controlledTransformIdeal I.blowupMap I J c).comap
        (I.blowupMap ⁻¹ᵁ I.support.compl).ι =
      (J.comap I.blowupMap).comap (I.blowupMap ⁻¹ᵁ I.support.compl).ι ∧
    E'.map (fun D ↦ D.comap
        ((I.map j).blowupMap ⁻¹ᵁ (I.map j).support.compl).ι) =
      E.map (fun D ↦ D.comap
        (((I.map j).blowupMap ⁻¹ᵁ (I.map j).support.compl).ι ≫ (I.map j).blowupMap)) ++
          [⊤] := by
  sorry

/-- The intrinsic controlled ideal, the scheme-theoretic support identification, and the
ordered boundary commute with every smooth base change, including non-surjective ones.
Source: Stacks Project, Tags 0805, 080E, and the calculation of Tag 0804
(blueprint: lem-trf-marked-controlled-blowup-charts).

Proof:
10. A smooth morphism is flat. Apply the flat blowup comparison to the ambient and to N.
    Flat pullback commutes with powers and preserves the inclusion J <= I^c and the
    injectivity of multiplication by e. Consequently dividing a pulled-back generator
    by e^c pulls back to dividing that same generator by the pulled-back e^c.
11. Strict-transform ideals are kernels of restriction to the unchanged open. This
    open is schematically dense in the strict transform. Flat pullback preserves that
    density, so the base-changed closure is the same scheme-theoretic strict transform.
    The intrinsic blowup identification agrees on the dense unchanged open, hence
    agrees everywhere. Each boundary label follows the same closure calculation;
    the exceptional ideal is the extended center ideal and therefore pulls back too.
    All local chart equations are equalities of functions, hence pull back identically.
    Empty schemes and deleted components require no additional choice or exception.
-/
theorem smooth_marked_controlled_blowup_baseChange
    {Z N Z₁ : Scheme.{u}} (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (j : N ⟶ Z)
    [IsClosedImmersion j] [Smooth p] [Smooth (j ≫ p)]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (I J : N.IdealSheafData) [Smooth (I.subschemeι ≫ j ≫ p)]
    (hJ : Scheme.Modules.IsQuasiCoherentFiniteType J.toModules)
    (c : ℕ) (hc : 1 ≤ c) (E : List Z.IdealSheafData)
    (hE : IsStrictNormalCrossingsBoundary E.prod)
    (hflag : HasEtaleCoordinateFlag p j.ker (I.map j) E)
    (horder : ∀ x : N, x ∈ I.support →
      HilbertSamuel.stalkIdeal J x ≤ IsLocalRing.maximalIdeal (N.presheaf.stalk x) ^ c)
    (g : Z₁ ⟶ Z) [Smooth g] :
    controlledTransformIdeal (I.comap (pullback.fst j g)).blowupMap
        (I.comap (pullback.fst j g)) (J.comap (pullback.fst j g)) c =
      (controlledTransformIdeal I.blowupMap I J c).comap
        ((I.blowupFlatBaseChangeIso (pullback.fst j g)).hom ≫
          pullback.fst I.blowupMap (pullback.fst j g)) ∧
    (∃ q : ((I.map j).comap g).strictTransform (pullback.snd j g) ⟶
        (I.map j).strictTransform j,
      IsPullback q
        (strictTransformMap (pullback.snd j g) ((I.map j).comap g).blowupMap
          ((I.map j).comap g).support.compl)
        (strictTransformMap j (I.map j).blowupMap (I.map j).support.compl)
        (((I.map j).blowupFlatBaseChangeIso g).hom ≫
          pullback.fst (I.map j).blowupMap g) ∧
      q ≫ strictTransformToSource j (I.map j).blowupMap (I.map j).support.compl =
        strictTransformToSource (pullback.snd j g) ((I.map j).comap g).blowupMap
          ((I.map j).comap g).support.compl ≫ pullback.fst j g) ∧
    (E.map (fun D ↦
        (strictTransformMap D.subschemeι (I.map j).blowupMap (I.map j).support.compl).ker) ++
      [(I.map j).comap (I.map j).blowupMap]).map
        (fun D ↦ D.comap (((I.map j).blowupFlatBaseChangeIso g).hom ≫
          pullback.fst (I.map j).blowupMap g)) =
      E.map (fun D ↦
        (strictTransformMap (D.comap g).subschemeι ((I.map j).comap g).blowupMap
          ((I.map j).comap g).support.compl).ker) ++
        [((I.map j).comap g).comap ((I.map j).comap g).blowupMap] := by
  sorry

/-- Actual affine blowup chart rings in étale coordinates. The chart coordinates are the
exceptional equation, ratios of the other center coordinates, and unchanged coordinates.
Saturation describes scheme-theoretic old strict transforms, including the missing
`i`-hyperplane; the colon gives the stated monomial controlled transform.
Source: Stacks Project, Tags 0804, 0FUE, 0FUT, and More on Algebra, Tag 0BIQ
(blueprint: lem-trf-marked-controlled-blowup-charts).

Proof:
4. In the polynomial model the coordinate center generators form a regular sequence.
   The regular-sequence chart presentation has relations u_j = u_i t_j. Eliminating
   the other center coordinates leaves a polynomial ring in e = u_i, the t_j, and
   unchanged coordinates. The finite generator charts cover the blowup. Flat base
   change transports the charts to any étale coordinate algebra R. Their maps to
   this polynomial chart remain étale. The denominator e is a nonzerodivisor.
5. For an ambient flag, restrict to N by setting its normal coordinates equal to zero.
   On a tangent-coordinate chart this sets the normal ratios equal to zero; on a
   normal-coordinate chart the ratio of that coordinate to itself is 1, so N' is
   empty. Thus the chart rings below are precisely the surviving support charts.
6. Saturating the old equation u_i by e gives the unit ideal. For another center
   coordinate u_j = e t_j saturation removes e and leaves t_j. For j outside the
   center it leaves u_j. Polynomial coordinate quotients have no e-torsion and
   this remains true after étale base change, proving the scheme-theoretic claims.
9. Substitute u_i = e and u_j = e t_j for the remaining center coordinates into
   the monomial. Its total exceptional power is sum_{j in A} a_j. Dividing by e^c
   leaves exponent sum a_j - c and exactly the other old exponents a_j. The assumed
   inequality prevents negative powers. The missing i-hyperplane has no old factor.
10. All displayed identities and their chart maps are obtained by ring operations
    and localization and hence are compatible with the smooth base changes above.
-/
theorem etale_coordinate_marked_blowup_charts
    {R : Type u} [CommRing R] [Algebra (ULift.{u} ℚ) R]
    (n : ℕ) (u : Fin n → R) (A : Finset (Fin n)) (I : Ideal R)
    (hI : Ideal.span (u '' (A : Set (Fin n))) = I)
    (het : (MvPolynomial.eval₂Hom (algebraMap (ULift.{u} ℚ) R) u).Etale) :
    (⨆ i : A, Proj.basicOpen (reesGrading I)
      (reesX I (u i) (hI ▸ Ideal.subset_span ⟨i, i.property, rfl⟩))) = ⊤ ∧
    ∀ i : A, ∃ v : Fin n → AffineBlowup.chartRing I (u i),
      v i = algebraMap R _ (u i) ∧
      (∀ j : Fin n, j ∈ A → j ≠ i →
        (v j : Localization.Away (u i)) = AffineBlowup.chartFraction (u i) 1 (u j)) ∧
      (∀ j : Fin n, j ∉ A → v j = algebraMap R _ (u j)) ∧
      (MvPolynomial.eval₂Hom
        (algebraMap (ULift.{u} ℚ) (AffineBlowup.chartRing I (u i))) v).Etale ∧
      (∀ j : Fin n, algebraMap R (AffineBlowup.chartRing I (u i)) (u j) =
        if j ∈ A ∧ j ≠ i then v i * v j else v j) ∧
      (∀ j : Fin n,
        Ideal.comap (algebraMap (AffineBlowup.chartRing I (u i))
            (Localization.Away (v i)))
          ((Ideal.span {algebraMap R (AffineBlowup.chartRing I (u i)) (u j)}).map
            (algebraMap (AffineBlowup.chartRing I (u i)) (Localization.Away (v i)))) =
          if j = i then ⊤ else Ideal.span {v j}) ∧
      ∀ (T : Finset (Fin n)) (a : Fin n → ℕ) (c : ℕ),
        A ⊆ T → 1 ≤ c → c ≤ ∑ j ∈ A, a j →
        Submodule.colon
          ((Ideal.span {∏ j ∈ T, u j ^ a j}).map
            (algebraMap R (AffineBlowup.chartRing I (u i)))) {v i ^ c} =
          Ideal.span {v i ^ ((∑ j ∈ A, a j) - c) * ∏ j ∈ T.erase i, v j ^ a j} := by
  sorry

private theorem map_colon_singleton_of_le_span
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (K : Ideal A) (e : A) (hK : K ≤ Ideal.span {e})
    (he : IsSMulRegular B (f e)) :
    (K.colon {e}).map f = (K.map f).colon {f e} := by
  have hfactor : Ideal.span {e} * K.colon {e} = K := by
    apply le_antisymm
    · rw [Ideal.span_singleton_mul_le_iff]
      intro x hx
      simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hx
    · intro x hx
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp (hK hx)
      refine Ideal.mem_span_singleton_mul.mpr ⟨y, ?_, hy.symm⟩
      simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm, hy] using hx
  have hmap : Ideal.span {f e} * (K.colon {e}).map f = K.map f := by
    simpa only [Ideal.map_mul, Ideal.map_span, Set.image_singleton] using
      congrArg (Ideal.map f) hfactor
  ext x
  rw [Submodule.mem_colon_singleton, smul_eq_mul, ← hmap,
    Ideal.mem_span_singleton_mul]
  constructor
  · intro hx
    exact ⟨x, hx, mul_comm _ _⟩
  · rintro ⟨y, hy, hxy⟩
    have : y = x := he (by simpa only [smul_eq_mul, mul_comm] using hxy)
    exact this ▸ hy

private theorem chart_exceptional_regular
    {R : Type u} [CommRing R] (I : Ideal R) (a : R) :
    IsSMulRegular (AffineBlowup.chartRing I a)
      (algebraMap R (AffineBlowup.chartRing I a) a) := by
  intro x y h
  apply Subtype.ext
  apply (IsLocalization.Away.algebraMap_isUnit a).isRegular.left
  exact congrArg (fun z : AffineBlowup.chartRing I a ↦ (z : Localization.Away a)) h

private theorem chart_center_principal
    {R : Type u} [CommRing R] (I : Ideal R) (a : R) (ha : a ∈ I) :
    I.map (algebraMap R (AffineBlowup.chartRing I a)) =
      Ideal.span {algebraMap R (AffineBlowup.chartRing I a) a} := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    let v : AffineBlowup.chartRing I a :=
      ⟨AffineBlowup.chartFraction a 1 x,
        AffineBlowup.chartFraction_mem_chartRing I (by simpa using hx)⟩
    refine Ideal.mem_span_singleton.mpr ⟨v, ?_⟩
    apply Subtype.ext
    change algebraMap R (Localization.Away a) x =
      algebraMap R (Localization.Away a) a * AffineBlowup.chartFraction a 1 x
    rw [← AffineBlowup.chartFraction_zero, ← AffineBlowup.chartFraction_zero,
      ← AffineBlowup.chartFraction_mul, AffineBlowup.chartFraction_eq_iff]
    exact ⟨0, by ring⟩
  · exact Ideal.span_le.mpr (by
      rintro _ rfl
      exact Ideal.mem_map_of_mem _ ha)

private theorem strict_chart_map_injective_of_flat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (I : Ideal R) (a : R) (ha : a ∈ I) :
    Function.Injective (AffineBlowup.strictChartMap S I a ha) := by
  let C := AffineBlowup.chartRing I a
  let m : C →ₗ[R] C := LinearMap.mul R C (algebraMap R C a)
  have hm : Function.Injective m := chart_exceptional_regular I a
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := S) m hm
  have ht (z : AffineBlowup.BaseChangeChart S I a) :
      m.lTensor S z = algebraMap R _ a * z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
      rw [LinearMap.lTensor_tmul]
      change s ⊗ₜ[R] ((algebraMap R C a) * x) = _
      rw [Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      simpa only [Algebra.smul_def] using
        (TensorProduct.smul_tmul (R := R) a s x).symm
    | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  have hreg : IsSMulRegular (AffineBlowup.BaseChangeChart S I a)
      (algebraMap R (AffineBlowup.BaseChangeChart S I a) a) := by
    intro x y h
    exact hinj (by simpa only [ht, smul_eq_mul] using h)
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  rw [AffineBlowup.ker_strictChartMap]
  apply le_antisymm
  · intro z hz
    obtain ⟨n, hn⟩ := Submodule.mem_powTorsion_iff.mp hz
    exact (hreg.pow n).right_eq_zero_of_smul hn
  · exact bot_le

/-- The chart formulas themselves commute with smooth coefficient change: the canonical
base-change chart map is bijective, ideal division commutes with its coefficient map,
and every ratio is sent to the ratio of the pulled-back coordinates.
Source: Stacks Project, Tags 0804 and 0805
(blueprint: lem-trf-marked-controlled-blowup-charts).

Proof (steps 4, 7, 9--11 of the node): Smooth coefficient change is flat, so it preserves
injectivity of multiplication by the exceptional equation on the original chart ring.
The kernel of the canonical base-change chart map is the exceptional-power torsion;
it therefore vanishes, and the map is surjective by its fraction presentation. The
total transform K is contained in (e^c), so K = (e^c)(K:e^c). Mapping this equality
and cancelling the new exceptional equation identifies the two colon ideals.
The canonical map sends each pure tensor 1 tensor
(x/e) to the fraction of the images. This proves compatibility of the coordinate and
monomial formulas, including the denominator and unchanged coordinates. -/
theorem marked_blowup_chart_smooth_baseChange
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (I J : Ideal R) (a : R) (ha : a ∈ I) (c : ℕ) (hc : 1 ≤ c) (hJ : J ≤ I ^ c) :
    Function.Bijective (AffineBlowup.strictChartMap S I a ha) ∧
    (Submodule.colon (J.map (algebraMap R (AffineBlowup.chartRing I a)))
        {(algebraMap R (AffineBlowup.chartRing I a) a) ^ c}).map
      ((AffineBlowup.strictChartMap S I a ha).toRingHom.comp
        (Algebra.TensorProduct.includeRight : AffineBlowup.chartRing I a →ₐ[R]
          AffineBlowup.BaseChangeChart S I a).toRingHom) =
      Submodule.colon
        ((J.map (algebraMap R S)).map
          (algebraMap S (AffineBlowup.chartRing (I.map (algebraMap R S)) (algebraMap R S a))))
        {(algebraMap S (AffineBlowup.chartRing (I.map (algebraMap R S)) (algebraMap R S a))
          (algebraMap R S a)) ^ c} ∧
    ∀ (x : R) (hx : AffineBlowup.chartFraction a 1 x ∈ AffineBlowup.chartRing I a),
      (AffineBlowup.strictChartMap S I a ha
          (Algebra.TensorProduct.includeRight
            (⟨AffineBlowup.chartFraction a 1 x, hx⟩ : AffineBlowup.chartRing I a)) :
            Localization.Away (algebraMap R S a)) =
        AffineBlowup.chartFraction (algebraMap R S a) 1 (algebraMap R S x) := by
  have hbij : Function.Bijective (AffineBlowup.strictChartMap S I a ha) :=
    ⟨strict_chart_map_injective_of_flat I a ha,
      AffineBlowup.strictChartMap_surjective S I ha⟩
  refine ⟨hbij, ?_, ?_⟩
  · let C := AffineBlowup.chartRing I a
    let D := AffineBlowup.chartRing (I.map (algebraMap R S)) (algebraMap R S a)
    let f : C →+* D := (AffineBlowup.strictChartMap S I a ha).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[R]
        AffineBlowup.BaseChangeChart S I a).toRingHom
    have hf (x : R) : f (algebraMap R C x) = algebraMap S D (algebraMap R S x) := by
      change AffineBlowup.strictChartMap S I a ha
        ((Algebra.TensorProduct.includeRight : C →ₐ[R]
          AffineBlowup.BaseChangeChart S I a) (algebraMap R C x)) = _
      rw [AlgHom.commutes,
        IsScalarTower.algebraMap_apply R S (AffineBlowup.BaseChangeChart S I a),
        AlgHom.commutes]
    have hcomp : f.comp (algebraMap R C) = (algebraMap S D).comp (algebraMap R S) :=
      RingHom.ext hf
    have hle : J.map (algebraMap R C) ≤ Ideal.span {(algebraMap R C a) ^ c} := by
      change J.map (algebraMap R (AffineBlowup.chartRing I a)) ≤ _
      exact (Ideal.map_mono (f := algebraMap R (AffineBlowup.chartRing I a)) hJ).trans_eq
        (by rw [Ideal.map_pow, chart_center_principal I a ha, Ideal.span_singleton_pow])
    have hcolon := map_colon_singleton_of_le_span f (J.map (algebraMap R C))
      ((algebraMap R C a) ^ c) hle (by
        rw [map_pow, hf]
        exact (IsSMulRegular.pow_iff hc).mpr
          (chart_exceptional_regular (I.map (algebraMap R S)) (algebraMap R S a)))
    simpa only [Ideal.map_map, hcomp, map_pow, hf] using hcolon
  · intro x hx
    simpa only [Algebra.TensorProduct.includeRight_apply, map_one, one_mul] using
      AffineBlowup.coe_strictChartMap_tmul S I ha 1 x hx

end AlgebraicGeometry
