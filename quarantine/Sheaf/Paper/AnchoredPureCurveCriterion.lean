/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Paper.AdicPunctualWeights
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.EtaleWeilFundamentalRepresentation
public import Sheaf.Paper.LocalFrobeniusTrace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.WeilIndSheafCategory
public import Sheaf.Paper.NormalizedClassicalWeilRealization
public import Sheaf.Paper.ConstantExtensionWeilHeartEquivalence
public import Sheaf.Paper.RealSheavesSetup
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Sheaf.Paper.ClassicalRealizedAnchorEigenvalue
import Sheaf.Paper.CommonStageWeilIterate
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Sheaf.AlgebraicGeometry.ClosedPointField
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Purity detected by curves through a fixed anchor

Source: blueprint latest, sec-deligne-laumon-general/sk-i-dl-general-real,
thm-zl-real-mixed-by-curves.proof.md, paragraphs 3--4
(blueprint: lem-zl-anchored-pure-curve-criterion).

The auxiliary bundles only package the curves and the local power condition in
this criterion. Spectra are computed directly on the recorded finite-stage local
operators; characteristic-polynomial roots retain zero eigenvalues and multiplicities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- Evaluate the recorded normalized realization, with the inherited prime-unit fact.
Source: blueprint interpretation by the same local operators
(blueprint: lem-zl-anchored-pure-curve-criterion). -/
def anchoredRealizedSheaf (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (R : @ZlClassicalRealization D l _ hl Ω _ _ _ X₀ _ _ _
      (⟨fun x ↦ @isUnit_of_invertible _ _ _
        (zlClassicalStalkInvertible D l hl X₀ x)⟩))
    (S : @ZlClassicalWeil D l _ Ω _ _ _ X₀ _ _ _ (⟨fun x ↦ @isUnit_of_invertible _ _ _
        (zlClassicalStalkInvertible D l hl X₀ x)⟩)) :
    sfCommonStageWeilSheaf D l hl X₀ Ω :=
  (@ZlClassicalRealization.weil D l _ hl Ω _ _ _ X₀ _ _ _
    (⟨fun x ↦ @isUnit_of_invertible _ _ _
        (zlClassicalStalkInvertible D l hl X₀ x)⟩) R).obj S

/-- A test is precisely a positive constant extension and a closed immersion of a
smooth geometrically connected affine curve into the constant-extension model.
Source: blueprint two-point curve argument
(blueprint: lem-zl-anchored-pure-curve-criterion). -/
structure AnchoredCurveTest (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) where
  m : ℕ
  positive : 1 ≤ m
  curve : Over (Spec (.of (D.extensionSubfield m positive)))
  [finiteType : LocallyOfFiniteType curve.hom]
  [quasiCompact : QuasiCompact curve.hom]
  smooth : Smooth curve.hom
  geometricallyConnected : GeometricallyConnected curve.hom
  affine : IsAffine curve.left
  dimension : curve.left.IsPureDimension 1
  immersion : curve ⟶ constantExtensionModel D m positive X₀
  closedImmersion : IsClosedImmersion immersion.left

attribute [instance] AnchoredCurveTest.finiteType AnchoredCurveTest.quasiCompact

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

/-- The actual composite C_m to X_(0,m) to X_0, used for residue degrees.
Source: blueprint curve and constant-extension projections
(blueprint: lem-zl-anchored-pure-curve-criterion). -/
def AnchoredCurveTest.projection (t : AnchoredCurveTest D X₀) :
    t.curve.left ⟶ X₀.left :=
  t.immersion.left ≫ (constantExtensionProjection D t.m t.positive X₀).left

/-- Constant restriction followed by the recorded immersion inverse image.
The theorem requires ConstantExtensionRestrictionSpec of the supplied functor.
Source: blueprint notation R_m S
(blueprint: lem-zl-anchored-pure-curve-criterion). -/
def AnchoredCurveTest.restriction (t : AnchoredCurveTest D X₀)
    (R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D t.m t.positive) l hl
        (constantExtensionModel D t.m t.positive X₀) Ω)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    sfCommonStageWeilSheaf (constantExtensionDatum D t.m t.positive) l hl t.curve Ω :=
  (zlWeilPull (constantExtensionDatum D t.m t.positive) l hl Ω t.immersion).obj (R.obj F)

/-- Finite-stage local spectrum, included in Ω, with algebraic multiplicities.
This uses charpoly itself, so a zero eigenvalue is retained. No presentation is chosen.
Source: blueprint condition (iii), local eigenvalue multiset
(blueprint: lem-zl-anchored-pure-curve-criterion). -/
def anchoredFiniteLocalSpectrum
    (L : Padic.FiniteCoefficientFields l Ω)
    (K : sfWeilComplex D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (ι : X₀.left.residueField x.val →+* D.k)
    (hι : ι.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    Multiset Ω :=
  letI : FiniteDimensional (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      ((DerivedCategory.coefficientFdCohomology
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) 0).obj
        (localPointComplex l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
          D hl X₀ K (localClosedPoint D X₀ x ι hι))) :=
    DerivedCategory.coefficientFdCohomology_finite _ 0 _
  ((localClosedFrobeniusCohomology l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) D hl X₀ K x ι hι 0).hom.charpoly.map
      (L.val.subtype.comp (Shrink.algEquiv ℚ_[l] L.val).toRingHom)).roots

/-- The precise local power hypothesis (iii), on every finite Weil presentation.
The residue degree is that of the actual composite projection. Universally quantifying
presentations and residue embeddings expresses independence of those choices.
Source: blueprint power calculation at the anchor and at the other point
(blueprint: lem-zl-anchored-pure-curve-criterion). -/
def AnchoredCurveTest.LocalPower (t : AnchoredCurveTest D X₀)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (G : sfCommonStageWeilSheaf (constantExtensionDatum D t.m t.positive) l hl t.curve Ω) :
    Prop :=
  ∀ (z : {z : t.curve.left // z ∈ closedPoints t.curve.left})
    (x : {x : X₀.left // x ∈ closedPoints X₀.left}),
    t.projection D X₀ z.val = x.val →
    1 ≤ (t.projection D X₀).residueDegree z.val ∧
    Nat.card (t.curve.left.residueField z.val) =
      Nat.card (X₀.left.residueField x.val) ^ (t.projection D X₀).residueDegree z.val ∧
    ∀ (L L' : Padic.FiniteCoefficientFields l Ω)
      (K : sfWeilComplex D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
      (K' : sfWeilComplex (constantExtensionDatum D t.m t.positive) l hl t.curve
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L')),
      Nonempty (F.obj ≅ sfWeilStageObject D l hl X₀ Ω L K) →
      Nonempty (G.obj ≅ sfWeilStageObject (constantExtensionDatum D t.m t.positive)
        l hl t.curve Ω L' K') →
      ∀ (ιx : X₀.left.residueField x.val →+* D.k)
        (hx : ιx.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
        (ιz : t.curve.left.residueField z.val →+* D.k)
        (hz : ιz.comp (t.curve.hom.residueFieldAlgebraMap z.val) =
          algebraMap (D.extensionSubfield t.m t.positive) D.k),
        anchoredFiniteLocalSpectrum (constantExtensionDatum D t.m t.positive) l hl Ω
            t.curve L' K' z ιz hz =
          (anchoredFiniteLocalSpectrum D l hl Ω X₀ L K x ιx hx).map
            (fun α ↦ α ^ (t.projection D X₀).residueDegree z.val)

private theorem finiteWeilPresentation
    (F : sfCommonStageWeilComplex D l hl X₀ Ω) :
    ∃ (L : Padic.FiniteCoefficientFields l Ω)
      (K : sfWeilComplex D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)),
      Nonempty (F ≅ sfWeilStageObject D l hl X₀ Ω L K) := by
  let : Quiver PUnit.{1} := ⟨fun _ _ ↦ PEmpty.{1}⟩
  have : ∀ i j : PUnit.{1}, Finite (i ⟶ j) := fun _ _ ↦ inferInstanceAs (Finite PEmpty)
  let Q : PUnit ⥤q sfCommonStageWeilComplex D l hl X₀ Ω :=
    ⟨fun _ ↦ F, fun e ↦ PEmpty.elim e⟩
  obtain ⟨L, _, _, Q₀, e, _⟩ := commonStageWeilFiniteRealization D l hl Ω X₀
    PUnit Q PEmpty.{1} PEmpty.elim PEmpty.elim (fun r ↦ PEmpty.elim r)
    (fun r ↦ PEmpty.elim r) (fun r ↦ PEmpty.elim r) ∅
  exact ⟨L, Q₀.obj PUnit.unit, ⟨(e PUnit.unit).symm⟩⟩

omit [IsAlgClosure ℚ_[l] Ω] [IsSeparated X₀.hom] in
private theorem finiteSpectrum_iff
    (L : Padic.FiniteCoefficientFields l Ω)
    (K : sfWeilComplex D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (ι : X₀.left.residueField x.val →+* D.k)
    (hι : ι.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) (α : Ω) :
    α ∈ anchoredFiniteLocalSpectrum D l hl Ω X₀ L K x ι hι ↔
      Module.End.HasEigenvalue
        ((ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω L)).map
          (localClosedFrobeniusCohomology l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
            D hl X₀ K x ι hι 0)).hom α := by
  let φ := sfAdicCoefficientEmbedding.{u} l Ω L
  let := φ.toAlgebra
  let : FiniteDimensional (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      ((DerivedCategory.coefficientFdCohomology
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) 0).obj
        (localPointComplex l _ D hl X₀ K (localClosedPoint D X₀ x ι hι))) :=
    DerivedCategory.coefficientFdCohomology_finite _ 0 _
  let : FiniteDimensional Ω
      ((ModuleCat.extendScalars φ).obj
        ((DerivedCategory.coefficientFdCohomology
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) 0).obj
          (localPointComplex l _ D hl X₀ K (localClosedPoint D X₀ x ι hι)))) := by
    change Module.Finite Ω (TensorProduct _ Ω _)
    infer_instance
  let f := (localClosedFrobeniusCohomology l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) D hl X₀ K x ι hι 0).hom
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
  change α ∈ (f.charpoly.map φ).roots ↔ _
  rw [Polynomial.mem_roots ((LinearMap.charpoly_monic _).map φ).ne_zero]
  change _ ↔ (LinearMap.baseChange Ω _).charpoly.IsRoot α
  rw [LinearMap.charpoly_baseChange]
  rfl

omit [IsSeparated X₀.hom] in
private theorem closedPoint_card_gt_one
    (x : {x : X₀.left // x ∈ closedPoints X₀.left}) :
    1 < (Nat.card (X₀.left.residueField x.val) : ℝ) := by
  let := (X₀.hom.residueFieldAlgebraMap x.val).toAlgebra
  let := (closedPoint_iff_residueField_trdeg_zero_and_finite X₀.hom x.val).2.1.mp x.prop
  have : Finite (X₀.left.residueField x.val) := Module.finite_of_finite D.k₀
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card (X₀.left.residueField x.val))

private theorem power_purity_norm
    {a q v : ℝ} (ha : 0 ≤ a) (hq : 0 < q) {f : ℕ} (hf : 1 ≤ f)
    (h : a ^ f = (q ^ f) ^ (v / 2)) : a = q ^ (v / 2) := by
  apply (pow_left_inj₀ ha (Real.rpow_nonneg hq.le _) (by omega : f ≠ 0)).mp
  rw [h, ← Real.rpow_mul_natCast hq.le, ← Real.rpow_natCast_mul hq.le]
  congr 1
  ring

omit [IsSeparated X₀.hom] in
private theorem curve_purity_at_point
    (iota : Ω ≃+* ℂ) (t : AnchoredCurveTest D X₀)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (G : sfCommonStageWeilSheaf (constantExtensionDatum D t.m t.positive)
      l hl t.curve Ω)
    (hpow : t.LocalPower D l hl Ω X₀ F G) (v : ℝ)
    (hp : SfIsPunctuallyPureOfWeight (constantExtensionDatum D t.m t.positive)
      l hl Ω t.curve iota.toRingHom G v)
    (z : {z : t.curve.left // z ∈ closedPoints t.curve.left})
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (hzx : t.projection D X₀ z.val = x.val) (β : Ω)
    (hβ : SfPunctualEigenvalue D l hl Ω X₀ F x β) :
    ‖iota β‖ = (Nat.card (X₀.left.residueField x.val) : ℝ) ^ (v / 2) := by
  classical
  obtain ⟨L, K, hK, ιx, hx, hβ⟩ := hβ
  have : IsSeparated t.curve.hom := by
    have := t.affine
    infer_instance
  obtain ⟨L', K', hK'⟩ := finiteWeilPresentation
    (constantExtensionDatum D t.m t.positive) l hl Ω t.curve G.obj
  let := (t.curve.hom.residueFieldAlgebraMap z.val).toAlgebra
  have := (closedPoint_iff_residueField_trdeg_zero_and_finite
    t.curve.hom z.val).2.1.mp z.prop
  let ιz : t.curve.left.residueField z.val →ₐ[D.extensionSubfield t.m t.positive] D.k :=
    IsAlgClosed.lift
  have hz : ιz.toRingHom.comp (t.curve.hom.residueFieldAlgebraMap z.val) =
      algebraMap (D.extensionSubfield t.m t.positive) D.k := by
    ext a
    exact ιz.commutes a
  obtain ⟨hf, hcard, hs⟩ := hpow z x hzx
  have hbmem := (finiteSpectrum_iff D l hl Ω X₀ L K x ιx hx β).mpr hβ
  have hzmem : β ^ (t.projection D X₀).residueDegree z.val ∈
      anchoredFiniteLocalSpectrum (constantExtensionDatum D t.m t.positive)
        l hl Ω t.curve L' K' z ιz.toRingHom hz := by
    rw [hs L L' K K' hK hK' ιx hx ιz.toRingHom hz]
    exact Multiset.mem_map.mpr ⟨β, hbmem, rfl⟩
  have hzeig : SfPunctualEigenvalue (constantExtensionDatum D t.m t.positive)
      l hl Ω t.curve G z (β ^ (t.projection D X₀).residueDegree z.val) :=
    ⟨L', K', hK', ιz.toRingHom, hz,
      (finiteSpectrum_iff (constantExtensionDatum D t.m t.positive)
        l hl Ω t.curve L' K' z ιz.toRingHom hz _).mp hzmem⟩
  have heq := hp z _ hzeig
  rw [map_pow, norm_pow, hcard, Nat.cast_pow] at heq
  exact power_purity_norm (norm_nonneg _) (lt_trans zero_lt_one
    (closedPoint_card_gt_one D X₀ x)) hf heq

/-- A fixed nonzero classical lisse Weil sheaf has a unique global weight if pure
curve restrictions connect every closed point to one anchor and obey the local power law.
The anchor formula holds for every eigenvalue, every supplied curve through it has that
weight, and the same conclusion holds for any further such pure curve.

Source: blueprint latest, thm-zl-real-mixed-by-curves.proof.md, paragraphs 3--4
(blueprint: lem-zl-anchored-pure-curve-criterion).

Proof: (1) Geometric connectedness makes the geometric fibre connected; separated finite
type base change makes it noetherian. The coefficient-field fibre equivalence of
cor-galois-lisse-representations reflects zero objects. The nonzero classical lisse
sheaf therefore has a nonzero finite-dimensional anchor fibre. The normalized local
comparison of lem-zl-classical-local-frobenius-iterate-comparison identifies its local
operator with the recorded one. Lem-zl-alg-closed-endomorphism-eigenvalue supplies an
anchor eigenvalue alpha_*; invertibility is not assumed at this step.
(2) Lem-kun-closed-point-field makes every closed residue field finite over k_0;
its distinct elements zero and one show q_x >= 2. Thus log q_x > 0.
(3) For any test curve of weight v and point z above x, the multiset power law and
purity give a^f = (q_x^f)^(v/2), where a = norm(iota beta) >= 0 and f >= 1.
The right side is positive, hence a > 0. Taking logarithms and cancelling f and
log q_x yields 2 log a / log q_x = v.
(4) Apply the covering hypothesis with x equal to the anchor. On that curve every
anchor eigenvalue has positive modulus, hence is nonzero. Put
w = 2 log(norm(iota alpha_*)) / log q_anchor. Step (3) identifies w with that
curve's weight and gives the same formula for every anchor eigenvalue.
(5) Apply (3) to alpha_* on any supplied or further pure curve through the anchor:
its weight is w, with no use of membership in the given family.
(6) For each closed x choose a curve through x and the anchor. Its weight is w;
(3) and lem-a1-real-logarithm-power give norm(iota beta) = q_x^(w/2) for every
local beta. This is precisely SfIsPunctuallyPureOfWeight.
(7) Any other global weight w' gives norm(iota alpha_*) = q_anchor^(w'/2).
Taking logarithms again yields w' = w. Zero fibres and repeated eigenvalues require
no modification of the power calculation. -/
theorem anchoredPureCurveCriterion
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (iota : Ω ≃+* ℂ) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [Nonempty X₀.left] [GeometricallyConnected X₀.hom]
    (A : @ZlClassicalRealization D l _ hl Ω _ _ _ X₀ _ _ _
      (⟨fun x ↦ @isUnit_of_invertible _ _ _
        (zlClassicalStalkInvertible D l hl X₀ x)⟩))
    (S : @ZlClassicalWeil D l _ Ω _ _ _ X₀ _ _ _ (⟨fun x ↦ @isUnit_of_invertible _ _ _
        (zlClassicalStalkInvertible D l hl X₀ x)⟩))
    (hne : ¬ IsZero S.carrier)
    (R : ∀ (m : ℕ) (hm : 1 ≤ m), sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (hR : ∀ (m : ℕ) (hm : 1 ≤ m), ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω (R m hm))
    (anchor : {x : X₀.left // x ∈ closedPoints X₀.left})
    (I : Type w) (tests : I → AnchoredCurveTest D X₀) (weights : I → ℝ)
    (hcover : ∀ x : {x : X₀.left // x ∈ closedPoints X₀.left},
      ∃ (i : I) (za z : {z : (tests i).curve.left // z ∈ closedPoints (tests i).curve.left}),
        (tests i).projection D X₀ za.val = anchor.val ∧
        (tests i).projection D X₀ z.val = x.val)
    (hpure : ∀ i : I,
      SfIsPunctuallyPureOfWeight (constantExtensionDatum D (tests i).m (tests i).positive)
        l hl Ω (tests i).curve iota.toRingHom
        ((tests i).restriction D l hl Ω X₀ (R (tests i).m (tests i).positive)
          (anchoredRealizedSheaf D l hl Ω X₀ A S)) (weights i))
    (hpower : ∀ i : I, (tests i).LocalPower D l hl Ω X₀
      (anchoredRealizedSheaf D l hl Ω X₀ A S)
      ((tests i).restriction D l hl Ω X₀ (R (tests i).m (tests i).positive)
        (anchoredRealizedSheaf D l hl Ω X₀ A S))) :
    ∃ weight : ℝ,
      SfIsPunctuallyPureOfWeight D l hl Ω X₀ iota.toRingHom
        (anchoredRealizedSheaf D l hl Ω X₀ A S) weight ∧
      (∀ weight' : ℝ, SfIsPunctuallyPureOfWeight D l hl Ω X₀ iota.toRingHom
        (anchoredRealizedSheaf D l hl Ω X₀ A S) weight' → weight' = weight) ∧
      (∀ α : Ω, SfPunctualEigenvalue D l hl Ω X₀
        (anchoredRealizedSheaf D l hl Ω X₀ A S) anchor α →
        α ≠ 0 ∧ weight = 2 * Real.logb
          (Nat.card (X₀.left.residueField anchor.val) : ℝ) ‖iota α‖) ∧
      (∀ i : I,
        (∃ z : {z : (tests i).curve.left // z ∈ closedPoints (tests i).curve.left},
          (tests i).projection D X₀ z.val = anchor.val) → weights i = weight) ∧
      (∀ (t : AnchoredCurveTest D X₀) (v : ℝ),
        (∃ z : {z : t.curve.left // z ∈ closedPoints t.curve.left},
          t.projection D X₀ z.val = anchor.val) →
        t.LocalPower D l hl Ω X₀ (anchoredRealizedSheaf D l hl Ω X₀ A S)
          (t.restriction D l hl Ω X₀ (R t.m t.positive)
            (anchoredRealizedSheaf D l hl Ω X₀ A S)) →
        SfIsPunctuallyPureOfWeight (constantExtensionDatum D t.m t.positive)
          l hl Ω t.curve iota.toRingHom
          (t.restriction D l hl Ω X₀ (R t.m t.positive)
            (anchoredRealizedSheaf D l hl Ω X₀ A S)) v → v = weight) ∧
      ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left}) (β : Ω),
        SfPunctualEigenvalue D l hl Ω X₀
          (anchoredRealizedSheaf D l hl Ω X₀ A S) x β →
        ‖iota β‖ = (Nat.card (X₀.left.residueField x.val) : ℝ) ^ (weight / 2) := by
  classical
  have _ := hR
  let F := anchoredRealizedSheaf D l hl Ω X₀ A S
  obtain ⟨α, hα⟩ := classicalRealized_anchor_eigenvalue D l hl Ω X₀ A S hne anchor
  obtain ⟨i₀, za₀, _, hza₀, _⟩ := hcover anchor
  let weight := weights i₀
  have hnorm (t : AnchoredCurveTest D X₀) (v : ℝ)
      (hpow : t.LocalPower D l hl Ω X₀ F
        (t.restriction D l hl Ω X₀ (R t.m t.positive) F))
      (hp : SfIsPunctuallyPureOfWeight (constantExtensionDatum D t.m t.positive)
        l hl Ω t.curve iota.toRingHom
        (t.restriction D l hl Ω X₀ (R t.m t.positive) F) v)
      (z : {z : t.curve.left // z ∈ closedPoints t.curve.left})
      (x : {x : X₀.left // x ∈ closedPoints X₀.left})
      (hz : t.projection D X₀ z.val = x.val) (β : Ω)
      (hb : SfPunctualEigenvalue D l hl Ω X₀ F x β) :
      ‖iota β‖ = (Nat.card (X₀.left.residueField x.val) : ℝ) ^ (v / 2) :=
    curve_purity_at_point D l hl Ω X₀ iota t F _ hpow v hp z x hz β hb
  have hbase := closedPoint_card_gt_one D X₀ anchor
  have hlog (v : ℝ) (β : Ω)
      (hb : ‖iota β‖ = (Nat.card (X₀.left.residueField anchor.val) : ℝ) ^ (v / 2)) :
      v = 2 * Real.logb (Nat.card (X₀.left.residueField anchor.val) : ℝ) ‖iota β‖ := by
    rw [hb, Real.logb_rpow (lt_trans zero_lt_one hbase) (ne_of_gt hbase)]
    ring
  have hweight : weight =
      2 * Real.logb (Nat.card (X₀.left.residueField anchor.val) : ℝ) ‖iota α‖ :=
    hlog weight α (hnorm (tests i₀) weight (hpower i₀) (hpure i₀) za₀ anchor hza₀ α hα)
  have htest (t : AnchoredCurveTest D X₀) (v : ℝ)
      (hz : ∃ z : {z : t.curve.left // z ∈ closedPoints t.curve.left},
        t.projection D X₀ z.val = anchor.val)
      (hpow : t.LocalPower D l hl Ω X₀ F
        (t.restriction D l hl Ω X₀ (R t.m t.positive) F))
      (hp : SfIsPunctuallyPureOfWeight (constantExtensionDatum D t.m t.positive)
        l hl Ω t.curve iota.toRingHom
        (t.restriction D l hl Ω X₀ (R t.m t.positive) F) v) : v = weight := by
    obtain ⟨z, hz⟩ := hz
    exact (hlog v α (hnorm t v hpow hp z anchor hz α hα)).trans hweight.symm
  have hfamily (i : I)
      (hz : ∃ z : {z : (tests i).curve.left // z ∈ closedPoints (tests i).curve.left},
        (tests i).projection D X₀ z.val = anchor.val) : weights i = weight :=
    htest (tests i) (weights i) hz (hpower i) (hpure i)
  have hglobal : SfIsPunctuallyPureOfWeight D l hl Ω X₀ iota.toRingHom F weight := by
    intro x β hb
    obtain ⟨i, za, z, hza, hz⟩ := hcover x
    have hw := hfamily i ⟨za, hza⟩
    exact (hnorm (tests i) (weights i) (hpower i) (hpure i) z x hz β hb).trans
      (by rw [hw])
  refine ⟨weight, hglobal, ?_, ?_, hfamily, htest, hglobal⟩
  · intro weight' hp
    exact (hlog weight' α (hp anchor α hα)).trans hweight.symm
  · intro β hb
    have hn := hnorm (tests i₀) weight (hpower i₀) (hpure i₀) za₀ anchor hza₀ β hb
    refine ⟨?_, hlog weight β hn⟩
    intro hz
    have hpos : 0 < ‖iota β‖ := by
      rw [hn]
      exact Real.rpow_pos_of_pos (lt_trans zero_lt_one hbase) _
    simp [hz] at hpos

end WeilConjectures
