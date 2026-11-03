/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleKummerLimitBoundary
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Admissible.AdmissibleDivisorClass
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Admissible.AdmissibleSupportedHom
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RankOneDivisorClassIntegral
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier

/-! # Supported divisor classes from the full compatible-root boundary

Source: latest blueprint part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/lem-pur-divisor-class.proof.md,
(b), the relative class and anticommuting boundaries; vector-bundle-thom proof,
Steps 1 and 3 (blueprint: lem-pur-supported-kummer-root-realization).

Ext is Mathlib's presentation of the displayed derived Hom. Its universe is
u+2 for internal modules and u+1 for abelian sheaves. The supported transpose
is explicitly forgetting scalars followed by the supported coefficient unit.
The abelian arrow is formed before any coefficient is selected.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.SupportedKummer
open CondensedRing.Admissible

/-- The actual supported integral abelian sheaf, in degree zero before taking Ext.
Source: divisor extension in divisor-class proof (b)
(blueprint: lem-pur-supported-kummer-root-realization). -/
abbrev integralSource {D X : Scheme.{u}} (i : D ⟶ X) :=
  (ProEtale.lowerStar Ab.{u + 1} i).obj
    (CompatibleKummerCoefficients.integralConstant D)

/-- The positive connecting class of the normalized inverse-equation pole extension.
Source: divisor-class proof (b), f inverse maps to one
(blueprint: lem-pur-supported-kummer-root-realization). -/
def alpha {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) :
    Ext.{u + 1} (integralSource i) (Scheme.proEtaleUnitsSheaf X) 1 :=
  cartierProBoundary i (Etale.cartierPoleBoundary i hI)

/-- The two root-limit presentations are identified by every positive coordinate.
Source: compatible-root-boundary, native linear realization; divisor-class root data
(blueprint: lem-pur-supported-kummer-root-realization).
Proof: insert a compatible root in each finite Tate level by z tensor one.
The native level comparison identifies this insertion with the root itself.
These maps give inverse cones on the positive cofinal subsystem. Their limits
are inverse; equality of every coordinate gives uniqueness. -/
theorem rootComparison_existsUnique (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) :
    ∃! e : compatibleRoots ell X ≅ (tateModule X ell).X,
      ∀ n : ℕ, e.hom ≫ (limit.π (tateModuleSystem X ell) (op (n + 1))).hom ≫
        ((kummerData ell X).level n).hom = compatibleRootsCoordinate ell X n := by
  sorry

/-- The coordinate-normalized root comparison, determined uniquely by the preceding theorem.
Source: compatible-root-boundary native realization
(blueprint: lem-pur-supported-kummer-root-realization). -/
def rootComparison (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) :=
  (rootComparison_existsUnique ell X).choose

private def rootComplexIso (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) :
    compatibleKummerComplex ell X ≅ kummerComplex ell X := by
  refine ShortComplex.isoMk (S₁ := compatibleKummerComplex ell X)
    (S₂ := kummerComplex ell X) (rootComparison ell X) (Iso.refl _) (Iso.refl _) ?_ ?_
  · change (rootComparison ell X).hom ≫ (kummerData ell X).inclusion =
      (compatibleRootInclusion ell X).hom ≫ 𝟙 _
    rw [Category.comp_id]
    apply limit.hom_ext
    rintro ⟨n⟩
    cases n with
    | zero =>
        rw [Category.assoc, (kummerData ell X).zeroth, comp_zero]
        exact (compatibleRootInclusion ell X).zeroth.symm
    | succ n =>
        rw [Category.assoc, (kummerData ell X).positive]
        calc
          _ = compatibleRootsCoordinate ell X n ≫
              Scheme.proEtaleRootsOfUnityInclusion X (ell ^ (n + 1)) := by
            simpa only [rootComparison, Category.assoc] using congrArg
              (fun f ↦ f ≫ Scheme.proEtaleRootsOfUnityInclusion X (ell ^ (n + 1)))
              ((rootComparison_existsUnique ell X).choose_spec.1 n)
          _ = _ := (compatibleRootInclusion ell X).positive n |>.symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl

/-- The full compatible-root row is exact on every scheme in the standing setting.
Source: compatible-root-boundary, exact-row clause
(blueprint: lem-pur-supported-kummer-root-realization).
Proof: the kernel is the compatible roots with zero zeroth coordinate; adjoining
successive prime-power roots gives a pro-etale cover lifting every unit. Thus the
specified inclusion is the kernel and projection is an epimorphism. -/
theorem root_exact (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) :
    (compatibleKummerComplex P.coefficients.l X).ShortExact := by
  exact ShortComplex.shortExact_of_iso (rootComplexIso P.coefficients.l X).symm
    (kummer_exact P X a)

/-- The single abelian arrow b_D = -delta[1] alpha, before choosing coefficients.
Source: divisor-class proof (b), the two boundaries anticommute
(blueprint: lem-pur-supported-kummer-root-realization). -/
def boundary (P : WeilConjectures.PurityFiniteSetting.{u})
    {D X : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of P.field.k))
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    Ext.{u + 1} (integralSource i) (compatibleRoots P.coefficients.l X) 2 :=
  -((alpha i hI).comp (ShortComplex.ShortExact.extClass (root_exact P X a)) rfl)

/-- j_Lambda inserts the compatible roots into the actual native Tate line.
Source: compatible-root-boundary, native coefficient insertion
(blueprint: lem-pur-supported-kummer-root-realization). -/
def insertion (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ) (X : Scheme.{u}) :
    compatibleRoots P.coefficients.l X ⟶ (line P Λ hΛ X).X :=
  (rootComparison P.coefficients.l X).hom ≫ rootInsertion P Λ hΛ X

/-- The displayed free/forgetful transpose, normalized by the supported unit.
Source: derived coefficient adjunction, unit m maps to m times one
(blueprint: lem-pur-supported-kummer-root-realization). -/
def transpose (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {D X : Scheme.{u}} (i : D ⟶ X) (M : Modules Λ X) (n : ℕ)
    (c : Ext.{u + 2} (source Λ i) M n) : Ext.{u + 1} (integralSource i) M.X n :=
  (Ext.mk₀ (supportedGenerator Λ i)).comp
    (c.mapExactFunctor (Mod.forget (condensedRingObj Λ.X X))) (zero_add n)

/-- The displayed supported transpose is bijective, with no flatness of coefficients.
Source: derived coefficient adjunction and internal/section scalar adjunction
(blueprint: lem-pur-supported-kummer-root-realization).
Proof: closed projection identifies the derived free module on i_*Z_D with
 i_*Lambda_D. The projection composite with the scalar unit is the supported
coefficient unit: on D it sends m to m times one and off D the source vanishes.
Apply the normalized derived adjunction and the internal/section equivalence.
Their transpose is exactly the displayed Ext composition. -/
theorem transpose_bijective (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (M : Modules Λ X) (n : ℕ) : Function.Bijective (transpose Λ i M n) := by
  sorry

/-- The canonical displayed Hom bijection, expressed in Mathlib Ext coordinates.
Source: normalized derived free-module/forgetful adjunction
(blueprint: lem-pur-supported-kummer-root-realization). -/
def homEquiv (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (M : Modules Λ X) (n : ℕ) :
    Ext.{u + 2} (source Λ i) M n ≃ Ext.{u + 1} (integralSource i) M.X n :=
  Equiv.ofBijective (transpose Λ i M n) (transpose_bijective Λ i M n)

/-- The displayed bijection in actual derived Hom coordinates, using Ext.homEquiv.
Source: derived free-module/forgetful adjunction
(blueprint: lem-pur-supported-kummer-root-realization). -/
def derivedHomEquiv (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (M : Modules Λ X) (n : ℕ) :
    ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (source Λ i) ⟶
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟦(n : ℤ)⟧) ≃
    ((DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) 0).obj
        (integralSource i) ⟶
      ((DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) 0).obj
        M.X) ⟦(n : ℤ)⟧) :=
  Ext.homEquiv.symm.trans ((homEquiv Λ i M n).trans Ext.homEquiv)

/-- The stated smooth Cartier family lies in the actual frame-class geometric scope.
Source: divisor-class opening hypotheses, specialized to relative dimensions one and zero
(blueprint: lem-pur-supported-kummer-root-realization).
Proof: a Cartier equation is a nonzerodivisor. Smooth relative coordinates over
S give codimension one and its stalk dimension formula, including a nonreduced
base. The separated finite-type structural maps are the given ones. They supply
the witnesses of SmoothDivisorPair; the empty divisor satisfies these pointwise
conditions vacuously. -/
theorem smooth_pair (P : WeilConjectures.PurityFiniteSetting.{u})
    {S X D : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (v : X ⟶ S) [SmoothOfRelativeDimension 1 v]
    [IsSeparated (v ≫ s)] [LocallyOfFiniteType (v ≫ s)] [QuasiCompact (v ≫ s)]
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    [SmoothOfRelativeDimension 0 (i ≫ v)] : SmoothDivisorPair P (v ≫ s) i := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (v ≫ s)
  let : Smooth (i ≫ v) := SmoothOfRelativeDimension.smooth 0 _
  apply smoothDivisorPair P s v 1 i
  intro z
  obtain ⟨U, hzU, hU⟩ := hI (i z)
  let := X.presheaf.algebra_section_stalk ⟨i z, hzU⟩
  have := U.2.isLocalization_stalk ⟨i z, hzU⟩
  have hflat : (X.presheaf.germ U.1 (i z) hzU).hom.Flat := by
    change (algebraMap Γ(X, U.1) (X.presheaf.stalk (i z))).Flat
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _
      (U.2.primeIdealOf ⟨i z, hzU⟩).asIdeal.primeCompl)
  obtain ⟨t, ht, hker⟩ := hU.map_of_flat hflat
  rw [← i.ker_stalkMap U z hzU] at hker
  have htker : t ∈ RingHom.ker (i.stalkMap z).hom := by
    rw [hker]
    exact Ideal.subset_span rfl
  have htmax : t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i z)) := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hunit
    have hzero := hunit.map (i.stalkMap z).hom
    rw [RingHom.mem_ker.mp htker] at hzero
    exact not_isUnit_zero hzero
  have hdim :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      ht htmax
  rw [← hker] at hdim
  rw [ringKrullDim_eq_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective (i.stalkMap_surjective z))] at hdim
  exact hdim.symm

private theorem root_extClass (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) :
    (root_exact P X a).extClass.comp
        (Ext.mk₀ (rootComparison P.coefficients.l X).hom) (add_zero 1) =
      (kummer_exact P X a).extClass := by
  have h := ShortComplex.ShortExact.extClass_naturality
    (root_exact P X a) (kummer_exact P X a) (rootComplexIso P.coefficients.l X).hom
  change (root_exact P X a).extClass.comp
      (Ext.mk₀ (rootComparison P.coefficients.l X).hom) (add_zero 1) =
    (Ext.mk₀ (𝟙 _)).comp (kummer_exact P X a).extClass (zero_add 1) at h
  simpa only [Ext.mk₀_id_comp] using h

private theorem kummerClass_eq (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) :
    kummerClass P Λ hΛ X a =
      (root_exact P X a).extClass.comp (Ext.mk₀ (insertion P Λ hΛ X)) (add_zero 1) := by
  dsimp only [kummerClass, cartierKummerClass, insertion]
  rw [← root_extClass P X a, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]

/-- The actual positive supported divisor class is the realization of one abelian arrow.

Source: latest blueprint divisor-class proof (b), relative class and anticommuting
boundaries; localized-top-chern (L1) and its universal Step 3; vector-bundle-thom
proof Steps 1 and 3 (blueprint: lem-pur-supported-kummer-root-realization).

Proof, following the nine DAG paragraphs.
1. Closed projection and the normalized free/forgetful adjunction give homEquiv;
its forward map is exactly forgetting scalars after the supported unit.
2. Take the inverse adjunct of j[2] b_D. Naturality of the adjunction and the
root insertion equations commute this specified map with scalar extension,
including nonflat reduction and every finite extension coefficient field.
3. In the divisor pole extension f inverse maps to one. A horseshoe injective
resolution with differential (a,b) maps to (da+hb,db) has h epsilon pi=-d psi.
Thus alpha on one is -d psi(f inverse), representing +partial_G(f).
4. In relative coordinates D(a,b)=(da,res(a)-db), the localization boundary is
(0,-b). Lifting f by r gives (0,dr) for delta_supp partial_G(f), while partial
delta(f) is (0,-dr). Hence -delta[1] alpha=partial delta(f) before coefficients.
5. On the line-bundle zero section the finite frame class has this chart formula;
the bottom supported-Hom sheaf property identifies the global classes.
6. At native coefficients use the same universal zero-section gluing and its
bottom-degree separation, as in localized-top-chern Step 3. The all-admissible
rank-one divisor class is that glued class, not an arbitrary lift of reductions.
7. For the given D, the inclusion of its ideal defines the regular section of
O_X(D). In a frame its total-space map sends t to f and pulls the zero scheme
back to D. Apply localized-top-chern (L2) to its universal rank-one class.
8. Inverse image of the pole extension carries f inverse to the inverse pulled
back equation; the root row and insertion are natural. The adjunction's unit
normalization identifies the pulled-back realization with the same b_D formula.
9. The resulting single global arrow therefore equals the actual glued class.
Its restrictions are the positive chart boundaries, compatibly on all opens.
The comparison is made before coefficients, not inferred from finite reductions.
-/
theorem supported_kummer_root_realization (P : WeilConjectures.PurityFiniteSetting.{u})
    {S X D : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (v : X ⟶ S) [SmoothOfRelativeDimension 1 v]
    [IsSeparated (v ≫ s)] [LocallyOfFiniteType (v ≫ s)] [QuasiCompact (v ≫ s)]
    (i : D ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    [SmoothOfRelativeDimension 0 (i ≫ v)] :
    ∀ (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
      (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ),
      derivedHomEquiv Λ i (line P Λ hΛ X) 2
          (divisorArrow P Λ hΛ (v ≫ s) i hI (smooth_pair P s v i hI)) =
        ((boundary P (v ≫ s) i hI).comp
          (Ext.mk₀ (insertion P Λ hΛ X)) (add_zero 2)).hom ∧
      LocalEquationLaw P Λ hΛ (v ≫ s) i hI (smooth_pair P s v i hI) := by
  intro Λ hcomm hΛ
  have : QuasiCompact i.openComplement.ι := cartierComplement_quasiCompact i hI
  -- Reuse the global sign comparison already established in divisor_class_full.
  let : Smooth (i ≫ v) := SmoothOfRelativeDimension.smooth 0 _
  have hdim : ∀ z : D, ringKrullDim (X.presheaf.stalk (i z)) =
      ringKrullDim (D.presheaf.stalk z) + (1 : WithBot ℕ∞) := by
    obtain ⟨B, b, w, n, heq, hbsep, hbft, hbqc, hasep, haft, haqc,
      hw, hiw, hdim⟩ := smooth_pair P s v i hI
    exact hdim
  obtain ⟨hI', hlaw, hclass, hrest⟩ := divisor_class_full P Λ hΛ s v 1 i hdim
  refine ⟨?_, (divisor_class P Λ hΛ (v ≫ s) i hI (smooth_pair P s v i hI)).2⟩
  let c : Ext.{u + 2} (source Λ i) (line P Λ hΛ X) 2 :=
    Ext.homEquiv.symm (divisorArrow P Λ hΛ (v ≫ s) i hI (smooth_pair P s v i hI))
  have hc : cartierExt P Λ hΛ (v ≫ s) i hI = -c := by
    apply Ext.ext
    have h := congrArg (supportedHom Λ i _ 2) hclass
    simpa only [cartierClass, AddEquiv.apply_symm_apply, map_neg, divisorArrow,
      c, Equiv.apply_symm_apply, Ext.neg_hom] using h
  have hcn : c = -cartierExt P Λ hΛ (v ≫ s) i hI := by
    rw [hc, neg_neg]
  have ht : transpose Λ i (line P Λ hΛ X) 2
      (cartierExt P Λ hΛ (v ≫ s) i hI) =
      (alpha i hI).comp (kummerClass P Λ hΛ X (v ≫ s)) rfl :=
    (cartier_existsUnique P Λ hΛ (v ≫ s) i hI).choose_spec.1
  have hn : transpose Λ i (line P Λ hΛ X) 2
      (-cartierExt P Λ hΛ (v ≫ s) i hI) =
      -transpose Λ i (line P Λ hΛ X) 2 (cartierExt P Λ hΛ (v ≫ s) i hI) := by
    dsimp only [transpose]
    rw [← Functor.mapExtAddHom_apply, map_neg, Ext.comp_neg]
    rfl
  have he : transpose Λ i (line P Λ hΛ X) 2 c =
      (boundary P (v ≫ s) i hI).comp
        (Ext.mk₀ (insertion P Λ hΛ X)) (add_zero 2) := by
    rw [hcn, hn, ht, kummerClass_eq]
    simp only [boundary, Ext.neg_comp, Ext.comp_assoc_of_third_deg_zero]
  change (transpose Λ i (line P Λ hΛ X) 2 c).hom = _
  exact congrArg Ext.hom he

/-- The same one-arrow realization for the canonical integral/rational rank-one Thom class.
Source: rank-one-divisor-class-integral and localized-top-chern (L1)
(blueprint: lem-pur-supported-kummer-root-realization).
Proof: canonicalThom is exactly the all-admissible divisorArrow of the zero
section. Apply the preceding construction to this smooth Cartier pair; the
rank-one zero-geometry theorem supplies its ideal and smooth-pair witnesses.
The root and supported unit maps are the same, so their normalized adjuncts
agree. This works separately for every admissible coefficient ring. -/
theorem zero_section_realization (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ) :
    derivedHomEquiv Λ V.zeroSection (line P Λ hΛ V.E) 2
        (canonicalThom P b V Λ hΛ) =
      ((boundary P (V.p ≫ b) V.zeroSection (rankOne_zero_ideal P b V)).comp
        (Ext.mk₀ (insertion P Λ hΛ V.E)) (add_zero 2)).hom := by
  obtain ⟨hB, hE, hsep, hft, hqc, hpsep, hpft, hpqc, hsm, hc,
    hzclosed, hzcomp, hzcartier, hzsm, hdim, hrest⟩ :=
      PurityVectorBundle.lineZeroGeometry P B b V
  let := hsep
  let := hft
  let := hqc
  let := hsm
  let := hzsm
  simpa only [canonicalThom] using
    (supported_kummer_root_realization P b V.p V.zeroSection
      (rankOne_zero_ideal P b V) Λ hΛ).1

end AlgebraicGeometry.ProEtale.SupportedKummer
