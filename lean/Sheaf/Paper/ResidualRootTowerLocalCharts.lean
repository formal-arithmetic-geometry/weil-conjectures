/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FullParameterRootTower
public import Sheaf.Paper.RootTowerProfiniteBaseChange
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.AlgebraicGeometry.SNCBoundaryParameterCriterion
import Sheaf.AlgebraicGeometry.UnitBinomialFiniteEtale
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.RingTheory.IndEtaleStability
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Residual full-root towers in local active parameters

Source: Stacks, etale.tex, Tag 0BIA; algebra.tex, Tags 00UB and 00UC;
blueprint direct-images proof (3), local coordinate-face argument
(blueprint: lem-sfb-residual-root-tower-local-charts).

The helpers spell out the quotients, the two successive existing full-root algebras,
and the coefficient-normalized comparison. No new root algebra is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory Limits
open scoped TensorProduct
namespace AlgebraicGeometry.ProEtale

open Classical in
/-- The ideal of a coordinate face. Source: Stacks 0BIA, scheme-theoretic intersections
(blueprint: lem-sfb-residual-root-tower-local-charts). -/
def residualFaceIdeal {I A : Type u} [Fintype I] [CommRing A]
    (t : I → A) (J : Finset I) : Ideal A :=
  Ideal.span (t '' (J : Set I))

open Classical in
/-- The actual face quotient. Source: Stacks 0BIA
(blueprint: lem-sfb-residual-root-tower-local-charts). -/
abbrev ResidualFaceRing {I A : Type u} [Fintype I] [CommRing A]
    (t : I → A) (J : Finset I) := A ⧸ residualFaceIdeal t J

open Classical in
/-- The quotient R_J, using the extended face ideal. Source: Stacks 00CT and 0BIA
(blueprint: lem-sfb-residual-root-tower-local-charts). -/
abbrev ResidualFaceCoefficients {I A R : Type u} [Fintype I] [CommRing A] [CommRing R]
    [Algebra A R] (t : I → A) (J : Finset I) :=
  R ⧸ (residualFaceIdeal t J).map (algebraMap A R)

open Classical in
/-- The canonical algebra of the face quotient, not an arbitrary map between quotients.
Source: Stacks 00CT (blueprint: lem-sfb-residual-root-tower-local-charts). -/
instance residualFaceCoefficientsAlgebra {I A R : Type u} [Fintype I]
    [CommRing A] [CommRing R] [Algebra A R] (t : I → A) (J : Finset I) :
    Algebra (ResidualFaceRing t J) (ResidualFaceCoefficients (R := R) t J) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

open Classical in
/-- The surviving parameters on the face. Source: Stacks 0BIA
(blueprint: lem-sfb-residual-root-tower-local-charts). -/
def residualFaceParameters {I A : Type u} [Fintype I] [CommRing A]
    (t : I → A) (J : Finset I) : {i : I // i ∉ J} → ResidualFaceRing t J :=
  fun i ↦ Ideal.Quotient.mk _ (t i.val)

open Classical in
/-- The canonical ideal sheaf of a principal equation on an affine spectrum.
Source: Stacks 0BIA (blueprint: lem-sfb-residual-root-tower-local-charts). -/
def residualPrincipalIdeal {A : Type u} [CommRing A] (a : A) :
    (Spec (.of A)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.span {(Scheme.ΓSpecIso (.of A)).inv a})

open Classical in
/-- A labelled family cuts out precisely the distinct reduced integral branches of an SNC
boundary: the product defines the boundary and the distinct principal quotients are domains.
Source: Stacks 0BIA (blueprint: lem-sfb-residual-root-tower-local-charts). -/
def HasResidualSNCEquations {I A : Type u} [Fintype I] [CommRing A] (t : I → A) : Prop :=
  IsStrictNormalCrossingsBoundary (residualPrincipalIdeal (∏ i, t i)) ∧
    Function.Injective (fun i ↦ Ideal.span {t i}) ∧
    ∀ i, IsDomain (A ⧸ Ideal.span {t i})

open Classical in
/-- Every vanishing named equation occupies a distinct position in an actual regular
parameter list at the prime. The local Noetherian structure is existential, not assumed.
Source: Stacks 0BIA and 00KU (blueprint: lem-sfb-residual-root-tower-local-charts). -/
def ResidualParametersAtPrimes {I A : Type u} [Fintype I] [CommRing A]
    (t : I → A) : Prop :=
  ∀ x : PrimeSpectrum A,
    ∃ (hN : IsNoetherianRing (Localization.AtPrime x.asIdeal))
      (s : List (Localization.AtPrime x.asIdeal)),
      @IsLocalRing.IsRegularSystemOfParameters _ _ _ hN s ∧
        ∃ e : {i : I // t i ∈ x.asIdeal} ↪ Fin s.length,
          ∀ i, s.get (e i) = algebraMap A (Localization.AtPrime x.asIdeal) (t i.val)

open Classical in
/-- The inactive unit-root algebra D_W, formed with the existing full root presentation.
Source: DAG proof step 5, Stacks 00UB/00UC
(blueprint: lem-sfb-residual-root-tower-local-charts). -/
abbrev ResidualInactiveRoots {I R : Type u} [Fintype I] [CommRing R]
    (p : ℕ) (t : I → R) (L : Finset I) :=
  FullParameterRootAlgebra p (fun i : {i : I // i ∉ L} ↦ t i.val)

open Classical in
/-- The active-root algebra over D_W. Source: DAG proof steps 6--7
(blueprint: lem-sfb-residual-root-tower-local-charts). -/
abbrev ResidualSplitRoots {I R : Type u} [Fintype I] [CommRing R]
    (p : ℕ) (t : I → R) (L : Finset I) :=
  FullParameterRootAlgebra p
    (fun i : L ↦ algebraMap R (ResidualInactiveRoots p t L) (t i.val))

open Classical in
/-- The inclusion of inactive roots into the active-root algebra. Source: DAG steps 6--7
(blueprint: lem-sfb-residual-root-tower-local-charts). -/
def residualInactiveInclusion {I R : Type u} [Fintype I] [CommRing R]
    (p : ℕ) (t : I → R) (L : Finset I) :
    ResidualInactiveRoots p t L →+* ResidualSplitRoots p t L :=
  algebraMap _ _

open Classical in
/-- Coefficients in the split presentation. Source: DAG proof step 6
(blueprint: lem-sfb-residual-root-tower-local-charts). -/
def residualSplitCoefficients {I R : Type u} [Fintype I] [CommRing R]
    (p : ℕ) (t : I → R) (L : Finset I) : R →+* ResidualSplitRoots p t L :=
  (residualInactiveInclusion p t L).comp (algebraMap R _)

open Classical in
/-- The split presentation under arbitrary ring base change. Its inner map is the recorded
root-preserving coefficient-change map; its outer map is the same construction on active
roots. Source: DAG proof step 9 (blueprint: lem-sfb-residual-root-tower-local-charts). -/
def residualSplitBaseMap {I R S : Type u} [Fintype I] [CommRing R] [CommRing S]
    (p : ℕ) (t : I → R) (L : Finset I) (f : R →+* S) :
    ResidualSplitRoots p t L →+* ResidualSplitRoots p (fun i ↦ f (t i)) L :=
  fullRootFamilyMap p
    (fun i : L ↦ algebraMap R (ResidualInactiveRoots p t L) (t i.val))
    (fun i : L ↦ algebraMap S
      (ResidualInactiveRoots p (fun j ↦ f (t j)) L) (f (t i.val)))
    (fullRootBaseMap p (fun i : {i : I // i ∉ L} ↦ t i.val) f)
    (fun i ↦ (fullRootFamilyMap_normalization p
      (fun i : {i : I // i ∉ L} ↦ t i.val)
      (fun i : {i : I // i ∉ L} ↦ f (t i.val)) f (fun _ ↦ rfl)).1 (t i.val))

open Classical in
/-- Exact coefficient, inactive-root, active-root and transition normalizations of the
comparison; principal-open equality specifies the scheme open structures, and the last
square is naturality for every ring map. Source: DAG proof steps 6--9
(blueprint: lem-sfb-residual-root-tower-local-charts). -/
def ResidualRootSplittingSpec {I : Type u} [Fintype I] (p : ℕ)
    (e : ∀ (R : Type u) [CommRing R] (t : I → R) (L : Finset I),
      FullParameterRootAlgebra p t ≃+* ResidualSplitRoots p t L) : Prop :=
  (∀ (R : Type u) [CommRing R] (t : I → R) (L : Finset I),
    (∀ a : R, e R t L (algebraMap R _ a) = residualSplitCoefficients p t L a) ∧
    (∀ (n : TameRootOrder p) (i : {i : I // i ∉ L}),
      e R t L (fullParameterRoot p t n i.val) =
        residualInactiveInclusion p t L
          (fullParameterRoot p (fun j : {j : I // j ∉ L} ↦ t j.val) n i)) ∧
    (∀ (n : TameRootOrder p) (i : L),
      e R t L (fullParameterRoot p t n i.val) =
        fullParameterRoot p
          (fun j : L ↦ algebraMap R (ResidualInactiveRoots p t L) (t j.val)) n i) ∧
    (∀ (n m : TameRootOrder p), n.val ∣ m.val → ∀ i : I,
      e R t L (fullParameterRoot p t m i) ^ (m.val / n.val) =
        e R t L (fullParameterRoot p t n i)) ∧
    (∀ (_hu : ∀ i : {i : I // i ∉ L}, IsUnit (t i.val)) (O : Finset I),
      (Spec.map (CommRingCat.ofHom (e R t L).toRingHom)) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen (algebraMap R _ (∏ i ∈ O, t i)) :
          (Spec (.of (FullParameterRootAlgebra p t))).Opens) =
        (PrimeSpectrum.basicOpen (residualSplitCoefficients p t L
          (∏ i ∈ O ∩ L, t i)) : (Spec (.of (ResidualSplitRoots p t L))).Opens))) ∧
  (∀ (R S : Type u) [CommRing R] [CommRing S] (t : I → R) (L : Finset I)
      (f : R →+* S),
    (residualSplitBaseMap p t L f).comp (e R t L).toRingHom =
      ((e S (fun i ↦ f (t i)) L).toRingHom).comp (fullRootBaseMap p t f))

open Classical in
/-- A chart's tensor coefficients R_W and surviving parameter values.
Source: DAG proof step 5 (blueprint: lem-sfb-residual-root-tower-local-charts). -/
abbrev ResidualChartTensor {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]
    (C : CommAlgCat.{u} A) := R ⊗[A] C

open Classical in
/-- The coefficient map from the affine chart to its tensor coefficients.
Source: Stacks 01I4 (blueprint: lem-sfb-residual-root-tower-local-charts). -/
def residualChartRightMap {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]
    (C : CommAlgCat.{u} A) : C →+* ResidualChartTensor (R := R) C :=
  (Algebra.TensorProduct.includeRight : C →ₐ[A] ResidualChartTensor (R := R) C).toRingHom

open Classical in
/-- The surviving parameters in R_W, using the left tensor coefficient map.
Source: DAG step 5 (blueprint: lem-sfb-residual-root-tower-local-charts). -/
def residualChartParameters {I A R : Type u} [Fintype I]
    [CommRing A] [CommRing R] [Algebra A R] (t : I → A) (C : CommAlgCat.{u} A) :
    I → ResidualChartTensor (R := R) C :=
  fun i ↦ algebraMap R (ResidualChartTensor (R := R) C) (algebraMap A R (t i))

open Classical in
/-- The inactive-root tower over W. Source: DAG step 5, Stacks 00UB/00UC
(blueprint: lem-sfb-residual-root-tower-local-charts). -/
def residualInactiveChartMap {I A R : Type u} [Fintype I]
    [CommRing A] [CommRing R] [Algebra A R] (p : ℕ) (t : I → A)
    (C : CommAlgCat.{u} A) (L : Finset I) :
    C →+* ResidualInactiveRoots p (residualChartParameters (R := R) t C) L :=
  (algebraMap (ResidualChartTensor (R := R) C) _).comp (residualChartRightMap C)

open Classical in
/-- The split tower over W. Source: DAG steps 6--7
(blueprint: lem-sfb-residual-root-tower-local-charts). -/
def residualSplitChartMap {I A R : Type u} [Fintype I]
    [CommRing A] [CommRing R] [Algebra A R] (p : ℕ) (t : I → A)
    (C : CommAlgCat.{u} A) (L : Finset I) :
    C →+* ResidualSplitRoots p (residualChartParameters (R := R) t C) L :=
  (residualSplitCoefficients p (residualChartParameters (R := R) t C) L).comp
    (residualChartRightMap C)

open Classical in
/-- The full residual root tower on a chart is the split presentation, over that chart.
Both pullback projections are fixed, so this is the canonical scheme comparison.
Source: DAG proof steps 5--9 (blueprint: lem-sfb-residual-root-tower-local-charts). -/
def ResidualRootChartPresentation {I A R : Type u} [Fintype I]
    [CommRing A] [CommRing R] [Algebra A R] (p : ℕ) (t : I → A)
    (C : CommAlgCat.{u} A) (L : Finset I)
    (e : ∀ (S : Type u) [CommRing S] (s : I → S) (M : Finset I),
      FullParameterRootAlgebra p s ≃+* ResidualSplitRoots p s M) : Prop :=
  WeaklyEtale (Spec.map (CommRingCat.ofHom
    (residualInactiveChartMap (R := R) p t C L))) ∧
  IsAffineHom (Spec.map (CommRingCat.ofHom
    (residualInactiveChartMap (R := R) p t C L))) ∧
  ∃ d : Spec (.of (ResidualSplitRoots p (residualChartParameters (R := R) t C) L)) ≅
    pullback (Spec.map (CommRingCat.ofHom
      ((algebraMap R (FullParameterRootAlgebra p (fun i ↦ algebraMap A R (t i)))).comp
        (algebraMap A R))))
      (Spec.map (CommRingCat.ofHom (algebraMap A C))),
    d.hom ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom
      (((e (ResidualChartTensor (R := R) C)
        (residualChartParameters (R := R) t C) L).toRingHom).comp
        (fullRootBaseMap p (fun i ↦ algebraMap A R (t i))
          (algebraMap R (ResidualChartTensor (R := R) C))))) ∧
    d.hom ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom
      (residualSplitChartMap (R := R) p t C L))

open Classical in
/-- Local active-parameter charts on every residual coordinate face of a full root tower.
Source: Stacks 0BIA, 00UB, 00UC and blueprint direct-images proof (3)
(blueprint: lem-sfb-residual-root-tower-local-charts).

Proof:
1. Quasi-compactness of the affine source and separatedness of Y make the etale chart
   finite type (lem-weil-pbc-qcqs-morphism-permanence, lem-kun-etale-lfp). Affineness gives
   separatedness. Quotient generators give finite type for the face. The SNC intersection
   condition gives regularity (def-trf-strict-normal-crossings-boundary).
2. At a point the vanishing branch ideals are distinct height-one primes. Apply
   lem-sfb-transverse-prime-ideal-parameters and rem-pc-regular-normal. Equality of principal
   ideals in the regular local domain makes the actual equations unit multiples of the
   resulting parameters, so scaling supplies the named equations as distinct parameters.
3. Quotient-localization identifies the face local ring with the quotient by its selected
   parameters (lem-weil-pbc-localization-at-prime-of-quotient). Permute them to the start;
   lem-weil-pbc-regular-local-generators-regular-sequence gives the residual parameter list.
4. Apply lem-sfb-snc-boundary-parameter-criterion to the product of surviving parameters.
   Use lem-sfb-snc-labelled-root-algebra-geometry to shrink affine neighbourhoods until each
   active branch is integral and every inactive equation is a unit; these opens cover.
5. Identify R_W with the indicated tensor product by the affine fibre-product formula.
   The chart is weakly etale by base change. Every prime-to-p order is a unit in characteristic
   p. Successive unit-binomial adjunctions are finite etale (lem-sfb-unit-binomial-finite-etale).
   Apply lem-weil-pbc-ind-etale-stability to their filtered colimit, then weakly etale
   composition, to obtain the affine pro-etale map Spec D_W to W.
6. By lem-sfb-root-tower-profinite-base-change, localizing the full residual tower gives
   the full root algebra over R_W. Send inactive roots to y, active roots to z, and fix
   coefficients. Polynomial evaluation and quotient descent give the map, respecting all
   power transitions (def-weil-pbc-mv-polynomial-ring, def-weil-pbc-algebra-hom-quotient).
7. In reverse send y and z to the same original root. Both composites fix coefficients
   and generators, hence are identities by quotient and colimit uniqueness. Finitely many
   orders have a common prime-to-p multiple (def-weil-pbc-category-colimit).
8. The product of inactive selected parameters is a unit. Thus inverting the selected
   product equals inverting its active part (def-weil-ring-localization-away), with the
   scheme open structure fixed by lem-weil-pbc-basic-open-pullback.
9. Coefficients and named roots agree on both sides of every base-change square, proving
   naturality including all transitions. The profinite formula of
   lem-sfb-root-tower-profinite-base-change identifies R_J tensor LC(P,Z) with U[P] on the
   face; repeat step 5. Empty faces have the empty cover. Empty active/inactive sets give
   their coefficient rings. The zero ring, empty boundary and empty profinite set are allowed.
-/
theorem residualRootTower_localCharts
    {I A R k : Type u} [Fintype I] [CommRing A] [CommRing R] [Algebra A R]
    [Field k] (p : ℕ) (hp : p.Prime) [CharP k p]
    (Y : Scheme.{u}) (g : Y ⟶ Spec (.of k)) (hY : IsRegularScheme Y)
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (b : Spec (.of A) ⟶ Y) [Etale b]
    (t : I → A) (ht : HasResidualSNCEquations t)
    [WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A R)))] (J : Finset I) :
    IsRegularScheme (Spec (.of A)) ∧ IsSeparated (b ≫ g) ∧
    LocallyOfFiniteType (b ≫ g) ∧ QuasiCompact (b ≫ g) ∧
    IsRegularScheme (Spec (.of (ResidualFaceRing t J))) ∧
    IsSeparated (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (residualFaceIdeal t J))) ≫
      b ≫ g) ∧
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (residualFaceIdeal t J))) ≫ b ≫ g) ∧
    QuasiCompact
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (residualFaceIdeal t J))) ≫ b ≫ g) ∧
    ∃ e : ∀ (S : Type u) [CommRing S] (s : {i : I // i ∉ J} → S)
        (L : Finset {i : I // i ∉ J}),
      FullParameterRootAlgebra p s ≃+* ResidualSplitRoots p s L,
      ResidualRootSplittingSpec p e ∧
      ∃ (V : Type u) (C : V → CommAlgCat.{u} (ResidualFaceRing t J))
        (L : V → Finset {i : I // i ∉ J}),
        (∀ v, IsOpenImmersion (Spec.map (CommRingCat.ofHom
          (algebraMap (ResidualFaceRing t J) (C v))))) ∧
        (∀ x : Spec (.of (ResidualFaceRing t J)), ∃ (v : V) (y : Spec (.of (C v))),
          Spec.map (CommRingCat.ofHom (algebraMap (ResidualFaceRing t J) (C v))) y = x) ∧
        (∀ v,
          (∀ i : {i : I // i ∉ J}, i ∉ L v →
            IsUnit (algebraMap (ResidualFaceRing t J) (C v) (residualFaceParameters t J i))) ∧
          HasResidualSNCEquations (fun i : L v ↦
            algebraMap (ResidualFaceRing t J) (C v) (residualFaceParameters t J i.val)) ∧
          ResidualParametersAtPrimes (fun i : {i : I // i ∉ J} ↦
            algebraMap (ResidualFaceRing t J) (C v) (residualFaceParameters t J i)) ∧
          ResidualRootChartPresentation (R := ResidualFaceCoefficients (R := R) t J)
            p (residualFaceParameters t J) (C v) (L v) e ∧
          ∀ P : Profinite.{u},
            ResidualRootChartPresentation
              (R := rootTestRing (ResidualFaceCoefficients (R := R) t J) P)
              p (residualFaceParameters t J) (C v) (L v) e) := by
  sorry

end AlgebraicGeometry.ProEtale
