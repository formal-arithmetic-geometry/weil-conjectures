module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.CoordinatePrimeResidueField
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite

/-!
# A quasi-finite affine chart with prescribed coordinate prime

Source: Stacks Project, More on Morphisms, Tag 052E, first proof paragraph, and Algebra,
Tag 0520 (blueprint: lem-trf-coordinate-prime-affine-chart-realization).
The principal opens and affine space use their canonical Mathlib identifications with
localized spectra and the polynomial spectrum. The residue-field isomorphism is required
to commute with the actual structural residue-field map.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry

noncomputable section

private theorem quasiFinite_of_coordinate_chart_primes
    {B C : Type u} [CommRing B] [CommRing C] [Algebra B C] [Algebra.FiniteType B C]
    (hq : ∀ q : PrimeSpectrum C, Algebra.IsQuasiFiniteAtPrime B C q) :
    Algebra.QuasiFinite B C := by
  apply Algebra.QuasiFinite.iff_finite_comap_preimage_singleton.mpr
  intro p
  let E := PrimeSpectrum.preimageHomeomorphFiber B C p
  have : DiscreteTopology (PrimeSpectrum (p.asIdeal.Fiber C)) :=
    discreteTopology_iff_isOpen_singleton.mpr fun Q ↦ by
      obtain ⟨⟨q, hp⟩, rfl⟩ := E.surjective Q
      have hp' : q.comap (algebraMap B C) = p := hp
      subst p
      exact hq q
  have : Finite (PrimeSpectrum (p.asIdeal.Fiber C)) := finite_of_compact_of_discrete
  have : Finite (PrimeSpectrum.comap (algebraMap B C) ⁻¹' {p}) :=
    E.toEquiv.finite_iff.mpr inferInstance
  exact Set.toFinite _

/-- The chart induced by the specified polynomial ring map, using `D(d) = Spec A_d` and
`AffineSpace.SpecIso`. Source: Stacks 052E, first proof paragraph, translating 0520
(blueprint: lem-trf-coordinate-prime-affine-chart-realization). -/
def coordinatePrimeChartMap {R A : Type u} [CommRing R] [CommRing A]
    (f : R) (d : A) (n : ℕ)
    (θ : MvPolynomial (ULift.{u} (Fin n)) (Localization.Away f) →+* Localization.Away d) :
    (Scheme.Opens.toScheme (X := Spec (.of A)) (PrimeSpectrum.basicOpen d)) ⟶
      AffineSpace (ULift.{u} (Fin n)) (Spec (.of (Localization.Away f))) :=
  (basicOpenIsoSpecAway (R := .of A) d).hom ≫ Spec.map (CommRingCat.ofHom θ) ≫
    (AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of (Localization.Away f))).inv

/-- The structural map from the chart's affine space to `Spec R`, through `Spec R_f`.
Source: Stacks 052E, first proof paragraph, translating 0520
(blueprint: lem-trf-coordinate-prime-affine-chart-realization). -/
def coordinatePrimeChartBaseProjection {R : Type u} [CommRing R] (f : R) (n : ℕ) :
    AffineSpace (ULift.{u} (Fin n)) (Spec (.of (Localization.Away f))) ⟶ Spec (.of R) :=
  (AffineSpace (ULift.{u} (Fin n)) (Spec (.of (Localization.Away f))) ↘
    Spec (.of (Localization.Away f))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))

/-- Realize the localized coordinate-prime ring chart as a finite-type quasi-finite
scheme chart, with finite discrete scheme fibres and the prescribed rational residue field.
Source: Stacks 052E, first proof paragraph, translating 0520
(blueprint: lem-trf-coordinate-prime-affine-chart-realization).

Proof:
1. The basic-open calculation (lem-weil-pbc-affine-open-section-vanishing-prime) puts the
   marked source and base points in D(d) and D(f). Since rho(f) is a unit in A_d, no prime
   of A_d contains it, so D(d) maps into D(f). The localization universal property
   (lem-weil-pbc-ring-localization-universal-property) gives the specified map R_f -> A_d.
2. Identify affine space with Spec of the polynomial ring (def-sbc-affine-space).
   Contravariant Spec functoriality (def-weil-affine-spectrum), and the constants-map
   compatibility of theta, give the over-S_0 equation.
3. The affine Spec criterion and theta's finite type give local finite type.
   A map of affine schemes is affine by
   lem-weil-pbc-morphism-affine-schemes-affine and hence quasi-compact by
   lem-weil-pbc-affine-morphism-permanence. Transport along the two canonical isomorphisms.
4. The primewise hypothesis makes every algebra fibre spectrum discrete. These spectra
   are compact, hence finite, so the ring map is quasi-finite by the finite-fibres criterion.
   The affine quasi-finite criterion and transport across isomorphisms give Mathlib's
   LocallyQuasiFinite for the chart. Its points are isolated in their fibres, yielding
   the project IsQuasiFinite predicate. The finite-fibres theorem and
   Scheme.Hom.discreteTopology_fiber_and_quasiFiniteAt give finite discrete scheme fibres.
5. The basic-open isomorphism's structural equation identifies the contraction of the
   marked localized prime with q_A. Extension of contraction is the identity for a
   localization, hence this prime is q_A A_d. Cancel the affine-space isomorphisms
   and use the assumed contraction formula to identify its image with P. Evaluating
   the structural equation over Spec R identifies the base point with the image of q_A.
6. Apply coordinatePrimeAffineSpace_residueField to this image point, using its prime
   formula and the base-point equality. This is exactly the remaining coordinate-prime
   calculation (lem-trf-coordinate-prime-rational-residue-field), independent of the
   source chart and quasi-finiteness assumptions. It gives the isomorphism compatible
   with the actual structural residue-field map, including when r = 0.
-/
theorem coordinatePrimeAffineChart_realization
    {R A : Type u} [CommRing R] [CommRing A] (ρ : R →+* A)
    (qA : PrimeSpectrum A) (f : R) (d : A)
    (hf : f ∉ (qA.comap ρ).asIdeal) (hd : d ∉ qA.asIdeal)
    (hunit : IsUnit (algebraMap A (Localization.Away d) (ρ f)))
    (n r : ℕ) (hrn : r ≤ n)
    (θ : MvPolynomial (ULift.{u} (Fin n)) (Localization.Away f) →+* Localization.Away d)
    (hθ : θ.comp MvPolynomial.C =
      IsLocalization.Away.lift f (S := Localization.Away f)
        (g := (algebraMap A (Localization.Away d)).comp ρ) hunit)
    (hft : θ.FiniteType)
    (hqf : ∀ Q : PrimeSpectrum (Localization.Away d),
      @Algebra.IsQuasiFiniteAtPrime _ _ _ _ θ.toAlgebra hft Q)
    (hprime : (qA.asIdeal.map (algebraMap A (Localization.Away d))).comap θ =
      (qA.comap ρ).asIdeal.map (MvPolynomial.C.comp (algebraMap R (Localization.Away f))) ⊔
        Ideal.span {x | ∃ i : ULift.{u} (Fin n), r ≤ i.down.val ∧ x = MvPolynomial.X i}) :
    Spec.map (CommRingCat.ofHom ρ) qA ∈ PrimeSpectrum.basicOpen f ∧
    qA ∈ PrimeSpectrum.basicOpen d ∧
    (PrimeSpectrum.basicOpen d).carrier ⊆
      (Spec.map (CommRingCat.ofHom ρ)) ⁻¹' (PrimeSpectrum.basicOpen f).carrier ∧
    coordinatePrimeChartMap f d n θ ≫
        (AffineSpace (ULift.{u} (Fin n)) (Spec (.of (Localization.Away f))) ↘
          Spec (.of (Localization.Away f))) =
      (basicOpenIsoSpecAway (R := .of A) d).hom ≫
        Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.lift f (S := Localization.Away f)
            (g := (algebraMap A (Localization.Away d)).comp ρ) hunit)) ∧
    LocallyOfFiniteType (coordinatePrimeChartMap f d n θ) ∧
    QuasiCompact (coordinatePrimeChartMap f d n θ) ∧
    (coordinatePrimeChartMap f d n θ).IsQuasiFinite ∧
    (∀ t : AffineSpace (ULift.{u} (Fin n)) (Spec (.of (Localization.Away f))),
      Finite ((coordinatePrimeChartMap f d n θ).fiber t) ∧
        DiscreteTopology ((coordinatePrimeChartMap f d n θ).fiber t)) ∧
    ∀ z0 : Scheme.Opens.toScheme (X := Spec (.of A)) (PrimeSpectrum.basicOpen d),
      z0.val = qA →
      ((AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of (Localization.Away f))).hom
        (coordinatePrimeChartMap f d n θ z0)).asIdeal =
        (qA.comap ρ).asIdeal.map (MvPolynomial.C.comp (algebraMap R (Localization.Away f))) ⊔
          Ideal.span {x | ∃ i : ULift.{u} (Fin n), r ≤ i.down.val ∧ x = MvPolynomial.X i} ∧
      coordinatePrimeChartBaseProjection f n (coordinatePrimeChartMap f d n θ z0) =
        Spec.map (CommRingCat.ofHom ρ) qA ∧
      ∃ e : (AffineSpace (ULift.{u} (Fin n)) (Spec (.of (Localization.Away f)))).residueField
          (coordinatePrimeChartMap f d n θ z0) ≃+*
          FractionRing (MvPolynomial (Fin r) ((Spec (.of R)).residueField
            (coordinatePrimeChartBaseProjection f n (coordinatePrimeChartMap f d n θ z0)))),
        ∀ a : (Spec (.of R)).residueField
            (coordinatePrimeChartBaseProjection f n (coordinatePrimeChartMap f d n θ z0)),
          e (((coordinatePrimeChartBaseProjection f n).residueFieldMap
            (coordinatePrimeChartMap f d n θ z0)).hom a) = algebraMap _ _ a := by
  let B := MvPolynomial (ULift.{u} (Fin n)) (Localization.Away f)
  let C := Localization.Away d
  let : Algebra B C := θ.toAlgebra
  let : Algebra.FiniteType B C := hft
  have hq : θ.QuasiFinite := quasiFinite_of_coordinate_chart_primes hqf
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom θ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hft
  have : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom θ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mpr hq
  have hlft : LocallyOfFiniteType (coordinatePrimeChartMap f d n θ) := by
    dsimp [coordinatePrimeChartMap]
    infer_instance
  have hqc : QuasiCompact (coordinatePrimeChartMap f d n θ) := by
    dsimp [coordinatePrimeChartMap]
    infer_instance
  have hlqf : LocallyQuasiFinite (coordinatePrimeChartMap f d n θ) := by
    dsimp [coordinatePrimeChartMap]
    infer_instance
  have hover : coordinatePrimeChartMap f d n θ ≫
      (AffineSpace (ULift.{u} (Fin n)) (Spec (.of (Localization.Away f))) ↘
        Spec (.of (Localization.Away f))) =
      (basicOpenIsoSpecAway (R := .of A) d).hom ≫
        Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.lift f (S := Localization.Away f)
            (g := (algebraMap A (Localization.Away d)).comp ρ) hunit)) := by
    dsimp [coordinatePrimeChartMap]
    rw [Category.assoc, Category.assoc, AffineSpace.SpecIso_inv_over,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ]
  have hbase : coordinatePrimeChartMap f d n θ ≫ coordinatePrimeChartBaseProjection f n =
      Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen d) ≫
        Spec.map (CommRingCat.ofHom ρ) := by
    dsimp [coordinatePrimeChartBaseProjection]
    rw [← Category.assoc, hover, Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    have hc : (IsLocalization.Away.lift f (S := Localization.Away f)
        (g := (algebraMap A (Localization.Away d)).comp ρ) hunit).comp
        (algebraMap R (Localization.Away f)) =
        (algebraMap A (Localization.Away d)).comp ρ := by
      ext a
      exact IsLocalization.Away.lift_eq f hunit a
    rw [hc, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc,
      basicOpenIsoSpecAway_hom_SpecMap]
  refine ⟨hf, hd, ?_, hover, hlft, hqc, ?_, ?_, ?_⟩
  · intro x hx
    let z : Scheme.Opens.toScheme (X := Spec (.of A)) (PrimeSpectrum.basicOpen d) := ⟨x, hx⟩
    let Q := (basicOpenIsoSpecAway (R := .of A) d).hom z
    have hQ : Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away d))) Q = x := by
      change ((basicOpenIsoSpecAway (R := .of A) d).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away d)))) z = x
      rw [basicOpenIsoSpecAway_hom_SpecMap]
      rfl
    change ρ f ∉ x.asIdeal
    rw [← hQ]
    exact Q.asIdeal.notMem_of_isUnit hunit
  · exact ⟨hlft, hqc, fun x ↦
      Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp
        ((coordinatePrimeChartMap f d n θ).quasiFiniteAt x)⟩
  · intro t
    obtain ⟨hfin, hdis, _⟩ :=
      (coordinatePrimeChartMap f d n θ).discreteTopology_fiber_and_quasiFiniteAt t
        ((coordinatePrimeChartMap f d n θ).finite_preimage_singleton t)
    exact ⟨hfin, hdis⟩
  · intro z0 hz0
    have hloc : ((basicOpenIsoSpecAway (R := .of A) d).hom z0).asIdeal =
        qA.asIdeal.map (algebraMap A (Localization.Away d)) := by
      have hc : (((basicOpenIsoSpecAway (R := .of A) d).hom z0).asIdeal).comap
          (algebraMap A (Localization.Away d)) = qA.asIdeal := by
        have hh := congrArg (fun m ↦ m z0) (basicOpenIsoSpecAway_hom_SpecMap (R := .of A) d)
        exact congrArg PrimeSpectrum.asIdeal (hh.trans hz0)
      rw [← hc]
      exact (IsLocalization.map_under (Submonoid.powers d) (Localization.Away d) _).symm
    have hpoint : ((AffineSpace.SpecIso (ULift.{u} (Fin n))
        (.of (Localization.Away f))).hom (coordinatePrimeChartMap f d n θ z0)).asIdeal =
        (qA.comap ρ).asIdeal.map (MvPolynomial.C.comp (algebraMap R (Localization.Away f))) ⊔
          Ideal.span {x | ∃ i : ULift.{u} (Fin n), r ≤ i.down.val ∧ x = MvPolynomial.X i} := by
      dsimp [coordinatePrimeChartMap]
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      change (((basicOpenIsoSpecAway (R := .of A) d).hom z0).asIdeal).comap θ = _
      rw [hloc, hprime]
      rfl
    have hb : coordinatePrimeChartBaseProjection f n (coordinatePrimeChartMap f d n θ z0) =
        Spec.map (CommRingCat.ofHom ρ) qA := by
      have hh := congrArg (fun m ↦ m z0) hbase
      simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, hz0] using hh
    refine ⟨hpoint, hb, ?_⟩
    apply coordinatePrimeAffineSpace_residueField f n r hrn
      (coordinatePrimeChartMap f d n θ z0)
    change _ = (coordinatePrimeChartBaseProjection f n
      (coordinatePrimeChartMap f d n θ z0)).asIdeal.map _ ⊔ _
    rw [hb]
    exact hpoint

end

end AlgebraicGeometry
