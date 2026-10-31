/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

import WeilConjectures.AlgebraicGeometry.Affine.AffineChartStalkDifferentials
import WeilConjectures.AlgebraicGeometry.Affine.AffineFibrePointDimension
import WeilConjectures.RingTheory.FibreLocalization.FibreCotangentLocalizationGenerators
import WeilConjectures.RingTheory.SmoothAtPrimeOfDifferentialsDimensionBound
import WeilConjectures.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Modules.GenericRank
import WeilConjectures.AlgebraicGeometry.RestrictStalkInvSmul

/-!
# Smoothness at a point from relative differentials

Source: Stacks Project, Morphisms, Tag 01V9 (lemma-smooth-at-point), (1) iff (3),
and Definition 01V5 (blueprint: lem-trf-smooth-at-point-differential-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

private theorem span_eq_top_of_semilinear_equiv
    {R T M N : Type*} [CommRing R] [CommRing T]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module T N]
    (e : M ≃+ N) (phi : R →+* T)
    (he : ∀ r m, e (r • m) = phi r • e m)
    {n : ℕ} (v : Fin n → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span T (Set.range (e ∘ v)) = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨m, rfl⟩ := e.surjective z
  have hm : m ∈ Submodule.span R (Set.range v) := by rw [hv]; trivial
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp
  | add y z hy hz hy' hz' => simpa using Submodule.add_mem _ hy' hz'
  | smul r y hy hy' => rw [he]; exact Submodule.smul_mem _ _ hy'

private theorem generators_of_smooth_relative_dimension
    {X S : Scheme.{u}} (f : X ⟶ S) (O : X.Opens) (x : X) (hx : x ∈ O)
    (d : ℕ) [SmoothOfRelativeDimension d (O.ι ≫ f)] :
    ∃ v : Fin d → (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        f.relativeDifferentials,
      Submodule.span (X.presheaf.stalk x) (Set.range v) = ⊤ := by
  classical
  let z : O.toScheme := ⟨x, hx⟩
  let g := O.ι ≫ f
  have := g.isFiniteLocallyFreeOfRank_relativeDifferentials d
  obtain ⟨I, U, hU, e⟩ :=
    SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}.1
      (inferInstance : g.relativeDifferentials.IsFiniteLocallyFreeOfRank d)
  obtain ⟨V, k, ⟨i, ⟨a⟩⟩, hzV⟩ := hU ⊤ z trivial
  obtain ⟨ei⟩ := e i
  obtain ⟨b, hb⟩ := Scheme.Modules.exists_basis_stalk_of_over_iso_free ei (a.le hzV)
  let basis := b.reindex Equiv.ulift
  let E := ((RingedSpace.moduleStalkFunctor O.toScheme.toRingedSpace z).mapIso
    (f.relativeDifferentialsRestrictIso O.ι)).symm.toLinearEquiv
  let c := (Scheme.Modules.restrictStalkNatIso O.ι z).app f.relativeDifferentials
  let T : (RingedSpace.moduleStalkFunctor O.toScheme.toRingedSpace z).obj
      g.relativeDifferentials ≃+
        (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj f.relativeDifferentials :=
    E.toAddEquiv.trans c.addCommGroupIsoToAddEquiv
  refine ⟨T ∘ basis, span_eq_top_of_semilinear_equiv T
    (inv (O.ι.stalkMap z)).hom ?_ basis basis.span_eq⟩
  intro r m
  change c.hom (E (r • m)) = (inv (O.ι.stalkMap z)) r •
    (show (RingedSpace.moduleStalkFunctor X.toRingedSpace (O.ι z)).obj
      f.relativeDifferentials from c.hom (E m))
  rw [E.map_smul]
  apply (ConcreteCategory.bijective_of_isIso c.inv).1
  change c.inv (c.hom (r • E m)) =
    (Scheme.Modules.restrictStalkNatIso O.ι z).inv.app f.relativeDifferentials
      ((inv (O.ι.stalkMap z)) r •
        (show (RingedSpace.moduleStalkFunctor X.toRingedSpace (O.ι z)).obj
          f.relativeDifferentials from c.hom (E m)))
  rw [Scheme.Modules.restrictStalkNatIso_inv_smul]
  simp only [Iso.hom_inv_id_apply, IsIso.inv_hom_id_apply]
  congr 1
  exact (Iso.hom_inv_id_apply c (E m)).symm

/-- A locally finitely presented morphism is smooth on a neighbourhood of `x` precisely when
its local ring map at `x` is flat and its differential stalk has a spanning family of size
at most the dimension of the fibre at `x`. The fibre point is the canonical `f.asFiber x`.
Source: Stacks Project, Morphisms, Tag 01V9, (1) iff (3), and Definition 01V5
(blueprint: lem-trf-smooth-at-point-differential-criterion).

Proof:
1. If `f` is smooth on an open neighbourhood, its stalk map is flat by
   `lem-pc-smooth-flat` and `def-weil-flat-morphism`. Apply
   `lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension` to the restriction.
   The open fibre identification (`lem-weil-pbc-open-fibre-product`) and
   `lem-weil-pbc-dimension-at-point-open-subspace` preserve the fibre dimension.
   Use `def-sc-relative-differential-sheaf` and
   `lem-weil-pbc-spec-tilde-stalk-localization` to localize the differential basis.
   Its localized vectors span the stalk, with the same number of generators.
2. Conversely, choose finite-presentation affine neighbourhoods `W = Spec A` and
   `V = Spec R` by `def-sbc-locally-finite-presentation`. Write `q` for the prime of `x`
   and `p` for its contraction, using
   `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`. The stalk identifications
   `lem-weil-pbc-affine-open-stalk-localization` and
   `lem-weil-pbc-spec-map-stalk-localization` give flatness of `R_p → A_q`.
   The affine differential description and tilde-stalk localization identify the
   differential stalk with the localization of `Omega A/R`, preserving its generators.
3. Set `k = kappa(p)` and `F = k ⊗[R] A`. Use
   `lem-weil-pbc-affine-open-stalk-localization`,
   `lem-weil-pbc-spec-residue-field-identification`,
   `lem-weil-pbc-open-fibre-product`, and `lem-weil-pbc-fibre-product-affine-spectra`
   to identify `Spec F` with an open of the scheme fibre. The prime `Q` above `x`
   is the kernel of `F → kappa(q)`. Its contraction is `q`, and its dimension is `d`
   by `lem-weil-pbc-dimension-at-point-open-subspace` and `def-pc-scheme-fibre`.
   The algebra `F` is finite type over `k`, by base changing a finite presentation,
   so `lem-kun-dimension-finite-type` makes this dimension finite and nonnegative.
4. By `lem-weil-pbc-kahler-differentials-base-change`, tensoring the localized
   differential module with `L = kappa(Q)` gives `Omega F/k` tensored with `L`.
   The comparison sends `(omega/a) ⊗ lambda` to `(1 ⊗ omega) ⊗ (lambda/a)`;
   its inverse sends `(b ⊗ omega) ⊗ lambda` to `(omega/1) ⊗ (b*lambda)`.
   Tensor balancing and localization relations make these inverse. The images
   of the stalk generators span this vector space, so its dimension is at most `d`.
5. Apply `lem-weil-pbc-differentials-dimension-bound-smooth-at-prime` to `F/k` at `Q`.
   Apply `lem-weil-pbc-flat-smooth-fibre-smooth-at-prime` with localization parameter
   one to the original finite-presentation map `R → A`. Thus it is smooth at `q`.
   By `def-weil-pbc-singular-ideal`, some `g` outside `q` makes `R → A_g` smooth.
6. The principal localization is an open neighbourhood of `x` by
   `lem-weil-pbc-principal-localization-open-immersion`, and its map to `V` is smooth by
   `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`. It is locally finitely presented
   over `S` by `def-sbc-locally-finite-presentation`. For a first-order thickening
   lifting problem over `S`, its two schemes have the same points
   (`def-sbc-first-order-thickening`), so the larger scheme also factors through `V`
   (`def-weil-open-immersion`). Formal smoothness over `V` supplies the lift
   (`def-sbc-formally-smooth`). Thus the neighbourhood map to `S` is smooth by
   `def-sbc-smooth-morphisms`, as required. -/
theorem smoothAtPoint_iff_flat_stalkMap_and_differentials_generators
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X) :
    (∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) ↔
      (f.stalkMap x).hom.Flat ∧
        ∃ (n : ℕ)
          (v : Fin n → (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
            f.relativeDifferentials),
          (n : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.asFiber x) ∧
            Submodule.span (X.presheaf.stalk x) (Set.range v) = ⊤ := by
  classical
  constructor
  · rintro ⟨U, hx, hsm⟩
    have := hsm
    let g := U.ι ≫ f
    obtain ⟨V, W, hV, hW, hxW, hWV, d, hd⟩ :=
      Smooth.exists_smoothOfRelativeDimension_resLE g ⟨x, hx⟩
    have : SmoothOfRelativeDimension d (W.ι ≫ g) := by
      rw [← Scheme.Hom.resLE_comp_ι g hWV]
      have := hd
      have h : SmoothOfRelativeDimension (d + 0) (g.resLE V W hWV ≫ V.ι) :=
        inferInstance
      simpa using h
    let j := W.ι ≫ U.ι
    let O := j.opensRange
    have hxO : x ∈ O := ⟨⟨⟨x, hx⟩, hxW⟩, rfl⟩
    have : SmoothOfRelativeDimension d (j ≫ f) := by
      simpa only [j, g, Category.assoc] using
        (inferInstance : SmoothOfRelativeDimension d (W.ι ≫ g))
    have : SmoothOfRelativeDimension d (O.ι ≫ f) := by
      rw [← j.isoOpensRange_inv_comp, Category.assoc]
      have h : SmoothOfRelativeDimension (0 + d) (j.isoOpensRange.inv ≫ (j ≫ f)) :=
        inferInstance
      simpa using h
    have hflatU := Flat.stalkMap g (⟨x, hx⟩ : U.toScheme)
    have hflat : (f.stalkMap x).hom.Flat := by
      rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at hflatU
      exact (RingHom.Flat.respectsIso.cancel_right_isIso _ (U.ι.stalkMap ⟨x, hx⟩)).mp
        hflatU
    obtain ⟨v, hv⟩ := generators_of_smooth_relative_dimension f O x hxO d
    refine ⟨hflat, d, v, ?_, hv⟩
    let B := (f.fiberι (f x)) ⁻¹ᵁ O
    have hxB : f.asFiber x ∈ B := by
      change f.fiberι _ (f.asFiber x) ∈ O
      simpa using hxO
    have hpb : IsPullback (f.fiberι (f x) ∣_ O)
        (B.ι ≫ f.fiberToSpecResidueField (f x))
        (O.ι ≫ f) (S.fromSpecResidueField (f x)) :=
      (isPullback_morphismRestrict (f.fiberι (f x)) O).paste_vert
        (IsPullback.of_hasPullback _ _)
    have : SmoothOfRelativeDimension d (B.ι ≫ f.fiberToSpecResidueField (f x)) := by
      have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
      exact MorphismProperty.of_isPullback hpb inferInstance
    have hdim := topologicalKrullDimAt_eq_of_smoothOfRelativeDimension
      (B.ι ≫ f.fiberToSpecResidueField (f x)) d (⟨f.asFiber x, hxB⟩ : B)
    rw [IsOpen.topologicalKrullDimAt_eq B.isOpen hxB] at hdim
    exact hdim.ge
  · rintro ⟨hflat, n, v, hn, hv⟩
    obtain ⟨W, V, hW, hV, hx, hWV, q, hq, hfp, hp, e, h, theta,
      he, hh, hmap, hlin, hd, hflat', hgen⟩ :=
      exists_affineChart_stalk_differentials f x
    let R := Γ(S, V)
    let A := Γ(X, W)
    let := (f.appLE V W hWV).hom.toAlgebra
    have : Algebra.FinitePresentation R A := hfp
    let p := PrimeSpectrum.comap (algebraMap R A) q
    have hxq : hW.fromSpec q = x := by
      rw [hq]
      exact hW.fromSpec_primeIdealOf ⟨x, hx⟩
    have hxp : hV.fromSpec p = f x := by
      change hV.fromSpec (q.comap (f.appLE V W hWV).hom) = f x
      rw [hp]
      exact hV.fromSpec_primeIdealOf ⟨f x, hWV hx⟩
    obtain ⟨ef, psi, Q, j, hef, hpsi, hker, hcontract, hj, hji, hjf, hrange,
      hjQ, hft, hdim, hfinite, hpresentation⟩ :=
      affine_fibre_point_dimension X S f x R A hW.fromSpec hV.fromSpec
        (hV.SpecMap_appLE_fromSpec f hW hWV) q p hxq hxp rfl
    have hQ : Q = PrimeSpectrum.preimageEquivFiber R A p ⟨q, rfl⟩ := by
      apply (PrimeSpectrum.preimageEquivFiber R A p).symm.injective
      apply Subtype.ext
      simpa using (PrimeSpectrum.ext hcontract)
    subst Q
    have : Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber A) :=
      RingHom.finiteType_algebraMap.mp hft
    obtain ⟨m, hm⟩ := (hgen n).mp ⟨v, hv⟩
    obtain ⟨rho, hrho, hcomp⟩ :=
      KaehlerDifferential.FibreLocalization.comparison (R := R) q.asIdeal
    let := KaehlerDifferential.FibreLocalization.fibreAlgebra (R := R) q.asIdeal
    let := rho.toAlgebra
    obtain ⟨comparison, hc, hci, hbound⟩ := hcomp
    obtain ⟨hspan, hfd, hle⟩ := hbound n m hm
    let F := p.asIdeal.Fiber A
    let Q := PrimeSpectrum.preimageEquivFiber R A p ⟨q, rfl⟩
    let L := Q.asIdeal.ResidueField
    let N := KaehlerDifferential p.asIdeal.ResidueField F
    have hfinrank : Module.finrank L (L ⊗[F] N) ≤ n := by
      let : Module L (N ⊗[F] L) :=
        (TensorProduct.comm F N L).toAddEquiv.module L
      have hEq := ((TensorProduct.comm F N L).toAddEquiv.linearEquiv L).finrank_eq
      exact hEq ▸ hle
    have hsmF : Algebra.IsSmoothAtPrime p.asIdeal.ResidueField Q :=
      Algebra.isSmoothAtPrime_of_finrank_kaehlerDifferential_le Q
        ((show (Module.finrank L (L ⊗[F] N) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞)
          by exact_mod_cast hfinrank).trans (hn.trans_eq hdim.symm))
    have hsmA : Algebra.IsSmoothAtPrime R q :=
      flat_smooth_fibre_smooth_at_prime q
        ⟨1, q.asIdeal.one_notMem, by
          have : Algebra.FinitePresentation A (Localization.Away (1 : A)) :=
            IsLocalization.Away.finitePresentation 1
          exact Algebra.FinitePresentation.trans R A _⟩ (hflat'.mp hflat) hsmF
    obtain ⟨g, hg, hsmg⟩ := hsmA
    have := hsmg
    have hsmoothAt : Algebra.IsSmoothAt R q.asIdeal :=
      (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hsmg) hg
    have hstalk : (f.stalkMap x).hom.FormallySmooth :=
      (formallySmooth_stalkMap_iff V hV W hW hWV hx).mpr (hq ▸ hsmoothAt)
    refine ⟨f.smoothLocus, hstalk, ?_⟩
    rw [← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq]
    ext y
    exact iff_of_true y.property trivial

end AlgebraicGeometry.Scheme.Hom
