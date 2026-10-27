/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Principal-open geometry of an open relative affine line

Source: Stacks Project, Tags 01T6, 01VC, 02NL and 01I3; principal-cover expansion of
Tag 0GKY, `lemma-loc-constant-shriek-rel-dim-1`
(blueprint: lem-weil-pbc-open-relative-line-principal-geometry).

The affine line is represented by its specified affine chart `Spec R[t]` and its
projection is induced by the coefficient inclusion `Polynomial.C`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped BigOperators

namespace AlgebraicGeometry

/-- An open of the relative affine line over a Noetherian affine base has a finite
principal cover. The ambient line and the open are Noetherian and quasi-separated;
the restricted projection is separated and of finite type. Finite nonempty
subfamilies have principal affine intersections. All principal opens, and clopen
pieces of their finite étale covers, have affine separated finite-type projections
smooth of relative dimension one. The clopen pieces are affine and Noetherian.
Source: Stacks Project, Tags 01T6, 01VC, 02NL, 01I3 and 0GKY
(blueprint: lem-weil-pbc-open-relative-line-principal-geometry).

Proof plan, following the eight steps of the node:
1. The affine-line projection is smooth of relative dimension one by
   `sbc-lem-affine-space-smooth`. It is affine by
   `lem-weil-pbc-morphism-affine-schemes-affine`, hence separated and quasi-compact
   by `lem-weil-pbc-affine-morphism-permanence`. Smoothness gives local finite
   presentation; use `lem-weil-pbc-lfp-affine-opens-finite-presentation` and
   `lem-weil-pbc-lft-affine-pairs` to obtain local finite type, hence finite type.
2. Apply `lem-weil-pbc-finite-type-over-noetherian` to the projection, then
   `lem-weil-pbc-noetherian-open-subscheme-noetherian` to the open. Apply
   `lem-weil-pbc-locally-noetherian-quasi-separated` to both schemes and the base.
3. The open inclusion is locally of finite type and separated by
   `lem-weil-pbc-immersion-base-change-lft` and
   `lem-weil-pbc-separated-cancellation`. Compose using
   `lem-weil-pbc-proper-fp-permanence`; quasi-compactness follows from
   `lem-weil-pbc-qcqs-morphism-permanence` since the source is quasi-compact and
   the base quasi-separated. This gives the finite-type restricted projection.
4. The basic opens form a basis by
   `lem-weil-pbc-spec-localization-away-basic-open`. Quasi-compactness of the
   open supplies a finite subcover; the empty open admits the empty family.
5. For any polynomial, `lem-weil-pbc-principal-localization-open-immersion`
   identifies its basic open with the spectrum of the localization. The inclusion
   is étale by `lem-weil-pbc-etale-composition-cancellation`, and smooth of relative
   dimension zero by `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`.
   Compose using `lem-sbc-smooth-relative-dimension-permanence`. Affineness and
   finite type follow as in step 1, also when this basic open is empty.
6. A prime contains a finite product precisely when it contains a factor. Thus
   finite nonempty intersections equal the basic open of the product. Step 5
   supplies affineness and all projection properties of the identified open.
7. A finite cover of an affine is affine by
   `lem-weil-pbc-finite-morphism-permanence`. A clopen inclusion is a closed
   immersion: sections extend by zero across its open complement. It is finite
   by `lem-weil-pbc-closed-immersion-finite`, so its source is again affine.
8. The clopen inclusion is also an open immersion. Its composite with the finite
   étale map is étale by `lem-weil-pbc-etale-composition-cancellation`, hence smooth
   of relative dimension zero by `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`.
   Compose with step 5 using `lem-sbc-smooth-relative-dimension-permanence`.
   Affineness gives separatedness and quasi-compactness; smoothness gives local
   finite type as above. Finally `lem-weil-pbc-finite-type-over-noetherian` makes
   the clopen piece Noetherian. All arguments include the empty source. -/
theorem openRelativeLine_principal_geometry
    (R : CommRingCat.{u}) [IsNoetherian (Spec R)]
    (U : (Spec (.of (Polynomial R))).Opens) :
    IsNoetherian (Spec (.of (Polynomial R))) ∧
    QuasiSeparatedSpace (Spec (.of (Polynomial R))) ∧
    IsNoetherian U.toScheme ∧ QuasiSeparatedSpace U.toScheme ∧
    IsSeparated (U.ι ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ∧
    LocallyOfFiniteType
      (U.ι ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ∧
    QuasiCompact (U.ι ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ∧
    (∃ (r : ℕ) (s : Fin r → Polynomial R),
      (∀ i : Fin r, PrimeSpectrum.basicOpen (s i) ≤ U) ∧
      U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (s i) ∧
      ∀ J : Finset (Fin r), J.Nonempty →
        (⨅ i : J, PrimeSpectrum.basicOpen (s i.val)) =
          PrimeSpectrum.basicOpen (∏ i ∈ J, s i) ∧
        IsAffineOpen (⨅ i : J, PrimeSpectrum.basicOpen (s i.val) :
          (Spec (.of (Polynomial R))).Opens)) ∧
    (∀ s : Polynomial R,
      IsAffineOpen (X := Spec (.of (Polynomial R))) (PrimeSpectrum.basicOpen s) ∧
      IsAffineHom
        (Scheme.Opens.ι (X := Spec (.of (Polynomial R))) (PrimeSpectrum.basicOpen s) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ∧
      IsSeparated
        (Scheme.Opens.ι (X := Spec (.of (Polynomial R))) (PrimeSpectrum.basicOpen s) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ∧
      LocallyOfFiniteType
        (Scheme.Opens.ι (X := Spec (.of (Polynomial R))) (PrimeSpectrum.basicOpen s) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ∧
      QuasiCompact
        (Scheme.Opens.ι (X := Spec (.of (Polynomial R))) (PrimeSpectrum.basicOpen s) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ∧
      SmoothOfRelativeDimension 1
        (Scheme.Opens.ι (X := Spec (.of (Polynomial R))) (PrimeSpectrum.basicOpen s) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))) ∧
    (∀ (s : Polynomial R) (T : Scheme.{u})
      (g : T ⟶ Scheme.Opens.toScheme (X := Spec (.of (Polynomial R))) (PrimeSpectrum.basicOpen s)),
      IsFinite g → Etale g → ∀ V : T.Opens, IsClosed (V : Set T) →
      IsAffine V.toScheme ∧ IsNoetherian V.toScheme ∧
      IsAffineHom (V.ι ≫ g ≫
        Scheme.Opens.ι (X := Spec (.of (Polynomial R))) (PrimeSpectrum.basicOpen s) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ∧
      IsSeparated (V.ι ≫ g ≫
        Scheme.Opens.ι (X := Spec (.of (Polynomial R))) (PrimeSpectrum.basicOpen s) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ∧
      LocallyOfFiniteType (V.ι ≫ g ≫
        Scheme.Opens.ι (X := Spec (.of (Polynomial R))) (PrimeSpectrum.basicOpen s) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ∧
      QuasiCompact (V.ι ≫ g ≫
        Scheme.Opens.ι (X := Spec (.of (Polynomial R))) (PrimeSpectrum.basicOpen s) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ∧
      SmoothOfRelativeDimension 1 (V.ι ≫ g ≫
        Scheme.Opens.ι (X := Spec (.of (Polynomial R))) (PrimeSpectrum.basicOpen s) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))) := by
  classical
  let p := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  -- Work directly with the specified polynomial chart.
  have hsmooth : SmoothOfRelativeDimension 1 p := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    apply (RingHom.isStandardSmoothOfRelativeDimension_algebraMap
      (R := R) (S := Polynomial R) (n := 1)).2
    have : Algebra.IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial Unit R) := by
      simpa using MvPolynomial.isStandardSmoothOfRelativeDimension R Unit
    exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
      (MvPolynomial.uniqueAlgEquiv R Unit)
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.mp inferInstance
  have : IsNoetherian (Spec (.of (Polynomial R))) := inferInstance
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (U : Set (Spec (.of (Polynomial R)))))
  have : IsNoetherian U.toScheme := ⟨⟩
  let D (s : Polynomial R) : (Spec (.of (Polynomial R))).Opens := PrimeSpectrum.basicOpen s
  have hprincipal (s : Polynomial R) := IsAffineOpen.Spec_basicOpen (R := .of (Polynomial R)) s
  have hproj (s : Polynomial R) :
      SmoothOfRelativeDimension 1 ((D s).ι ≫ p) := by
    have : SmoothOfRelativeDimension (0 + 1) ((D s).ι ≫ p) :=
      inferInstance
    exact this
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · let B := {s : Polynomial R // PrimeSpectrum.basicOpen s ≤ U}
    have hU := TopologicalSpace.NoetherianSpace.isCompact (U : Set (Spec (.of (Polynomial R))))
    obtain ⟨t, ht⟩ := hU.elim_finite_subcover
      (fun s : B ↦ (D s.val : Set _))
      (fun s ↦ (PrimeSpectrum.basicOpen s.val).isOpen) (by
        intro x hx
        obtain ⟨_, ⟨s, rfl⟩, hxs, hsU⟩ :=
          PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx U.isOpen
        change x ∈ ⋃ a : B, (D a.val : Set _)
        exact Set.mem_iUnion.mpr ⟨(⟨s, hsU⟩ : B), hxs⟩)
    let e := (Fintype.equivFin t).symm
    let s : Fin (Fintype.card t) → Polynomial R := fun i ↦ (e i).val.val
    have hle (i) : PrimeSpectrum.basicOpen (s i) ≤ U := (e i).val.property
    refine ⟨Fintype.card t, s, hle, le_antisymm ?_ (iSup_le hle), ?_⟩
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
      exact TopologicalSpace.Opens.mem_iSup.mpr
        ⟨e.symm ⟨a, ha⟩, by simpa [s] using hxa⟩
    · intro J _hJ
      have heq : (⨅ i : J, PrimeSpectrum.basicOpen (s i.val)) =
          PrimeSpectrum.basicOpen (∏ i ∈ J, s i) := by
        apply SetLike.coe_injective
        rw [TopologicalSpace.Opens.coe_iInf]
        ext x
        simp [Ideal.IsPrime.prod_mem_iff]
      exact ⟨heq, heq ▸ hprincipal _⟩
  · intro s
    have : IsAffine (D s).toScheme := hprincipal s
    have := hproj s
    have : Smooth ((D s).ι ≫ p) :=
      SmoothOfRelativeDimension.smooth 1 _
    exact ⟨hprincipal s, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance⟩
  · intro s T g hg he V hV
    have : IsAffine (D s).toScheme := hprincipal s
    have : IsAffine T := isAffine_of_isAffineHom g
    -- A clopen inclusion has inducing underlying map and closed range.
    have : IsAffineHom V.ι := isAffineHom_of_isInducing V.ι
      V.ι.isOpenEmbedding.isInducing (by simpa only [Scheme.Opens.range_ι] using hV)
    have : IsAffine V.toScheme := isAffine_of_isAffineHom V.ι
    have := hproj s
    have : SmoothOfRelativeDimension (0 + 1) (g ≫ (D s).ι ≫ p) :=
      smoothOfRelativeDimension_comp 0 1 g _
    have : SmoothOfRelativeDimension (0 + 1) (V.ι ≫ g ≫ (D s).ι ≫ p) :=
      smoothOfRelativeDimension_comp 0 1 V.ι _
    have : Smooth (V.ι ≫ g ≫ (D s).ι ≫ p) :=
      SmoothOfRelativeDimension.smooth 1 _
    have : IsLocallyNoetherian V.toScheme :=
      LocallyOfFiniteType.isLocallyNoetherian
        (V.ι ≫ g ≫ (D s).ι ≫ p)
    have : IsNoetherian V.toScheme := ⟨⟩
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry
