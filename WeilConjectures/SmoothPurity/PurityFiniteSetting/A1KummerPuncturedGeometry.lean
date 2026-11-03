/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.MvPolynomial.Equiv
import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.Algebra.Polynomial.Laurent

/-! # The Laurent model is the actual punctured affine line
Source: det-prop-a1-kummer.proof.md, Reduction to a geometric fibre.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.PurityFiniteSetting

/-- Localization away from X is an open immersion.
Source: det-prop-a1-kummer.proof.md
(blueprint: new-pur-a1-kummer-punctured-geometry). -/
instance a1KummerLaurent_open (k : Type u) [Field k] :
    IsOpenImmersion (KummerLine.inclusion k) :=
  IsOpenImmersion.of_isLocalization (S := LaurentPolynomial k) Polynomial.X

/-- The actual coordinate basic open is an open immersion.
Source: det-prop-a1-kummer.proof.md
(blueprint: new-pur-a1-kummer-punctured-geometry). -/
instance a1KummerPunctured_open (X : Scheme.{u}) : IsOpenImmersion (openImmersion X) := by
  dsimp only [openImmersion]
  infer_instance

/-- The Laurent inclusion and actual coordinate basic open have the same image.
Source: det-prop-a1-kummer.proof.md
(blueprint: new-pur-a1-kummer-punctured-geometry).
Proof: localization has image D(X); the absolute line isomorphism preserves X. -/
theorem a1KummerLaurent_range (k : Type u) [Field k] :
    Set.range (KummerLine.inclusion k ≫ (a1KummerAbsoluteLineIso k).hom) =
      Set.range (openImmersion (Spec (.of k))) := by
  have hpre : (a1KummerAbsoluteLineIso k).hom ⁻¹ᵁ
      (Line (Spec (.of k))).basicOpen (coordinate (Spec (.of k))) =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) := by
    rw [Scheme.preimage_basicOpen_top, a1KummerAbsoluteLineIso_coordinate]
    exact basicOpen_eq_of_affine (R := CommRingCat.of (Polynomial k)) Polynomial.X
  have hr : Set.range (KummerLine.inclusion k) =
      (↑(PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k)) :
        Set (PrimeSpectrum (Polynomial k))) := by
    change Set.range (PrimeSpectrum.comap (Polynomial.toLaurent (R := k))) = _
    have h := PrimeSpectrum.localization_away_comap_range (LaurentPolynomial k)
      (Polynomial.X : Polynomial k)
    have he : algebraMap (Polynomial k) (LaurentPolynomial k) = Polynomial.toLaurent := by
      apply RingHom.ext
      intro p
      exact LaurentPolynomial.algebraMap_eq_toLaurent p
    rw [he] at h
    exact h
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hr, ← hpre]
  change (a1KummerAbsoluteLineIso k).hom ''
      ((a1KummerAbsoluteLineIso k).hom ⁻¹'
        (((Line (Spec (.of k))).basicOpen (coordinate (Spec (.of k)))) : Set _)) = _
  have hs : Function.Surjective ((a1KummerAbsoluteLineIso k).hom :
      KummerLine.curve k false → Line (Spec (.of k))) :=
    (a1KummerAbsoluteLineIso k).hom.homeomorph.surjective
  rw [Set.image_preimage_eq _ hs]
  exact (Scheme.Opens.range_ι
    ((Line (Spec (.of k))).basicOpen (coordinate (Spec (.of k))))).symm

/-- The Laurent spectrum is the actual coordinate basic open of the affine line.
Source: det-prop-a1-kummer.proof.md, Reduction to a geometric fibre
(blueprint: new-pur-a1-kummer-punctured-geometry).
Proof: the polynomial-to-Laurent map is localization away from X, whose spectrum
has image D(X). The absolute line isomorphism preserves the coordinate, so it carries
this image to the actual coordinate basic open. The two open immersions with equal
image determine the displayed isomorphism. -/
def a1KummerAbsolutePuncturedIso (k : Type u) [Field k] :
    KummerLine.curve k true ≅ Punctured (Spec (.of k)) :=
  IsOpenImmersion.isoOfRangeEq
    (KummerLine.inclusion k ≫ (a1KummerAbsoluteLineIso k).hom)
    (openImmersion (Spec (.of k))) (a1KummerLaurent_range k)

/-- The punctured-line identification preserves the open immersion.
Source: det-prop-a1-kummer.proof.md
(blueprint: new-pur-a1-kummer-punctured-geometry).
Proof: this is the defining factorization of the open-image isomorphism. -/
theorem a1KummerAbsolutePuncturedIso_open (k : Type u) [Field k] :
    (a1KummerAbsolutePuncturedIso k).hom ≫ openImmersion (Spec (.of k)) =
      KummerLine.inclusion k ≫ (a1KummerAbsoluteLineIso k).hom := by
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The punctured-line identification is over the ground field.
Source: det-prop-a1-kummer.proof.md
(blueprint: new-pur-a1-kummer-punctured-geometry).
Proof: compose the open-immersion equation with the affine projection, and use the
polynomial-line over-base identity and the polynomial/Laurent scalar identity. -/
theorem a1KummerAbsolutePuncturedIso_over (k : Type u) [Field k] :
    (a1KummerAbsolutePuncturedIso k).hom ≫ puncturedProjection (Spec (.of k)) =
      KummerLine.structureMap k true := by
  change (a1KummerAbsolutePuncturedIso k).hom ≫
    (openImmersion (Spec (.of k)) ≫ lineProjection (Spec (.of k))) = _
  rw [← Category.assoc, a1KummerAbsolutePuncturedIso_open, Category.assoc,
    a1KummerAbsoluteLineIso_over, Etale.normalizedKummerInclusion_over]

/-- The Laurent-to-punctured-line identification preserves the actual coordinate unit.
Source: det-prop-a1-kummer.proof.md, the named class kappa(t)
(blueprint: new-pur-a1-kummer-punctured-geometry).
Proof: units are determined by values. The open-immersion equation reduces the value
to the polynomial variable restricted along polynomial-to-Laurent inclusion. Naturality
of global sections of Spec sends that variable to the Laurent monomial T(1). -/
theorem a1KummerAbsolutePuncturedIso_coordinate (k : Type u) [Field k] :
    Units.map (a1KummerAbsolutePuncturedIso k).hom.appTop.hom.toMonoidHom
        (coordinateUnit (Spec (.of k))) = KummerLine.coordinateUnit k := by
  apply Units.ext
  change (a1KummerAbsolutePuncturedIso k).hom.appTop
      ((Line (Spec (.of k))).isUnit_ι_appTop_basicOpen
        (coordinate (Spec (.of k)))).unit.val = _
  rw [IsUnit.unit_spec]
  change (a1KummerAbsolutePuncturedIso k).hom.appTop
      ((openImmersion (Spec (.of k))).appTop (coordinate (Spec (.of k)))) =
    (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv
      (LaurentPolynomial.isUnit_T (R := k) 1).unit.val
  rw [IsUnit.unit_spec, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    a1KummerAbsolutePuncturedIso_open, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    a1KummerAbsoluteLineIso_coordinate]
  have h := congrArg (fun f : CommRingCat.of (Polynomial k) ⟶
      Γ(Spec (.of (LaurentPolynomial k)), ⊤) ↦ f Polynomial.X)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.toLaurent (R := k))))
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv
      (Polynomial.toLaurent Polynomial.X) =
    (KummerLine.inclusion k).appTop
      ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X) at h
  rw [Polynomial.toLaurent_X] at h
  exact h.symm

/-- The actual punctured line is the Laurent family's pullback square.
Source: det-prop-a1-kummer.proof.md, Reduction to a geometric fibre
(blueprint: new-pur-a1-kummer-punctured-geometry).
Proof: transport the proved actual punctured-line square along the absolute Laurent
isomorphism, using its over-base identity. -/
theorem a1KummerPuncturedFamily_isPullback {k : Type u} [Field k] {Y : Scheme.{u}}
    (a : Y ⟶ Spec (.of k)) :
    IsPullback (puncturedMap a ≫ (a1KummerAbsolutePuncturedIso k).inv)
      (puncturedProjection Y) (KummerLine.structureMap k true) a := by
  apply (a1KummerPunctured_isPullback a).of_iso
    (Iso.refl _) (a1KummerAbsolutePuncturedIso k).symm (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    rw [← a1KummerAbsolutePuncturedIso_over, Iso.inv_hom_id_assoc]
  · simp

/-- The canonical Laurent-family presentation, determined by its two projections.
Source: det-prop-a1-kummer.proof.md, Reduction to a geometric fibre
(blueprint: new-pur-a1-kummer-punctured-geometry). -/
def a1KummerPuncturedFamilyIso {k : Type u} [Field k] {Y : Scheme.{u}}
    (a : Y ⟶ Spec (.of k)) :
    pullback (KummerLine.structureMap k true) a ≅ Punctured Y :=
  (a1KummerPuncturedFamily_isPullback a).isoPullback.symm

/-- The Laurent-family presentation preserves the projection and coordinate unit.
Source: det-prop-a1-kummer.proof.md, geometric reduction and the named class kappa(t)
(blueprint: new-pur-a1-kummer-punctured-geometry).
Proof: the universal isomorphism preserves both projections. Cancel the inverse
absolute isomorphism in the first projection equation. Apply global functions and
use the proved coordinate identities for the horizontal map and absolute isomorphism. -/
theorem a1KummerPuncturedFamilyIso_normalization {k : Type u} [Field k] {Y : Scheme.{u}}
    (a : Y ⟶ Spec (.of k)) :
    (a1KummerPuncturedFamilyIso a).hom ≫ puncturedProjection Y =
        pullback.snd (KummerLine.structureMap k true) a ∧
    Units.map (a1KummerPuncturedFamilyIso a).hom.appTop.hom.toMonoidHom (coordinateUnit Y) =
      Units.map (pullback.fst (KummerLine.structureMap k true) a).appTop.hom.toMonoidHom
        (KummerLine.coordinateUnit k) := by
  constructor
  · exact (a1KummerPuncturedFamily_isPullback a).isoPullback_inv_snd
  · have hf : (a1KummerPuncturedFamilyIso a).hom ≫ puncturedMap a =
        pullback.fst (KummerLine.structureMap k true) a ≫
          (a1KummerAbsolutePuncturedIso k).hom := by
      rw [← cancel_mono (a1KummerAbsolutePuncturedIso k).inv]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      exact (a1KummerPuncturedFamily_isPullback a).isoPullback_inv_fst
    apply Units.ext
    have hc := congrArg Units.val (a1KummerPuncturedMap_coordinate a)
    have ha := congrArg Units.val (a1KummerAbsolutePuncturedIso_coordinate k)
    change (puncturedMap a).appTop (coordinateUnit (Spec (.of k))).val =
      (coordinateUnit Y).val at hc
    change (a1KummerAbsolutePuncturedIso k).hom.appTop
      (coordinateUnit (Spec (.of k))).val = (KummerLine.coordinateUnit k).val at ha
    change (a1KummerPuncturedFamilyIso a).hom.appTop (coordinateUnit Y).val =
      (pullback.fst (KummerLine.structureMap k true) a).appTop
        (KummerLine.coordinateUnit k).val
    rw [← hc, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hf,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ha]

end WeilConjectures.PurityFiniteSetting
