/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.AlgebraicGeometry.RegularCoordinateFibreDimensionFormula
import WeilConjectures.AlgebraicGeometry.FibrewiseFlatnessCriterion
import WeilConjectures.AlgebraicGeometry.UnramifiedLocusBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleAtPrimeFlatUnramifiedCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.MiracleFlatness

/-!
# Étaleness near a regular coordinate fibre

Source: Stacks Project, More on Morphisms, Tag 0FUE, local flatness argument
(blueprint: lem-pur-etale-near-regular-coordinate-fibre).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem regular_local_depth_ge (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    (d : ℕ∞) ≤ IsLocalRing.depth (R := R) R := by
  classical
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (show (IsLocalRing.maximalIdeal R).FG from
        (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing)
  have hlen : s.toList.length = d := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hd] at h
    have hsd : (IsLocalRing.maximalIdeal R).spanFinrank = d := by exact_mod_cast h
    simpa [hsd] using hcard
  have hrs : IsLocalRing.IsRegularSystemOfParameters s.toList :=
    ⟨by simpa using hspan, by rw [hlen, hd]⟩
  have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators R d hd
    s.toList hrs).1
  unfold IsLocalRing.depth Ideal.depth
  split
  · exact le_top
  · apply le_sSup
    exact ⟨s.toList, hreg, fun x hx ↦ hrs.1 ▸ Ideal.subset_span hx, by rw [hlen]⟩

private theorem flat_of_regular_dimension_formula
    {R L : Type u} [CommRing R] [CommRing L]
    [IsRegularLocalRing R] [IsRegularLocalRing L]
    (φ : R →+* L) [IsLocalHom φ]
    (hdim : ringKrullDim L = ringKrullDim R +
      ringKrullDim (L ⧸ (IsLocalRing.maximalIdeal R).map φ)) : φ.Flat := by
  let d := (IsLocalRing.maximalIdeal L).spanFinrank
  have hd : ringKrullDim L = (d : WithBot ℕ∞) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  exact RingHom.flat_of_regular_of_depth_ge φ d hd (regular_local_depth_ge L d hd) hdim

private theorem etale_open_of_flat_unramified_stalk
    {X Z : Scheme.{u}} (f : X ⟶ Z) [LocallyOfFinitePresentation f] (x : X)
    (hflat : (f.stalkMap x).hom.Flat)
    (hunram : (f.stalkMap x).hom.FormallyUnramified) :
    ∃ W : X.Opens, x ∈ W ∧ Etale (W.ι ≫ f) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hfxU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, e⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hfxU (f ⁻¹ᵁ U).isOpen
  let := (f.appLE U V e).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, e hxV⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hqp : q.under Γ(Z, U) = p :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV e hxV).1)
  have : q.LiesOver p := ⟨hqp.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  have hu : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    exact (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV e hxV)).mp hunram
  have : Algebra.FormallyUnramified Γ(Z, U) (Localization.AtPrime p) :=
    .of_isLocalization p.primeCompl
  have : Algebra.FormallyUnramified Γ(Z, U) (Localization.AtPrime q) :=
    .comp Γ(Z, U) (Localization.AtPrime p) _
  have hflocal : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := by
    rw [← RingHom.flat_algebraMap_iff]
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV e hxV)).mp hflat
  have hfbase : Module.Flat Γ(Z, U) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p)
      p.primeCompl (Localization.AtPrime q)).mp hflocal
  have hf : RingHom.Flat
      (Localization.localRingHom (q.under Γ(Z, U)) q
        (algebraMap Γ(Z, U) Γ(X, V)) rfl) := by
    let := (Localization.localRingHom (q.under Γ(Z, U)) q
      (algebraMap Γ(Z, U) Γ(X, V)) rfl).toAlgebra
    have : IsScalarTower Γ(Z, U) (Localization.AtPrime (q.under Γ(Z, U)))
        (Localization.AtPrime q) := .of_algebraMap_eq fun r ↦
      (Localization.localRingHom_to_map (q.under Γ(Z, U)) q
        (algebraMap Γ(Z, U) Γ(X, V)) rfl r).symm
    exact (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.under Γ(Z, U)))
      (q.under Γ(Z, U)).primeCompl (Localization.AtPrime q)).mpr hfbase
  have hΩ : Subsingleton (LocalizedModule q.primeCompl
      (KaehlerDifferential Γ(Z, U) Γ(X, V))) :=
    (IsLocalizedModule.iso q.primeCompl
      (KaehlerDifferential.map Γ(Z, U) Γ(Z, U) Γ(X, V)
        (Localization.AtPrime q))).subsingleton_congr.mpr inferInstance
  have : Algebra.FinitePresentation Γ(Z, U) Γ(X, V) := f.finitePresentation_appLE hU hV e
  have het := (Algebra.isEtaleAt_iff_exists_away_etale_iff_flat_localized_kaehler q).2.mpr
    ⟨hf, hΩ⟩
  obtain ⟨g, hg, hge⟩ :=
    (Algebra.isEtaleAt_iff_exists_away_etale_iff_flat_localized_kaehler q).1.mp het
  let W := X.basicOpen g
  have hW : IsAffineOpen W := hV.basicOpen g
  have hxW : x ∈ W := by
    have hmem : hV.primeIdealOf ⟨x, hxV⟩ ∈ PrimeSpectrum.basicOpen g := hg
    rw [← hV.fromSpec_preimage_basicOpen] at hmem
    change hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) ∈ X.basicOpen g at hmem
    rwa [hV.fromSpec_primeIdealOf] at hmem
  have heW : W ≤ f ⁻¹ᵁ U := (X.basicOpen_le g).trans e
  have hres : Etale (f.resLE U W heW) := by
    have : IsAffine (Scheme.Opens.toScheme U) := hU
    have : IsAffine W.toScheme := hW
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
    apply (RingHom.Etale.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f U W heW)).mpr
    let := (f.appLE U W heW).hom.toAlgebra
    have := hge
    have := hV.isLocalization_basicOpen g
    have : IsScalarTower Γ(Z, U) Γ(X, V) Γ(X, W) := by
      apply IsScalarTower.of_algebraMap_eq
      intro r
      change (f.appLE U W heW) r =
        (X.presheaf.map (homOfLE (X.basicOpen_le g)).op) ((f.appLE U V e) r)
      exact congr($(f.appLE_map e (homOfLE (X.basicOpen_le g)).op) r).symm
    rw [← RingHom.algebraMap_toAlgebra (f.appLE U W heW).hom,
      RingHom.etale_algebraMap]
    exact Algebra.Etale.of_equiv
      ((IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, W)).restrictScalars
        Γ(Z, U))
  have : Etale ((f.resLE U W heW) ≫ Scheme.Opens.ι U) :=
    MorphismProperty.comp_mem @Etale _ _ hres inferInstance
  exact ⟨W, hxW, by simpa only [Scheme.Hom.resLE_comp_ι] using this⟩

/-- A specified map from a smooth scheme to affine space is étale near an étale
regular coordinate fibre. This is a criterion for a given map, without constructing
coordinates or choosing equations.

Source: Stacks Project, More on Morphisms, Tag 0FUE, last two proof paragraphs,
using Tags 039C, 00R4 and 02GU
(blueprint: lem-pur-etale-near-regular-coordinate-fibre).

Proof. Work on affine neighbourhoods in the base and source. The map is finitely
presented by finite-presentation permanence, since its composite with affine-space
projection is smooth. On the fibre through `y`, the ambient local ring is regular,
as is the local ring of affine space. The last `b` equations remain regular after
base change because both the ambient scheme and its closed coordinate fibre are
flat over the base; the latter follows from its étale map to affine space. Taking
the quotient by this regular sequence drops the local dimension by `b` on both
sides. Étaleness of `v` equates the remaining dimensions and identifies the local
fibre as a finite separable field extension, of dimension zero. Miracle flatness
therefore makes the map on the fibre flat at `y`. The fibre criterion of flatness,
applied to the two local rings over the local base, makes the original map flat
at `y`. The unramified-locus base-change theorem, applied to the given cartesian
square and the étale map `v`, gives an unramified neighbourhood of `i(y)` for `h`.
Thus the actual stalk map is formally unramified. On affine charts, transport
flatness and formal unramifiedness to prime localizations. Localization of
relative differentials and the finite-presentation étale-at-prime criterion give
a basic open neighbourhood of `i(y)` where the specified map is étale. The sole
remaining obligation is the numerical dimension comparison, isolated in
`Scheme.Hom.fibre_dimension_formula_of_regular_coordinate_fibre`. -/
theorem Scheme.Hom.exists_etale_open_of_regular_coordinate_fibre
    {S X Y : Scheme.{u}} (p : X ⟶ S) [Smooth p] (i : Y ⟶ X)
    [IsClosedImmersion i] (a b : ℕ)
    (h : X ⟶ AffineSpace (ULift.{u} (Fin (a + b))) S)
    (v : Y ⟶ AffineSpace (ULift.{u} (Fin a)) S) [Etale v]
    (hh : h ≫ (AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S) = p)
    (H : IsPullback v i
      (AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) S ↘ S)
        (fun j ↦ Fin.addCases (fun k ↦ AffineSpace.coord S (ULift.up k))
          (fun _ ↦ 0) j.down)) h)
    (hreg : ∀ W : X.affineOpens,
      RingTheory.Sequence.IsWeaklyRegular Γ(X, W)
        (List.ofFn (fun j : Fin b ↦
          X.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op
            (h.appTop (AffineSpace.coord S (ULift.up (Fin.natAdd a j)))))))
    (y : Y) :
    ∃ T : X.Opens, i y ∈ T ∧ Etale (T.ι ≫ h) := by
  let q := AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S
  have : Smooth q :=
    SmoothOfRelativeDimension.smooth (Nat.card (ULift.{u} (Fin (a + b)))) q
  have : LocallyOfFinitePresentation (h ≫ q) := by rw [hh]; infer_instance
  have : LocallyOfFinitePresentation h := locallyOfFinitePresentation_of_comp h q
  let c : AffineSpace (ULift.{u} (Fin a)) S ⟶
      AffineSpace (ULift.{u} (Fin (a + b))) S :=
    AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) S ↘ S)
    (fun j ↦ Fin.addCases (fun k ↦ AffineSpace.coord S (ULift.up k))
      (fun _ ↦ 0) j.down)
  change IsPullback v i c h at H
  have he : Etale (pullback.snd h c) := by
    rw [← H.flip.isoPullback_inv_snd]
    infer_instance
  have hy : i y ∈ unramifiedLocus h := by
    have hz : H.flip.isoPullback.hom y ∈ unramifiedLocus (pullback.snd h c) := by
      refine ⟨⊤, trivial, ?_, ?_⟩ <;> infer_instance
    rw [(unramifiedLocus_baseChange h).2.2.2 c] at hz
    change (H.flip.isoPullback.hom ≫ pullback.fst h c) y ∈ unramifiedLocus h at hz
    simpa only [H.flip.isoPullback_hom_fst] using hz
  obtain ⟨W, hyW, hWft, hWdiag⟩ := hy
  have huW : FormallyUnramified (W.ι ≫ h) := inferInstance
  have hu := FormallyUnramified.stalkMap (W.ι ≫ h) ⟨i y, hyW⟩
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.FormallyUnramified.respectsIso.cancel_right_isIso] at hu
  let s := p (i y)
  let m := pullback.map p (S.fromSpecResidueField s) q (S.fromSpecResidueField s)
    h (𝟙 _) (𝟙 S) (by simpa only [Category.comp_id] using hh.symm) (by simp)
  let z := p.asFiber (i y)
  have : Smooth (p.fiberToSpecResidueField s) :=
    inferInstanceAs (Smooth (pullback.snd p (S.fromSpecResidueField s)))
  have : Smooth (q.fiberToSpecResidueField s) :=
    inferInstanceAs (Smooth (pullback.snd q (S.fromSpecResidueField s)))
  have : IsRegularLocalRing ((p.fiber s).presheaf.stalk z) :=
    Smooth.isRegularLocalRing_stalk (p.fiberToSpecResidueField s) z
  have : IsRegularLocalRing ((q.fiber s).presheaf.stalk (m z)) :=
    Smooth.isRegularLocalRing_stalk (q.fiberToSpecResidueField s) (m z)
  have hdim := Scheme.Hom.fibre_dimension_formula_of_regular_coordinate_fibre
    p i a b h v hh H hreg y
  have hm : (m.stalkMap z).hom.Flat :=
    flat_of_regular_dimension_formula
      (R := (q.fiber s).presheaf.stalk (m z))
      (L := (p.fiber s).presheaf.stalk z) (m.stalkMap z).hom hdim
  have hflat := (Scheme.Hom.flatAt_and_base_flatAt_of_fiber_flatAt p q h hh
    (i y) (Flat.stalkMap p (i y)) hm).1
  exact etale_open_of_flat_unramified_stalk h (i y) hflat hu

end AlgebraicGeometry
