/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityVectorBundle.PurityVectorBundleZeroSection
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.VectorProjectiveCompletion.VectorProjectiveCompletionData
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.AlgebraicGeometry.VectorProjectiveCompletion.VectorProjectiveCompletion
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Geometry of the zero section of a line bundle

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
thm-pur-rank-one-thom.proof.md, Step 1; Stacks Tags 01LX, 01OB, 01OE,
01T6, 01WR, 01WS and 00KW (blueprint: lem-pur-line-zero-geometry).

The projective completion uses the published presentation of Sym(O_B ⊕ E),
its relative Proj and its normalized dehomogenization chart. The affine equations
are equations of schemes and sections, including arbitrary, possibly nonflat,
non-Noetherian base changes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.PurityVectorBundle

private theorem section_cartier {X S : Scheme.{u}} (p : X ⟶ S)
    [SmoothOfRelativeDimension 1 p] [IsSeparated p]
    (z : S ⟶ X) (hz : z ≫ p = 𝟙 S) : IsEffectiveCartierCenter z := by
  have : IsClosedImmersion (z ≫ p) := hz ▸ inferInstance
  have : IsClosedImmersion z := IsClosedImmersion.of_comp z p
  apply isEffectiveCartierCenter_iff_isInvertible_ker.mpr
  let l := IsClosedImmersion.lift z z.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι z.ker).ge
  have : IsIso l := IsClosedImmersion.isIso_lift z z.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι z.ker).symm
  have hl : z.ker.subschemeι ≫ p = l := by
    rw [← IsClosedImmersion.lift_fac z z.ker.subschemeι
      (Scheme.IdealSheafData.ker_subschemeι z.ker).ge, Category.assoc, hz,
      Category.comp_id]
  have : IsIso (z.ker.subschemeι ≫ p) := hl ▸ inferInstance
  exact Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat p
    inferInstance inferInstance inferInstance

private theorem cartier_stalk_dimension {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (z : Z ⟶ X) [IsClosedImmersion z] (hz : IsEffectiveCartierCenter z) (x : Z) :
    ringKrullDim (X.presheaf.stalk (z x)) =
      ringKrullDim (Z.presheaf.stalk x) + (1 : WithBot ℕ∞) := by
  obtain ⟨U, hxU, hU⟩ := isEffectiveCartierCenter_iff_isInvertible_ker.mp hz (z x)
  let := X.presheaf.algebra_section_stalk ⟨z x, hxU⟩
  have := U.2.isLocalization_stalk ⟨z x, hxU⟩
  have hflat : (X.presheaf.germ U.1 (z x) hxU).hom.Flat := by
    change (algebraMap Γ(X, U.1) (X.presheaf.stalk (z x))).Flat
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _
      (U.2.primeIdealOf ⟨z x, hxU⟩).asIdeal.primeCompl)
  obtain ⟨t, ht, hker⟩ := hU.map_of_flat hflat
  rw [← z.ker_stalkMap U x hxU] at hker
  have htker : t ∈ RingHom.ker (z.stalkMap x).hom := by
    rw [hker]
    exact Ideal.subset_span rfl
  have htmax : t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (z x)) := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hunit
    have := hunit.map (z.stalkMap x).hom
    rw [RingHom.mem_ker.mp htker] at this
    exact not_isUnit_zero this
  have hdim :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      ht htmax
  rw [← hker] at hdim
  rw [ringKrullDim_eq_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective (z.stalkMap_surjective x))] at hdim
  exact hdim.symm

private theorem projection_smooth
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] :
    SmoothOfRelativeDimension d (VectorBundleZeroSection.π S d F) := by
  obtain ⟨I, U, hU, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := d)
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @SmoothOfRelativeDimension d) U hU
  intro i
  obtain ⟨hi, ho, _⟩ := VectorBundleZeroSection.trivializationMap_spec S d F (U i)
    (e i).some
  have := hi
  rw [← ho]
  have : SmoothOfRelativeDimension d
      (AffineSpace (ULift.{u} (Fin d)) (U i).toScheme ↘ (U i).toScheme) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over
      (ULift.{u} (Fin d)) (U i).toScheme
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension d) _ _).mpr this

private theorem polynomial_chart (R' : CommRingCat.{u}) :
    ∃ ea : AffineSpace (ULift.{u} (Fin 1)) (Spec R') ≅
        Spec (CommRingCat.of (Polynomial R')),
      ea.hom ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R' →+* Polynomial R')) =
        AffineSpace (ULift.{u} (Fin 1)) (Spec R') ↘ Spec R' ∧
      AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec R') ≫ ea.hom =
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R'))) := by
  let n := ULift.{u} (Fin 1)
  let ep := MvPolynomial.uniqueAlgEquiv R' n
  let ea : AffineSpace n (Spec R') ≅ Spec (CommRingCat.of (Polynomial R')) :=
    AffineSpace.SpecIso n R' ≪≫
      Scheme.Spec.mapIso ep.symm.toRingEquiv.toCommRingCatIso.op
  have hea : ea.hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R' →+* Polynomial R')) =
        AffineSpace n (Spec R') ↘ Spec R' := by
    apply (cancel_epi ea.inv).mp
    simp only [Iso.inv_hom_id_assoc]
    dsimp only [ea, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv]
    simp only [Scheme.Spec_map]
    rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
    congr 1
    change CommRingCat.ofHom (Polynomial.C : R' →+* Polynomial R') =
      CommRingCat.ofHom (MvPolynomial.C : R' →+* MvPolynomial n R') ≫
        CommRingCat.ofHom ep.toRingHom
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (ep.commutes r).symm
  have hez : AffineSpace.zeroSection n (Spec R') ≫ ea.hom =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R'))) := by
    apply (cancel_mono ea.inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply AffineSpace.hom_ext
    · calc
        _ = 𝟙 (Spec R') := AffineSpace.zeroSection_over n (Spec R')
        _ = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R'))) ≫
            Spec.map (CommRingCat.ofHom (Polynomial.C : R' →+* Polynomial R')) := by
          rw [← Spec.map_comp, ← Spec.map_id]
          congr 1
          apply CommRingCat.hom_ext
          apply RingHom.ext
          intro r
          simp
        _ = _ := by rw [← hea]; simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · intro i
      simp only [AffineSpace.zeroSection_appTop_coord, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply]
      dsimp only [ea, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv]
      simp only [Scheme.Spec_map]
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.SpecIso_inv_appTop_coord]
      change 0 = (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R'))) ≫
        Spec.map (CommRingCat.ofHom ep.toRingHom)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n R'))).inv (MvPolynomial.X i))
      rw [← Spec.map_comp, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
        CommRingCat.comp_apply]
      simp [ep, MvPolynomial.uniqueAlgEquiv]
  exact ⟨ea, hea, hez⟩

/-- The complete geometry and universally Cartier property of a line-bundle zero section.
Source: blueprint main-20261015, thm-pur-rank-one-thom.proof.md, Step 1
(blueprint: lem-pur-line-zero-geometry).

Proof:
1. Choose Zariski affine frames of the rank-one module. The relative-Spec affine charts
and SymmetricAlgebra.equivMvPolynomial identify the bundle with Spec R[t]. The
augmentation fixes constants and kills t, so the section is V(t). A change e'=ue
changes coordinates by t'=ut and preserves both the ideal and augmentation
(def-pur-vector-bundle-zero-section, def-amb-finite-locally-free-module,
lem-weil-pbc-symmetric-algebra-free-module-polynomial).
2. Relative Spec is affine, hence separated and quasi-compact. The local map R → R[t]
is finite type; the pointwise criterion makes the projection locally finite type.
Composition with the given structure map gives absolute separatedness and finite type
(lem-weil-pbc-affine-morphism-relative-spec, lem-weil-pbc-affine-morphism-permanence,
lem-weil-pbc-lft-pointwise-criterion, lem-sfb-finite-type-composition-base-change,
lem-weil-pbc-proper-fp-permanence).
3. The frame projection is A^1_U → U, smooth of relative dimension one. Open restriction
and source locality give the global assertion (sbc-lem-affine-space-smooth,
lem-weil-pbc-smooth-restrict-open-subschemes, lem-weil-pbc-smooth-local-on-source).
4. The projective bundle of O_B ⊕ E is proper. In each frame its standard chart is
D_+(T_0), with t=T_1/T_0. On overlaps T'_0=T_0 and T'_1=uT_1, matching t'=ut.
Glue the chart maps and their inverses; they give the open immersion over B with the
stated image and normalized dehomogenization equations
(lem-pur-projective-bundle-tautological-geometry,
lemma-nagata-relative-affine-space-open-immersion, lem-weil-pbc-scheme-morphism-gluing).
5. Multiplication by t is injective by comparing polynomial coefficients. Thus V(t)
is Cartier. Its quotient is R, so the divisor is B and its map to B is the identity,
smooth of relative dimension zero (def-pc-divisor-line-bundle,
sbc-lem-affine-space-smooth, def-sbc-affine-space).
6. Spec k is Noetherian since k is a field. Finite type over a Noetherian base makes
first B and then E Noetherian (pqf-def-locnoeth, def-weil-pbc-noetherian-ring,
lem-weil-pbc-finite-type-over-noetherian).
7. At a zero-section point the stalk is R[t]_q with t ∈ q. Localization preserves
Noetherianity and t is still a nonzerodivisor. Evaluation at zero is surjective onto
R_p, with kernel (t): denominators outside q evaluate outside p, and a constant
multiple killing the evaluation makes the numerator divisible by t. Thus the quotient
is the divisor's stalk. The nonzerodivisor dimension-drop theorem gives the displayed
Krull-dimension equality (lem-weil-pbc-affine-open-stalk-localization,
pqf-lem-affine-open-locnoeth, lem-weil-pbc-localization-noetherian,
lem-weil-pbc-dimension-quotient-nonzerodivisor).
8. The complement in every affine target open is an open of a Noetherian scheme,
hence quasi-compact; this is the quasi-compact-morphism criterion
(lem-weil-pbc-noetherian-open-subscheme-noetherian).
9. For arbitrary B' → B, on each affine chart over a frame the fibre product ring is
R[t] ⊗_R R' ≅ R'[t], by the mutually inverse maps on constants and t. The pulled-back
augmentation is evaluation at zero. Closed immersions survive base change and t is a
nonzerodivisor over every R', including rings with nilpotents. The pulled-back units
still give the same frame transitions, so these local Cartier divisors glue. No
flatness or Noetherian hypothesis is used (def-pc-base-change,
lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-closed-immersion-base-change,
def-pc-divisor-line-bundle). -/
theorem lineZeroGeometry
    (P : WeilConjectures.PurityFiniteSetting.{u}) (B : Scheme.{u})
    (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1) :
    ∃ hB : IsNoetherian B,
      IsNoetherian V.E ∧ IsSeparated (V.p ≫ b) ∧
      LocallyOfFiniteType (V.p ≫ b) ∧ QuasiCompact (V.p ≫ b) ∧
      IsSeparated V.p ∧ LocallyOfFiniteType V.p ∧ QuasiCompact V.p ∧
      SmoothOfRelativeDimension 1 V.p ∧
      (∃ (Q : VectorProjectiveCompletion.Presentation B V.𝓔)
          (ht : ∀ U : B.affineOpens,
            VectorProjectiveCompletion.t Q U ∈ Q.algebra.grading U 1)
          (a : ∀ U : B.affineOpens,
            SymmetricAlgebraSheaf.sections V.𝓔 (op U.1) ≃+*
              HomogeneousLocalization.Away (Q.algebra.grading U)
                (VectorProjectiveCompletion.t Q U)),
        (∀ (U : B.affineOpens) (m : V.𝓔.val.obj (op U.1)),
          (a U (SymmetricAlgebra.ι _ _ m)).val =
            algebraMap (Q.algebra.obj U)
              (Localization.Away (VectorProjectiveCompletion.t Q U))
                (VectorProjectiveCompletion.x Q U m) *
              IsLocalization.Away.invSelf (VectorProjectiveCompletion.t Q U)) ∧
        (∀ (U : B.affineOpens) (r : Γ(B, U.1)),
          (a U (algebraMap Γ(B, U.1) (SymmetricAlgebraSheaf.sections V.𝓔 (op U.1)) r)).val =
            algebraMap (Q.algebra.obj U)
              (Localization.Away (VectorProjectiveCompletion.t Q U))
                (algebraMap Γ(B, U.1) (Q.algebra.obj U) r)) ∧
        ∃ (c : Compactification V.p) (e : c.Z ≅ Q.algebra.relProj),
          e.hom ≫ Q.algebra.relProjHom = c.g ∧
          (c.i ≫ e.hom).opensRange = VectorProjectiveCompletion.chartOpen Q ∧
          ∀ U : B.affineOpens,
            @VectorBundleZeroSection.affineChart B hB 1 V.𝓔 V.locallyFree U ≫
                VectorProjectiveCompletion.chartMap Q ht a U =
              ((@VectorBundleZeroSection.π B hB 1 V.𝓔 V.locallyFree) ⁻¹ᵁ U.1).ι ≫
                V.phi.inv ≫ c.i ≫ e.hom) ∧
      IsClosedImmersion V.zeroSection ∧ V.zeroSection ≫ V.p = 𝟙 B ∧
      IsEffectiveCartierCenter V.zeroSection ∧
      SmoothOfRelativeDimension 0 (V.zeroSection ≫ V.p) ∧
      (∀ x : B, ringKrullDim (V.E.presheaf.stalk (V.zeroSection x)) =
        ringKrullDim (B.presheaf.stalk x) + (1 : WithBot ℕ∞)) ∧
      QuasiCompact (Scheme.Opens.ι (X := V.E) V.zeroSection.ker.support.compl) ∧
      (∀ (B' : Scheme.{u}) (h : B' ⟶ B),
        IsEffectiveCartierCenter
          (sectionBaseChange V.p V.zeroSection V.zeroSection_spec.1 (Over.mk h))) ∧
      (∀ (U : B.affineOpens)
          (frame : VectorBundleZeroSection.Trivialization B 1 V.𝓔 U.1),
        IsIso (@VectorBundleZeroSection.trivializationMap B hB 1 V.𝓔 V.locallyFree
          U.1 frame) ∧
        (@VectorBundleZeroSection.trivializationMap B hB 1 V.𝓔 V.locallyFree U.1 frame ≫
          (AffineSpace (ULift.{u} (Fin 1)) U.1.toScheme ↘ U.1.toScheme) =
            (@VectorBundleZeroSection.π B hB 1 V.𝓔 V.locallyFree) ∣_ U.1) ∧
        (@VectorBundleZeroSection.zeroRestricted B hB 1 V.𝓔 V.locallyFree U.1 ≫
          @VectorBundleZeroSection.trivializationMap B hB 1 V.𝓔 V.locallyFree U.1 frame =
            AffineSpace.zeroSection (ULift.{u} (Fin 1)) U.1.toScheme) ∧
        ∀ (R' : CommRingCat.{u}) (g : Spec R' ⟶ U.1.toScheme),
          ∃ e' : pullback V.p (g ≫ U.1.ι) ≅ Spec (CommRingCat.of (Polynomial R')),
            e'.hom ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R' →+* Polynomial R')) =
              pullback.snd V.p (g ≫ U.1.ι) ∧
            sectionBaseChange V.p V.zeroSection V.zeroSection_spec.1
                (Over.mk (g ≫ U.1.ι)) ≫ e'.hom =
              Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R')))) := by
  classical
  let : IsNoetherian B := isNoetherian_of_locallyOfFiniteType b
  let := V.locallyFree
  let p := VectorBundleZeroSection.π B 1 V.𝓔
  have hp : V.phi.hom ≫ p = V.p := V.over_commutes
  have : SmoothOfRelativeDimension 1 p := projection_smooth B 1 V.𝓔
  have hsmooth : SmoothOfRelativeDimension 1 V.p := by
    rw [← hp]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension 1) _ _).mpr inferInstance
  let := hsmooth
  have : Smooth V.p := SmoothOfRelativeDimension.smooth 1 V.p
  obtain ⟨Q, ht, a, hQnoeth, hproper, hgen, hcoeff, _, _, _,
    hsep, hlft, hqc, hnoeth, c, hZ, hg, hrange, hchart, _, _⟩ :=
      VectorProjectiveCompletion.exists_projective_completion B 1 V.𝓔
  let := hsep
  let := hlft
  let := hqc
  let := hnoeth
  have : IsSeparated V.p := by rw [← hp]; infer_instance
  have : QuasiCompact V.p := by rw [← hp]; infer_instance
  have : IsNoetherian V.E := isNoetherian_of_locallyOfFiniteType V.p
  have : IsClosedImmersion V.zeroSection := V.zeroSection_spec.2.1
  let c' : Compactification V.p :=
    { Z := c.Z
      g := c.g
      i := V.phi.hom ≫ c.i
      comm := hp.symm.trans
        ((congrArg (fun q ↦ V.phi.hom ≫ q) c.comm).trans
          (Category.assoc _ _ _).symm)
      isProper := c.isProper
      isOpenImmersion := inferInstance }
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hsmooth, ?_,
    V.zeroSection_spec.2.1, V.zeroSection_spec.1,
    section_cartier V.p V.zeroSection V.zeroSection_spec.1, ?_, ?_, inferInstance, ?_, ?_⟩
  · refine ⟨Q, ht, a, hgen, hcoeff, c', eqToIso hZ, hg.symm, ?_, ?_⟩
    · change (V.phi.hom ≫ c.i ≫ eqToHom hZ).opensRange = _
      rw [Scheme.Hom.opensRange_comp_of_isIso]
      exact hrange
    · intro U
      simpa only [c', Category.assoc, Iso.inv_hom_id_assoc, eqToIso] using hchart U
  · rw [V.zeroSection_spec.1]
    infer_instance
  · exact cartier_stalk_dimension V.zeroSection
      (section_cartier V.p V.zeroSection V.zeroSection_spec.1)
  · intro B' h
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    have : SmoothOfRelativeDimension 1 (pullback.snd V.p h) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    exact section_cartier (pullback.snd V.p h) _
      (sectionBaseChange_snd V.p V.zeroSection V.zeroSection_spec.1 (Over.mk h))
  · intro U frame
    obtain ⟨hi, ho, hz⟩ := VectorBundleZeroSection.trivializationMap_spec B 1 V.𝓔 U.1 frame
    refine ⟨hi, ho, hz, ?_⟩
    intro R' g
    let τ := VectorBundleZeroSection.trivializationMap B 1 V.𝓔 U.1 frame
    let n := ULift.{u} (Fin 1)
    let f : AffineSpace n (Spec R') ⟶ V.E :=
      AffineSpace.map n g ≫ inv τ ≫ (p ⁻¹ᵁ U.1).ι ≫ V.phi.inv
    have hτ : inv τ ≫ (p ∣_ U.1) = AffineSpace n U.1.toScheme ↘ U.1.toScheme := by
      rw [← ho, IsIso.inv_hom_id_assoc]
    have hφ : V.phi.inv ≫ V.p = p := by
      rw [← hp, Iso.inv_hom_id_assoc]
    have hpb : IsPullback f (AffineSpace n (Spec R') ↘ Spec R')
        V.p (g ≫ U.1.ι) := by
      have h₁ := AffineSpace.isPullback_map (n := n) g
      have h₂ : IsPullback (inv τ)
          (AffineSpace n U.1.toScheme ↘ U.1.toScheme) (p ∣_ U.1) (𝟙 _) :=
        IsPullback.of_horiz_isIso ⟨by simpa using hτ⟩
      have h₃ := (isPullback_morphismRestrict p U.1).flip
      have h₄ : IsPullback V.phi.inv p V.p (𝟙 B) :=
        IsPullback.of_horiz_isIso ⟨by simpa using hφ⟩
      simpa only [Category.id_comp, Category.comp_id, Category.assoc] using
        ((h₁.paste_horiz h₂).paste_horiz h₃).paste_horiz h₄
    obtain ⟨ea, hea, hez⟩ := polynomial_chart R'
    have hfzero : AffineSpace.zeroSection n (Spec R') ≫ f =
        (g ≫ U.1.ι) ≫ V.zeroSection := by
      have hzτ : AffineSpace.zeroSection n U.1.toScheme ≫ inv τ =
          VectorBundleZeroSection.zeroRestricted B 1 V.𝓔 U.1 := by
        rw [← hz, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      calc
        AffineSpace.zeroSection n (Spec R') ≫ f =
            g ≫ (AffineSpace.zeroSection n U.1.toScheme ≫ inv τ) ≫
              (p ⁻¹ᵁ U.1).ι ≫ V.phi.inv := by
          dsimp only [f]
          rw [← Category.assoc, AffineSpace.zeroSection_comp_map]
          simp only [Category.assoc]
        _ = g ≫ VectorBundleZeroSection.zeroRestricted B 1 V.𝓔 U.1 ≫
              (p ⁻¹ᵁ U.1).ι ≫ V.phi.inv := by rw [hzτ]
        _ = (g ≫ U.1.ι) ≫ V.zeroSection := by
          dsimp only [VectorBundleZeroSection.zeroRestricted, zeroSection]
          have he : U.1 ≤ VectorBundleZeroSection.zero B 1 V.𝓔 ⁻¹ᵁ p ⁻¹ᵁ U.1 := by
            dsimp only [p]
            rw [← Scheme.Hom.comp_preimage, (VectorBundleZeroSection.zero_spec B 1 V.𝓔).1]
            simp
          change g ≫ (VectorBundleZeroSection.zero B 1 V.𝓔).resLE
            (p ⁻¹ᵁ U.1) U.1 he ≫ (p ⁻¹ᵁ U.1).ι ≫ V.phi.inv = _
          have hres : (VectorBundleZeroSection.zero B 1 V.𝓔).resLE
              (p ⁻¹ᵁ U.1) U.1 he ≫ (p ⁻¹ᵁ U.1).ι =
                U.1.ι ≫ VectorBundleZeroSection.zero B 1 V.𝓔 :=
            Scheme.Hom.resLE_comp_ι _ he
          set_option backward.isDefEq.respectTransparency false in
            simpa only [Category.assoc] using
              congrArg (fun k ↦ g ≫ k ≫ V.phi.inv) hres
    let eb := hpb.isoPullback.symm
    refine ⟨eb ≪≫ ea, ?_, ?_⟩
    · simp only [Iso.trans_hom, Category.assoc, hea]
      exact hpb.isoPullback_inv_snd
    · have hsz : sectionBaseChange V.p V.zeroSection V.zeroSection_spec.1
          (Over.mk (g ≫ U.1.ι)) ≫ eb.hom = AffineSpace.zeroSection n (Spec R') := by
        apply hpb.hom_ext
        · dsimp only [eb, Iso.symm_hom]
          rw [Category.assoc, hpb.isoPullback_inv_fst, hfzero]
          exact pullback.lift_fst _ _ _
        · dsimp only [eb, Iso.symm_hom]
          calc
            _ = 𝟙 (Spec R') := by
              rw [Category.assoc, hpb.isoPullback_inv_snd]
              exact sectionBaseChange_snd _ _ _ _
            _ = _ := (AffineSpace.zeroSection_over n (Spec R')).symm
      simpa only [Iso.trans_hom, ← Category.assoc, hsz] using hez

end AlgebraicGeometry.PurityVectorBundle
