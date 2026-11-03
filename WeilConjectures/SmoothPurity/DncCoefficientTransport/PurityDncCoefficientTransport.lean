/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.DncCoefficientTransport.DncCoefficientTransportData
import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.FiniteSectionFamilyConstancy
import WeilConjectures.AlgebraicGeometry.Finite.Smooth.FiniteSmoothDualizingScalar
import WeilConjectures.SixFunctors.DncCoefficientTransport.SectionScalarBaseChange
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarSectionCompositor
import all WeilConjectures.AlgebraicGeometry.AffineLineNormalizedDescent.EtaleShiftedLineNormalizedDescent
import all WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SmoothPurity.DncCoefficientTransportGeneral.DncCoefficientTransportGeneralData

/-! # Finite coefficient transport for the actual smooth-section deformation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

attribute [local instance] Scheme.Etale.essentiallySmall

attribute [local irreducible] DncCoefficientTransport.dualizingMap
  DncCoefficientTransport.sectionMap DncCoefficientTransport.realizedSectionMap
  ProEtale.reductionEtaleChartRightIso ProEtale.reductionEtaleChartScalarIso

namespace DncCoefficientTransport

/-- The domain facts follow from the source hypotheses, rather than being additional
hypotheses of the coefficient theorem.
Source: Proof (2) Step 1, sk-lem-geometry (blueprint: lem-pur-dnc-coefficient-transport).
Proof: finite type over the field makes S and V Noetherian. A closed section of a
smooth relative-dimension d map is regular of codimension d. On its extended-Rees
charts x_i=t*u_i the deformation projection is smooth of dimension d; its zero
fibre is the actual rank-d normal bundle. The projections are separated finite type,
and Nagata gives the three coefficient-independent compactifications. -/
theorem geometry (k : Type u) [Field k] {V S : Scheme.{u}}
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aS : S ⟶ Spec (.of k)) [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) : Geometry g s := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have := SmoothOfRelativeDimension.smooth d g
  have : HasCompactification g := (NagataCompactification g).hasCompactification
  have := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have : QuasiCompact (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have : IsSeparated (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have := SmoothOfRelativeDimension.smooth d (Scheme.Hom.normalConeProj g s)
  exact ⟨inferInstance, Scheme.Hom.hasCompactification_deformationSpaceProj g s d hs,
    (NagataCompactification (Scheme.Hom.normalConeProj g s)).hasCompactification,
    inferInstance⟩

/-- The prime-power coefficient is a unit on every structural base in the theorem.
Source: Proof (2), Step 1 (blueprint: lem-pur-dnc-coefficient-transport).
Proof: ell is prime and differs from the characteristic of the field, so it is a unit
in k; its power maps to a unit in the global sections of S along aS. -/
private theorem exponent_unit (k : Type u) [Field k] (ell n : ℕ)
    [Fact ell.Prime] (hchar : ringChar k ≠ ell) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤)) := by
  have hl : IsUnit (ell : k) := by
    refine isUnit_iff_ne_zero.mpr fun h => hchar ?_
    rw [CharP.cast_eq_zero_iff k (ringChar k)] at h
    exact ((Fact.out : ell.Prime).eq_one_or_self_of_dvd _ h).resolve_left
      CharP.ringChar_ne_one
  have hu := ((hl.pow n).map (Scheme.ΓSpecIso (.of k)).inv.hom).map aS.appTop.hom
  simpa only [map_pow, map_natCast, Nat.cast_pow] using hu

private theorem section_iso {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] (s : S ⟶ V)
    (h : IsIso (Etale.ExceptionalCoefficients.dualizingScalarMap φ g)) :
    IsIso (sectionMap φ g s) := by
  have : IsIso (dualizingMap φ g) := by
    simpa only [dualizingMap, Etale.ExceptionalCoefficients.dualizingScalarMap] using h
  unfold sectionMap
  infer_instance

private theorem realized_iso {A B : Type u}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] (s : S ⟶ V)
    (h : IsIso (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s)) :
    IsIso (realizedSectionMap φ g s) := by
  unfold realizedSectionMap
  infer_instance

private theorem coordinate_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    (m : ℤ)
    (hC : ∃ Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty ((Etale.sectionInvariant A g s)⟦m⟧ ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj Q))
    (h1 : IsIso (Etale.NoetherianSectionSpecialization.atOne A g s hs))
    (κ : Etale.NoetherianSectionSpecialization.family A g s ≅
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (Etale.sectionInvariant A g s))
    (hκ : Etale.NoetherianSectionSpecialization.Normalized A g s hs κ) :
    CoordinateNormalization A g s hs h1 κ := by
  intro T b _ _ _ C0 e
  let theta := asIso (Etale.NoetherianSectionSpecialization.atOne A g s hs)
  let a := (Etale.upperStar (ModuleCat.{u + 1} A)
    (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor
  let ratio := Etale.sectionRestrictionIso (ModuleCat.{u + 1} A) b
    (AffineSpace.map (ULift.{u} (Fin 1)) b) (AffineSpace.oneSection_comp_map b)
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) T) theta e
  let en := e ≪≫ a.mapIso ratio.symm
  have hen : Etale.AffineLineNormalizedDescent.LocallyNormalized A b theta en := by
    unfold Etale.AffineLineNormalizedDescent.LocallyNormalized
    rw [Etale.sectionRestrictionIso_trans_right]
    exact Iso.self_symm_id ratio
  let res := (Etale.upperStar (ModuleCat.{u + 1} A)
    (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.mapIso κ ≪≫
      Etale.NoetherianSectionSpecialization.linePullback A b (Etale.sectionInvariant A g s)
  have hres : Etale.AffineLineNormalizedDescent.LocallyNormalized A b theta res := by
    have htheta : (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.mapIso κ ≪≫
        (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
          (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)).app _ = theta :=
      Iso.ext hκ
    change Etale.sectionRestrictionIso (ModuleCat.{u + 1} A) b _ _ _ theta res = Iso.refl _
    rw [← htheta]
    exact Etale.sectionRestrictionIso_restrict (ModuleCat.{u + 1} A) b
      (AffineSpace.map (ULift.{u} (Fin 1)) b) (AffineSpace.oneSection_comp_map b)
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) T)
      (AffineSpace.map_over b) (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S) κ
  have heq := Etale.AffineLineNormalizedDescent.local_comparison_unique A b m hC
    theta en res hen hres
  have hh := congrArg Iso.hom heq
  change e.hom ≫ a.map ratio.inv = res.hom at hh
  rw [← Category.assoc]
  change res.hom ≫ a.map ratio.hom = e.hom
  apply (cancel_mono (a.map ratio.inv)).1
  rw [Category.assoc, ← a.map_comp, Iso.hom_inv_id, a.map_id, Category.comp_id]
  exact hh.symm

private theorem normalized_transport
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V S : Scheme.{u}} (g : V ⟶ S)
    [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)]
    (hcompat : FibreCompatibility φ g s hs)
    (hq : IsIso (sectionMap φ g s))
    (hqF : IsIso (sectionMap φ (Scheme.Hom.deformationSpaceProj g s)
      s.deformationSpaceSection))
    (h0 : IsIso (Etale.NoetherianSectionSpecialization.atZero B g s))
    (m : ℤ)
    (hC : ∃ Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B),
      Nonempty ((Etale.sectionInvariant B g s)⟦m⟧ ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj Q)) :
    NormalizedTransport φ g s hs := by
  intro κR hκR
  let a := AffineSpace (ULift.{u} (Fin 1)) S ↘ S
  let EA := Etale.scalarExtension φ (AffineSpace (ULift.{u} (Fin 1)) S)
  let ES := Etale.scalarExtension φ S
  let aB := (Etale.upperStar (ModuleCat.{u + 1} B) a).leftDerivedFunctor
  let q := asIso (sectionMap φ g s)
  let qF := asIso (sectionMap φ (Scheme.Hom.deformationSpaceProj g s)
    s.deformationSpaceSection)
  let κB := qF.symm ≪≫ EA.mapIso κR ≪≫
    (Etale.scalarPullbackIso φ a).symm.app _ ≪≫ aB.mapIso q
  have hconj : sectionMap φ (Scheme.Hom.deformationSpaceProj g s)
      s.deformationSpaceSection ≫ κB.hom =
      EA.map κR.hom ≫ (Etale.scalarPullbackIso φ a).inv.app _ ≫
        aB.map (sectionMap φ g s) := by
    simp [κB, qF, q]
  have hnorm : Etale.NoetherianSectionSpecialization.Normalized B g s hs κB := by
    let i := AffineSpace.oneSection (ULift.{u} (Fin 1)) S
    let iA := (Etale.upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor
    let iB := (Etale.upperStar (ModuleCat.{u + 1} B) i).leftDerivedFunctor
    let cA := Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) i a
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)
    let cB := Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} B) i a
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)
    have hn := ((Etale.scalarPullbackIso φ i).inv.naturality κR.hom).symm
    change (Etale.scalarPullbackIso φ i).inv.app _ ≫ iB.map (EA.map κR.hom) =
      ES.map (iA.map κR.hom) ≫ (Etale.scalarPullbackIso φ i).inv.app _ at hn
    have hc := cB.hom.naturality (sectionMap φ g s)
    change iB.map (aB.map (sectionMap φ g s)) ≫ cB.hom.app _ =
      cB.hom.app _ ≫ sectionMap φ g s at hc
    have hcoh := Etale.scalar_section_compositor φ i a
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)
      (Etale.sectionInvariant A g s)
    change (Etale.scalarPullbackIso φ i).inv.app _ ≫
      iB.map ((Etale.scalarPullbackIso φ a).inv.app _) ≫ cB.hom.app _ =
      ES.map (cA.hom.app _) at hcoh
    change iB.map κB.hom ≫ cB.hom.app _ = _
    apply (cancel_epi ((Etale.scalarPullbackIso φ i).inv.app _ ≫
      iB.map (sectionMap φ (Scheme.Hom.deformationSpaceProj g s)
        s.deformationSpaceSection))).1
    simp only [Category.assoc]
    erw [← iB.map_comp_assoc, hconj]
    simp only [Functor.map_comp, Category.assoc]
    rw [hc]
    erw [reassoc_of% hn, reassoc_of% hcoh]
    erw [← ES.map_comp_assoc, hκR]
    exact hcompat.1.symm
  have hspecial : sectionMap φ g s ≫
      Etale.NoetherianSectionSpecialization.specialization B g s κB =
      ES.map (Etale.NoetherianSectionSpecialization.specialization A g s κR) ≫
        sectionMap φ (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection := by
    let i := AffineSpace.zeroSection (ULift.{u} (Fin 1)) S
    let iA := (Etale.upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor
    let iB := (Etale.upperStar (ModuleCat.{u + 1} B) i).leftDerivedFunctor
    let cA := Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) i a
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) S)
    let cB := Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} B) i a
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) S)
    have hconjInv : aB.map (sectionMap φ g s) ≫ κB.inv =
        (Etale.scalarPullbackIso φ a).hom.app _ ≫ EA.map κR.inv ≫
          sectionMap φ (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection := by
      simp [κB, q, qF, Category.assoc]
    have hc := cB.inv.naturality (sectionMap φ g s)
    change sectionMap φ g s ≫ cB.inv.app _ =
      cB.inv.app _ ≫ iB.map (aB.map (sectionMap φ g s)) at hc
    have hn := ((Etale.scalarPullbackIso φ i).inv.naturality κR.inv).symm
    change (Etale.scalarPullbackIso φ i).inv.app _ ≫ iB.map (EA.map κR.inv) =
      ES.map (iA.map κR.inv) ≫ (Etale.scalarPullbackIso φ i).inv.app _ at hn
    have hcoh := Etale.scalar_section_compositor φ i a
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) S)
      (Etale.sectionInvariant A g s)
    have hcohInv : cB.inv.app (ES.obj (Etale.sectionInvariant A g s)) ≫
        iB.map ((Etale.scalarPullbackIso φ a).hom.app (Etale.sectionInvariant A g s)) =
        ES.map (cA.inv.app (Etale.sectionInvariant A g s)) ≫
          (Etale.scalarPullbackIso φ i).inv.app
            ((Etale.upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctor.obj
              (Etale.sectionInvariant A g s)) := by
      apply (cancel_mono (iB.map ((Etale.scalarPullbackIso φ a).inv.app _))).1
      simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
      apply (cancel_mono (cB.hom.app _)).1
      simp only [Category.assoc]
      rw [hcoh, ← ES.map_comp, Iso.inv_hom_id_app]
      erw [iB.map_id, Category.id_comp, Iso.inv_hom_id_app, ES.map_id]
      rfl
    change sectionMap φ g s ≫ (cB.inv.app _ ≫ iB.map κB.inv ≫ _) =
      ES.map (cA.inv.app _ ≫ iA.map κR.inv ≫ _) ≫ _
    rw [← Category.assoc, hc]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hconjInv]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hcohInv, reassoc_of% hn, hcompat.2]
  refine ⟨κB, hnorm, ?_, hconj, ?_, ?_, hspecial⟩
  · intro κ hκ
    apply Iso.ext
    apply Etale.AffineLineNormalizedDescent.map_eq_of_oneSection B S m hC
    exact (cancel_mono
      ((Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} B)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S) a
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)).hom.app _)).1
      (hκ.trans hnorm.symm)
  · intro h1'
    exact coordinate_normalization B g s hs m hC h1' κB hnorm
  · unfold Etale.NoetherianSectionSpecialization.specialization
    infer_instance

/-- Coefficient transport for the actual smooth-section deformation family.
Source: Proof (2), sk-thm-smooth-purity-general-ring
(blueprint: lem-pur-dnc-coefficient-transport).
Proof, in the seven DAG steps:
1. At E=Q_ell identify the positive finite coefficient ring with Z/ell^n. Apply
   det-sp-reduction-exceptional to g, the actual Rees deformation projection, and
   the actual normal projection. Pull its counit transpose back to the sections
   using lem-weil-pbc-ringed-topoi-derived-tensor-pullback to obtain the defined q maps.
2. Apply det-sp-mixed-base-change at the coefficient unit. Its square gives the
   arbitrary-base-change equation without a section on g0. Apply it to i1 and i0
   and compose the section pullbacks to obtain both displayed fibre equations.
3. On centered etale charts x_i=t*u_i, the counit is the etale fibre sum followed
   by the ordered affine trace. det-sp-reduction-exceptional therefore computes q
   as canonical Tate-line reassociation, x tensor b mapping to bx. The scalar and
   pullback identifications in det-sp-scalar-extension-functor and
   lem-asd-etale-finite-twist-pullback prove localization and the standard-pair value.
4. Scalar-extend the R-family comparison of prop-pur-dnc-family-constancy and
   conjugate by qF and a*q. The one-fibre equation cancels these q maps at t=1.
5. Remove the common shift [2d] from the finite locally constant B-lines and use
   lem-weil-pbc-derived-single-fully-faithful. On restriction to R the sheaves
   remain finite locally constant, even for a nonflat B. The section t=1 meets
   every affine-line component (lem-pur-a1-components). The difference of two
   normalized maps is zero there and hence everywhere by lem-pur-lisse-morphism-rigidity.
   For empty S all maps are unique.
6. The local constant-family comparison on each centered coordinate chart is
   normalized at one, so Step 5 identifies it with kappaB. Glue using
   lem-pur-sheaf-hom-cover-gluing after removing the common shift.
7. Restrict the conjugation equation at zero and apply the zero-fibre square.
   Invert i0*kappa to get deltaB q = qNormal (deltaR)_B. The same formulas include
   d=0, empty bases and B=0; no flatness assumption on the ring map is used. -/
theorem dncCoefficientTransport (D : FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p) (n : ℕ) (hn : 1 ≤ n)
    {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aS : S ⟶ Spec (.of D.k)) [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    {B : Type u} [CommRing B] [Finite B]
    (φ : DncCoefficientTransport.BaseRing.{u} ell n →+* B) :
    DncCoefficientTransport.Assertions D ell n g s hs
      (DncCoefficientTransport.geometry D d g aS s hs) φ := by
  classical
  let G := DncCoefficientTransport.geometry D d g aS s hs
  have := G.compact
  have := G.compactFamily
  have := G.compactNormal
  have := G.quasiCompactNormal
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian S := ⟨⟩
  have := SmoothOfRelativeDimension.smooth d g
  have : IsNoetherian V := isNoetherian_of_locallyOfFiniteType g
  have hD := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have : IsNoetherian (AffineSpace (ULift.{u} (Fin 1)) S) :=
    isNoetherian_of_locallyOfFiniteType (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
  have : IsNoetherian s.ker.deformationSpace :=
    isNoetherian_of_locallyOfFiniteType (Scheme.Hom.deformationSpaceProj g s)
  have hNormal : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have : IsSeparated (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have := SmoothOfRelativeDimension.smooth d (Scheme.Hom.normalConeProj g s)
  have : IsNoetherian s.ker.normalCone :=
    isNoetherian_of_locallyOfFiniteType (Scheme.Hom.normalConeProj g s)
  let A := ULift.{u + 1, u} (DncCoefficientTransport.BaseRing.{u} ell n)
  let C := ULift.{u + 1, u} B
  let ψ : A →+* C := RingHom.ulift.{u + 1, u + 1, u, u} φ
  have hN : 0 < ell ^ n := pow_pos (Fact.out : ell.Prime).pos n
  have hA : ((ell ^ n : ℕ) : A) = 0 := by
    apply ULift.ext
    apply ULift.ext
    exact ZMod.natCast_self _
  have hB : ((ell ^ n : ℕ) : C) = 0 := by
    rw [← map_natCast ψ, hA, map_zero]
  have hS := DncCoefficientTransport.exponent_unit D ell n hell aS
  have hLine := DncCoefficientTransport.exponent_unit D ell n hell
    ((AffineSpace (ULift.{u} (Fin 1)) S ↘ S) ≫ aS)
  have hScalar := Etale.finite_smooth_dualizing_scalar ψ ell n hn hA hB hS g d
  have hScalarF := Etale.finite_smooth_dualizing_scalar ψ ell n hn hA hB hLine
    (Scheme.Hom.deformationSpaceProj g s) d
  have hScalarN := Etale.finite_smooth_dualizing_scalar ψ ell n hn hA hB hS
    (Scheme.Hom.normalConeProj g s) d
  have hq := DncCoefficientTransport.section_iso ψ g s hScalar.1
  have hqF := DncCoefficientTransport.section_iso ψ (Scheme.Hom.deformationSpaceProj g s)
    s.deformationSpaceSection hScalarF.1
  have hqN := DncCoefficientTransport.section_iso ψ (Scheme.Hom.normalConeProj g s)
    s.normalConeZeroSection hScalarN.1
  have hBase := DncCoefficientTransport.section_scalar_base_change ψ (ell ^ n)
    hN hA hB hS g d
  have hBaseF := DncCoefficientTransport.section_scalar_base_change ψ (ell ^ n)
    hN hA hB hLine (Scheme.Hom.deformationSpaceProj g s) d
  have hFibre : DncCoefficientTransport.FibreCompatibility ψ g s hs :=
    ⟨hBaseF.2 g (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
        (Scheme.Hom.deformationSpaceOneFibre g s)
        (Scheme.Hom.isPullback_deformationSpaceOneFibre g s)
        s.deformationSpaceSection s (Scheme.Hom.comp_deformationSpaceOneFibre hs),
      hBaseF.2 (Scheme.Hom.normalConeProj g s)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) s.ker.normalConeToDeformationSpace
        (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
        s.deformationSpaceSection s.normalConeZeroSection
        Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace⟩
  have hConstA := Etale.NoetherianSectionSpecialization.finite_family_constancy
    A (ell ^ n) hN hA hS d g s hs
  have hConstB := Etale.NoetherianSectionSpecialization.finite_family_constancy
    C (ell ^ n) hN hB hS d g s hs
  have := Etale.NoetherianSectionSpecialization.compact_normalProjection d g s hs
  have hlines := Etale.SectionLocalDualizingComparisons.section_local_dualizing_comparisons
    C (ell ^ n) hN hB hS d g s hs
  have hshape := Etale.NoetherianSectionSpecialization.line_shape C d S _ hlines.1
  change DncCoefficientTransport.Assertions D ell n g s hs G φ
  refine ⟨DncCoefficientTransport.realized_iso φ g s hq,
    DncCoefficientTransport.realized_iso φ _ _ hqF,
    DncCoefficientTransport.realized_iso φ _ _ hqN, hq, hqF, hqN,
    hConstA.1, hConstA.2.1, hConstB.1, hConstB.2.1, hConstA.2.2,
    hFibre, ?_, ?_, ?_, ?_⟩
  · intro V' S' g' _ _ b _ v sq s' hsection
    have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian b
    exact hBase.2 g' b v sq s s' hsection
  · intro V0 S0 S0' _ _ _ _ _ _ _ _ _ g0 r _ _ _ b
    have : IsNoetherian V0.left := by
      have := LocallyOfFiniteType.isLocallyNoetherian V0.hom
      have := QuasiCompact.compactSpace_of_compactSpace V0.hom
      exact ⟨⟩
    have : IsNoetherian S0.left := by
      have := LocallyOfFiniteType.isLocallyNoetherian S0.hom
      have := QuasiCompact.compactSpace_of_compactSpace S0.hom
      exact ⟨⟩
    have : IsNoetherian S0'.left := by
      have := LocallyOfFiniteType.isLocallyNoetherian S0'.hom
      have := QuasiCompact.compactSpace_of_compactSpace S0'.hom
      exact ⟨⟩
    have := SmoothOfRelativeDimension.smooth r g0.left
    have : IsSeparated (g0.left ≫ S0.hom) := by
      simpa only [g0.w] using inferInstanceAs (IsSeparated V0.hom)
    have : IsSeparated g0.left := IsSeparated.of_comp g0.left S0.hom
    have hu := DncCoefficientTransport.exponent_unit D ell n hell S0.hom
    have huStalk (x : S0.left) : IsUnit ((ell ^ n : ℕ) : S0.left.presheaf.stalk x) := by
      simpa only [map_natCast] using hu.map (S0.left.presheaf.germ ⊤ x trivial).hom
    exact ⟨(Etale.smooth_exceptional_base_change A (ell ^ n) hN hA huStalk
        g0.left r b.left).2.1,
      (Etale.smooth_exceptional_base_change C (ell ^ n) hN hB huStalk
        g0.left r b.left).2.1,
      (DncCoefficientTransport.section_scalar_base_change ψ (ell ^ n) hN hA hB hu
        g0.left r).1 b.left⟩
  · intro V0 S0 _ _ _ _ _ _ _ _ g0 _ r _ U _ i _ e _ _ _ _ he MA MB hA' hB'
        tA tB PA PB hu
    have := SmoothOfRelativeDimension.smooth r g0.left
    have : IsSeparated (g0.left ≫ S0.hom) := by
      simpa only [g0.w] using inferInstanceAs (IsSeparated V0.hom)
    have : QuasiCompact (g0.left ≫ S0.hom) := by
      simpa only [g0.w] using inferInstanceAs (QuasiCompact V0.hom)
    have : IsSeparated g0.left := IsSeparated.of_comp g0.left S0.hom
    have : QuasiCompact g0.left := QuasiCompact.of_comp g0.left S0.hom
    exact (Etale.finite_smooth_dualizing_scalar ψ ell n hn hA' hB' hu g0.left r).2
      i e he MA MB tA tB PA PB
  · exact DncCoefficientTransport.normalized_transport ψ g s hs hFibre hq hqF
      hConstB.2.1 (-(2 * (d : ℤ))) (hshape.imp fun _ h ↦ h.2)

attribute [-instance] CategoryTheory.catToReflQuiver in
end DncCoefficientTransport

attribute [-instance] CategoryTheory.catToReflQuiver in
end WeilConjectures
