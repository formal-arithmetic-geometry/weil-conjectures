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
public import WeilConjectures.AlgebraicGeometry.OrdinaryChart.OrdinaryChartAdjunctionObjects

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

/-- Coefficient transport for an arbitrary finite or algebraically closed base field.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-smooth-purity/
sk-thm-smooth-purity-general-ring.proof.md,
Proof (2)
(blueprint: lem-pur-dnc-coefficient-transport).

Proof step 1: Put $Q_T=(-)_B$ and $N=\ell^n$. The unital map $R\to B$ gives $NB=0$; $N$ is
  invertible on
  every scheme here. Finite-type schemes over a field are locally Noetherian by
  [pqf-lem-locnoeth-lft], and quasi-compactness makes them Noetherian. The structural maps,
  normal projection and Rees projection have the compactifications fixed in the statement. For
  any of their smooth base changes the same dimension is preserved by
  [lem-sbc-smooth-relative-dimension-permanence]. Apply [det-sp-reduction-exceptional] at the
  coefficient unit and then its scalar-unit isomorphism. Thus each $c_g$ is invertible. The
  tensor/pullback comparison [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] gives exactly
  the specified $q_{g,s}$ and $q_F$, so these and the normal-pair $q$ are invertible. Scalar
  extension preserves finite Tor bounds and sends a rank-one line to its ordinary rank-one
  extension by [det-sp-scalar-extension-functor].
Proof step 2: We identify only the ordinary finite-coefficient adjoints needed for the existing
  family
  input and local models. By [thm-asd-smooth-tensor], the ordinary etale right adjoint for
  every smooth structural map is inverse image followed by tensor with a shifted locally free
  rank-one sheaf. It restricts to $\Dctf$: pull back a finite constructible stratification and
  its locally constant finite modules, then tensor on a cover trivializing the line; the Tor
  interval changes only by the displayed shift. The finite-site equivalences and
  compact-support compatibility of [sk-prop-sp-et-proet] therefore meet the hypotheses of
  [det-sp-et-proet-adjunction-transfer]. Its counit formula identifies this restricted adjoint
  with the specified pro-etale Brown adjoint. The canonical pullback/site square
  [lem-weil-pbc-comparison-pullback] and mate pasting [lem-weil-pbc-mate-pasting] identify the
  exceptional fibre and locality maps as well: they are the mates of the same compact-support
  squares with these transferred counits. This is a comparison of actual arrows, not a choice
  of isomorphisms between objects.
Proof step 3: For the scalar/base-change calculation fix a square $X'\xrightarrow uX$,
  $f':X'\to Y'$,
  $f:X\to Y$, $v:Y'\to Y$, first with a compactification $f=pj$ and its pullback. Write
  $F_D=Rf_{!,D}$, $F'_D=Rf'_{!,D}$ and $\beta_D:v_D^*F_D\to F'_Du_D^*$. The maps $b_f$ are the
  proper-counit mate followed by the open tensor map, precisely as in
  [def-sp-reduction-direct-image-comparison]. Apply [lem-fix-direct-image-scalar-exchange] to
  the proper square at $j_!M$. Its internal-module equation is an equation for these ordinary
  constant-ring maps: [lem-sf-module-object-ordinary-coefficient-equivalence] identifies
  finite coefficient tensors and the compactification composites,
  [lem-sfb-internal-module-operations-transport] identifies the geometric adjunctions, and
  [lem-fix-proetale-scalar-mate-normalization] fixes the proper scalar mate by its counit
  equation. Consequently the proper-factor scalar/exchange square commutes for the actual
  maps, without any flatness condition.
Proof step 4: The open-factor square is exactly [lem-fix-open-scalar-exchange]. Compose it with
  the proper
  square of Step 3. Naturality moves the proper scalar mate past the open exchange, and the
  open equation replaces $o_B\,\bar v_B^*e_j$ by $e_{j'}Q(o_R)$, with scalar/pullback
  comparisons inserted. Thus, writing $\lambda_w:w_B^*Q\simeq Qw_R^*$, the resulting equation
  is
  $$F'_B(\lambda_{u,M})\,\beta_B(QM)\,v_B^*b_f(M)=b_{f'}(u_R^*M)\,Q(\beta_R(M))\,\lambda_{v,F_R
  M}.$$
  On bounded constructible inputs, [lem-weil-pbc-finite-ring-constructible-derived-origin]
  gives bounded etale origins; [lem-pur-co-smooth-exchange-transport] and
  [thm-cbc-finite-level-proetale] identify this proper/open composite with the specified
  compact-support exchange and give its inverse. The same holds for $QM$, which is $\Dctf$ by
  Step 1.
Proof step 5: Step 4 also holds for the fixed primed compactification if it differs from the
  pulled-back
  one. [lem-sfb-scalar-refinement-pasting] says exactly that the proper/open scalar arrow
  commutes with each boundary-preserving refinement. Interpret its arrows through the finite
  module equivalence and the counit normalization of Step 3. The proper-refinement comparisons
  are isomorphisms and satisfy the cocycle identity by
  [lem-amb-unbounded-compact-support-comparisons]; their pro-etale realizations are the same
  comparisons under [sk-prop-sp-et-proet]. Pass through a common refinement and invert these
  comparisons. The witness and compactification independence of
  [thm-cbc-finite-level-proetale] then transports Step 4 to the prescribed
  $b_f,b_{f'},\beta_R,\beta_B$. No exceptional or orientation map is used in this refinement
  argument.
Proof step 6: Now let $f$ be smooth and $K\in\Dctf(Y,R)$, and abbreviate $G_D=f_D^!$,
  $G'_D=f_D'^!$,
  $P_D=u_D^*$, $H_D=v_D^*$. Put $M=G_RK$, which is $\Dctf$ by the constructible adjunction in
  the statement. Under the canonical $\lambda$ identifications, compare
  $c_{f'}(H_RK)Q(e_R(K))$ and $e_B(QK)P_B(c_f(K))$. Transpose under $F'_B\dashv G'_B$ using
  [def-weil-pbc-adjunction-mate]. The counit equation of [det-sp-reduction-exceptional] and
  naturality of $b$ in [det-sp-reduction-direct-image] give respectively
  $$Q(H_R\varepsilon_R(K)\circ\beta_R(M)^{-1})\circ b_{f'}(P_RM)^{-1},$$
  $$H_B(Q\varepsilon_R(K)\circ b_f(M)^{-1})\circ\beta_B(QM)^{-1}.$$ The inverse of Step 4 at
  $M$ identifies these composites. Injectivity of transposition gives
  $c_{f'}(H_RK)Q(e_R(K))=e_B(QK)P_B(c_f(K))$. This proves equality of the specified counit
  mates.
Proof step 7: Apply Step 6 at $K=R_Y$. The dualizing map used in the statement includes
  $G_B(u_Y)$, where
  $u_Y:Q(R_Y)\simeq B_Y$ is multiplication. Naturality of exceptional exchange moves this
  factor to $G'_B(H_Bu_Y)$; the monoidal unit/composition equations of
  [lem-sfb-ringed-derived-monoidal-comparisons] identify it with the primed scalar unit. We
  obtain the required equation $e_B\,u_B^*c_f=c_{f'}Q(e_R)$, including its unit factors.
  [prop-asd-smooth-base-change], transported by Step 2, makes the actual $e_D$ invertible for
  $D=R,B$: its bases are Noetherian and $N$ is invertible. This applies to the arbitrary
  $g_0,h$ of the statement; no section on $g_0$ has entered the argument.
Proof step 8: For a cartesian pair square with base $v:S'\to S$, pull Step 7 back by the primed
  section.
  By definition $q_{g,s}$ is this pullback of $c_g$ after the canonical inverse
  scalar/pullback comparison. [lem-sfb-ringed-derived-monoidal-comparisons] says these
  comparisons respect geometric composition, units and the two factorizations of the same
  ringed pullback; hence naturality and $us'=sv$ give $$r_B\,v_B^*q_{g,s}=q_{g',s'}Q(r_R),$$
  where $r_D:v_D^*C_D(g,s)\simeq C_D(g',s')$ is the specified section exchange. For the family
  and $v=i_1,i_0$ this gives $$\theta_B i_1^*q_F=q_{g,s}Q(\theta_R),\qquad\eta_B
  i_0^*q_F=q_{\pi_N,0_N}Q(\eta_R).$$ Here $\theta_D,\eta_D$ are the actual one/zero-fibre
  maps. The coefficient-independent Rees geometry in the statement identifies the primed
  pairs; no arbitrary replacement fibre map is used.
Proof step 9: For etale base localization Step 8 already gives the requested pair and family
  squares. For
  a centred etale source chart use the counit-preserving chart clause of
  [det-sp-reduction-exceptional]: for both the original and chart pair it reads $c$ as the
  same canonical Tate reassociation under etale inverse image. The ordinary chart locality
  maps are the counit-normalized maps of [lem-trf-section-local-dualizing-comparisons],
  identified on the pro-etale site by Step 2. Scalar extension and Tate pullback commute by
  [det-sp-scalar-extension-functor] and [lem-asd-etale-finite-twist-pullback], so the two
  routes through each chart are the same tensor map. This proves the source-chart localization
  square. On the standard pair it reads exactly $(R_S(r)[2r])_B\simeq B_S(r)[2r]$. Equalities
  can be checked on these charts: remove the common shift using
  [lem-weil-pbc-derived-single-fully-faithful] and use uniqueness of sheaf-map gluing in
  [lem-pur-sheaf-hom-cover-gluing].
Proof step 10: Take $\kappa_R$ from the existing finite family theorem
  [lem-pur-finite-section-family-constancy], through Step 2. Its hypotheses are exactly the
  Noetherian/invertible-annihilator and actual compactifiable Rees/normal pairs already
  checked in Step 1. This supplies the existing R comparison, without repeating its
  construction. [lem-trf-section-local-dualizing-comparisons] also gives the ordinary models
  $C_R[-2r],F_R[-2r]$ as locally constant free rank-one sheaves and the normalized local
  coordinate comparisons. Step 2 realizes these as the objects of this item. Step 1 and the
  rank-one scalar clause of [det-sp-scalar-extension-functor] give the corresponding B models.
  In the original finite-field conventions uniqueness in [prop-pur-dnc-family-constancy]
  identifies the supplied $\kappa_R$ with that proposition's comparison.
Proof step 11: Define $\kappa_B=a^*q_{g,s}\,Q(\kappa_R)\,q_F^{-1}$. Each factor is invertible.
  At $i_1$,
  substitute the first equation of Step 8 and $i_1^*\kappa_R=\theta_R$; the result is
  $i_1^*\kappa_B=\theta_B$. The scalar/pullback and section cancellations here are compatible
  by the unit and composition equations of [lem-sfb-ringed-derived-monoidal-comparisons], so
  this is the stated normalization under the actual fibre identification.
Proof step 12: By Step 10 the B objects have ordinary bounded-below shifted-line presentations.
  Full
  faithfulness of [thm-weil-pbc-site-comparison], together with Step 2, converts any
  normalized B comparison to an ordinary etale comparison with the same $\theta_B$. Apply
  [lem-trf-etale-shifted-line-normalized-descent] with the one-member identity cover and the
  already constructed $\kappa_B$. Its uniqueness is among all normalized global isomorphisms;
  hence the comparison is unique. On a centred coordinate chart the direct B comparison of
  [lem-trf-section-local-dualizing-comparisons] is normalized by its displayed correction
  $a^*(h^{-1})\lambda$. Step 8 and Step 9 show that the restriction of $\kappa_B$ is
  normalized for that same chart's actual fibre map. The same uniqueness identifies the two.
  Thus the scalar conjugate is the direct coordinate comparison, rather than merely an
  abstract trivialization.
Proof step 13: Write $j_D=i_0^*\kappa_D$, including the canonical cancellation
  $i_0^*a^*C_D\simeq C_D$.
  Thus $\delta_D=\eta_Dj_D^{-1}$. Restrict Step 11 at zero and use the scalar/composition
  coherence of [lem-sfb-ringed-derived-monoidal-comparisons] to get
  $j_B=q_{g,s}Q(j_R)(i_0^*q_F)^{-1}$. The second equation of Step 8 now gives
  $$\delta_Bq_{g,s}=\eta_B(i_0^*q_F)Q(j_R^{-1})=q_{\pi_N,0_N}Q(\eta_Rj_R^{-1})=q_{\pi_N,0_N}
  Q(\delta_R).$$
  For $r=0$ the twist is the unit and all formulas still apply. For $B=0$ all B objects and
  arrows are the unique objects and arrows of the zero category, so the same normalization and
  uniqueness assertions hold.
-/
theorem dncCoefficientTransport (k : Type u) [Field k]
    (hk : Finite k ∨ IsAlgClosed k) (ell : ℕ) [Fact ell.Prime]
    (hchar : ringChar k ≠ ell) (n : ℕ) (hn : 1 ≤ n)
    {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aS : S ⟶ Spec (.of k)) [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    {B : Type u} [CommRing B] [Finite B]
    (φ : DncCoefficientTransport.BaseRing.{u} ell n →+* B) :
    DncCoefficientTransportGeneral.Assertions k ell n g s hs
      (DncCoefficientTransport.geometry k d g aS s hs) φ := by
  classical
  have _hbase := hk
  let G := DncCoefficientTransport.geometry k d g aS s hs
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
  have hS := DncCoefficientTransport.exponent_unit k ell n hchar aS
  have hLine := DncCoefficientTransport.exponent_unit k ell n hchar
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
  change DncCoefficientTransportGeneral.Assertions k ell n g s hs G φ
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
    have hu := DncCoefficientTransport.exponent_unit k ell n hchar S0.hom
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
