/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedDncFamily
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionInvariant
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Purity.PurityNormalProjection
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
public import WeilConjectures.AlgebraicGeometry.SmoothSectionCentredCoordinates.SmoothSectionCentredCoordinates
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleReesChart
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.AffineSpace
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DncInvariance.PurityDncInvarianceStage2
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Geometry and native family comparisons for a section deformation

Source: latest blueprint, sec-smooth-purity/sk-lem-geometry,
lem-pur-dnc-section-geometry.md, clauses (1)--(5)
(blueprint: lem-pur-dnc-section-geometry).

The geometric objects are the actual extended-Rees scheme, its augmentation section,
and the associated-graded normal cone. The sheaf clauses below use the recorded native
condensed family and Q50 section invariant on the small pro-etale site. Every comparison
is the specified exceptional counit mate with the canonical pullback compositors.
The finite Tate value is transported by the fixed site comparison and section-action encoding.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.DncSectionGeometry

variable (D : FiniteFieldDatum.{u})
  (B V : Over (Spec (.of D.k)))
  [hBft : LocallyOfFiniteType B.hom] [hBqc : QuasiCompact B.hom] [hBsep : IsSeparated B.hom]
  [hVft : LocallyOfFiniteType V.hom] [hVqc : QuasiCompact V.hom] [hVsep : IsSeparated V.hom]
  (d : ℕ) (g : V ⟶ B) [hgsm : SmoothOfRelativeDimension d g.left]
  [hgsep : IsSeparated g.left] [hgft : LocallyOfFiniteType g.left]
  [hgqc : QuasiCompact g.left]
  (s : B ⟶ V) [hclosed : IsClosedImmersion s.left] (hs : s ≫ g = 𝟙 B)

include hBft hBqc hBsep hVft hVqc hVsep hgsm hgsep hgft hgqc hclosed hs

/-- Typing consequences of the standing hypotheses, rather than additional assumptions.
Source: sk-lem-geometry (1),(2),(4), and the sk-thm-dnc domain check
(blueprint: lem-pur-dnc-section-geometry).

Proof: finite type over the field makes B Noetherian. Centred coordinates identify
I/I^2 with a locally free rank-d module, and the Rees deformation with an etale chart over
B[t,u]. Together with the punctured product this proves smoothness of the family.
The zero fibre is its base change, hence smooth separated and quasi-compact. Nagata
compactification applies to g, the family, its normal fibre, and the standard pair.
These assertions supply geometric proof arguments only. -/
theorem domains :
    IsNoetherian B.left ∧
    HasCompactification g.left ∧
    HasCompactification (Scheme.Hom.deformationSpaceProj g.left s.left) ∧
    HasCompactification (Scheme.Hom.normalConeProj g.left s.left) ∧
    QuasiCompact (Scheme.Hom.normalConeProj g.left s.left) ∧
    HasCompactification (Scheme.Hom.deformationSpaceProj
      (AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left)
      (AffineSpace.zeroSection (ULift.{u} (Fin d)) B.left)) := by
  have hs' : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f ↦ f.left) hs
  haveI := LocallyOfFiniteType.isLocallyNoetherian B.hom
  haveI := QuasiCompact.compactSpace_of_compactSpace B.hom
  haveI : IsNoetherian B.left := ⟨⟩
  haveI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g.left s.left) :=
    (Scheme.Hom.normalConeData d hs').smoothOfRelativeDimension_proj
  haveI := SmoothOfRelativeDimension.smooth d
    (Scheme.Hom.normalConeProj g.left s.left)
  haveI : QuasiCompact (Scheme.Hom.normalConeProj g.left s.left) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g.left s.left) inferInstance
  haveI : IsSeparated (Scheme.Hom.normalConeProj g.left s.left) :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g.left s.left) inferInstance
  haveI : SmoothOfRelativeDimension d
      (AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left) := by
    simpa using (inferInstance : SmoothOfRelativeDimension (Nat.card (ULift.{u} (Fin d)))
      (AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left))
  exact ⟨inferInstance, (NagataCompactification g.left).hasCompactification,
    Scheme.Hom.hasCompactification_deformationSpaceProj g.left s.left d hs',
    (NagataCompactification (Scheme.Hom.normalConeProj g.left s.left)).hasCompactification,
    inferInstance, Scheme.Hom.hasCompactification_deformationSpaceProj _ _ d
      (AffineSpace.zeroSection_over _ _)⟩

/-- The fibres, centred coordinates and punctured product of the actual Rees scheme.
Source: sk-lem-geometry (1)--(3), geometric part
(blueprint: lem-pur-dnc-section-geometry).

Proof: first use finite-type Noetherian permanence and the centred-coordinate lemma.
In a centred etale chart P=S[x] -> R the section ideal is (x)R. The extended Rees
algebra is R tensor_P S[t,u], with x_i=t*u_i, by etale_rees_chart. Inverting t gives
R[t,t^-1], evaluation at one gives R, and quotienting by t gives gr_I R. The
homogeneous comparison sends [f]_r to [f/t^r]; the symmetric-to-graded comparison
identifies this with the normal bundle. The augmentation kills its positive degrees,
so the zero-fibre section is precisely zero. The coordinate charts and the punctured
product cover the deformation and prove smoothness of pure dimension d.
The fibre and generic squares below use the specified coefficientwise maps. -/
theorem geometry :
    IsPullback (Scheme.Hom.deformationSpaceOneFibre g.left s.left) g.left
      (Scheme.Hom.deformationSpaceProj g.left s.left)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left) ∧
    s.left ≫ Scheme.Hom.deformationSpaceOneFibre g.left s.left =
      AffineSpace.oneSection (ULift.{u} (Fin 1)) B.left ≫ s.left.deformationSpaceSection ∧
    IsPullback s.left.ker.normalConeToDeformationSpace
      (Scheme.Hom.normalConeProj g.left s.left)
      (Scheme.Hom.deformationSpaceProj g.left s.left)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left) ∧
    s.left.normalConeZeroSection ≫ s.left.ker.normalConeToDeformationSpace =
      AffineSpace.zeroSection (ULift.{u} (Fin 1)) B.left ≫ s.left.deformationSpaceSection ∧
    Scheme.Hom.purityNormalProjection s.left = Scheme.Hom.normalConeProj g.left s.left ∧
    (ConormalGradedAlgebra.piece s.left 1).IsFiniteLocallyFreeOfRank d ∧
    IsIso (ConormalGradedAlgebra.symmetricComparison s.left) ∧
    (∃ (I : Type u) (c : I → SmoothSectionCentredCoordinates.Chart d g.left s.left),
      ⨆ i, (c i).T.1 = ⊤) ∧
    (∀ c : SmoothSectionCentredCoordinates.Chart d g.left s.left,
      let A := Γ(B.left, c.T.1)
      let R := Γ(V.left, c.U.1)
      letI : Algebra (MvPolynomial (Fin d) A) R :=
        (MvPolynomial.eval₂Hom (g.left.appLE c.T.1 c.U.1 c.mapsInto).hom c.x).toAlgebra
      Function.Bijective (etaleReesTensorMap A R d) ∧
      (∀ i : Fin d, (Ideal.mvPolynomialExtendedReesAlgebraEquiv A (Fin d)).symm
        (algebraMap (MvPolynomial (Fin d) A)
          (Ideal.mvPolynomialOrigin A (Fin d)).extendedReesAlgebra (MvPolynomial.X i)) =
            MvPolynomial.C Polynomial.X * MvPolynomial.X i) ∧
      Etale (Spec.map (CommRingCat.ofHom (etaleReesChartSchemeMap A R d)))) ∧
    SmoothOfRelativeDimension d (Scheme.Hom.deformationSpaceProj g.left s.left) ∧
    IsPullback (Scheme.Hom.deformationSpaceGeneric g.left s.left) (pullback.snd _ _)
      (Scheme.Hom.deformationSpaceProj g.left s.left) (Scheme.Hom.puncturedLine B.left).ι ∧
    (∃ σ : (Scheme.Hom.puncturedLine B.left).toScheme ⟶
        pullback g.left ((Scheme.Hom.puncturedLine B.left).ι ≫
          (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)),
      σ ≫ pullback.snd _ _ = 𝟙 _ ∧
      σ ≫ pullback.fst _ _ = (Scheme.Hom.puncturedLine B.left).ι ≫
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ s.left ∧
      σ ≫ Scheme.Hom.deformationSpaceGeneric g.left s.left =
        (Scheme.Hom.puncturedLine B.left).ι ≫ s.left.deformationSpaceSection) := by
  have hs' : s.left ≫ g.left = 𝟙 B.left := congrArg (fun f ↦ f.left) hs
  haveI := LocallyOfFiniteType.isLocallyNoetherian B.hom
  haveI := QuasiCompact.compactSpace_of_compactSpace B.hom
  haveI : IsNoetherian B.left := ⟨⟩
  have H := SmoothSectionCentredCoordinates.exists_centred_coordinates d g.left s.left hs'
  refine ⟨Scheme.Hom.isPullback_deformationSpaceOneFibre g.left s.left,
    Scheme.Hom.comp_deformationSpaceOneFibre hs',
    Scheme.Hom.isPullback_normalConeToDeformationSpace g.left s.left,
    Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace,
    Scheme.Hom.purityNormalProjection_eq s.left g.left hs', H.2.2.1, H.2.2.2, H.1, ?_,
    Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g.left s.left hs',
    Scheme.Hom.isPullback_deformationSpaceGeneric g.left s.left, ?_⟩
  · intro c
    letI : Algebra (MvPolynomial (Fin d) Γ(B.left, c.T.1)) Γ(V.left, c.U.1) :=
      (MvPolynomial.eval₂Hom (g.left.appLE c.T.1 c.U.1 c.mapsInto).hom c.x).toAlgebra
    have h := etale_rees_chart Γ(B.left, c.T.1) Γ(V.left, c.U.1) d c.algebraEtale
    exact ⟨h.2.2.1, h.2.1, h.2.2.2.2.1⟩
  · let P := Scheme.Hom.isPullback_deformationSpaceGeneric g.left s.left
    have hm : ((Scheme.Hom.puncturedLine B.left).ι ≫ s.left.deformationSpaceSection) ≫
        Scheme.Hom.deformationSpaceProj g.left s.left =
          𝟙 _ ≫ (Scheme.Hom.puncturedLine B.left).ι := by
      rw [Category.assoc, Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs',
        Category.comp_id, Category.id_comp]
    refine ⟨P.lift _ _ hm, P.lift_snd _ _ _, ?_, P.lift_fst _ _ _⟩
    rw [← Scheme.Hom.deformationSpaceGeneric_toBase g.left s.left,
      P.lift_fst_assoc, Category.assoc, Scheme.Hom.deformationSpaceSection_toBase]

end WeilConjectures.PurityFiniteSetting.DncSectionGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing.SectionGeometry

variable {D : WeilConjectures.FiniteFieldDatum.{u}}

/-- The canonical standard-pair coordinate isomorphism and the formula x_k=t*u_k.
Source: sk-lem-geometry (4) (blueprint: lem-pur-dnc-section-geometry).
Proof: the polynomial-origin extended Rees equivalence is S[t,u]; its inverse sends
x_k to t*u_k. Taking Spec gives the specified isomorphism. This works also for d=0
and the zero ring on an empty affine open. -/
theorem standardCoordinates (B : Over (Spec (.of D.k))) (d : ℕ) :
    IsIso (Scheme.Hom.deformationSpaceToAffineSpace (ULift.{u} (Fin d)) B.left) ∧
    (∀ (U : B.left.affineOpens) (i : Fin d),
      (Ideal.mvPolynomialExtendedReesAlgebraEquiv Γ(B.left, U.1) (Fin d)).symm
        (algebraMap (MvPolynomial (Fin d) Γ(B.left, U.1))
          (Ideal.mvPolynomialOrigin Γ(B.left, U.1) (Fin d)).extendedReesAlgebra
            (MvPolynomial.X i)) = MvPolynomial.C Polynomial.X * MvPolynomial.X i) := by
  refine ⟨inferInstance, ?_⟩
  intro U i
  apply (Ideal.mvPolynomialExtendedReesAlgebraEquiv Γ(B.left, U.1) (Fin d)).injective
  apply Subtype.ext
  rw [RingEquiv.apply_symm_apply]
  change LaurentPolynomial.C (MvPolynomial.X i) =
    Ideal.mvPolynomialToLaurent Γ(B.left, U.1) (Fin d)
      (MvPolynomial.C Polynomial.X * MvPolynomial.X i)
  rw [map_mul, Ideal.mvPolynomialToLaurent_C, Ideal.mvPolynomialToLaurent_X,
    Polynomial.map_X, Polynomial.toLaurent_X]
  simp

/-- The punctured affine line, with its actual fixed-field structure.
Source: sk-lem-geometry (3) (blueprint: lem-pur-dnc-section-geometry). -/
def Pair.puncturedBase (Q : Pair D) : Over (Spec (.of D.k)) :=
  Over.mk ((Scheme.Hom.puncturedLine Q.B.left).ι ≫
    (AffineSpace (ULift.{u} (Fin 1)) Q.B.left ↘ Q.B.left) ≫ Q.B.hom)

/-- The punctured-line projection to the original base.
Source: sk-lem-geometry (3) (blueprint: lem-pur-dnc-section-geometry). -/
def Pair.puncturedBaseMap (Q : Pair D) : Q.puncturedBase ⟶ Q.B :=
  Over.homMk ((Scheme.Hom.puncturedLine Q.B.left).ι ≫
    (AffineSpace (ULift.{u} (Fin 1)) Q.B.left ↘ Q.B.left)) rfl

/-- The punctured base is separated finite type over the fixed field.
Source: sk-lem-geometry (3) (blueprint: lem-pur-dnc-section-geometry).
Proof: Gm_B is the principal open t!=0 in A1_B, affine of finite presentation over B;
compose with the separated finite-type field map. Empty bases cause no exception. -/
theorem Pair.puncturedProperties (Q : Pair D) :
    LocallyOfFiniteType Q.puncturedBase.hom ∧ QuasiCompact Q.puncturedBase.hom ∧
    IsSeparated Q.puncturedBase.hom := by
  haveI := LocallyOfFiniteType.isLocallyNoetherian Q.B.hom
  haveI := QuasiCompact.compactSpace_of_compactSpace Q.B.hom
  haveI : IsNoetherian Q.B.left := ⟨⟩
  haveI := LocallyOfFiniteType.isLocallyNoetherian
    (AffineSpace (ULift.{u} (Fin 1)) Q.B.left ↘ Q.B.left)
  haveI := QuasiCompact.compactSpace_of_compactSpace
    (AffineSpace (ULift.{u} (Fin 1)) Q.B.left ↘ Q.B.left)
  haveI : IsNoetherian (AffineSpace (ULift.{u} (Fin 1)) Q.B.left) := ⟨⟩
  change LocallyOfFiniteType ((Scheme.Hom.puncturedLine Q.B.left).ι ≫
      (AffineSpace (ULift.{u} (Fin 1)) Q.B.left ↘ Q.B.left) ≫ Q.B.hom) ∧
    QuasiCompact ((Scheme.Hom.puncturedLine Q.B.left).ι ≫
      (AffineSpace (ULift.{u} (Fin 1)) Q.B.left ↘ Q.B.left) ≫ Q.B.hom) ∧
    IsSeparated ((Scheme.Hom.puncturedLine Q.B.left).ι ≫
      (AffineSpace (ULift.{u} (Fin 1)) Q.B.left ↘ Q.B.left) ≫ Q.B.hom)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The actual product pair over the punctured line.
Source: sk-lem-geometry (3) (blueprint: lem-pur-dnc-section-geometry). -/
def Pair.punctured (Q : Pair D) : Pair D :=
  let H := Q.puncturedProperties
  letI := H.1
  letI := H.2.1
  letI := H.2.2
  Q.changed Q.puncturedBase Q.puncturedBaseMap

/-- The canonical product section is carried to the Rees augmentation section.
Source: sk-lem-geometry (3) (blueprint: lem-pur-dnc-section-geometry).
Proof: after inverting t the Rees algebra is R[t,t^-1]; both augmentations send
r to its value on s and preserve t. The chart identities glue to this equality. -/
theorem Pair.puncturedSection (Q : Pair D) :
    Q.punctured.s.left ≫ Scheme.Hom.deformationSpaceGeneric Q.g.left Q.s.left =
      (Scheme.Hom.puncturedLine Q.B.left).ι ≫ Q.rees.s.left := by
  change Scheme.Hom.baseChangeSection Q.g.left Q.s.left
      (congrArg (fun f ↦ f.left) Q.section_eq) _ ≫
        Scheme.Hom.deformationSpaceGeneric Q.g.left Q.s.left =
      (Scheme.Hom.puncturedLine Q.B.left).ι ≫ Q.s.left.deformationSpaceSection
  let P := Scheme.Hom.isPullback_deformationSpaceGeneric Q.g.left Q.s.left
  have hm : ((Scheme.Hom.puncturedLine Q.B.left).ι ≫
      Q.s.left.deformationSpaceSection) ≫
      Scheme.Hom.deformationSpaceProj Q.g.left Q.s.left =
      𝟙 _ ≫ (Scheme.Hom.puncturedLine Q.B.left).ι := by
    rw [Category.assoc, Scheme.Hom.deformationSpaceSection_deformationSpaceProj
      (congrArg (fun f ↦ f.left) Q.section_eq), Category.comp_id, Category.id_comp]
  have he : P.lift _ _ hm = Scheme.Hom.baseChangeSection Q.g.left Q.s.left
      (congrArg (fun f ↦ f.left) Q.section_eq)
      ((Scheme.Hom.puncturedLine Q.B.left).ι ≫
        (AffineSpace (ULift.{u} (Fin 1)) Q.B.left ↘ Q.B.left)) := by
    apply pullback.hom_ext
    · rw [Scheme.Hom.baseChangeSection_fst]
      have hf := congrArg (fun f ↦ f ≫ Q.s.left.ker.deformationSpaceProj)
        (P.lift_fst _ _ hm)
      change P.lift _ _ hm ≫ pullback.fst _ _ =
        ((Scheme.Hom.puncturedLine Q.B.left).ι ≫
          (AffineSpace (ULift.{u} (Fin 1)) Q.B.left ↘ Q.B.left)) ≫ Q.s.left
      simpa only [Category.assoc, Scheme.Hom.deformationSpaceGeneric_toBase,
        Scheme.Hom.deformationSpaceSection_toBase] using hf
    · rw [P.lift_snd, Scheme.Hom.baseChangeSection_snd]
  rw [← he]
  exact P.lift_fst _ _ _

/-- The standard Rees coordinates give the actual product square, with its zero section.
Source: sk-lem-geometry (4) (blueprint: lem-pur-dnc-section-geometry).
Proof: for I=(x_1,...,x_d), the extended Rees ring is S[t,u] with x_k=t*u_k.
The coordinate isomorphism respects the two projections and takes the augmentation
to zero. Composing with A^d(a) yields this Cartesian square and section equation. -/
theorem standardSquare (B : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (d : ℕ) :
    let Q := standard B d
    let v := Scheme.Hom.deformationSpaceToAffineSpace (ULift.{u} (Fin d)) B.left ≫
      AffineSpace.map (ULift.{u} (Fin d))
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)
    IsPullback v Q.rees.g.left Q.g.left
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ∧
      Q.rees.s.left ≫ v =
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ≫ Q.s.left := by
  dsimp only
  change IsPullback
      (Scheme.Hom.deformationSpaceToAffineSpace (ULift.{u} (Fin d)) B.left ≫
        AffineSpace.map (ULift.{u} (Fin d))
          (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left))
      (Scheme.Hom.deformationSpaceProj
        (AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left)
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) B.left))
      (AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left)
      (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left) ∧ _
  constructor
  · have h := IsPullback.of_horiz_isIso
      (fst := Scheme.Hom.deformationSpaceToAffineSpace (ULift.{u} (Fin d)) B.left)
      (snd := Scheme.Hom.deformationSpaceProj
        (AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left)
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) B.left))
      (f := AffineSpace (ULift.{u} (Fin d))
        (AffineSpace (ULift.{u} (Fin 1)) B.left) ↘ _)
      (g := 𝟙 _) ⟨(Scheme.Hom.deformationSpaceToAffineSpace_over _ _).trans
        (Category.comp_id _).symm⟩
    simpa only [Category.id_comp] using h.paste_horiz
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin d))
        (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left))
  · change (AffineSpace.zeroSection (ULift.{u} (Fin d)) B.left).deformationSpaceSection ≫
      (Scheme.Hom.deformationSpaceToAffineSpace (ULift.{u} (Fin d)) B.left ≫ _) = _
    rw [← Category.assoc,
      Scheme.Hom.deformationSpaceSection_comp_deformationSpaceToAffineSpace,
      AffineSpace.zeroSection_comp_map]
    rfl

/-- The actual quotient topology of the embedded finite coefficient ring is discrete.
Source: the coefficient convention and sk-lem-geometry Step 6
(blueprint: lem-pur-dnc-section-geometry).
Proof: at n=0 the quotient is the zero ring, hence discrete. At positive n,
uniqueness of the extension of the ell-adic absolute value identifies the topology
induced from the given embedding in Qbar_ell with the spectral-norm valuation
topology. The DVR uniformizer powers form a neighborhood basis at zero, so
pi_E^n O_E is open. Its translates are exactly the fibres of the quotient map.
The quotient topology therefore has every singleton open. This proves discreteness
of the existing topology, without replacing it by a new coefficient presentation. -/
theorem finiteCoefficient_discrete (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) :
    DiscreteTopology (Padic.coefficientExtensionRing ell E n) := by
  by_cases hn : n = 0
  · subst n
    haveI : Subsingleton (Padic.coefficientExtensionRing ell E 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp [Padic.coefficientExtensionIdeal])
    exact Subsingleton.discreteTopology
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    let O := Padic.coefficientExtensionIntegers ell E
    have h := (Padic.extension_integers_dvr ell E
      (Padic.coefficientExtensionAbsoluteValue ell E)
      (spectralNorm_extends (K := Padic ell) (L := E))).choose_spec.choose_spec
    letI : IsDiscreteValuationRing O := h.2.2.2.2.2.2.2.1
    letI : ProperSpace E := FiniteDimensional.proper (Padic ell) E
    have hO : ∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1 := by
      intro x
      rw [NormedAlgebra.norm_eq_spectralNorm (Padic ell)]
      exact h.1 x
    letI : CompactSpace O := by
      rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ,
        Subtype.range_coe_subtype]
      have he : (O : Set E) = Metric.closedBall 0 1 := by
        ext x
        change x ∈ O ↔ _
        rw [hO]
        simp only [Metric.mem_closedBall, dist_zero_right]
      change IsCompact (O : Set E)
      rw [he]
      exact isCompact_closedBall (0 : E) 1
    letI : Finite (Padic.coefficientExtensionRing ell E n) :=
      Padic.finite_coefficientExtensionRing ell E n hn
    exact QuotientAddGroup.discreteTopology
      ((IsLocalRing.isOpen_iff_finite_quotient
        (I := Padic.coefficientExtensionIdeal ell E n)).mpr inferInstance)

variable (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (hcoeff :
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell E n))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))

set_option maxHeartbeats 2000000 in
-- Comparing the nested coherence witnesses instantiates large derived-functor types.
/-- Pull the exact invertible native mate to the sections and compose the pullback
isomorphisms, including the equality transport for the section square.
Source: cohomological smoothness, condition (3)
(blueprint: lem-pur-dnc-section-geometry, Step 5). -/
private theorem sectionMate_isIso
    {X Y X' Y' : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (g : X ⟶ Y) (g' : X' ⟶ Y') (v : X'.left ⟶ X.left) (b : Y'.left ⟶ Y.left)
    (sq : IsPullback v g'.left g.left b)
    (s : Y.left ⟶ X.left) (s' : Y'.left ⟶ X'.left)
    (hsection : s' ≫ v = b ≫ s) (d : ℕ) [SmoothOfRelativeDimension d g.left] :
    IsIso (sectionBaseChangeMap D ell hell E n hn Λ hcoeff g g' v b sq s s' hsection) := by
  have := nativeMate_isIso ell hell E n hn Λ hcoeff g g' v b sq d
  let Ω := (dualizing D ell hell E n hn Λ hcoeff g).obj
  let c₁ := (leftDerivedUpperStarComp Λ b s).app Ω
  let c₂ := (leftDerivedUpperStarComp Λ s' v).app Ω
  let e := congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj Ω) hsection.symm
  let β := dualizingBaseChangeMap D ell hell E n hn Λ hcoeff g g' v b sq
  have hβ : IsIso ((moduleObjectDerivedPullback Λ s').map β) := inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ c₁.inv _ (inferInstance) (
    @IsIso.comp_isIso _ _ _ _ _ (eqToHom e) _ (inferInstance) (
      @IsIso.comp_isIso _ _ _ _ _ c₂.hom _ (inferInstance) hβ))

/-- Abbreviation of the dependency's recorded Q50 section invariant, without new data.
Source: def-pur-section-invariant (blueprint: lem-pur-dnc-section-geometry). -/
abbrev Pair.C (Q : Pair D) :=
  sectionInvariant D ell hell E n hn Λ hcoeff Q.B Q.V Q.g Q.s Q.section_eq

/-- Abbreviation of the dependency's repaired native Rees family, without new data.
Source: def-pur-dnc-section-family (blueprint: lem-pur-dnc-section-geometry). -/
abbrev Pair.F (Q : Pair D) (d : ℕ) [SmoothOfRelativeDimension d Q.g.left] :=
  condensedDncFamily D Q.B Q.V Q.g Q.s ell hell E n hn Λ hcoeff d Q.section_eq

/-- The two specified native fibre comparisons, with their homomorphisms fixed by beta.
Source: sk-lem-geometry (1), proof Step 5 (blueprint: lem-pur-dnc-section-geometry).
Proof: the extended-Rees one and zero squares identify the pairs with (g,s) and
(pi_N,0_N). Condition (3) of cohomological smoothness makes the native beta invertible.
Pull beta to the section and compose the pullback compositors. These are the displayed
maps. At finite coefficients the normalized comparison identifies beta with finiteCompared
beta; the other three coefficients use the stipulated coefficient transports. No smooth
orientation or alternative exceptional functor is assumed. -/
theorem fibreComparisons (Q : Pair D) (d : ℕ)
    [SmoothOfRelativeDimension d Q.g.left] :
    (∃ e : (moduleObjectDerivedPullback Λ
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) Q.B.left)).obj
          (Q.F ell hell E n hn Λ hcoeff d) ≅ Q.C ell hell E n hn Λ hcoeff,
      e.hom = sectionBaseChangeMap D ell hell E n hn Λ hcoeff
        Q.rees.g Q.g (Scheme.Hom.deformationSpaceOneFibre Q.g.left Q.s.left)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) Q.B.left)
        (Scheme.Hom.isPullback_deformationSpaceOneFibre Q.g.left Q.s.left)
        Q.rees.s.left Q.s.left
        (Scheme.Hom.comp_deformationSpaceOneFibre
          (congrArg (fun f ↦ f.left) Q.section_eq))) ∧
    (∃ e : (moduleObjectDerivedPullback Λ
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Q.B.left)).obj
          (Q.F ell hell E n hn Λ hcoeff d) ≅ Q.normal.C ell hell E n hn Λ hcoeff,
      e.hom = sectionBaseChangeMap D ell hell E n hn Λ hcoeff
        Q.rees.g Q.normal.g Q.s.left.ker.normalConeToDeformationSpace
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Q.B.left)
        (Scheme.Hom.isPullback_normalConeToDeformationSpace Q.g.left Q.s.left)
        Q.rees.s.left Q.normal.s.left
        Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace) := by
  have : SmoothOfRelativeDimension d Q.rees.g.left :=
    condensedDncRelativeDimension D Q.B Q.V Q.g Q.s d Q.section_eq
  constructor
  · let m := sectionBaseChangeMap D ell hell E n hn Λ hcoeff
      Q.rees.g Q.g (Scheme.Hom.deformationSpaceOneFibre Q.g.left Q.s.left)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) Q.B.left)
      (Scheme.Hom.isPullback_deformationSpaceOneFibre Q.g.left Q.s.left)
      Q.rees.s.left Q.s.left
      (Scheme.Hom.comp_deformationSpaceOneFibre
        (congrArg (fun f ↦ f.left) Q.section_eq))
    have : IsIso m := sectionMate_isIso ell hell E n hn Λ hcoeff _ _ _ _ _ _ _ _ d
    exact ⟨asIso m, rfl⟩
  · let m := sectionBaseChangeMap D ell hell E n hn Λ hcoeff
      Q.rees.g Q.normal.g Q.s.left.ker.normalConeToDeformationSpace
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Q.B.left)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace Q.g.left Q.s.left)
      Q.rees.s.left Q.normal.s.left
      Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace
    have : IsIso m := sectionMate_isIso ell hell E n hn Λ hcoeff _ _ _ _ _ _ _ _ d
    exact ⟨asIso m, rfl⟩

/-- The punctured native comparison is the ratio of the two fixed section mates.
Source: sk-lem-geometry (3), proof Step 5 (blueprint: lem-pur-dnc-section-geometry).
Proof: the canonical Rees product square and its section are Pair.punctured and
puncturedSection. Apply beta to this square and to the product square for g. Their
section pullbacks alpha and beta are invertible. Alpha followed by beta inverse and
the j,a pullback compositor is exactly kappa-circ. The same counit normalization is
preserved by the finite comparison and the stipulated coefficient transports. -/
theorem puncturedComparison (Q : Pair D) (d : ℕ)
    [SmoothOfRelativeDimension d Q.g.left] :
    let j := (Scheme.Hom.puncturedLine Q.B.left).ι
    let a := (AffineSpace (ULift.{u} (Fin 1)) Q.B.left ↘ Q.B.left)
    let α := sectionBaseChangeMap D ell hell E n hn Λ hcoeff Q.rees.g Q.punctured.g
      (Scheme.Hom.deformationSpaceGeneric Q.g.left Q.s.left) j
      (Scheme.Hom.isPullback_deformationSpaceGeneric Q.g.left Q.s.left)
      Q.rees.s.left Q.punctured.s.left Q.puncturedSection
    let β := sectionBaseChangeMap D ell hell E n hn Λ hcoeff Q.g Q.punctured.g
      (pullback.fst Q.g.left Q.puncturedBaseMap.left) (j ≫ a)
      (IsPullback.of_hasPullback Q.g.left Q.puncturedBaseMap.left)
      Q.s.left Q.punctured.s.left
      (Scheme.Hom.baseChangeSection_fst Q.g.left Q.s.left
        (congrArg (fun f ↦ f.left) Q.section_eq) Q.puncturedBaseMap.left)
    ∃ (hα : IsIso α) (hβ : IsIso β),
      letI := hα
      letI := hβ
      ∃ κ : (moduleObjectDerivedPullback Λ j).obj (Q.F ell hell E n hn Λ hcoeff d) ≅
          (moduleObjectDerivedPullback Λ j).obj
            ((moduleObjectDerivedPullback Λ a).obj (Q.C ell hell E n hn Λ hcoeff)),
        κ.hom = α ≫ inv β ≫
          ((leftDerivedUpperStarComp Λ j a).app (Q.C ell hell E n hn Λ hcoeff)).hom := by
  dsimp only
  have : SmoothOfRelativeDimension d Q.rees.g.left :=
    condensedDncRelativeDimension D Q.B Q.V Q.g Q.s d Q.section_eq
  let j := (Scheme.Hom.puncturedLine Q.B.left).ι
  let a := (AffineSpace (ULift.{u} (Fin 1)) Q.B.left ↘ Q.B.left)
  let α := sectionBaseChangeMap D ell hell E n hn Λ hcoeff Q.rees.g Q.punctured.g
    (Scheme.Hom.deformationSpaceGeneric Q.g.left Q.s.left) j
    (Scheme.Hom.isPullback_deformationSpaceGeneric Q.g.left Q.s.left)
    Q.rees.s.left Q.punctured.s.left Q.puncturedSection
  let β := sectionBaseChangeMap D ell hell E n hn Λ hcoeff Q.g Q.punctured.g
    (pullback.fst Q.g.left Q.puncturedBaseMap.left) (j ≫ a)
    (IsPullback.of_hasPullback Q.g.left Q.puncturedBaseMap.left)
    Q.s.left Q.punctured.s.left
    (Scheme.Hom.baseChangeSection_fst Q.g.left Q.s.left
      (congrArg (fun f ↦ f.left) Q.section_eq) Q.puncturedBaseMap.left)
  have hα : IsIso α := sectionMate_isIso ell hell E n hn Λ hcoeff _ _ _ _ _ _ _ _ d
  have hβ : IsIso β := sectionMate_isIso ell hell E n hn Λ hcoeff _ _ _ _ _ _ _ _ d
  refine ⟨hα, hβ, ?_⟩
  let := hα
  let := hβ
  exact ⟨asIso α ≪≫ (asIso β).symm ≪≫
    (leftDerivedUpperStarComp Λ j a).app (Q.C ell hell E n hn Λ hcoeff), rfl⟩

/-- The standard family comparison is the inverse of the canonical section mate.
Source: sk-lem-geometry (4), proof Step 6 (blueprint: lem-pur-dnc-section-geometry).
Proof: x_k=t*u_k makes the deformation the standard affine bundle over A1_B.
Use the product square standardSquare, apply beta for the standard projection and
pull it to zero. The resulting map a*C -> F is invertible by cohomological smoothness.
Its inverse is the requested comparison, so no unspecified endpoint isomorphism is used. -/
theorem standardComparison (B : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (d : ℕ) :
    let Q := standard B d
    let a := (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)
    let v := Scheme.Hom.deformationSpaceToAffineSpace (ULift.{u} (Fin d)) B.left ≫
      AffineSpace.map (ULift.{u} (Fin d)) a
    ∃ κ : Q.F ell hell E n hn Λ hcoeff d ≅
        (moduleObjectDerivedPullback Λ a).obj (Q.C ell hell E n hn Λ hcoeff),
      κ.inv = sectionBaseChangeMap D ell hell E n hn Λ hcoeff Q.g Q.rees.g v a
        (standardSquare B d).1 Q.s.left Q.rees.s.left (standardSquare B d).2 := by
  dsimp only
  let Q := standard B d
  let a := (AffineSpace (ULift.{u} (Fin 1)) B.left ↘ B.left)
  let v := Scheme.Hom.deformationSpaceToAffineSpace (ULift.{u} (Fin d)) B.left ≫
    AffineSpace.map (ULift.{u} (Fin d)) a
  let m := sectionBaseChangeMap D ell hell E n hn Λ hcoeff Q.g Q.rees.g v a
    (standardSquare B d).1 Q.s.left Q.rees.s.left (standardSquare B d).2
  have : IsIso m := sectionMate_isIso ell hell E n hn Λ hcoeff _ _ _ _ _ _ _ _ d
  exact ⟨(asIso m).symm, rfl⟩

/-- The standard zero-section invariant is the actual native root-tower Tate line.
Source: sk-lem-geometry (4), vector-bundle purity and Step 6
(blueprint: lem-pur-dnc-section-geometry).
Proof: vector-bundle purity identifies the standard dualizing object with Lambda(d)[2d].
Pull to zero. The finite root-line comparison and the stipulated integral, rational and
closure coefficient transports identify this with the already constructed root-tower
line; no orientation of an arbitrary g is used. -/
theorem standardPair
    (c : ProEtale.PurityTransport.Coefficient ell)
    (hc :
      Nonempty (Mon.mk (c.obj.{u} ell) ≅ Mon.mk (Profinite.continuousMapRingObj
        (Padic.coefficientExtensionRing ell E n))) ∨
      Nonempty (Mon.mk (c.obj.{u} ell) ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk (c.obj.{u} ell) ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk (c.obj.{u} ell) ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (B : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (d : ℕ) :
    Nonempty ((standard B d).C ell hell E n hn (c.obj ell) hc ≅
      c.derivedLine ell B.left d) := by
  sorry

/-- Nonflat Rees base change and the specified native family mate.
Source: sk-lem-geometry (5), proof Step 7 (blueprint: lem-pur-dnc-section-geometry).
Proof: tensor centred Rees charts R tensor_P S[t,u] with S'. The coordinatewise map
preserves t, x_i/t, Laurent localization, augmentation, one and zero fibres, with no
flatness hypothesis. It gives the displayed Cartesian square and Compatible. Native
beta for that square, pulled to the augmentation, is invertible by condition (3).
Compact-support exchange pasting and the mate-pasting identity give compatibility with
iterated base change. This is the canonical comparison of the actual native F objects. -/
theorem baseChange (Q : Pair D) (d : ℕ) [SmoothOfRelativeDimension d Q.g.left]
    (B' : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    (b : B' ⟶ Q.B) :
    let Q' := Q.changed B' b
    let v := Scheme.IdealSheafData.deformationSpaceMap (pullback.fst Q.g.left b.left)
      Q.s.left.ker Q'.s.left.ker (Scheme.Hom.map_siteIdeal_ker_le_baseChangeSection
        Q.g.left Q.s.left (congrArg (fun f ↦ f.left) Q.section_eq) b.left)
    ∃ sq : IsPullback v Q'.rees.g.left Q.rees.g.left
        (AffineSpace.map (ULift.{u} (Fin 1)) b.left),
      SectionReesBaseChange.Compatible Q.g.left Q'.g.left Q.s.left Q'.s.left
        (pullback.fst Q.g.left b.left) b.left v ∧
      ∃ κ : (moduleObjectDerivedPullback Λ
          (AffineSpace.map (ULift.{u} (Fin 1)) b.left)).obj
            (Q.F ell hell E n hn Λ hcoeff d) ≅ Q'.F ell hell E n hn Λ hcoeff d,
        κ.hom = sectionBaseChangeMap D ell hell E n hn Λ hcoeff Q.rees.g Q'.rees.g v
          (AffineSpace.map (ULift.{u} (Fin 1)) b.left) sq Q.rees.s.left Q'.rees.s.left
          (Scheme.Hom.deformationSpaceSection_comp_deformationSpaceMap_baseChangeSection
            Q.g.left Q.s.left (congrArg (fun f ↦ f.left) Q.section_eq) b.left) := by
  dsimp only
  have := LocallyOfFiniteType.isLocallyNoetherian Q.B.hom
  have := QuasiCompact.compactSpace_of_compactSpace Q.B.hom
  have : IsNoetherian Q.B.left := ⟨⟩
  have := LocallyOfFiniteType.isLocallyNoetherian B'.hom
  have := QuasiCompact.compactSpace_of_compactSpace B'.hom
  have : IsNoetherian B'.left := ⟨⟩
  let Q' := Q.changed B' b
  let v := Scheme.IdealSheafData.deformationSpaceMap (pullback.fst Q.g.left b.left)
    Q.s.left.ker Q'.s.left.ker (Scheme.Hom.map_siteIdeal_ker_le_baseChangeSection
      Q.g.left Q.s.left (congrArg (fun f ↦ f.left) Q.section_eq) b.left)
  let R := Scheme.IdealSheafData.extendedReesPullbackData
    (pullback.fst Q.g.left b.left) Q.s.left.ker Q'.s.left.ker
    (Scheme.Hom.map_siteIdeal_ker_le_baseChangeSection
      Q.g.left Q.s.left (congrArg (fun f ↦ f.left) Q.section_eq) b.left)
  have hcov : ∀ x : (pullback Q.g.left b.left : Scheme.{u}),
      ∃ (U' : (pullback Q.g.left b.left).AffineZariskiSite)
        (U : Q.V.left.AffineZariskiSite)
        (hU : U'.1 ≤ pullback.fst Q.g.left b.left ⁻¹ᵁ U.1), x ∈ U'.1 ∧
        IsPushout ((pullback.fst Q.g.left b.left).appLE U.1 U'.1 hU)
          (Q.s.left.ker.toReesPresheaf.app (Opposite.op U))
          (Q'.s.left.ker.toReesPresheaf.app (Opposite.op U')) (R.map hU) := by
    intro x
    obtain ⟨U', U, hU, hx, _, H⟩ :=
      Scheme.Hom.exists_isPushout_extendedReesAlgebraMap_baseChange
        Q.g.left Q.s.left (congrArg (fun f ↦ f.left) Q.section_eq) b.left d x
    exact ⟨U', U, hU, hx, H⟩
  have sq : IsPullback v Q'.rees.g.left Q.rees.g.left
      (AffineSpace.map (ULift.{u} (Fin 1)) b.left) :=
    Scheme.IdealSheafData.isPullback_deformationSpaceMap_proj
      (pullback.fst Q.g.left b.left) Q.s.left.ker Q'.s.left.ker
      (Scheme.Hom.map_siteIdeal_ker_le_baseChangeSection
        Q.g.left Q.s.left (congrArg (fun f ↦ f.left) Q.section_eq) b.left) hcov
      Q.g.left Q'.g.left b.left (IsPullback.of_hasPullback Q.g.left b.left)
  obtain ⟨s', hs', w, he, _, hc, _⟩ := SectionReesBaseChange.base_change d
    Q.g.left Q.s.left (congrArg (fun f ↦ f.left) Q.section_eq) b.left
  subst s'
  refine ⟨sq, hc, ?_⟩
  have : SmoothOfRelativeDimension d Q.rees.g.left :=
    condensedDncRelativeDimension D Q.B Q.V Q.g Q.s d Q.section_eq
  let m := sectionBaseChangeMap D ell hell E n hn Λ hcoeff Q.rees.g Q'.rees.g v
    (AffineSpace.map (ULift.{u} (Fin 1)) b.left) sq Q.rees.s.left Q'.rees.s.left
    (Scheme.Hom.deformationSpaceSection_comp_deformationSpaceMap_baseChangeSection
      Q.g.left Q.s.left (congrArg (fun f ↦ f.left) Q.section_eq) b.left)
  have : IsIso m := sectionMate_isIso ell hell E n hn Λ hcoeff _ _ _ _ _ _ _ _ d
  exact ⟨asIso m, rfl⟩

end AlgebraicGeometry.ProEtale.CondensedRing.SectionGeometry
