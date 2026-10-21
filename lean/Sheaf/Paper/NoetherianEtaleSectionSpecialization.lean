/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
public import Sheaf.Paper.PurityNormalCone
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.Paper.PurityConventions
public import Sheaf.SixFunctors.SmoothDualityBaseChangeCompat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction
import Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Normalized ordinary etale specialization along a smooth section

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-dnc, Local construction,
Gluing and base change (blueprint: lem-pur-noetherian-etale-section-specialization).
The schemes and all maps below are the published extended-Rees construction and its
adjunction-mate fibre maps. Coefficients are the universe lift of Z/(ell^n).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
noncomputable section
namespace AlgebraicGeometry.Etale.NoetherianSectionSpecialization

/-- The standard locally bijective description of abelian sheafification on each
open slice, with its concrete sheafification witnesses supplied explicitly.
Source: Stacks Tag 03DA (blueprint: lem-pur-noetherian-etale-section-specialization).
This is only the existing Mathlib construction, with no size restriction on S. -/
instance opensOverLocallyBijective (S : Scheme.{u}) (U : S.Opens) :
    ((Opens.grothendieckTopology S).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
      Presheaf.IsLocallyInjective ((Opens.grothendieckTopology S).over U)
        (toSheafify ((Opens.grothendieckTopology S).over U) P) :=
    Presheaf.isLocallyInjective_toSheafify' _ P
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
      Presheaf.IsLocallySurjective ((Opens.grothendieckTopology S).over U)
        (toSheafify ((Opens.grothendieckTopology S).over U) P) :=
    Presheaf.isLocallySurjective_toSheafify' _ P
  GrothendieckTopology.WEqualsLocallyBijective.mk' _ _

/-- Z/(ell^n) in the coefficient universe of the ordinary small etale derived category.
Source: sk-thm-dnc, finite coefficients
(blueprint: lem-pur-noetherian-etale-section-specialization). -/
abbrev Coeff (ell n : ℕ) : Type (u + 1) := ULift.{u + 1} (ZMod (ell ^ n))

/-- The actual ordinary etale family on the extended-Rees deformation.
Source: sk-thm-dnc, opening paragraph
(blueprint: lem-pur-noetherian-etale-section-specialization). -/
def family (A : Type (u + 1)) [CommRing A] [Finite A] {V S : Scheme.{u}}
    (g : V ⟶ S) (s : S ⟶ V) [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] :
    DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S) :=
  sectionInvariant A (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection

/-- Pull the canonical exceptional base-change mate to compatible sections. This is a map,
not an arbitrarily chosen isomorphism. Source: sk-thm-dnc, fibre identifications;
prop-asd-smooth-base-change (blueprint: lem-pur-noetherian-etale-section-specialization). -/
def sectionMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (f' : X' ⟶ Y') [HasCompactification f'] [QuasiCompact f']
    (b : Y' ⟶ Y) (v : X' ⟶ X) (sq : IsPullback v f' f b)
    (s : Y ⟶ X) (s' : Y' ⟶ X') (hs : s' ≫ v = b ≫ s) :
    (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj
      (sectionInvariant A f s) ⟶ sectionInvariant A f' s' :=
  ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b s).app _).inv ≫
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' v (b ≫ s) hs.symm).app _).hom ≫
      (upperStar (ModuleCat.{u + 1} A) s').leftDerivedFunctor.map
        (dualizingComplexBaseChangeMap A sq)

/-- The specified fibre map at t=1. Source: sk-thm-dnc, opening fibre comparison
(blueprint: lem-pur-noetherian-etale-section-specialization). -/
def atOne (A : Type (u + 1)) [CommRing A] [Finite A] {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj
        (family A g s) ⟶ sectionInvariant A g s :=
  sectionMap A (Scheme.Hom.deformationSpaceProj g s) g
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
    (Scheme.Hom.deformationSpaceOneFibre g s)
    (Scheme.Hom.isPullback_deformationSpaceOneFibre g s)
    s.deformationSpaceSection s (Scheme.Hom.comp_deformationSpaceOneFibre hs)

/-- The specified fibre map at t=0 to the actual normal cone.
Source: sk-thm-dnc, opening fibre comparison
(blueprint: lem-pur-noetherian-etale-section-specialization). -/
def atZero (A : Type (u + 1)) [CommRing A] [Finite A] {V S : Scheme.{u}}
    (g : V ⟶ S) (s : S ⟶ V) [IsClosedImmersion s]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj
        (family A g s) ⟶
      sectionInvariant A (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection :=
  sectionMap A (Scheme.Hom.deformationSpaceProj g s) (Scheme.Hom.normalConeProj g s)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) s.ker.normalConeToDeformationSpace
    (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
    s.deformationSpaceSection s.normalConeZeroSection
    Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace

/-- Normalization at t=1, with the identity on the source section complex expressed using
its canonical fibre identification. Source: sk-thm-dnc, normalization
(blueprint: lem-pur-noetherian-etale-section-specialization). -/
def Normalized (A : Type (u + 1)) [CommRing A] [Finite A] {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    (κ : family A g s ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A g s)) : Prop :=
  (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map κ.hom ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)).hom.app _ =
    atOne A g s hs

/-- Specialization at zero, read through the canonical zero-fibre mate. When that mate
is invertible, this is the isomorphism denoted delta in the node. Its formula is the
inverse of the zero restriction of kappa, with both canonical fibre identifications.
Source: sk-thm-dnc, final specialization
(blueprint: lem-pur-noetherian-etale-section-specialization). -/
def specialization (A : Type (u + 1)) [CommRing A] [Finite A] {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)]
    (κ : family A g s ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A g s)) :
    sectionInvariant A g s ⟶
      sectionInvariant A (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) S)).inv.app _ ≫
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map κ.inv ≫
          atZero A g s

/-- The canonical comparison between pullback from S and pullback from S' on affine lines.
Source: sk-thm-dnc, base-change formula for kappa
(blueprint: lem-pur-noetherian-etale-section-specialization). -/
def linePullback (A : Type (u + 1)) [CommRing A] {S S' : Scheme.{u}}
    (b : S' ⟶ S) (C : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj C) ≅
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj C) :=
  ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace.map (ULift.{u} (Fin 1)) b)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).app C).symm ≪≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S') b
        (AffineSpace.map (ULift.{u} (Fin 1)) b ≫
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
        (AffineSpace.map_over (n := ULift.{u} (Fin 1)) b)).app C

/-- The canonical map of extended-Rees deformations under arbitrary base change.
On charts it sends a, t and a/t to their pulled-back representatives. Source: sk-thm-dnc,
base change, flat Rees computation
(blueprint: lem-pur-noetherian-etale-section-specialization). -/
def deformationMap {V S S' : Scheme.{u}} (g : V ⟶ S) (s : S ⟶ V)
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) (b : S' ⟶ S) :
    (Scheme.Hom.baseChangeSection g s hs b).ker.deformationSpace ⟶ s.ker.deformationSpace :=
  Scheme.IdealSheafData.deformationSpaceMap (pullback.fst g b) s.ker
    (Scheme.Hom.baseChangeSection g s hs b).ker
    (Scheme.Hom.map_siteIdeal_ker_le_baseChangeSection g s hs b)

/-- Geometric and normal-bundle clauses, with the actual Rees space and the actual
conormal symmetric-algebra comparison. The canonical identification of the Rees cone
with the relative spectrum of the conormal graded algebra is the recorded
purityNormalCone_comparison; invertibility of symmetricComparison below identifies
that same cone with Spec Sym(I/I^2), compatibly with projection and augmentation.
Source: sk-thm-dnc, Local construction, paragraphs 1--2
(blueprint: lem-pur-noetherian-etale-section-specialization).
Proof: use etale coordinates centered on the section and remove the complementary
clopen zero component. If P=R[x] and B is the etale chart, flat tensor exactness gives
B[t,I/t]=B tensor_P R[t,u], x_i=t*u_i, and gr_I(B)=Sym(I/I^2). These canonical
identifications glue. The coordinates identify both fibres and their sections.
The Rees algebra is finitely generated over each Noetherian affine chart; hence the
space is Noetherian. Smoothness follows on the deformation charts and the punctured
product; separatedness follows from the affine map to V times A1. The regular
sequence basis makes the conormal locally free of rank d. This includes d=0 and the
empty base. Uses Steps 1--4 of the DAG proof, including flat-tensor exactness,
etale base change and finite-type Noetherian permanence. -/
theorem geometry
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (hV : ∀ x : V, IsUnit (ell : V.presheaf.stalk x))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (hregular : ∀ x : S, ∃ U : V.affineOpens, s x ∈ U.1 ∧
      ∃ r : Fin d → Γ(V, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn r) ∧
          Ideal.span (Set.range r) = s.ker.ideal U)
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] :
    IsNoetherian s.ker.deformationSpace ∧
    SmoothOfRelativeDimension d (Scheme.Hom.deformationSpaceProj g s) ∧
    IsSeparated (Scheme.Hom.deformationSpaceProj g s) ∧
    QuasiCompact (Scheme.Hom.normalConeProj g s) ∧
    IsPullback (Scheme.Hom.deformationSpaceOneFibre g s) g
      (Scheme.Hom.deformationSpaceProj g s)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S) ∧
    s ≫ Scheme.Hom.deformationSpaceOneFibre g s =
      AffineSpace.oneSection (ULift.{u} (Fin 1)) S ≫ s.deformationSpaceSection ∧
    IsPullback s.ker.normalConeToDeformationSpace (Scheme.Hom.normalConeProj g s)
      (Scheme.Hom.deformationSpaceProj g s)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) ∧
    s.normalConeZeroSection ≫ s.ker.normalConeToDeformationSpace =
      AffineSpace.zeroSection (ULift.{u} (Fin 1)) S ≫ s.deformationSpaceSection ∧
    (ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d ∧
    IsIso (ConormalGradedAlgebra.symmetricComparison s) := by
  have _ := hn
  have _ := hS
  have _ := hV
  have hD := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have hA : IsLocallyNoetherian (AffineSpace (ULift.{u} (Fin 1)) S) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
  have hAC : CompactSpace (AffineSpace (ULift.{u} (Fin 1)) S) :=
    QuasiCompact.compactSpace_of_compactSpace
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
  have hDN : IsLocallyNoetherian s.ker.deformationSpace :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.Hom.deformationSpaceProj g s)
  have hDC : CompactSpace s.ker.deformationSpace :=
    QuasiCompact.compactSpace_of_compactSpace (Scheme.Hom.deformationSpaceProj g s)
  have hqc : QuasiCompact (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  refine ⟨{}, hD, inferInstance, hqc,
    Scheme.Hom.isPullback_deformationSpaceOneFibre g s,
    Scheme.Hom.comp_deformationSpaceOneFibre hs,
    Scheme.Hom.isPullback_normalConeToDeformationSpace g s,
    Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace, ?_⟩
  apply WeilConjectures.PurityConventions.regularNormalBundle s d
  intro x
  obtain ⟨U, hx, r, hr, hI⟩ := hregular x
  have hL : Ideal.ofList (List.ofFn r) = s.ker.ideal U := by
    simpa only [Ideal.ofList, List.mem_ofFn', Set.ofPred_mem_eq] using hI
  refine ⟨U, hx, List.ofFn r, List.length_ofFn, ⟨hr, ?_⟩, hL⟩
  intro htop
  have htopI : s.ker.ideal U = ⊤ := by
    rw [← hL]
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using htop.symm
  have hz := s.ker.mem_support_iff.mp (s.range_subset_ker_support ⟨x, rfl⟩) U
  have hnunit := (V.mem_zeroLocus_iff _ _).mp hz 1 (htopI ▸ trivial)
  exact hnunit (by simpa only [Scheme.basicOpen_one] using hx)

private theorem section_line
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f] [HasInvertibleExponent A X]
    (t : T ⟶ X) :
    ∃ L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty (((upperStar (ModuleCat.{u + 1} A) t).leftDerivedFunctor.obj
        (dualizingComplex (ModuleCat.{u + 1} A) f))⟦-(2 * (d : ℤ))⟧ ≅
          (_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
      ∃ cover : Scheme.Cover.{u} Scheme.etalePrecoverage T,
        ∀ i : cover.I₀, Nonempty (L.over (cover.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) := by
  classical
  obtain ⟨L₀, hLC₀, hStalk₀, ⟨e₀⟩, _⟩ := exists_dualizingComplex_iso_and_tensor A f d
  let L := (upperStar (ModuleCat.{u + 1} A) t).obj L₀
  have hLC : Scheme.IsLocallyConstantSheaf L :=
    Scheme.IsLocallyConstantSheaf.upperStar t L₀
  have hStalk : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ T),
      Nonempty ((Scheme.pointSmallEtale x).sheafFiber.obj L ≅ ModuleCat.of A A) := by
    intro Ω _ _ x
    exact ⟨(upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) t x).app L₀ ≪≫
      (hStalk₀ Ω (x ≫ t)).some⟩
  refine ⟨L, ?_, ?_⟩
  · let P := (upperStar (ModuleCat.{u + 1} A) t).leftDerivedFunctor
    let e : P.obj (dualizingComplex (ModuleCat.{u + 1} A) f) ≅
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L)⟦(2 * (d : ℤ))⟧ :=
      P.mapIso e₀ ≪≫ (P.commShiftIso (2 * (d : ℤ))).app _ ≪≫
        (shiftFunctor _ (2 * (d : ℤ))).mapIso
          ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) t).app L₀)
    exact ⟨(shiftFunctor _ (-(2 * (d : ℤ)))).mapIso e ≪≫
      shiftShiftNeg _ (2 * (d : ℤ))⟩
  · obtain ⟨datum⟩ := hLC.nonempty_locallyConstantDatum
    let cover : Scheme.Cover.{u} Scheme.etalePrecoverage T :=
      Scheme.Cover.mkOfCovers (Σ i : datum.cover.I₀, datum.cover.X i)
        (fun i ↦ datum.cover.X i.1) (fun i ↦ datum.cover.f i.1)
        (by
          intro x
          obtain ⟨i, y, hy⟩ := datum.cover.exists_eq x
          exact ⟨⟨i, y⟩, y, hy⟩)
        (fun i ↦ datum.cover.map_prop i.1)
    refine ⟨cover, ?_⟩
    intro i
    let U := datum.cover.etalePrecoverageToEtale i.1
    have hC := datum.isConstant i.1
    obtain ⟨M, ⟨eM⟩⟩ := (L.over U).mem_essImage_of_isConstant
    let x := (datum.cover.X i.1).algClosurePoint i.2
    let P := upperStar (ModuleCat.{u + 1} A) U.hom
    let eP : (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ≅ P.obj L :=
      ((Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
        (T.smallEtaleTopology.over U) U.left.smallEtaleTopology (ModuleCat.{u + 1} A)
        Over.mkIdTerminal).symm.app M ≪≫
      (Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} A)).functor.mapIso eM ≪≫
      Scheme.overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A) U L
    have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} A)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    let eFree : M ≅ ModuleCat.of A A :=
      ((Scheme.pointSmallEtale x).sheafFiberConstantSheafIso M).symm ≪≫
      (Scheme.pointSmallEtale x).sheafFiber.mapIso eP ≪≫
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) U.hom x).app L ≪≫
      (hStalk _ (x ≫ U.hom)).some
    exact ⟨eM.symm ≪≫
      (constantSheaf (T.smallEtaleTopology.over U) (ModuleCat.{u + 1} A)).mapIso eFree⟩

private theorem invertible_exponent (ell n : ℕ) [Fact ell.Prime]
    (S : Scheme.{u}) (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x)) :
    HasInvertibleExponent (Coeff ell n) S := by
  refine ⟨ell ^ n, pow_pos (Nat.Prime.pos Fact.out) n, ?_, ?_⟩
  · apply ULift.ext
    exact ZMod.natCast_self (ell ^ n)
  · apply S.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    change IsUnit ((S.presheaf.germ ⊤ x hx).hom _)
    simpa only [map_pow, map_natCast, Nat.cast_pow] using (hS x).pow n

private theorem isIso_sectionMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f] [HasInvertibleExponent A X]
    (f' : X' ⟶ Y') [HasCompactification f'] [QuasiCompact f']
    (b : Y' ⟶ Y) (v : X' ⟶ X) (sq : IsPullback v f' f b)
    (s : Y ⟶ X) (s' : Y' ⟶ X') (hs : s' ≫ v = b ≫ s) :
    IsIso (sectionMap A f f' b v sq s s' hs) := by
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general A f d sq
  have : IsIso (dualizingComplexBaseChangeMap A sq) := by
    rw [isIso_dualizingComplexBaseChangeMap_iff]
    infer_instance
  unfold sectionMap
  infer_instance

/-- The two shifted complexes are actual locally constant free rank-one module sheaves;
the canonical exceptional fibre maps are isomorphisms.
Source: sk-thm-dnc, opening paragraph and fibre identifications
(blueprint: lem-pur-noetherian-etale-section-specialization).
Proof: Step 5 applies ordinary smooth tensor duality to g and its Rees deformation,
whose geometric hypotheses are geometry above. The coefficients are finite and
annihilated by ell^n, invertible on the base. Exact inverse image preserves the
local trivializations and the shift, giving the two displayed sheaves. Step 6
applies the canonical smooth exceptional base-change theorem to the two fibre
squares. All categories remain ordinary and unbounded. -/
theorem lines_and_fibres
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (hV : ∀ x : V, IsUnit (ell : V.presheaf.stalk x))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (hregular : ∀ x : S, ∃ U : V.affineOpens, s x ∈ U.1 ∧
      ∃ r : Fin d → Γ(V, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn r) ∧
          Ideal.span (Set.range r) = s.ker.ideal U)
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] :
    (∃ L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (Coeff ell n)),
      Nonempty ((sectionInvariant (Coeff ell n) g s)⟦-(2 * (d : ℤ))⟧ ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
      ∃ cover : Scheme.Cover.{u} Scheme.etalePrecoverage S,
        ∀ i : cover.I₀, Nonempty (L.over (cover.etalePrecoverageToEtale i) ≅
          (constantSheaf (S.smallEtaleTopology.over (cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} (Coeff ell n))).obj
              (ModuleCat.of (Coeff ell n) (Coeff ell n)))) ∧
    (∃ L : Sheaf (AffineSpace (ULift.{u} (Fin 1)) S).smallEtaleTopology
        (ModuleCat.{u + 1} (Coeff ell n)),
      Nonempty ((family (Coeff ell n) g s)⟦-(2 * (d : ℤ))⟧ ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
      ∃ cover : Scheme.Cover.{u} Scheme.etalePrecoverage
          (AffineSpace (ULift.{u} (Fin 1)) S),
        ∀ i : cover.I₀, Nonempty (L.over (cover.etalePrecoverageToEtale i) ≅
          (constantSheaf
            ((AffineSpace (ULift.{u} (Fin 1)) S).smallEtaleTopology.over
              (cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} (Coeff ell n))).obj
              (ModuleCat.of (Coeff ell n) (Coeff ell n)))) ∧
    IsIso (atOne (Coeff ell n) g s hs) ∧ IsIso (atZero (Coeff ell n) g s) := by
  have _ := hn
  have _ := hV
  have _ := hregular
  have hInv : HasInvertibleExponent (Coeff ell n) S := invertible_exponent ell n S hS
  have : HasInvertibleExponent (Coeff ell n) V := HasInvertibleExponent.of_hom g
  have : HasInvertibleExponent (Coeff ell n) s.ker.deformationSpace :=
    HasInvertibleExponent.of_hom (s.ker.deformationSpaceProj ≫ g)
  have hD := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  refine ⟨section_line (Coeff ell n) g d s,
    section_line (Coeff ell n) (Scheme.Hom.deformationSpaceProj g s) d
      s.deformationSpaceSection, ?_, ?_⟩
  · exact isIso_sectionMap (Coeff ell n) (Scheme.Hom.deformationSpaceProj g s) d g
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
      (Scheme.Hom.deformationSpaceOneFibre g s)
      (Scheme.Hom.isPullback_deformationSpaceOneFibre g s) s.deformationSpaceSection s
      (Scheme.Hom.comp_deformationSpaceOneFibre hs)
  · exact isIso_sectionMap (Coeff ell n) (Scheme.Hom.deformationSpaceProj g s) d
      (Scheme.Hom.normalConeProj g s) (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
      s.ker.normalConeToDeformationSpace
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
      s.deformationSpaceSection s.normalConeZeroSection
      Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace

/-- Existence and uniqueness of the comparison normalized at one.
Source: sk-thm-dnc, Local construction and Gluing
(blueprint: lem-pur-noetherian-etale-section-specialization).
Proof: Step 7 uses the centered etale charts and etale/open exceptional-adjoint
locality, Nagata compactification and ordinary affine-space duality to construct
local comparisons with the pullback of the source line. Normalize each by the
inverse of its value at one. Step 8 uses full faithfulness of degree-zero sheaves
after the common shift. The ratio on an overlap is an intrinsic unit-valued
section, since A is commutative. Each geometric affine line is connected, so its
ratio is constant, and equals one because of the normalization. Conservative
exact geometric stalks detect equality of these sheaf maps. Step 9 glues the
maps and their inverses using sheaf-Hom gluing; the same ratio argument proves
uniqueness. No general A1-invariance claim for locally constant sheaves is used. -/
theorem existsUnique_normalized
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (hV : ∀ x : V, IsUnit (ell : V.presheaf.stalk x))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (hregular : ∀ x : S, ∃ U : V.affineOpens, s x ∈ U.1 ∧
      ∃ r : Fin d → Γ(V, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn r) ∧
          Ideal.span (Set.range r) = s.ker.ideal U)
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] :
    ∃! κ : family (Coeff ell n) g s ≅
      (upperStar (ModuleCat.{u + 1} (Coeff ell n))
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant (Coeff ell n) g s),
      Normalized (Coeff ell n) g s hs κ := by
  sorry

/-- The inverse zero restriction is an isomorphism from the original section line to
the normal-bundle zero-section line, in its canonical Rees-cone presentation.
Source: sk-thm-dnc, final specialization
(blueprint: lem-pur-noetherian-etale-section-specialization).
Proof: Step 9 restricts the global comparison at zero and inverts, then composes
with the canonical zero-fibre base-change isomorphism. The inverse-image section
compositor identifies i0*a* with the identity. Every factor is an isomorphism,
as shown in lines_and_fibres, giving exactly delta=(i0*kappa)^(-1) under the stated
fibre identifications. -/
theorem isIso_specialization
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (hV : ∀ x : V, IsUnit (ell : V.presheaf.stalk x))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (hregular : ∀ x : S, ∃ U : V.affineOpens, s x ∈ U.1 ∧
      ∃ r : Fin d → Γ(V, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn r) ∧
          Ideal.span (Set.range r) = s.ker.ideal U)
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)]
    (κ : family (Coeff ell n) g s ≅
      (upperStar (ModuleCat.{u + 1} (Coeff ell n))
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant (Coeff ell n) g s))
    (hκ : Normalized (Coeff ell n) g s hs κ) :
    IsIso (specialization (Coeff ell n) g s κ) := by
  have _ := hκ
  have := (lines_and_fibres ell n hn hS hV d g s hs hregular).2.2.2
  unfold specialization
  infer_instance

/-- The zero-fibre maps commute with the fixed Rees base-change map. This is the
well-definedness condition for the universal-property definition of normalMap.
Source: sk-thm-dnc, arbitrary base change
(blueprint: lem-pur-noetherian-etale-section-specialization).
Proof: compose the deformation square with the zero-fibre inclusion. Replace the
composite through the primed deformation by its zero-fibre square, then use
zeroSection_comp_map to move the base-change map past the zero section. Associativity
gives the displayed equality, which is the required pullback-lift condition. -/
theorem normalMap_condition {V S S' : Scheme.{u}} (g : V ⟶ S) (s : S ⟶ V)
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) (b : S' ⟶ S)
    (sq : IsPullback (deformationMap g s hs b)
      (Scheme.Hom.deformationSpaceProj (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b))
      (Scheme.Hom.deformationSpaceProj g s) (AffineSpace.map (ULift.{u} (Fin 1)) b)) :
    ((Scheme.Hom.baseChangeSection g s hs b).ker.normalConeToDeformationSpace ≫
      deformationMap g s hs b) ≫ Scheme.Hom.deformationSpaceProj g s =
    (Scheme.Hom.normalConeProj (pullback.snd g b)
      (Scheme.Hom.baseChangeSection g s hs b) ≫ b) ≫
      AffineSpace.zeroSection (ULift.{u} (Fin 1)) S := by
  calc
    _ = (Scheme.Hom.baseChangeSection g s hs b).ker.normalConeToDeformationSpace ≫
        Scheme.Hom.deformationSpaceProj (pullback.snd g b)
          (Scheme.Hom.baseChangeSection g s hs b) ≫
        AffineSpace.map (ULift.{u} (Fin 1)) b := by
      rw [Category.assoc, sq.w]
    _ = _ := by
      rw [← Category.assoc,
        (Scheme.Hom.isPullback_normalConeToDeformationSpace (pullback.snd g b)
          (Scheme.Hom.baseChangeSection g s hs b)).w, Category.assoc,
        AffineSpace.zeroSection_comp_map, ← Category.assoc]

/-- The normal-cone map induced from the canonical Rees map at zero, by the
universal property of the specified zero-fibre square. Source: sk-thm-dnc, base change
(blueprint: lem-pur-noetherian-etale-section-specialization). -/
def normalMap {V S S' : Scheme.{u}} (g : V ⟶ S) (s : S ⟶ V)
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) (b : S' ⟶ S)
    (sq : IsPullback (deformationMap g s hs b)
      (Scheme.Hom.deformationSpaceProj (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b))
      (Scheme.Hom.deformationSpaceProj g s) (AffineSpace.map (ULift.{u} (Fin 1)) b)) :
    (Scheme.Hom.baseChangeSection g s hs b).ker.normalCone ⟶ s.ker.normalCone :=
  (Scheme.Hom.isPullback_normalConeToDeformationSpace g s).lift
    ((Scheme.Hom.baseChangeSection g s hs b).ker.normalConeToDeformationSpace ≫
      deformationMap g s hs b)
    (Scheme.Hom.normalConeProj (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b) ≫ b)
    (normalMap_condition g s hs b sq)

/-- Canonical pullback of the source section complex. Source: sk-thm-dnc, base change
(blueprint: lem-pur-noetherian-etale-section-specialization). -/
def sourceBaseChange (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S S' : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) (hs : s ≫ g = 𝟙 S) (b : S' ⟶ S) :
    (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj
      (sectionInvariant A g s) ⟶
        sectionInvariant A (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b) :=
  sectionMap A g (pullback.snd g b) b (pullback.fst g b)
    (IsPullback.of_hasPullback g b) s (Scheme.Hom.baseChangeSection g s hs b)
    (Scheme.Hom.baseChangeSection_fst g s hs b)

/-- Canonical pullback of the actual family complex, using the fixed Rees map.
Source: sk-thm-dnc, base change
(blueprint: lem-pur-noetherian-etale-section-specialization). -/
def familyBaseChange (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S S' : Scheme.{u}} (g : V ⟶ S) [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) (b : S' ⟶ S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj (pullback.snd g b)
      (Scheme.Hom.baseChangeSection g s hs b))]
    (sq : IsPullback (deformationMap g s hs b)
      (Scheme.Hom.deformationSpaceProj (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b))
      (Scheme.Hom.deformationSpaceProj g s) (AffineSpace.map (ULift.{u} (Fin 1)) b)) :
    (upperStar (ModuleCat.{u + 1} A) (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj
        (family A g s) ⟶
    family A (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b) :=
  sectionMap A (Scheme.Hom.deformationSpaceProj g s)
    (Scheme.Hom.deformationSpaceProj (pullback.snd g b)
      (Scheme.Hom.baseChangeSection g s hs b))
    (AffineSpace.map (ULift.{u} (Fin 1)) b) (deformationMap g s hs b) sq
    s.deformationSpaceSection (Scheme.Hom.baseChangeSection g s hs b).deformationSpaceSection
    (Scheme.Hom.deformationSpaceSection_comp_deformationSpaceMap_baseChangeSection g s hs b)

/-- Arbitrary base change preserves the Rees deformation, its sections and its normal
cone. This establishes the auxiliary class instances used in the naturality interface;
only compactifiability is assumed for the three base-changed maps.
Source: sk-thm-dnc, final base-change paragraph
(blueprint: lem-pur-noetherian-etale-section-specialization).
Proof: Step 4 writes B'=B tensor_R R' and P'=R'[x]. The base-changed etale chart
is flat over P', so the same monomial computation gives the canonical Rees map
B[t,I/t] tensor_R R'=B'[t,I'/t], even for nonflat R'. It commutes with t, both
augmentations, and the associated-graded quotient. Thus the specified Rees map
is Cartesian, and its zero-fibre lift is the Cartesian normal-cone map. Closedness
of the base-changed section follows by base change of the original closed immersion.
The normal bundle is affine of finite rank, so its projection is quasi-compact.
These arguments cover the empty base and zero rank. -/
theorem baseChange_geometry
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (hV : ∀ x : V, IsUnit (ell : V.presheaf.stalk x))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (hregular : ∀ x : S, ∃ U : V.affineOpens, s x ∈ U.1 ∧
      ∃ r : Fin d → Γ(V, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn r) ∧
          Ideal.span (Set.range r) = s.ker.ideal U)
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    {S' : Scheme.{u}} [IsNoetherian S'] (b : S' ⟶ S)
    [HasCompactification (Scheme.Hom.normalConeProj (pullback.snd g b)
      (Scheme.Hom.baseChangeSection g s hs b))]
    [HasCompactification (Scheme.Hom.deformationSpaceProj (pullback.snd g b)
      (Scheme.Hom.baseChangeSection g s hs b))] :
    IsClosedImmersion (Scheme.Hom.baseChangeSection g s hs b) ∧
    QuasiCompact (Scheme.Hom.normalConeProj g s) ∧
    QuasiCompact (Scheme.Hom.normalConeProj (pullback.snd g b)
      (Scheme.Hom.baseChangeSection g s hs b)) ∧
    ∃ sq : IsPullback (deformationMap g s hs b)
        (Scheme.Hom.deformationSpaceProj (pullback.snd g b)
          (Scheme.Hom.baseChangeSection g s hs b))
        (Scheme.Hom.deformationSpaceProj g s) (AffineSpace.map (ULift.{u} (Fin 1)) b),
      IsPullback (normalMap g s hs b sq)
        (Scheme.Hom.normalConeProj (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b))
        (Scheme.Hom.normalConeProj g s) b ∧
      (Scheme.Hom.baseChangeSection g s hs b).normalConeZeroSection ≫
          normalMap g s hs b sq = b ≫ s.normalConeZeroSection := by
  have _ := hn
  have _ := hS
  have _ := hV
  have _ := hregular
  have hs' : IsClosedImmersion (Scheme.Hom.baseChangeSection g s hs b) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (Scheme.Hom.isPullback_baseChangeSection g s hs b).flip inferInstance
  have hqc : QuasiCompact (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have hqc' : QuasiCompact (Scheme.Hom.normalConeProj (pullback.snd g b)
      (Scheme.Hom.baseChangeSection g s hs b)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b)) inferInstance
  have sq : IsPullback (deformationMap g s hs b)
      (Scheme.Hom.deformationSpaceProj (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b))
      (Scheme.Hom.deformationSpaceProj g s) (AffineSpace.map (ULift.{u} (Fin 1)) b) := by
    apply Scheme.IdealSheafData.isPullback_deformationSpaceMap_proj
      (pullback.fst g b) s.ker (Scheme.Hom.baseChangeSection g s hs b).ker
      (Scheme.Hom.map_siteIdeal_ker_le_baseChangeSection g s hs b) _ g _ b
      (IsPullback.of_hasPullback g b)
    intro x
    obtain ⟨U', U, hU, hx, _, H⟩ :=
      Scheme.Hom.exists_isPushout_extendedReesAlgebraMap_baseChange g s hs b d x
    exact ⟨U', U, hU, hx, H⟩
  have hfst : normalMap g s hs b sq ≫ s.ker.normalConeToDeformationSpace =
      (Scheme.Hom.baseChangeSection g s hs b).ker.normalConeToDeformationSpace ≫
        deformationMap g s hs b := by
    exact IsPullback.lift_fst _ _ _ _
  have hsnd : normalMap g s hs b sq ≫ Scheme.Hom.normalConeProj g s =
      Scheme.Hom.normalConeProj (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b) ≫ b := by
    exact IsPullback.lift_snd _ _ _ _
  refine ⟨hs', hqc, hqc', sq, ?_, ?_⟩
  · have hp := (Scheme.Hom.isPullback_normalConeToDeformationSpace (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b)).paste_horiz sq
    rw [AffineSpace.zeroSection_comp_map, ← hfst] at hp
    exact hp.of_right hsnd (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
  · apply (Scheme.Hom.isPullback_normalConeToDeformationSpace g s).hom_ext
    · rw [Category.assoc, hfst, ← Category.assoc,
        Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace,
        Category.assoc]
      rw [show (Scheme.Hom.baseChangeSection g s hs b).deformationSpaceSection ≫
          deformationMap g s hs b = AffineSpace.map _ b ≫ s.deformationSpaceSection from
        Scheme.Hom.deformationSpaceSection_comp_deformationSpaceMap_baseChangeSection
          g s hs b, ← Category.assoc, AffineSpace.zeroSection_comp_map]
      simp only [Category.assoc,
        Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace]
    · rw [Category.assoc, hsnd, ← Category.assoc,
        Scheme.Hom.normalConeZeroSection_normalConeProj
          (Scheme.Hom.baseChangeSection_snd g s hs b),
        Category.id_comp, Category.assoc,
        Scheme.Hom.normalConeZeroSection_normalConeProj hs, Category.comp_id]

/-- Both normalized comparisons commute with arbitrary Noetherian base change under the
canonical exceptional mates. The first equation is b_F followed by kappa', equal to
pullback(kappa) followed by the projection compositor and a'^*b_C. The second is
b_C followed by delta', equal to pullback(delta) followed by b_N. All deformation
and normal maps are fixed by the Rees construction, not freely chosen maps.
Source: sk-thm-dnc, final base-change paragraph
(blueprint: lem-pur-noetherian-etale-section-specialization).
Proof: Step 10 uses composition of unbounded compact-support exchange and mate pasting
for the two decompositions of the fibre/base-change rectangles. This proves
θ' i1'^*b_F = b_C b^*θ and η' i0'^*b_F = b_N b^*η, with the inverse-image
compositors. All b maps are invertible by smooth exceptional base change. Hence
Step 11 forms a'^*b_C composed with pullback(kappa) and b_F^(-1). Its value at one
is θ' by the first identity, so uniqueness of normalized comparisons identifies
it with kappa'. At zero, the second identity and inversion give precisely the
second displayed equality. This includes the identity, etale and nonflat cases. -/
theorem baseChange_compatibility
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (hV : ∀ x : V, IsUnit (ell : V.presheaf.stalk x))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (hregular : ∀ x : S, ∃ U : V.affineOpens, s x ∈ U.1 ∧
      ∃ r : Fin d → Γ(V, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn r) ∧
          Ideal.span (Set.range r) = s.ker.ideal U)
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)]
    {S' : Scheme.{u}} [IsNoetherian S'] (b : S' ⟶ S)
    [IsClosedImmersion (Scheme.Hom.baseChangeSection g s hs b)]
    [HasCompactification (Scheme.Hom.normalConeProj (pullback.snd g b)
      (Scheme.Hom.baseChangeSection g s hs b))]
    [QuasiCompact (Scheme.Hom.normalConeProj (pullback.snd g b)
      (Scheme.Hom.baseChangeSection g s hs b))]
    [HasCompactification (Scheme.Hom.deformationSpaceProj (pullback.snd g b)
      (Scheme.Hom.baseChangeSection g s hs b))]
    (sq : IsPullback (deformationMap g s hs b)
      (Scheme.Hom.deformationSpaceProj (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b))
      (Scheme.Hom.deformationSpaceProj g s) (AffineSpace.map (ULift.{u} (Fin 1)) b))
    (sqN : IsPullback (normalMap g s hs b sq)
      (Scheme.Hom.normalConeProj (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b))
      (Scheme.Hom.normalConeProj g s) b)
    (hz : (Scheme.Hom.baseChangeSection g s hs b).normalConeZeroSection ≫
      normalMap g s hs b sq = b ≫ s.normalConeZeroSection)
    (κ : family (Coeff ell n) g s ≅
      (upperStar (ModuleCat.{u + 1} (Coeff ell n))
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant (Coeff ell n) g s))
    (hκ : Normalized (Coeff ell n) g s hs κ)
    (κ' : family (Coeff ell n) (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b) ≅
      (upperStar (ModuleCat.{u + 1} (Coeff ell n))
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.obj
          (sectionInvariant (Coeff ell n) (pullback.snd g b)
            (Scheme.Hom.baseChangeSection g s hs b)))
    (hκ' : Normalized (Coeff ell n) (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b)
      (Scheme.Hom.baseChangeSection_snd g s hs b) κ') :
    IsIso (sourceBaseChange (Coeff ell n) g s hs b) ∧
    IsIso (familyBaseChange (Coeff ell n) g s hs b sq) ∧
    IsIso (sectionMap (Coeff ell n) (Scheme.Hom.normalConeProj g s)
      (Scheme.Hom.normalConeProj (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b))
      b (normalMap g s hs b sq) sqN s.normalConeZeroSection
      (Scheme.Hom.baseChangeSection g s hs b).normalConeZeroSection hz) ∧
    familyBaseChange (Coeff ell n) g s hs b sq ≫ κ'.hom =
      (upperStar (ModuleCat.{u + 1} (Coeff ell n))
        (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.map κ.hom ≫
      (linePullback (Coeff ell n) b (sectionInvariant (Coeff ell n) g s)).hom ≫
      (upperStar (ModuleCat.{u + 1} (Coeff ell n))
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.map
          (sourceBaseChange (Coeff ell n) g s hs b) ∧
    sourceBaseChange (Coeff ell n) g s hs b ≫
      specialization (Coeff ell n) (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b) κ' =
      (upperStar (ModuleCat.{u + 1} (Coeff ell n)) b).leftDerivedFunctor.map
        (specialization (Coeff ell n) g s κ) ≫
      sectionMap (Coeff ell n) (Scheme.Hom.normalConeProj g s)
        (Scheme.Hom.normalConeProj (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b))
        b (normalMap g s hs b sq) sqN s.normalConeZeroSection
        (Scheme.Hom.baseChangeSection g s hs b).normalConeZeroSection hz := by
  sorry

end AlgebraicGeometry.Etale.NoetherianSectionSpecialization
