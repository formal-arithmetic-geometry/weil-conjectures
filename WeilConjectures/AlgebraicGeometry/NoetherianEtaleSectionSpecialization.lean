/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.PurityNormalCone
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.SectionLocalDualizingComparisons
import WeilConjectures.AlgebraicGeometry.SmoothSectionAffineCoordinates
import WeilConjectures.AlgebraicGeometry.EtaleShiftedLineNormalizedDescent
import all WeilConjectures.AlgebraicGeometry.SectionExceptionalFibreCoherence
import WeilConjectures.AlgebraicGeometry.PurityConventions
public import WeilConjectures.SixFunctors.SmoothDualityBaseChangeCompat
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

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

private theorem compact_normalProjection {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [SmoothOfRelativeDimension d (Scheme.Hom.deformationSpaceProj g s)] :
    HasCompactification (SectionLocalDualizingComparisons.normalProjection d g s hs) := by
  have hsq := (SectionLocalDualizingComparisons.normalFibre_spec d g s hs).1
  have : SmoothOfRelativeDimension d
      (SectionLocalDualizingComparisons.normalProjection d g s hs) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback hsq inferInstance
  have : IsSeparated (SectionLocalDualizingComparisons.normalProjection d g s hs) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hsq inferInstance
  have : Smooth (SectionLocalDualizingComparisons.normalProjection d g s hs) :=
    SmoothOfRelativeDimension.smooth d _
  have := SectionLocalDualizingComparisons.normalProjectionQuasiCompact d g s hs
  exact (NagataCompactification _).hasCompactification

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
  have : IsNoetherian (AffineSpace (ULift.{u} (Fin 1)) S) :=
    isNoetherian_of_locallyOfFiniteType (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
  have : IsNoetherian s.ker.deformationSpace :=
    isNoetherian_of_locallyOfFiniteType (Scheme.Hom.deformationSpaceProj g s)
  have := compact_normalProjection d g s hs
  obtain ⟨N, hN, hA, hNS⟩ :=
    HasInvertibleExponent.exists_isUnit_natCast (Λ := Coeff ell n) (X := S)
  have hlocal := SectionLocalDualizingComparisons.section_local_dualizing_comparisons
    (Coeff ell n) N hN hA hNS d g s hs
  refine ⟨hlocal.1, hlocal.2.1, ?_, ?_⟩
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

private def pointChart {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) (x : S) :
    SmoothSectionCentredCoordinates.AffineChart d g s :=
  (SmoothSectionCentredCoordinates.exists_affineChart d g s hs x).choose

private theorem pointChart_mem {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) (x : S) : x ∈ (pointChart d g s hs x).T.1 :=
  (SmoothSectionCentredCoordinates.exists_affineChart d g s hs x).choose_spec

private def centredChart {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S)
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (c : SmoothSectionCentredCoordinates.AffineChart d g s) :
    SectionLocalDualizingComparisons.Chart d g s hs := by
  let j := pullback.lift c.U.1.ι (g.resLE c.T.1 c.U.1 c.mapsInto)
    (g.resLE_comp_ι c.mapsInto).symm
  let r := s.resLE c.U.1 c.T.1 c.sectionInto
  have hr : r ≫ c.U.1.ι = c.T.1.ι ≫ s := s.resLE_comp_ι c.sectionInto
  have hrpb : IsPullback r c.T.1.ι c.U.1.ι s :=
    IsOpenImmersion.isPullback _ _ _ _ hr.symm (by
      simpa only [Scheme.Opens.opensRange_ι] using c.sectionPreimage)
  have hclosed : IsClosedImmersion r :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hrpb.flip inferInstance
  refine
    { T := c.T.1.toScheme
      b := c.T.1.ι
      affineT := c.T.2
      openB := inferInstance
      U := c.U.1.toScheme
      affineU := c.U.2
      j := j
      openJ := c.openInBaseChange
      r := r
      closedR := hclosed
      section_eq := ?_
      e := c.e
      etaleE := c.etale
      separatedE := c.separated
      overE := ?_
      centres := ?_ }
  · apply pullback.hom_ext
    · simpa only [Category.assoc, j, pullback.lift_fst,
        Scheme.Hom.baseChangeSection_fst] using hr
    · simp only [Category.assoc, j, pullback.lift_snd,
        Scheme.Hom.baseChangeSection_snd]
      apply (cancel_mono c.T.1.ι).mp
      rw [Category.assoc, g.resLE_comp_ι, ← Category.assoc, hr, Category.assoc, hs]
      simp
  · simpa only [j, pullback.lift_snd] using c.over
  · exact c.zeroFiber

private theorem line_shape (A : Type (u + 1)) [CommRing A] (d : ℕ)
    (T : Scheme.{u}) (K : DerivedCategoryModule A T)
    (hK : ∃ L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty (K⟦-(2 * (d : ℤ))⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
      ∃ cov : Scheme.Cover.{u} Scheme.etalePrecoverage T,
        ∀ i : cov.I₀, Nonempty (L.over (cov.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (cov.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) :
    ∃ L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
      Scheme.IsLisseRankOneSheaf L ∧
        Nonempty (K⟦-(2 * (d : ℤ))⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj L) := by
  obtain ⟨L, hKL, cov, hcov⟩ := hK
  refine ⟨L, ⟨cov, fun i ↦ ?_⟩, hKL⟩
  obtain ⟨e⟩ := hcov i
  let U := cov.etalePrecoverageToEtale i
  let E := Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} A)
  let ec := ((Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
    (T.smallEtaleTopology.over U) U.left.smallEtaleTopology
    (ModuleCat.{u + 1} A) Over.mkIdTerminal).app (ModuleCat.of A A)
  exact ⟨(Scheme.overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A) U L).symm ≪≫
    E.functor.mapIso e ≪≫ ec⟩

private theorem chart_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (SectionLocalDualizingComparisons.normalProjection d g s hs)]
    [IsNoetherian s.ker.deformationSpace]
    [SmoothOfRelativeDimension d (Scheme.Hom.deformationSpaceProj g s)]
    (c : SectionLocalDualizingComparisons.Chart d g s hs) :
    Nonempty ((upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.map (ULift.{u} (Fin 1)) c.b)).leftDerivedFunctor.obj (family A g s) ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) c.T ↘ c.T)).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) c.b).leftDerivedFunctor.obj
            (sectionInvariant A g s))) := by
  obtain ⟨adjT, adjL, cIso, fIso, _⟩ :=
    (SectionLocalDualizingComparisons.section_local_dualizing_comparisons
      A N hN hA hS d g s hs).2.2.2.2 c
  exact ⟨SectionLocalDualizingComparisons.rawComparison A N hN hA _
    (SectionLocalDualizingComparisons.invertibleOnSource _ c.b hS) d _ _ cIso fIso⟩

private theorem local_comparisons_exist
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (SectionLocalDualizingComparisons.normalProjection d g s hs)]
    [IsNoetherian s.ker.deformationSpace]
    [SmoothOfRelativeDimension d (Scheme.Hom.deformationSpaceProj g s)] :
    ∃ cover : Scheme.Cover.{u} Scheme.etalePrecoverage S,
      ∀ x : cover.I₀, Nonempty
        ((upperStar (ModuleCat.{u + 1} A)
          (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f x))).leftDerivedFunctor.obj
            (family A g s) ≅
          (upperStar (ModuleCat.{u + 1} A)
            (AffineSpace (ULift.{u} (Fin 1)) (cover.X x) ↘ cover.X x)).leftDerivedFunctor.obj
              ((upperStar (ModuleCat.{u + 1} A) (cover.f x)).leftDerivedFunctor.obj
                (sectionInvariant A g s))) := by
  let c := pointChart d g s hs
  let cover : Scheme.Cover.{u} Scheme.etalePrecoverage S :=
    Scheme.Cover.mkOfCovers S (fun x ↦ (c x).T.1.toScheme) (fun x ↦ (c x).T.1.ι)
      (fun x ↦ ⟨x, ⟨x, pointChart_mem d g s hs x⟩, rfl⟩) (fun _ ↦ inferInstance)
  refine ⟨cover, fun x ↦ ?_⟩
  exact chart_comparison A N hN hA hS d g s hs (centredChart d g s hs (c x))

private theorem normalize_chart (A : Type (u + 1)) [CommRing A]
    {S T : Scheme.{u}} (b : T ⟶ S) (C : DerivedCategoryModule A S)
    (F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S))
    (theta : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj F ≅ C)
    (e : (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj F ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj C)) :
    ∃ k, AffineLineNormalizedDescent.LocallyNormalized A b theta k := by
  let ratio := sectionRestrictionIso (ModuleCat.{u + 1} A)
    b (AffineSpace.map (ULift.{u} (Fin 1)) b) (AffineSpace.oneSection_comp_map b)
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) T) theta e
  refine ⟨e ≪≫ (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.mapIso ratio.symm, ?_⟩
  unfold AffineLineNormalizedDescent.LocallyNormalized
  rw [sectionRestrictionIso_trans_right]
  exact Iso.self_symm_id ratio

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
  classical
  let A := Coeff ell n
  have hD := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have : IsNoetherian (AffineSpace (ULift.{u} (Fin 1)) S) :=
    isNoetherian_of_locallyOfFiniteType (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
  have : IsNoetherian s.ker.deformationSpace :=
    isNoetherian_of_locallyOfFiniteType (Scheme.Hom.deformationSpaceProj g s)
  have : QuasiCompact (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have hlines := lines_and_fibres ell n hn hS hV d g s hs hregular
  have := hlines.2.2.1
  let theta := asIso (atOne A g s hs)
  have hN : 0 < ell ^ n := pow_pos (Nat.Prime.pos Fact.out) n
  have hA : ((ell ^ n : ℕ) : A) = 0 := by
    apply ULift.ext
    exact ZMod.natCast_self _
  have hNS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤)) := by
    apply S.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    change IsUnit ((S.presheaf.germ ⊤ x hx).hom _)
    simpa only [map_pow, map_natCast, Nat.cast_pow] using (hS x).pow n
  have hnormal := compact_normalProjection d g s hs
  obtain ⟨cover, local_exists⟩ :=
    local_comparisons_exist A (ell ^ n) hN hA hNS d g s hs
  choose normalized hnormalized using fun x : cover.I₀ ↦
    normalize_chart A (cover.f x) (sectionInvariant A g s) (family A g s)
      theta (local_exists x).some
  obtain ⟨kappa, hkappa, _, huniq, _⟩ :=
    (AffineLineNormalizedDescent.normalized_descent A S (2 * (d : ℤ))
      (sectionInvariant A g s) (family A g s)
      (line_shape A d S _ hlines.1) (line_shape A d _ _ hlines.2.1) theta cover
      normalized hnormalized).2.2
  exact ⟨kappa, hkappa, huniq⟩

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

private theorem comparison_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {d : ℕ} {B B' : Scheme.{u}} {Q : ExceptionalSectionPair B d}
    {Q' : ExceptionalSectionPair B' d} {v : B' ⟶ B}
    (e : ExceptionalSectionChange Q Q' v) :
    sectionExceptionalComparison A e =
      sectionMap A Q.map Q'.map v e.upper e.square
        Q.sect Q'.sect e.section_comm := by
  simp only [sectionExceptionalComparison, sectionCoherencePullbackIso, sectionMap,
    Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Category.assoc]

private def reesFamily {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)] :
    ExceptionalSectionFamily S d := by
  have hd := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have hline : IsNoetherian (AffineSpace (ULift.{u} (Fin 1)) S) :=
    isNoetherian_of_locallyOfFiniteType (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
  have hD : IsNoetherian s.ker.deformationSpace :=
    isNoetherian_of_locallyOfFiniteType (Scheme.Hom.deformationSpaceProj g s)
  have hn : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) hd
  have hsep : IsSeparated (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
        (inferInstance : IsSeparated (Scheme.Hom.deformationSpaceProj g s))
  have : QuasiCompact (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have hN : IsNoetherian s.ker.normalCone :=
    isNoetherian_of_locallyOfFiniteType (Scheme.Hom.normalConeProj g s)
  have hcD : IsClosedImmersion s.deformationSpaceSection := by
    have : IsClosedImmersion
        (s.deformationSpaceSection ≫ Scheme.Hom.deformationSpaceProj g s) := by
      rw [Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs]
      infer_instance
    exact IsClosedImmersion.of_comp s.deformationSpaceSection
      (Scheme.Hom.deformationSpaceProj g s)
  have hcN : IsClosedImmersion s.normalConeZeroSection := by
    have : IsClosedImmersion (s.normalConeZeroSection ≫ Scheme.Hom.normalConeProj g s) := by
      rw [Scheme.Hom.normalConeZeroSection_normalConeProj hs]
      infer_instance
    exact IsClosedImmersion.of_comp s.normalConeZeroSection
      (Scheme.Hom.normalConeProj g s)
  let source : ExceptionalSectionPair S d :=
    { total := V, map := g, sect := s, section_map := hs }
  let normal : ExceptionalSectionPair S d :=
    { total := s.ker.normalCone
      map := Scheme.Hom.normalConeProj g s
      sect := s.normalConeZeroSection
      section_map := Scheme.Hom.normalConeZeroSection_normalConeProj hs }
  refine
    { ambient :=
        { total := s.ker.deformationSpace
          map := Scheme.Hom.deformationSpaceProj g s
          sect := s.deformationSpaceSection
          section_map := Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs }
      fibre := fun t ↦ if t then source else normal
      restriction := ?_ }
  intro t
  cases t
  · exact
      { upper := s.ker.normalConeToDeformationSpace
        square := Scheme.Hom.isPullback_normalConeToDeformationSpace g s
        section_comm := Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace }
  · exact
      { upper := Scheme.Hom.deformationSpaceOneFibre g s
        square := Scheme.Hom.isPullback_deformationSpaceOneFibre g s
        section_comm := Scheme.Hom.comp_deformationSpaceOneFibre hs }

private theorem oneFibre_toBase {V S : Scheme.{u}} (g : V ⟶ S) (s : S ⟶ V) :
    Scheme.Hom.deformationSpaceOneFibre g s ≫ s.ker.deformationSpaceProj = 𝟙 V := by
  simp [Scheme.Hom.deformationSpaceOneFibre]

private theorem oneFibre_naturality {V S S' : Scheme.{u}} (g : V ⟶ S)
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) (b : S' ⟶ S)
    (sq : IsPullback (deformationMap g s hs b)
      (Scheme.Hom.deformationSpaceProj (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b))
      (Scheme.Hom.deformationSpaceProj g s) (AffineSpace.map (ULift.{u} (Fin 1)) b)) :
    pullback.fst g b ≫ Scheme.Hom.deformationSpaceOneFibre g s =
      Scheme.Hom.deformationSpaceOneFibre (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b) ≫ deformationMap g s hs b := by
  let f := Scheme.Hom.deformationSpaceOneFibre (pullback.snd g b)
    (Scheme.Hom.baseChangeSection g s hs b) ≫ deformationMap g s hs b
  have hw : f ≫ Scheme.Hom.deformationSpaceProj g s =
      (pullback.snd g b ≫ b) ≫ AffineSpace.oneSection (ULift.{u} (Fin 1)) S := by
    dsimp only [f]
    rw [Category.assoc, sq.w, ← Category.assoc,
      (Scheme.Hom.isPullback_deformationSpaceOneFibre (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b)).w, Category.assoc,
      AffineSpace.oneSection_comp_map, ← Category.assoc]
  let l := (Scheme.Hom.isPullback_deformationSpaceOneFibre g s).lift f
    (pullback.snd g b ≫ b) hw
  have hl : l ≫ Scheme.Hom.deformationSpaceOneFibre g s = f := IsPullback.lift_fst _ _ _ _
  have he : l = pullback.fst g b := by
    calc
      l = l ≫ (Scheme.Hom.deformationSpaceOneFibre g s ≫ s.ker.deformationSpaceProj) := by
        rw [oneFibre_toBase, Category.comp_id]
      _ = f ≫ s.ker.deformationSpaceProj := by rw [← Category.assoc, hl]
      _ = pullback.fst g b := by
        dsimp only [f, deformationMap]
        rw [Category.assoc, Scheme.IdealSheafData.deformationSpaceMap_toBase,
          ← Category.assoc, oneFibre_toBase, Category.id_comp]
  rw [← he]
  exact hl

private def reesBaseChange {V S S' : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    [IsNoetherian S'] (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) (b : S' ⟶ S)
    [IsNoetherian (pullback g b)]
    [SmoothOfRelativeDimension d (pullback.snd g b)]
    [IsClosedImmersion (Scheme.Hom.baseChangeSection g s hs b)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj (pullback.snd g b)
      (Scheme.Hom.baseChangeSection g s hs b))]
    [HasCompactification (Scheme.Hom.normalConeProj (pullback.snd g b)
      (Scheme.Hom.baseChangeSection g s hs b))]
    (sq : IsPullback (deformationMap g s hs b)
      (Scheme.Hom.deformationSpaceProj (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b))
      (Scheme.Hom.deformationSpaceProj g s) (AffineSpace.map (ULift.{u} (Fin 1)) b))
    (sqN : IsPullback (normalMap g s hs b sq)
      (Scheme.Hom.normalConeProj (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b))
      (Scheme.Hom.normalConeProj g s) b)
    (hz : (Scheme.Hom.baseChangeSection g s hs b).normalConeZeroSection ≫
      normalMap g s hs b sq = b ≫ s.normalConeZeroSection) :
    ExceptionalFamilyBaseChange (reesFamily d g s hs)
      (reesFamily d (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b)
        (Scheme.Hom.baseChangeSection_snd g s hs b)) b := by
  refine
    { ambient :=
        { upper := deformationMap g s hs b
          square := sq
          section_comm :=
            Scheme.Hom.deformationSpaceSection_comp_deformationSpaceMap_baseChangeSection
              g s hs b }
      fibre := ?_
      point_comm := ?_
      fibre_comm := ?_ }
  · intro t
    cases t
    · exact { upper := normalMap g s hs b sq, square := sqN, section_comm := hz }
    · exact
        { upper := pullback.fst g b
          square := IsPullback.of_hasPullback g b
          section_comm := Scheme.Hom.baseChangeSection_fst g s hs b }
  · intro t
    cases t
    · exact (AffineSpace.zeroSection_comp_map b).symm
    · exact (AffineSpace.oneSection_comp_map b).symm
  · intro t
    cases t
    · exact IsPullback.lift_fst _ _ _ _
    · exact oneFibre_naturality g s hs b sq

private theorem line_compositor (A : Type (u + 1)) [CommRing A]
    {S S' : Scheme.{u}} (b : S' ⟶ S) (C : DerivedCategoryModule A S) :
    (sectionCoherencePullbackIso A (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S') b
      (AffineSpace.map (ULift.{u} (Fin 1)) b)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) (AffineSpace.map_over b).symm C).inv =
        (linePullback A b C).hom := by
  have h := congrArg Iso.hom (sectionPullback_endpoint A
    (AffineSpace.map (ULift.{u} (Fin 1)) b)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S') b _ _
    (AffineSpace.map_over b).symm rfl rfl (AffineSpace.map_over b) C)
  simpa only [sectionCoherencePullbackIso, linePullback, Iso.trans_inv, Iso.symm_inv,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    NatTrans.comp_app] using h

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
  classical
  have hsm : SmoothOfRelativeDimension d (pullback.snd g b) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      (IsPullback.of_hasPullback g b) inferInstance
  have : Smooth (pullback.snd g b) := SmoothOfRelativeDimension.smooth d _
  have : IsNoetherian (pullback g b) :=
    isNoetherian_of_locallyOfFiniteType (pullback.snd g b)
  have hS' : ∀ x : S', IsUnit (ell : S'.presheaf.stalk x) := by
    intro x
    simpa only [map_natCast] using (hS (b x)).map (b.stalkMap x).hom
  have hV' : ∀ x : (pullback g b : Scheme.{u}), IsUnit (ell : (pullback g b).presheaf.stalk x) := by
    intro x
    simpa only [map_natCast] using (hS' (pullback.snd g b x)).map
      ((pullback.snd g b).stalkMap x).hom
  have hregular' : ∀ x : S', ∃ U : (pullback g b).affineOpens,
      (Scheme.Hom.baseChangeSection g s hs b) x ∈ U.1 ∧
      ∃ r : Fin d → Γ(pullback g b, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(pullback g b, U.1) (List.ofFn r) ∧
          Ideal.span (Set.range r) = (Scheme.Hom.baseChangeSection g s hs b).ker.ideal U := by
    intro x
    obtain ⟨c, hc⟩ := SmoothSectionCentredCoordinates.exists_affineChart d
      (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b)
      (Scheme.Hom.baseChangeSection_snd g s hs b) x
    refine ⟨c.U, c.sectionInto hc, c.x, c.regular.toIsWeaklyRegular, ?_⟩
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def,
      MvPolynomial.eval₂Hom_X'] using c.sectionIdeal
  have hu := existsUnique_normalized ell n hn hS hV d g s hs hregular
  have hu' := existsUnique_normalized ell n hn hS' hV' d (pullback.snd g b)
    (Scheme.Hom.baseChangeSection g s hs b)
    (Scheme.Hom.baseChangeSection_snd g s hs b) hregular'
  let P := reesFamily d g s hs
  let P' := reesFamily d (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b)
    (Scheme.Hom.baseChangeSection_snd g s hs b)
  let e := reesBaseChange d g s hs b sq sqN hz
  have norm_eq (k) : P.IsNormalized (Coeff ell n) k ↔ Normalized (Coeff ell n) g s hs k := by
    simp only [ExceptionalSectionFamily.IsNormalized, ExceptionalSectionFamily.fibreMap,
      comparison_eq, P, reesFamily, exceptionalFamilyPoint, Normalized,
      atOne]
    rfl
  have norm_eq' (k) : P'.IsNormalized (Coeff ell n) k ↔
      Normalized (Coeff ell n) (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b) (Scheme.Hom.baseChangeSection_snd g s hs b) k := by
    simp only [ExceptionalSectionFamily.IsNormalized, ExceptionalSectionFamily.fibreMap,
      comparison_eq, P', reesFamily, exceptionalFamilyPoint, Normalized,
      atOne]
    rfl
  have hk : P.IsNormalized (Coeff ell n) κ ∧
      ∀ τ, P.IsNormalized (Coeff ell n) τ → τ = κ :=
    ⟨(norm_eq κ).mpr hκ, fun τ hτ ↦ hu.unique ((norm_eq τ).mp hτ) hκ⟩
  have hk' : P'.IsNormalized (Coeff ell n) κ' ∧
      ∀ τ, P'.IsNormalized (Coeff ell n) τ → τ = κ' :=
    ⟨(norm_eq' κ').mpr hκ', fun τ hτ ↦ hu'.unique ((norm_eq' τ).mp hτ) hκ'⟩
  have hN : 0 < ell ^ n := pow_pos (Nat.Prime.pos Fact.out) n
  have hA : ((ell ^ n : ℕ) : Coeff ell n) = 0 := by
    apply ULift.ext
    exact ZMod.natCast_self _
  have hInv : ∀ x : S, IsUnit ((ell ^ n : ℕ) : S.presheaf.stalk x) := by
    intro x
    simpa only [Nat.cast_pow] using (hS x).pow n
  have hc := sectionExceptional_fibre_coherence (Coeff ell n) (ell ^ n) hN hA
    P P' hInv b e
  have hbc := sectionExceptional_normalized_baseChange (Coeff ell n) (ell ^ n) hN hA
    P P' hInv b e κ κ' hk hk'
  simp only [comparison_eq] at hc hbc
  have ha := hc.1
  have hf := (hc.2 true).2.2.1
  have hn := (hc.2 false).2.2.1
  have hfirst := hbc.1
  have hsecond := hbc.2
  change IsIso (familyBaseChange (Coeff ell n) g s hs b sq) at ha
  change IsIso (sourceBaseChange (Coeff ell n) g s hs b) at hf
  change IsIso (sectionMap (Coeff ell n) (Scheme.Hom.normalConeProj g s)
      (Scheme.Hom.normalConeProj (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b)) b (normalMap g s hs b sq) sqN
      s.normalConeZeroSection
      (Scheme.Hom.baseChangeSection g s hs b).normalConeZeroSection hz) at hn
  change familyBaseChange (Coeff ell n) g s hs b sq ≫ κ'.hom = _ at hfirst
  simp only [ExceptionalSectionFamily.specialization,
    ExceptionalSectionFamily.fibreMap, comparison_eq] at hsecond
  change sourceBaseChange (Coeff ell n) g s hs b ≫
      specialization (Coeff ell n) (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b) κ' = _ at hsecond
  refine ⟨hf, ha, hn, ?_, hsecond⟩
  rw [line_compositor] at hfirst
  exact hfirst

end AlgebraicGeometry.Etale.NoetherianSectionSpecialization
