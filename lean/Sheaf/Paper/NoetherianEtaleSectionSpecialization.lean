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
public import Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.Paper.RingedTopoiDerivedTensorPullback
import Mathlib.Topology.Connected.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import WeilConjectures.Compactification.NagataCompactification

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
