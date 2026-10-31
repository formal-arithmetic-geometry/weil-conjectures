/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianEtaleSectionSpecialization
public import WeilConjectures.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import WeilConjectures.Targets.VectorBundlePurity
public import WeilConjectures.AlgebraicGeometry.FiniteRingBundleSectionOrientation
public import WeilConjectures.AlgebraicGeometry.AffineSpaceLinearTraceInvariance
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.AffineSpace
public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows
import WeilConjectures.AlgebraicGeometry.SectionCoordinateTowerOneFibre
import WeilConjectures.AlgebraicGeometry.CoordinateTowerAdjointIsIso
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.AlgebraicGeometry.VectorIntegrationFrameAdjoint
import WeilConjectures.AlgebraicGeometry.SectionPullbackCoefficientNaturality
import WeilConjectures.AlgebraicGeometry.BundleSectionProjectionUnit
import all WeilConjectures.AlgebraicGeometry.NoetherianEtaleSectionSpecialization
import WeilConjectures.AlgebraicGeometry.EtaleShiftedLineNormalizedDescent
import WeilConjectures.AlgebraicGeometry.SectionExceptionalFibreCoherence
import all WeilConjectures.AlgebraicGeometry.SectionReesBaseChangeEtale
import all WeilConjectures.AlgebraicGeometry.VectorIntegrationMate
import all WeilConjectures.AlgebraicGeometry.SectionLocalDualizingComparisons
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.SectionReesNoetherianGeometry
import WeilConjectures.AlgebraicGeometry.SmoothSectionCentredCoordinates
/-! # Normalized section deformation for arbitrary finite rings

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-dnc, Local construction and
Gluing; sk-prop-sp-orientation-charts, Steps 1--4
(blueprint: lem-trf-finite-ring-section-deformation).

The spaces are the actual extended-Rees deformation and associated-graded cone. The
coefficient-independent maps in NoetherianSectionSpecialization are reused. In particular
no arbitrary deformation datum, orientation, or fibre identification is a parameter.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option linter.all false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20001]
  CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local instance 20001]
  CategoryTheory.GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize
namespace AlgebraicGeometry.Etale.FiniteRingSectionDeformation
open NoetherianSectionSpecialization

/-- The geometric conclusions of the smooth-section construction, collected as proofs
so the derived functors can use the compactification instances they require.
Source: sk-thm-dnc, Local construction (blueprint: lem-trf-finite-ring-section-deformation).
The regular-sequence condition is local at every point of the centre, including rank zero. -/
class Geometry {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S) (s : S ⟶ V)
    [IsClosedImmersion s] : Prop where
  lineNoetherian : IsNoetherian (AffineSpace (ULift.{u} (Fin 1)) S)
  sourceNoetherian : IsNoetherian V
  deformationNoetherian : IsNoetherian s.ker.deformationSpace
  deformationSmooth : SmoothOfRelativeDimension d (Scheme.Hom.deformationSpaceProj g s)
  deformationSeparated : IsSeparated (Scheme.Hom.deformationSpaceProj g s)
  deformationCompact : HasCompactification (Scheme.Hom.deformationSpaceProj g s)
  deformationQuasiCompact : QuasiCompact (Scheme.Hom.deformationSpaceProj g s)
  coneNoetherian : IsNoetherian s.ker.normalCone
  coneCompact : HasCompactification (Scheme.Hom.normalConeProj g s)
  coneQuasiCompact : QuasiCompact (Scheme.Hom.normalConeProj g s)
  conormal : (ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d
  symmetric : IsIso (ConormalGradedAlgebra.symmetricComparison s)
  regular : ∀ x : S, ∃ U : V.affineOpens, s x ∈ U.1 ∧
    ∃ r : Fin d → Γ(V, U.1),
      RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn r) ∧
        Ideal.span (Set.range r) = s.ker.ideal U

attribute [instance] Geometry.lineNoetherian Geometry.sourceNoetherian
  Geometry.deformationNoetherian
  Geometry.deformationSmooth Geometry.deformationSeparated Geometry.deformationCompact
  Geometry.deformationQuasiCompact Geometry.coneCompact Geometry.coneQuasiCompact
  Geometry.conormal Geometry.symmetric
  Geometry.coneNoetherian

/-- Regularity, the conormal rank, and geometry of the actual Rees deformation are
conclusions, with no regularity or auxiliary compactification assumption.
Source: sk-thm-dnc, Local construction (blueprint: lem-trf-finite-ring-section-deformation).
Proof: Steps 1--2 choose centred etale coordinates and remove the complementary clopen
zero component. Polynomial variables form a regular sequence, and etale flatness preserves
it. Monomials identify the associated graded with Sym(I/I^2), and give conormal rank d.
Step 3 identifies B[t,I/t] with B tensor_R[x] R[t,u], x_j=t*u_j. These charts and the
punctured product cover the deformation, proving smoothness of dimension d. Step 4 uses
finite generation of I over Noetherian affine rings to prove the deformation Noetherian
and finite type. Its map to V times A1 is affine, giving separatedness. Nagata supplies
both compactifications. The same argument includes the empty base and d=0. -/
theorem geometry {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) :
    Geometry d g s := by
  obtain ⟨⟨I, c, hc⟩, _, hE, hSym⟩ :=
    SmoothSectionCentredCoordinates.exists_centred_coordinates d g s hs
  obtain ⟨_, e, _, hp, _, _, hline, hdef, hsm, hsep, hft, hqc, _, hcomp, _, _, _⟩ :=
    SectionReesNoetherianGeometry.geometry d g s hs
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian V := ⟨⟩
  have hpb := Scheme.Hom.isPullback_normalConeToDeformationSpace g s
  have : LocallyOfFiniteType (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb hft
  have : IsSeparated (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hpb hsep
  have : QuasiCompact (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hpb hqc
  have : IsLocallyNoetherian s.ker.normalCone :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.Hom.normalConeProj g s)
  have : CompactSpace s.ker.normalCone :=
    QuasiCompact.compactSpace_of_compactSpace (Scheme.Hom.normalConeProj g s)
  refine ⟨hline, inferInstance, hdef, hsm, hsep, hcomp, hqc, ⟨⟩,
    (NagataCompactification (Scheme.Hom.normalConeProj g s)).hasCompactification,
    inferInstance, hE, hSym, ?_⟩
  intro x
  have hx : x ∈ (⨆ i, (c i).T.1) := by rw [hc]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨(c i).U, (c i).sectionInto hi, (c i).x, (c i).regular.1, ?_⟩
  simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, MvPolynomial.eval₂Hom_X'] using
    (c i).sectionIdeal


/-- The canonical relative-Spec comparison induced by Sym(I/I^2) → gr_I.
Source: sk-thm-dnc, regular-coordinate algebra
(blueprint: lem-trf-finite-ring-section-deformation). -/
def coneBundleIso {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    (s : S ⟶ V) [IsClosedImmersion s] [Geometry d g s] :
    PurityNormalBundle.normalCone s ≅
      VectorBundleZeroSection.scheme S d (ConormalGradedAlgebra.piece s 1) :=
  (Over.forget S).mapIso
    ((ObjectProperty.ι (fun Y : Over S ↦ IsAffineHom Y.hom)).mapIso
      (((VectorBundleZeroSection.antiEquivalence S).inverse.mapIso
        (ObjectProperty.isoMk _ (asIso (ConormalGradedAlgebra.symmetricComparison s)))).unop))

/-- The specified cone-bundle comparison preserves the projection and zero section.
Together with purityNormalCone_comparison this identifies the actual zero fibre with
Spec_S Sym(I/I^2), not merely an unspecified bundle of rank d.
Source: sk-thm-dnc, Local construction (blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 2 identifies the graded algebra by its degree-one generators. Relative Spec
is contravariant and preserves its structural map, giving the projection identity. Both
augmentations fix degree zero and kill positive degrees, so the symmetric-algebra universal
property identifies them. Full faithfulness of relative Spec gives the section identity.
The published purityNormalCone_comparison identifies the Rees quotient with this cone. -/
theorem coneBundleIso_spec {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    (s : S ⟶ V) [IsClosedImmersion s] [Geometry d g s] (hs : s ≫ g = 𝟙 S) :
    (coneBundleIso d g s).hom ≫
        VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1) =
      PurityNormalBundle.projection s ∧
    PurityNormalBundle.zeroSection s ≫ (coneBundleIso d g s).hom =
      VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1) := by
  let E := VectorBundleZeroSection.antiEquivalence S
  let f : VectorBundleZeroSection.algebraObject S d (ConormalGradedAlgebra.piece s 1) ≅
      PurityNormalBundle.algebraObject s := ObjectProperty.isoMk _
    (asIso (ConormalGradedAlgebra.symmetricComparison s))
  let fOver := (ObjectProperty.ι (fun Y : Over S ↦ IsAffineHom Y.hom)).mapIso
    ((E.inverse.mapIso f).unop)
  refine ⟨Over.w fOver.hom, ?_⟩
  have hpb := Scheme.Hom.isPullback_deformationSpaceOneFibre g s
  have : SmoothOfRelativeDimension d g :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      hpb inferInstance
  have : IsSeparated g := MorphismProperty.of_isPullback (P := @IsSeparated) hpb
    inferInstance
  have : QuasiCompact g := MorphismProperty.of_isPullback (P := @QuasiCompact) hpb
    inferInstance
  have : Smooth g := SmoothOfRelativeDimension.smooth d g
  have hgeo := (SectionReesNoetherianGeometry.geometry d g s hs).choose_spec
  have hz := hgeo.choose_spec.2.2.1
  have he := hgeo.choose_spec.1
  rw [he] at hz
  change s.normalConeZeroSection ≫
    (FiniteSmoothPurity.reesConeComparison s).hom ≫ (coneBundleIso d g s).hom = _ at hz
  rw [← Category.assoc, (FiniteSmoothPurity.reesConeComparison_spec s).2.1] at hz
  exact hz

/-- The locally constant free rank-one property written in the existing sheaf category.
Source: sk-thm-dnc, opening paragraph
(blueprint: lem-trf-finite-ring-section-deformation). -/
def IsShiftedLine (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) (d : ℕ)
    (K : DerivedCategoryModule A T) : Prop :=
  ∃ L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
    Nonempty (K⟦-(2 * (d : ℤ))⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
    ∃ cover : Scheme.Cover.{u} Scheme.etalePrecoverage T,
      ∀ i : cover.I₀, Nonempty (L.over (cover.etalePrecoverageToEtale i) ≅
        (constantSheaf (T.smallEtaleTopology.over (cover.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))

/-- The shifted section and deformation complexes are lines, with the actual
counit-defined fibre comparisons invertible.
Source: sk-thm-dnc, opening paragraph (blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 7 applies smooth tensor duality to g and its Rees deformation, whose geometry
is supplied above, using NA=0 and N invertible. Exact inverse image preserves the shift
and the local free rank-one trivializations. Step 8 applies exceptional smooth base change
to the actual squares at one and zero. Thus the specified atOne and atZero, rather than
arbitrary fibre isomorphisms, are invertible. This holds for mixed-prime and zero rings. -/
theorem lines_and_fibres (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) [Geometry d g s] :
    IsShiftedLine A S d (sectionInvariant A g s) ∧
    IsShiftedLine A (AffineSpace (ULift.{u} (Fin 1)) S) d (family A g s) ∧
    IsIso (atOne A g s hs) ∧ IsIso (atZero A g s) := by
  have : HasInvertibleExponent A S := ⟨N, hN, hA, hS⟩
  have : HasInvertibleExponent A V := HasInvertibleExponent.of_hom g
  have : HasInvertibleExponent A s.ker.deformationSpace :=
    HasInvertibleExponent.of_hom (s.ker.deformationSpaceProj ≫ g)
  have : HasCompactification
      (SectionLocalDualizingComparisons.normalProjection d g s hs) :=
    (vectorBundlePurityCompactification S d
      (ConormalGradedAlgebra.piece s 1)).hasCompactification
  have h := SectionLocalDualizingComparisons.section_local_dualizing_comparisons
    A N hN hA hS d g s hs
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · exact NoetherianSectionSpecialization.isIso_sectionMap A
      (Scheme.Hom.deformationSpaceProj g s) d g
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
      (Scheme.Hom.deformationSpaceOneFibre g s)
      (Scheme.Hom.isPullback_deformationSpaceOneFibre g s)
      s.deformationSpaceSection s (Scheme.Hom.comp_deformationSpaceOneFibre hs)
  · exact NoetherianSectionSpecialization.isIso_sectionMap A (Scheme.Hom.deformationSpaceProj g s) d
      (Scheme.Hom.normalConeProj g s) (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
      s.ker.normalConeToDeformationSpace
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
      s.deformationSpaceSection s.normalConeZeroSection
      Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace

/-- The uniquely normalized comparison for every finite commutative coefficient ring.
Source: sk-thm-dnc, Local construction and Gluing
(blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 9 constructs local comparisons using centred etale coordinates, exceptional
locality, and the affine-space adjunction. Correct by the inverse value at one. Step 10
shifts by -2d; full faithfulness of degree-zero complexes makes their ratios sheaf maps.
The constant-module Hom lemma identifies automorphisms of a free rank-one A-module with
units of A, independently of a basis because A is commutative. A geometric affine line
is connected, so a ratio equal to one at t=1 equals one throughout that fibre. Exact
conservative geometric stalks give equality globally. Step 11 glues maps and inverses;
the same argument proves uniqueness, including the empty base and the zero ring. -/
theorem existsUnique_normalized (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) [Geometry d g s] :
    ∃! κ : family A g s ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A g s), Normalized A g s hs κ := by
  classical
  have hlines := lines_and_fibres N hN A hA hS d g s hs
  have : IsIso (atOne A g s hs) := hlines.2.2.1
  have : HasCompactification
      (SectionLocalDualizingComparisons.normalProjection d g s hs) :=
    (vectorBundlePurityCompactification S d
      (ConormalGradedAlgebra.piece s 1)).hasCompactification
  obtain ⟨cover, local_exists⟩ :=
    NoetherianSectionSpecialization.local_comparisons_exist A N hN hA hS d g s hs
  choose localIso hn using fun i : cover.I₀ ↦
    NoetherianSectionSpecialization.normalize_chart A (cover.f i)
      (sectionInvariant A g s) (family A g s) (asIso (atOne A g s hs))
      (local_exists i).some
  obtain ⟨_, _, κ, hκ, _, huniq, _⟩ := AffineLineNormalizedDescent.normalized_descent
    A S (2 * (d : ℤ)) (sectionInvariant A g s) (family A g s)
    (NoetherianSectionSpecialization.line_shape A d S _ hlines.1)
    (NoetherianSectionSpecialization.line_shape A d _ _ hlines.2.1)
    (asIso (atOne A g s hs)) cover localIso hn
  exact ⟨κ, hκ, huniq⟩

/-- The inverse zero restriction is delta, using the two prescribed fibre identifications.
Source: sk-thm-dnc, final formula (blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 11 restricts kappa at zero, inverts it, and composes with the canonical
atZero mate. The inverse-image section compositor identifies i0*a* with the identity.
The two fibre maps are invertible by lines_and_fibres, as is every factor of kappa.
Thus the concrete specialization formula is an isomorphism with the stated direction. -/
theorem isIso_specialization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) [Geometry d g s]
    (κ : family A g s ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A g s)) (hκ : Normalized A g s hs κ) :
    IsIso (specialization A g s κ) := by
  have _hκ := hκ
  have : IsIso (atZero A g s) := (lines_and_fibres N hN A hA hS d g s hs).2.2.2
  unfold specialization
  infer_instance

/-- Arbitrary Noetherian base change supplies all the geometric instances needed
below; no compactifiability or regularity condition is imposed on the change of base.
Source: sk-thm-dnc, arbitrary base change
(blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 5 applies the centred etale chart over R' to B'=B tensor_R R'. The regular
sequence and Rees formulas remain the same even when R' is not flat over R. Smoothness,
separatedness and finite type are preserved by base change. The base-changed section is
closed. The geometry argument over Noetherian S' gives precisely the asserted Geometry,
including compactifications by Nagata. This includes identity and arbitrary nonflat maps. -/
theorem baseChange_geometry_exists {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) {S' : Scheme.{u}} [IsNoetherian S'] (b : S' ⟶ S) :
    ∃ hc : IsClosedImmersion (Scheme.Hom.baseChangeSection g s hs b),
      @Geometry (pullback g b) S' d (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b) hc := by
  have hc : IsClosedImmersion (Scheme.Hom.baseChangeSection g s hs b) := by
    exact MorphismProperty.of_isPullback
      (Scheme.Hom.isPullback_baseChangeSection g s hs b).flip inferInstance
  have : HasCompactification (pullback.snd g b) := by infer_instance
  exact ⟨hc, geometry d (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b)
    (Scheme.Hom.baseChangeSection_snd g s hs b)⟩

/-- Arbitrary base change preserves the Rees deformation, its sections and its normal
cone. This establishes the auxiliary class instances used in the naturality interface;
only compactifiability is assumed for the three base-changed maps.
Source: sk-thm-dnc, final base-change paragraph
(blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 4 writes B'=B tensor_R R' and P'=R'[x]. The base-changed etale chart
is flat over P', so the same monomial computation gives the canonical Rees map
B[t,I/t] tensor_R R'=B'[t,I'/t], even for nonflat R'. It commutes with t, both
augmentations, and the associated-graded quotient. Thus the specified Rees map
is Cartesian, and its zero-fibre lift is the Cartesian normal-cone map. Closedness
of the base-changed section follows by base change of the original closed immersion.
The normal bundle is affine of finite rank, so its projection is quasi-compact.
These arguments cover the empty base and zero rank. -/
theorem baseChange_geometry
    {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [Geometry d g s]
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
  obtain ⟨hc, G⟩ := baseChange_geometry_exists d g s hs b
  have := hc
  have := G
  have sq : IsPullback (deformationMap g s hs b)
      (Scheme.Hom.deformationSpaceProj (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b))
      (Scheme.Hom.deformationSpaceProj g s) (AffineSpace.map (ULift.{u} (Fin 1)) b) := by
    apply Scheme.IdealSheafData.isPullback_deformationSpaceMap_proj
    · intro x
      obtain ⟨U', U, hU, hx, _, H⟩ :=
        Scheme.Hom.exists_isPushout_extendedReesAlgebraMap_baseChange g s hs b d x
      exact ⟨U', U, hU, hx, H⟩
    · exact IsPullback.of_hasPullback g b
  refine ⟨hc, inferInstance, inferInstance, sq, ?_, ?_⟩
  · have hp := (Scheme.Hom.isPullback_normalConeToDeformationSpace
      (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b)).paste_horiz sq
    rw [AffineSpace.zeroSection_comp_map] at hp
    exact hp.of_right' (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
  · apply (Scheme.Hom.isPullback_normalConeToDeformationSpace g s).hom_ext
    · simp only [normalMap, Category.assoc, IsPullback.lift_fst]
      simp only [← Category.assoc,
        Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace]
      simp only [Category.assoc]
      unfold deformationMap
      rw [Scheme.Hom.deformationSpaceSection_comp_deformationSpaceMap_baseChangeSection,
        ← Category.assoc, AffineSpace.zeroSection_comp_map, Category.assoc]
    · simp only [normalMap, Category.assoc, IsPullback.lift_snd]
      rw [← Category.assoc, Scheme.Hom.normalConeZeroSection_normalConeProj
        (Scheme.Hom.baseChangeSection_snd g s hs b), Category.id_comp,
        Scheme.Hom.normalConeZeroSection_normalConeProj hs, Category.comp_id]

private theorem sectionExceptionalComparison_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B B' : Scheme.{u}} {d : ℕ} {P : ExceptionalSectionPair B d}
    {P' : ExceptionalSectionPair B' d} {v : B' ⟶ B}
    (e : ExceptionalSectionChange P P' v) :
    sectionExceptionalComparison A e = sectionMap A P.map P'.map v e.upper e.square
      P.sect P'.sect e.section_comm := by
  simp only [sectionExceptionalComparison, sectionCoherencePullbackIso, sectionMap,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]

private theorem familyPoint_false (S : Scheme.{u}) :
    exceptionalFamilyPoint S false = AffineSpace.zeroSection (ULift.{u} (Fin 1)) S := rfl

private theorem familyPoint_true (S : Scheme.{u}) :
    exceptionalFamilyPoint S true = AffineSpace.oneSection (ULift.{u} (Fin 1)) S := rfl

private def sectionFamily {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) [Geometry d g s] : ExceptionalSectionFamily S d := by
  have hpb := Scheme.Hom.isPullback_normalConeToDeformationSpace g s
  have : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    exact MorphismProperty.of_isPullback hpb inferInstance
  have : IsSeparated (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hpb inferInstance
  have : IsClosedImmersion (s.deformationSpaceSection ≫
      Scheme.Hom.deformationSpaceProj g s) :=
    (Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs) ▸ inferInstance
  have : IsClosedImmersion s.deformationSpaceSection :=
    IsClosedImmersion.of_comp _ (Scheme.Hom.deformationSpaceProj g s)
  let ambient : ExceptionalSectionPair (AffineSpace (ULift.{u} (Fin 1)) S) d := {
    total := s.ker.deformationSpace
    map := Scheme.Hom.deformationSpaceProj g s
    sect := s.deformationSpaceSection
    section_map := Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs }
  let one : ExceptionalSectionPair S d := {
    total := V
    map := g
    sect := s
    section_map := hs }
  let zero : ExceptionalSectionPair S d := {
    total := s.ker.normalCone
    map := Scheme.Hom.normalConeProj g s
    sect := s.normalConeZeroSection
    section_map := Scheme.Hom.normalConeZeroSection_normalConeProj hs }
  refine { ambient := ambient, fibre := fun t ↦ match t with
             | false => zero
             | true => one
           restriction := ?_ }
  intro t
  cases t
  · exact {
      upper := s.ker.normalConeToDeformationSpace
      square := hpb
      section_comm := Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace }
  · exact {
      upper := Scheme.Hom.deformationSpaceOneFibre g s
      square := Scheme.Hom.isPullback_deformationSpaceOneFibre g s
      section_comm := Scheme.Hom.comp_deformationSpaceOneFibre hs }

private theorem sectionFamily_normalized_iff
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) [Geometry d g s]
    (κ : family A g s ≅ (ordinaryFinitePullback A
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj (sectionInvariant A g s)) :
    (sectionFamily d g s hs).IsNormalized A κ ↔ Normalized A g s hs κ := by
  simp only [ExceptionalSectionFamily.IsNormalized, ExceptionalSectionFamily.fibreMap,
    sectionExceptionalComparison_eq, sectionFamily, exceptionalFamilyPoint, Normalized,
    atOne, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem sectionPullback_endpoint
    (A : Type (u + 1)) [CommRing A]
    {B B' X X' : Scheme.{u}} (v : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X')
    (r : X' ⟶ X) (z z' : B' ⟶ X)
    (h₁ : z = v ≫ i) (h₂ : z = i' ≫ r)
    (h₁' : z' = v ≫ i) (h₂' : z' = i' ≫ r) (K : DerivedCategoryModule A X) :
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v i z h₁).symm ≪≫
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i' r z h₂).app K =
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v i z' h₁').symm ≪≫
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i' r z' h₂').app K := by
  subst z
  subst z'
  rfl

private theorem linePullback_coherence (A : Type (u + 1)) [CommRing A]
    {S S' : Scheme.{u}} (b : S' ⟶ S) (C : DerivedCategoryModule A S) :
    linePullback A b C = (sectionCoherencePullbackIso A
      (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S') b
      (AffineSpace.map (ULift.{u} (Fin 1)) b)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
      (AffineSpace.map_over b).symm C).symm := by
  apply Iso.ext
  have h := sectionPullback_endpoint A (AffineSpace.map (ULift.{u} (Fin 1)) b)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S') b _ _ rfl
    (AffineSpace.map_over b) (AffineSpace.map_over b).symm rfl C
  simpa only [linePullback, sectionCoherencePullbackIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
    using congrArg Iso.hom h

/-- Both normalized comparisons commute with arbitrary Noetherian base change under the
canonical exceptional mates. The first equation is b_F followed by kappa', equal to
pullback(kappa) followed by the projection compositor and a'^*b_C. The second is
b_C followed by delta', equal to pullback(delta) followed by b_N. All deformation
and normal maps are fixed by the Rees construction, not freely chosen maps.
Source: sk-thm-dnc, final base-change paragraph
(blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 10 uses composition of unbounded compact-support exchange and mate pasting
for the two decompositions of the fibre/base-change rectangles. This proves
θ' i1'^*b_F = b_C b^*θ and η' i0'^*b_F = b_N b^*η, with the inverse-image
compositors. All b maps are invertible by smooth exceptional base change. Hence
Step 11 forms a'^*b_C composed with pullback(kappa) and b_F^(-1). Its value at one
is θ' by the first identity, so uniqueness of normalized comparisons identifies
it with kappa'. At zero, the second identity and inversion give precisely the
second displayed equality. This includes the identity, etale and nonflat cases. -/
theorem baseChange_compatibility (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [Geometry d g s]
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
    (κ : family A g s ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A g s))
    (hκ : Normalized A g s hs κ)
    (κ' : family A (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b) ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.obj
          (sectionInvariant A (pullback.snd g b)
            (Scheme.Hom.baseChangeSection g s hs b)))
    (hκ' : Normalized A (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b)
      (Scheme.Hom.baseChangeSection_snd g s hs b) κ') :
    IsIso (sourceBaseChange A g s hs b) ∧
    IsIso (familyBaseChange A g s hs b sq) ∧
    IsIso (sectionMap A (Scheme.Hom.normalConeProj g s)
      (Scheme.Hom.normalConeProj (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b))
      b (normalMap g s hs b sq) sqN s.normalConeZeroSection
      (Scheme.Hom.baseChangeSection g s hs b).normalConeZeroSection hz) ∧
    familyBaseChange A g s hs b sq ≫ κ'.hom =
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.map κ.hom ≫
      (linePullback A b (sectionInvariant A g s)).hom ≫
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.map
          (sourceBaseChange A g s hs b) ∧
    sourceBaseChange A g s hs b ≫
      specialization A (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b) κ' =
      (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map
        (specialization A g s κ) ≫
      sectionMap A (Scheme.Hom.normalConeProj g s)
        (Scheme.Hom.normalConeProj (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b))
        b (normalMap g s hs b sq) sqN s.normalConeZeroSection
        (Scheme.Hom.baseChangeSection g s hs b).normalConeZeroSection hz := by
  classical
  have : Geometry d (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b) :=
    (baseChange_geometry_exists d g s hs b).choose_spec
  let P := sectionFamily d g s hs
  let P' := sectionFamily d (pullback.snd g b) (Scheme.Hom.baseChangeSection g s hs b)
    (Scheme.Hom.baseChangeSection_snd g s hs b)
  have hD : (Scheme.Hom.baseChangeSection g s hs b).deformationSpaceSection ≫
      deformationMap g s hs b =
        AffineSpace.map (ULift.{u} (Fin 1)) b ≫ s.deformationSpaceSection :=
    Scheme.Hom.deformationSpaceSection_comp_deformationSpaceMap_baseChangeSection g s hs b
  obtain ⟨r, hr, w, rfl, _, hcomp, _⟩ := SectionReesBaseChange.base_change d g s hs b
  let e : ExceptionalFamilyBaseChange P P' b := {
    ambient := ⟨deformationMap g s hs b, sq, hD⟩
    fibre := fun t ↦ match t with
      | false => ⟨normalMap g s hs b sq, sqN, hz⟩
      | true => ⟨pullback.fst g b, IsPullback.of_hasPullback g b,
          Scheme.Hom.baseChangeSection_fst g s hs b⟩
    point_comm := by
      intro t
      cases t
      · exact (AffineSpace.zeroSection_comp_map b).symm
      · exact (AffineSpace.oneSection_comp_map b).symm
    fibre_comm := by
      intro t
      cases t
      · exact IsPullback.lift_fst _ _ _ _
      · exact hcomp.2.2.1.symm }
  have hinv (x : S) : IsUnit (N : S.presheaf.stalk x) := by
    simpa only [map_natCast] using hS.map (S.presheaf.germ ⊤ x (by trivial)).hom
  have hk : P.IsNormalized A κ ∧ ∀ τ, P.IsNormalized A τ → τ = κ := by
    refine ⟨?_, ?_⟩
    · exact (sectionFamily_normalized_iff A d g s hs κ).2 hκ
    intro τ hτ
    obtain ⟨k, hk, hu⟩ := existsUnique_normalized N hN A hA hS d g s hs
    have ht : Normalized A g s hs τ := by
      exact (sectionFamily_normalized_iff A d g s hs τ).1 hτ
    exact (hu τ ht).trans (hu κ hκ).symm
  have hk' : P'.IsNormalized A κ' ∧ ∀ τ, P'.IsNormalized A τ → τ = κ' := by
    refine ⟨?_, ?_⟩
    · exact (sectionFamily_normalized_iff A d (pullback.snd g b)
        (Scheme.Hom.baseChangeSection g s hs b)
        (Scheme.Hom.baseChangeSection_snd g s hs b) κ').2 hκ'
    intro τ hτ
    obtain ⟨k, hk, hu⟩ := existsUnique_normalized N hN A hA
      (SectionLocalDualizingComparisons.invertibleOnSource N b hS) d (pullback.snd g b)
      (Scheme.Hom.baseChangeSection g s hs b) (Scheme.Hom.baseChangeSection_snd g s hs b)
    apply (hu τ ?_).trans (hu κ' hκ').symm
    exact (sectionFamily_normalized_iff A d (pullback.snd g b)
      (Scheme.Hom.baseChangeSection g s hs b)
      (Scheme.Hom.baseChangeSection_snd g s hs b) τ).1 hτ
  have hi := sectionExceptional_fibre_coherence A N hN hA P P' hinv b e
  have hn := sectionExceptional_normalized_baseChange A N hN hA P P' hinv b e κ κ' hk hk'
  dsimp only [P, P', sectionFamily, e] at hi hn
  have h := And.intro (hi.2 true).2.2.1 (And.intro hi.1
    (And.intro (hi.2 false).2.2.1 hn))
  simp only [ExceptionalSectionFamily.specialization, ExceptionalSectionFamily.fibreMap,
    familyPoint_false, familyPoint_true] at h
  simpa only [linePullback_coherence, Iso.symm_hom, sectionExceptionalComparison_eq,
    P, P', sectionFamily, familyPoint_false, familyPoint_true, Normalized, atOne,
    sourceBaseChange, familyBaseChange,
    specialization, atZero, e, if_neg Bool.false_ne_true, if_pos rfl,
    Category.assoc] using h



attribute [local irreducible] rightDerivedUpperShriek

/-- The normalized etale-locality isomorphism for the chosen Brown right adjoints.
The existence theorem determines it uniquely by its adjoint transpose through compact
support composition, so this is not a choice of a bare isomorphism.
Source: sk-prop-sp-orientation-charts, Step 3
(blueprint: lem-trf-finite-ring-section-deformation). -/
def locality (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X S : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (h : U ⟶ X) [Etale h] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (f : X ⟶ S) [HasCompactification f] [HasCompactification (h ≫ f)] :
    rightDerivedUpperShriek A f ⋙
        (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory ≅
      rightDerivedUpperShriek A (h ≫ f) :=
  (existsUnique_etaleAmbientAdjointLocalityIso A h f
    (HasCompactification.compactification f) (HasCompactification.compactification (h ≫ f))
    (rightDerivedUpperShriek A f)
    (rightDerivedUpperShriek A (h ≫ f))
    (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction A (h ≫ f))).exists.choose

/-- Restrict etale locality to compatible sections. The ordinary inverse image is compared
with its left derived functor by the canonical exactness comparison.
Source: sk-prop-sp-orientation-charts, Step 3
(blueprint: lem-trf-finite-ring-section-deformation). -/
def etaleSectionMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X S : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (h : U ⟶ X) [Etale h] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (f : X ⟶ S) [HasCompactification f] (f' : U ⟶ S) [HasCompactification f']
    (w : h ≫ f = f') (s : S ⟶ X) (s' : S ⟶ U) (hs : s' ≫ h = s) :
    sectionInvariant A f s ⟶ sectionInvariant A f' s' := by
  subst f'
  exact ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' h s hs.symm).app _).hom ≫
    (upperStar (ModuleCat.{u + 1} A) s').leftDerivedFunctor.map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).hom.app _ ≫
        (locality A h f).hom.app (𝟙_ _))

private theorem sectionLocality_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X S : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (h : U ⟶ X) [Etale h] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (f : X ⟶ S) [HasCompactification f] (f' : U ⟶ S) [HasCompactification f']
    (w : h ≫ f = f') (s : S ⟶ X) (s' : S ⟶ U) (hs : s' ≫ h = s) :
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' h s hs.symm).app _).hom ≫
      (ordinaryFinitePullback A s').map
        (sectionStructuralLocalityIso A h f f' w).hom =
      etaleSectionMap A h f f' w s s' hs := by
  subst f'
  let E := existsUnique_etaleAmbientAdjointLocalityIso A h f
    (HasCompactification.compactification f) (HasCompactification.compactification (h ≫ f))
    (rightDerivedUpperShriek A f)
    (rightDerivedUpperShriek A (h ≫ f))
    (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction A (h ≫ f))
  have he : Classical.choose E = E.exists.choose :=
    (E.choose_spec.2 _ E.exists.choose_spec).symm
  simp only [sectionStructuralLocalityIso, Iso.trans_hom, Iso.app_hom,
    etaleSectionMap, locality, Functor.map_comp, he]
  rfl

private theorem sectionLocality_hom_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X S : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (h : U ⟶ X) [Etale h] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (f : X ⟶ S) [HasCompactification f] (f' : U ⟶ S) [HasCompactification f']
    (w : h ≫ f = f') (s : S ⟶ X) (s' : S ⟶ U) (hs : s' ≫ h = s) :
    (SectionLocalDualizingComparisons.sectionLocality A h f f' w s s' hs).hom =
      etaleSectionMap A h f f' w s s' hs := by
  subst f'
  simp only [SectionLocalDualizingComparisons.sectionLocality, etaleSectionMap,
    locality, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]

private theorem sectionExceptionalLocality_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B : Scheme.{u}} [IsNoetherian B] {d : ℕ} {P P' : ExceptionalSectionPair B d}
    (e : ExceptionalSectionEtaleMap P P') :
    (sectionExceptionalLocalityIso A e).hom =
      etaleSectionMap A e.upper P.map P'.map e.map_comm
        P.sect P'.sect e.section_comm := by
  dsimp only [sectionExceptionalLocalityIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom]
  exact sectionLocality_eq A e.upper P.map P'.map e.map_comm
    P.sect P'.sect e.section_comm

/-- Pullback of the centre ideal along an etale map of pairs. This bound is the
well-definedness proof for the actual map of extended Rees algebras.
Source: sk-thm-dnc, etale maps of pairs
(blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 6 uses the Cartesian centre square to identify I'=I O_U. The structure
maps on each affine open therefore send every section of I into I'. This proves the
bound, without choosing a map of deformation spaces. -/
theorem etalePair_ideal {U X S : Scheme.{u}} (h : U ⟶ X) (s : S ⟶ X)
    (s' : S ⟶ U) [IsClosedImmersion s] [IsClosedImmersion s']
    (sq : IsPullback s' (𝟙 S) h s) :
    ∀ ⦃U' : U.AffineZariskiSite⦄ ⦃W : X.AffineZariskiSite⦄ (hW : U'.1 ≤ h ⁻¹ᵁ W.1),
      (s.ker.siteIdeal W).map (h.appLE W.1 U'.1 hW).hom ≤ s'.ker.siteIdeal U' := by
  intro U' W hW
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have hx' := s.ideal_ker_le ⟨W.1, W.2⟩ hx
  rw [RingHom.mem_ker] at hx'
  rw [Ideal.mem_comap, Scheme.IdealSheafData.siteIdeal, Scheme.Hom.ker_apply,
    RingHom.mem_ker, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_congr_hom sq.w,
    Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  · rw [hx', map_zero]
  · rw [← sq.w, Scheme.Hom.comp_preimage]
    exact s'.preimage_mono hW

/-- The canonical Rees map of an etale map of pairs; its ring map fixes t and sends
b/t to h-sharp(b)/t. Source: sk-thm-dnc, etale maps of pairs
(blueprint: lem-trf-finite-ring-section-deformation). -/
def etaleDeformationMap {U X S : Scheme.{u}} (h : U ⟶ X) (s : S ⟶ X)
    (s' : S ⟶ U) [IsClosedImmersion s] [IsClosedImmersion s']
    (sq : IsPullback s' (𝟙 S) h s) : s'.ker.deformationSpace ⟶ s.ker.deformationSpace :=
  Scheme.IdealSheafData.deformationSpaceMap h s.ker s'.ker (etalePair_ideal h s s' sq)

/-- Geometry and section compatibility of the fixed Rees map for etale neighbourhoods.
The first square states that this map is a base change of h, not an arbitrary etale map.
Source: sk-thm-dnc, etale maps of pairs; orientation-charts Steps 1--2
(blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 6 applies flat tensor exactness to powers I^m and their successive quotients.
Degree by degree this identifies the extended Rees algebra with its flat base change.
The affine identifications agree on restrictions and give the Cartesian square. Etale
and separated properties follow by base change; finite type and quasi-compactness hold
over the Noetherian schemes in question. The maps fix t and both augmentations, proving
the structural and section identities. This applies also to the standard coordinates
x_j=t*u_j and to d=0. -/
theorem etaleDeformationMap_spec {U X S : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (h : U ⟶ X) [Etale h] [IsSeparated h] (g : X ⟶ S)
    (s : S ⟶ X) (s' : S ⟶ U) [IsClosedImmersion s] [IsClosedImmersion s']
    (sq : IsPullback s' (𝟙 S) h s) :
    IsPullback (etaleDeformationMap h s s' sq) s'.ker.deformationSpaceProj
      s.ker.deformationSpaceProj h ∧
    Etale (etaleDeformationMap h s s' sq) ∧
    IsSeparated (etaleDeformationMap h s s' sq) ∧
    LocallyOfFiniteType (etaleDeformationMap h s s' sq) ∧
    QuasiCompact (etaleDeformationMap h s s' sq) ∧
    etaleDeformationMap h s s' sq ≫ Scheme.Hom.deformationSpaceProj g s =
      Scheme.Hom.deformationSpaceProj (h ≫ g) s' ∧
    s'.deformationSpaceSection ≫ etaleDeformationMap h s s' sq =
      s.deformationSpaceSection := by
  have hk : s'.ker = s.ker.comap h := by
    rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hp : IsPullback (etaleDeformationMap h s s' sq) s'.ker.deformationSpaceProj
      s.ker.deformationSpaceProj h := by
    apply Scheme.AffineZariskiSite.PullbackData.isPullback_comparison
    intro x
    obtain ⟨W, hW, hxW, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X.isBasis_affineOpens (U := ⊤) (show h x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨W', hW', hxW', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      U.isBasis_affineOpens (U := h ⁻¹ᵁ W) hxW
    refine ⟨⟨W', hW'⟩, ⟨W, hW⟩, hle, hxW', ?_⟩
    have he : s'.ker.siteIdeal ⟨W', hW'⟩ =
        (s.ker.siteIdeal ⟨W, hW⟩).map (h.appLE W W' hle).hom := by
      rw [Scheme.IdealSheafData.siteIdeal, hk,
        Scheme.IdealSheafData.ideal_comap_appLE s.ker h ⟨W, hW⟩ ⟨W', hW'⟩ hle]
    change IsPushout _ _ _ (CommRingCat.ofHom
      ((s.ker.siteIdeal ⟨W, hW⟩).extendedReesAlgebraMap (h.appLE W W' hle).hom
        (s'.ker.siteIdeal ⟨W', hW'⟩) _))
    generalize_proofs hbound
    dsimp only [Scheme.IdealSheafData.toReesPresheaf]
    generalize s'.ker.siteIdeal ⟨W', hW'⟩ = J at he hbound ⊢
    subst J
    exact Ideal.isPushout_extendedReesAlgebraMap_of_flat _ (h.flat_appLE hW hW' hle) _
  have het : Etale (etaleDeformationMap h s s' sq) :=
    MorphismProperty.of_isPullback hp.flip inferInstance
  have hsep : IsSeparated (etaleDeformationMap h s s' sq) :=
    MorphismProperty.of_isPullback hp.flip inferInstance
  refine ⟨hp, het, hsep, inferInstance, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback hp.flip inferInstance
  · simpa only [etaleDeformationMap, Scheme.Hom.deformationSpaceProj,
      AffineSpace.map_id, Category.comp_id, Category.assoc] using
      Scheme.IdealSheafData.deformationSpaceMap_proj h s.ker s'.ker
        (etalePair_ideal h s s' sq) g (h ≫ g) (𝟙 S) (by simp)
  · open Scheme.AffineZariskiSite Scheme.IdealSheafData in
    have hq : s'.affineSpaceToQuotientPolynomialSpec ≫
        (Scheme.IdealSheafData.quotientPolynomialPullbackData h s.ker s'.ker
          (etalePair_ideal h s s' sq)).comparison _ _ =
        s.affineSpaceToQuotientPolynomialSpec := by
      rw [← cancel_mono (relativeGluingMap X.coequifibered_toPolynomialPresheaf
        s.ker.coequifibered_toQuotientPolynomialAlgebra s.ker.polynomialToQuotientPolynomial),
        Category.assoc, PullbackData.comparison_comp_relativeGluingMap
          (H := X.coequifibered_toPolynomialPresheaf)
          (H' := U.coequifibered_toPolynomialPresheaf) _ _ _ _ _ _
          (polynomialToQuotientPolynomial_comp_quotientPolynomialPullbackData_map _ _ _ _),
        Scheme.Hom.affineSpaceToQuotientPolynomialSpec_toPolynomialSpec_assoc,
        Scheme.Hom.affineSpaceToQuotientPolynomialSpec_toPolynomialSpec,
        ← Scheme.polynomialSpecMap,
        (IsIso.eq_comp_inv _).mpr (Scheme.polynomialSpecMap_polynomialSpecToAffineSpace h)]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc, ← AffineSpace.map_comp_assoc]
      rw [sq.w, Category.id_comp]
    rw [Scheme.Hom.deformationSpaceSection, Scheme.Hom.deformationSpaceSection,
      Category.assoc, etaleDeformationMap, Scheme.IdealSheafData.deformationSpaceMap,
      ← Scheme.AffineZariskiSite.PullbackData.comparison_comp_relativeGluingMap
        (HG := s.ker.coequifibered_toQuotientPolynomialAlgebra) _ _ _ _ _ _ _
        (Scheme.IdealSheafData.reesToQuotientPolynomial_comp_quotientPolynomialPullbackData_map
          _ _ _ _), ← Category.assoc, hq]

/-- The fixed Rees map is compatible with the zero fibre. This is the lift condition
used to define the induced normal-bundle map, not an independent choice of a linear map.
Source: sk-thm-dnc, etale pairs (blueprint: lem-trf-finite-ring-section-deformation).
Proof: the zero-fibre inclusions followed by the structural maps are the zero sections
of the affine line composed with the normal projections. Substitute the structural
identity of etaleDeformationMap_spec. Since the base is unchanged, associativity gives
the asserted equality and hence the universal-property lift. -/
theorem etaleNormalMap_condition {U X S : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (h : U ⟶ X) [Etale h] [IsSeparated h] (g : X ⟶ S)
    (s : S ⟶ X) (s' : S ⟶ U) [IsClosedImmersion s] [IsClosedImmersion s']
    (sq : IsPullback s' (𝟙 S) h s) :
    (s'.ker.normalConeToDeformationSpace ≫ etaleDeformationMap h s s' sq) ≫
        Scheme.Hom.deformationSpaceProj g s =
      Scheme.Hom.normalConeProj (h ≫ g) s' ≫
        AffineSpace.zeroSection (ULift.{u} (Fin 1)) S := by
  rw [Category.assoc, (etaleDeformationMap_spec h g s s' sq).2.2.2.2.2.1]
  exact (Scheme.Hom.isPullback_normalConeToDeformationSpace (h ≫ g) s').w

/-- The induced map on normal bundles, defined by the zero-fibre universal property.
On associated graded algebras it sends [b] to [h-sharp(b)] in degree one; this is exactly
the linear map induced on conormals. Source: sk-thm-dnc, etale pairs
(blueprint: lem-trf-finite-ring-section-deformation). -/
def etaleNormalMap {U X S : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (h : U ⟶ X) [Etale h] [IsSeparated h] (g : X ⟶ S)
    (s : S ⟶ X) (s' : S ⟶ U) [IsClosedImmersion s] [IsClosedImmersion s']
    (sq : IsPullback s' (𝟙 S) h s) : s'.ker.normalCone ⟶ s.ker.normalCone :=
  (Scheme.Hom.isPullback_normalConeToDeformationSpace g s).lift
    (s'.ker.normalConeToDeformationSpace ≫ etaleDeformationMap h s s' sq)
    (Scheme.Hom.normalConeProj (h ≫ g) s') (etaleNormalMap_condition h g s s' sq)

/-- The zero-fibre map is the induced linear isomorphism and carries zero to zero.
Source: sk-thm-dnc, etale maps of pairs; orientation-charts Step 2
(blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 6 identifies I'^m/I'^(m+1) with the pullback of I^m/I^(m+1).
Its degree-one map is [b] ↦ [h-sharp(b)] and is the conormal pullback isomorphism.
Under Sym(I/I^2)=gr_I this is precisely its symmetric algebra map, so relative Spec
gives the asserted isomorphism. The degree-zero augmentations commute, giving zero
section compatibility. The zero-fibre universal property identifies this map with
the specified etaleNormalMap. -/
theorem etaleNormalMap_spec {U X S : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (h : U ⟶ X) [Etale h] [IsSeparated h] (g : X ⟶ S)
    (s : S ⟶ X) (s' : S ⟶ U) [IsClosedImmersion s] [IsClosedImmersion s']
    (sq : IsPullback s' (𝟙 S) h s) :
    IsIso (etaleNormalMap h g s s' sq) ∧
    etaleNormalMap h g s s' sq ≫ Scheme.Hom.normalConeProj g s =
      Scheme.Hom.normalConeProj (h ≫ g) s' ∧
    s'.normalConeZeroSection ≫ etaleNormalMap h g s s' sq = s.normalConeZeroSection := by
  have : IsClosedImmersion s.ker.normalConeToDeformationSpace :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s).flip inferInstance
  open Scheme.AffineZariskiSite in
  have hn : IsPullback (etaleNormalMap h g s s' sq)
      (relativeGluingData s'.ker.coequifibered_toNormalConePresheaf).toBase
      (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase h := by
    have he : etaleNormalMap h g s s' sq =
        (SectionReesBaseChange.zeroPairData h s.ker s'.ker
          (etalePair_ideal h s s' sq)).comparison _ _ := by
      apply (cancel_mono s.ker.normalConeToDeformationSpace).mp
      exact (IsPullback.lift_fst _ _ _ _).trans
        (SectionReesBaseChange.zeroPairData_toRees h s.ker s'.ker
          (etalePair_ideal h s s' sq)).symm
    rw [he]
    apply SectionReesBaseChange.zeroPairData_isPullback
    have hk : s'.ker = s.ker.comap h := by
      rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
        Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    intro x
    obtain ⟨W, hW, hxW, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X.isBasis_affineOpens (U := ⊤) (show h x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨W', hW', hxW', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      U.isBasis_affineOpens (U := h ⁻¹ᵁ W) hxW
    refine ⟨⟨W', hW'⟩, ⟨W, hW⟩, hle, hxW', ?_⟩
    have he : s'.ker.siteIdeal ⟨W', hW'⟩ =
        (s.ker.siteIdeal ⟨W, hW⟩).map (h.appLE W W' hle).hom := by
      rw [Scheme.IdealSheafData.siteIdeal, hk,
        Scheme.IdealSheafData.ideal_comap_appLE s.ker h ⟨W, hW⟩ ⟨W', hW'⟩ hle]
    change IsPushout _ _ _ (CommRingCat.ofHom
      ((s.ker.siteIdeal ⟨W, hW⟩).extendedReesAlgebraMap (h.appLE W W' hle).hom
        (s'.ker.siteIdeal ⟨W', hW'⟩) _))
    generalize_proofs hbound
    dsimp only [Scheme.IdealSheafData.toReesPresheaf]
    generalize s'.ker.siteIdeal ⟨W', hW'⟩ = J at he hbound ⊢
    subst J
    exact Ideal.isPushout_extendedReesAlgebraMap_of_flat _ (h.flat_appLE hW hW' hle) _
  have hb : Scheme.Hom.purityNormalProjection s ≫ s =
      (Scheme.AffineZariskiSite.relativeGluingData
        s.ker.coequifibered_toNormalConePresheaf).toBase :=
    IsClosedImmersion.lift_fac _ _ _
  have hb' : Scheme.Hom.purityNormalProjection s' ≫ s' =
      (Scheme.AffineZariskiSite.relativeGluingData
        s'.ker.coequifibered_toNormalConePresheaf).toBase :=
    IsClosedImmersion.lift_fac _ _ _
  have hp : etaleNormalMap h g s s' sq ≫ Scheme.Hom.purityNormalProjection s =
      Scheme.Hom.purityNormalProjection s' ≫ 𝟙 S := by
    apply (cancel_mono s).mp
    rw [Category.assoc, hb, hn.w, ← hb', Category.assoc, sq.w, Category.id_comp]
    simp only [Category.comp_id]
  have hi : IsIso (etaleNormalMap h g s s' sq) := by
    rw [← hb, ← hb'] at hn
    exact (IsPullback.of_bot hn hp sq.flip).isIso_fst_of_isIso
  refine ⟨hi, IsPullback.lift_snd _ _ _ _, ?_⟩
  apply (cancel_mono s.ker.normalConeToDeformationSpace).mp
  rw [Category.assoc, etaleNormalMap, IsPullback.lift_fst, ← Category.assoc,
    Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace, Category.assoc,
    (etaleDeformationMap_spec h g s s' sq).2.2.2.2.2.2,
    Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace]


/-- Locality on the deformation section through the fixed etale Rees map.
Source: sk-thm-dnc, etale compatibility
(blueprint: lem-trf-finite-ring-section-deformation). -/
def etaleFamilyMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X S : Scheme.{u}} [IsNoetherian S] (d : ℕ)
    (h : U ⟶ X) [Etale h] [IsSeparated h] (g : X ⟶ S)
    (s : S ⟶ X) (s' : S ⟶ U) [IsClosedImmersion s] [IsClosedImmersion s']
    [Geometry d g s] [Geometry d (h ≫ g) s'] (sq : IsPullback s' (𝟙 S) h s) :
    family A g s ⟶ family A (h ≫ g) s' := by
  let q := etaleDeformationMap_spec h g s s' sq
  letI := q.2.1
  letI := q.2.2.1
  letI := q.2.2.2.1
  letI := q.2.2.2.2.1
  exact etaleSectionMap A (etaleDeformationMap h s s' sq)
    (Scheme.Hom.deformationSpaceProj g s) (Scheme.Hom.deformationSpaceProj (h ≫ g) s')
    q.2.2.2.2.2.1 s.deformationSpaceSection s'.deformationSpaceSection q.2.2.2.2.2.2

/-- Locality on the normal zero section through the induced linear isomorphism.
Source: sk-thm-dnc, etale compatibility
(blueprint: lem-trf-finite-ring-section-deformation). -/
def etaleNormalSectionMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X S : Scheme.{u}} [IsNoetherian S] (d : ℕ)
    (h : U ⟶ X) [Etale h] [IsSeparated h] (g : X ⟶ S)
    (s : S ⟶ X) (s' : S ⟶ U) [IsClosedImmersion s] [IsClosedImmersion s']
    [Geometry d g s] [Geometry d (h ≫ g) s'] (sq : IsPullback s' (𝟙 S) h s) :
    sectionInvariant A (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection ⟶
      sectionInvariant A (Scheme.Hom.normalConeProj (h ≫ g) s') s'.normalConeZeroSection := by
  let q := etaleNormalMap_spec h g s s' sq
  letI := q.1
  exact etaleSectionMap A (etaleNormalMap h g s s' sq)
    (Scheme.Hom.normalConeProj g s) (Scheme.Hom.normalConeProj (h ≫ g) s')
    q.2.1 s.normalConeZeroSection s'.normalConeZeroSection q.2.2

/-- Both comparisons commute with separated etale changes of neighbourhood having the
same Cartesian centre. The normal comparison is the map induced by the fixed Rees map.
Source: sk-thm-dnc, etale maps of pairs; orientation-charts Steps 1--3
(blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 14 compares the composite sum-extension/compact-support adjunction with
the adjunction of the structural composite. The normalized compact-support composition
and base-change comparisons commute by mate pasting. Thus the two fibre maps commute
with locality at one and zero. The transported kappa is normalized at one, hence equals
kappa' by uniqueness. Restricting at zero and inverting proves the delta equation.
The normal map is the conormal-induced linear isomorphism by etaleNormalMap_spec. -/
theorem etale_compatibility (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {U X S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (h : U ⟶ X) [Etale h] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (g : X ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] [HasCompactification (h ≫ g)]
    (s : S ⟶ X) (s' : S ⟶ U) [IsClosedImmersion s] [IsClosedImmersion s']
    (hs : s ≫ g = 𝟙 S) (hs' : s' ≫ (h ≫ g) = 𝟙 S)
    [Geometry d g s] [Geometry d (h ≫ g) s']
    (sq : IsPullback s' (𝟙 S) h s) (hc : s' ≫ h = s)
    (κ : family A g s ≅ (ordinaryFinitePullback A
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj (sectionInvariant A g s))
    (hκ : Normalized A g s hs κ)
    (κ' : family A (h ≫ g) s' ≅ (ordinaryFinitePullback A
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj (sectionInvariant A (h ≫ g) s'))
    (hκ' : Normalized A (h ≫ g) s' hs' κ') :
    etaleFamilyMap A d h g s s' sq ≫ κ'.hom = κ.hom ≫
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).map
        (etaleSectionMap A h g (h ≫ g) rfl s s' hc) ∧
    etaleSectionMap A h g (h ≫ g) rfl s s' hc ≫ specialization A (h ≫ g) s' κ' =
      specialization A g s κ ≫ etaleNormalSectionMap A d h g s s' sq := by
  classical
  have : Smooth g := SmoothOfRelativeDimension.smooth d g
  have : SmoothOfRelativeDimension d (h ≫ g) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    exact MorphismProperty.of_isPullback
      (Scheme.Hom.isPullback_deformationSpaceOneFibre (h ≫ g) s') inferInstance
  let P := sectionFamily d g s hs
  let P' := sectionFamily d (h ≫ g) s' hs'
  have hD := etaleDeformationMap_spec h g s s' sq
  have hNmap := etaleNormalMap_spec h g s s' sq
  have := hD.2.1
  have := hD.2.2.1
  have := hD.2.2.2.1
  have := hD.2.2.2.2.1
  have := hNmap.1
  have hcentres : IsPullback
      (𝟙 (AffineSpace (ULift.{u} (Fin 1)) S)) s'.deformationSpaceSection
      s.deformationSpaceSection (etaleDeformationMap h s s' sq) := by
    have ht : IsPullback (𝟙 (AffineSpace (ULift.{u} (Fin 1)) S))
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) (𝟙 S) :=
      IsPullback.of_horiz_isIso (by simp)
    have ho := ht.paste_vert sq.flip
    rw [← Scheme.Hom.deformationSpaceSection_toBase,
      ← Scheme.Hom.deformationSpaceSection_toBase] at ho
    exact ho.of_bot (by simpa using hD.2.2.2.2.2.2.symm) hD.1
  have hcomp := (SectionReesBaseChange.etale d g s hs h s' hs'
    (by simpa using hc) sq).2.2.1
  let e : ExceptionalFamilyEtaleMap P P' := {
    ambient := {
      upper := etaleDeformationMap h s s' sq
      map_comm := hD.2.2.2.2.2.1
      section_comm := hD.2.2.2.2.2.2
      centres := hcentres }
    fibre := fun t ↦ match t with
      | false => {
          upper := etaleNormalMap h g s s' sq
          map_comm := hNmap.2.1
          section_comm := hNmap.2.2
          centres := IsPullback.of_horiz_isIso ⟨by
            simpa only [P, P', sectionFamily, Bool.false_eq_true, if_false,
              Category.id_comp] using hNmap.2.2.symm⟩ }
      | true => {
          upper := h
          map_comm := rfl
          section_comm := hc
          centres := sq.flip }
    fibre_comm := by
      intro t
      cases t
      · exact (Scheme.Hom.isPullback_normalConeToDeformationSpace g s).lift_fst _ _ _
      · exact hcomp.2.2.1.symm }
  have hinv (x : S) : IsUnit (N : S.presheaf.stalk x) := by
    simpa only [map_natCast] using hS.map (S.presheaf.germ ⊤ x (by trivial)).hom
  have hk : P.IsNormalized A κ ∧ ∀ τ, P.IsNormalized A τ → τ = κ := by
    refine ⟨?_, ?_⟩
    · exact (sectionFamily_normalized_iff A d g s hs κ).2 hκ
    intro τ hτ
    obtain ⟨k, hk, hu⟩ := existsUnique_normalized N hN A hA hS d g s hs
    have ht : Normalized A g s hs τ := by
      exact (sectionFamily_normalized_iff A d g s hs τ).1 hτ
    exact (hu τ ht).trans (hu κ hκ).symm
  have hk' : P'.IsNormalized A κ' ∧ ∀ τ, P'.IsNormalized A τ → τ = κ' := by
    refine ⟨?_, ?_⟩
    · exact (sectionFamily_normalized_iff A d (h ≫ g) s' hs' κ').2 hκ'
    intro τ hτ
    obtain ⟨k, hk, hu⟩ := existsUnique_normalized N hN A hA hS d (h ≫ g) s' hs'
    apply (hu τ ?_).trans (hu κ' hκ').symm
    exact (sectionFamily_normalized_iff A d (h ≫ g) s' hs' τ).1 hτ
  have hcoh := sectionExceptional_normalized_etale A N hN hA P P' hinv e κ κ' hk hk'
  simp only [sectionExceptionalLocality_eq] at hcoh
  dsimp only [P, P', sectionFamily, e] at hcoh
  constructor
  · simpa only [ExceptionalSectionFamily.specialization,
    ExceptionalSectionFamily.fibreMap, sectionExceptionalComparison_eq,
    P, P', sectionFamily, familyPoint_false, familyPoint_true, specialization, atZero,
    e, family, ordinaryFinitePullback, if_neg Bool.false_ne_true, if_pos rfl,
    etaleFamilyMap, etaleNormalSectionMap,
    Category.assoc]
      using hcoh.1
  · simpa only [ExceptionalSectionFamily.specialization,
    ExceptionalSectionFamily.fibreMap, sectionExceptionalComparison_eq,
    P, P', sectionFamily, familyPoint_false, familyPoint_true, specialization, atZero,
    e, family, ordinaryFinitePullback, if_neg Bool.false_ne_true, if_pos rfl,
    etaleFamilyMap, etaleNormalSectionMap,
    Category.assoc]
    using hcoh.2



attribute [local irreducible] rightDerivedLowerShriek
  rightDerivedUpperShriekAdjunction
  affineLinearCompactComparison affineTraceCounit affineTraceProjection singleFunctorObjUnitIso
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The affine-space orientation is the adjoint of the specified coordinate-tower
counit, after its actual compact-support comparison and coefficient-unit identification.
Source: sk-thm-dnc, coordinate normalization
(blueprint: lem-trf-finite-ring-section-deformation). -/
abbrev affineAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ⟶
      dualizingComplex A (affineTraceProjection S d) :=
  CoordinateCounitArrows.towerAdjoint N hN A hA t D S hS d


/-- Section restriction of the affine adjoint orientation, using the ordered tensor
A_S(d)[2d] already used by linear trace invariance. The supplied section is any section
of the standard projection, so the same definition applies to its zero section.
Source: sk-thm-dnc, standard-pair normalization
(blueprint: lem-trf-finite-ring-section-deformation). -/
def affineSectionAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (z : S ⟶ affineTraceTower S d) (hz : z ≫ affineTraceProjection S d = 𝟙 S) :
    affineLinearBaseCoefficient A N hA S d ⟶
      sectionInvariant A (affineTraceProjection S d) z :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z
    (affineTraceProjection S d) hz).inv.app _ ≫
      (ordinaryFinitePullback A z).map
        ((affineLinearCoefficientDescent A N hA t S hS d).inv ≫
          affineAdjoint N hN A hA t D S hS d)

/-- The chart orientation, obtained by the counit-compatible etale comparison from the
standard affine-space adjoint. Source: sk-thm-dnc, coordinate normalization
(blueprint: lem-trf-finite-ring-section-deformation). -/
def chartAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {X S : Scheme.{u}} [IsNoetherian S] [IsNoetherian X]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (g : X ⟶ S) [HasCompactification g]
    (s : S ⟶ X) (hs : s ≫ g = 𝟙 S)
    (e : X ⟶ affineTraceTower S d) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (w : e ≫ affineTraceProjection S d = g) :
    affineLinearBaseCoefficient A N hA S d ⟶ sectionInvariant A g s := by
  letI := affineTraceNoetherian S d
  exact affineSectionAdjoint N hN A hA t D S hS d (s ≫ e)
    (by rw [Category.assoc, w, hs]) ≫
      etaleSectionMap A e (affineTraceProjection S d) g w (s ≫ e) s rfl

private theorem affineSectionAdjoint_isIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (z : S ⟶ affineTraceTower S d) (hz : z ≫ affineTraceProjection S d = 𝟙 S) :
    IsIso (affineSectionAdjoint N hN A hA t D S hS d z hz) := by
  let m := (affineLinearCoefficientDescent A N hA t S hS d).inv ≫
    CoordinateCounitArrows.towerAdjoint N hN A hA t D S hS d
  letI : IsIso m := IsIso.comp_isIso'
    (Iso.isIso_inv (affineLinearCoefficientDescent A N hA t S hS d))
    (coordinateTowerAdjoint_isIso N hN A hA t D S hS d)
  exact IsIso.comp_isIso'
    (Iso.isIso_inv ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      z (affineTraceProjection S d) hz).app _))
    (Functor.map_isIso (ordinaryFinitePullback A z) m)

private theorem chartAdjoint_isIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {X S : Scheme.{u}} [IsNoetherian S] [IsNoetherian X]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (g : X ⟶ S) [HasCompactification g]
    (s : S ⟶ X) (hs : s ≫ g = 𝟙 S)
    (e : X ⟶ affineTraceTower S d) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (w : e ≫ affineTraceProjection S d = g) :
    IsIso (chartAdjoint N hN A hA t D hS d g s hs e w) := by
  letI := affineTraceNoetherian S d
  have : IsIso (etaleSectionMap A e (affineTraceProjection S d) g w (s ≫ e) s rfl) := by
    rw [← sectionLocality_hom_eq]
    exact Iso.isIso_hom _
  unfold chartAdjoint
  exact IsIso.comp_isIso'
    (affineSectionAdjoint_isIso N hN A hA t D S hS d (s ≫ e)
      (by rw [Category.assoc, w, hs])) this

/-- The induced deformation chart in the coordinates u_j=x_j/t.
Source: sk-thm-dnc, standard Rees chart
(blueprint: lem-trf-finite-ring-section-deformation). -/
def coordinateDeformationMap {X S : Scheme.{u}} (d : ℕ)
    (s : S ⟶ X) [IsClosedImmersion s] (e : X ⟶ AffineSpace (ULift.{u} (Fin d)) S)
    (sq : IsPullback s (𝟙 S) e (AffineSpace.zeroSection (ULift.{u} (Fin d)) S)) :
    s.ker.deformationSpace ⟶ affineTraceTower (AffineSpace (ULift.{u} (Fin 1)) S) d :=
  etaleDeformationMap e (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) s sq ≫
    Scheme.Hom.deformationSpaceToAffineSpace (ULift.{u} (Fin d)) S ≫
      (affineTraceAffineSpaceIso (AffineSpace (ULift.{u} (Fin 1)) S) d).inv

/-- The deformation chart is etale, carries the deformed section to zero, and has the
standard coordinates x_j=t*u_j. The map is the actual Rees-algebra map in the definition.
Source: sk-thm-dnc, Rees charts (blueprint: lem-trf-finite-ring-section-deformation).
Proof: Steps 1, 3 and 6 identify the chart algebra with B tensor_R[x] R[t,u]. Thus
it is etale, and its structural map is the standard polynomial projection. The augmentation
kills u_j, so the section maps to the zero section. Noetherian finite type gives the
quasi-compact condition required by the compact-support locality comparison. -/
theorem coordinateDeformationMap_spec {X S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : X ⟶ S) (s : S ⟶ X) [IsClosedImmersion s] [Geometry d g s]
    (e : X ⟶ AffineSpace (ULift.{u} (Fin d)) S) [Etale e] [IsSeparated e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = g)
    (sq : IsPullback s (𝟙 S) e (AffineSpace.zeroSection (ULift.{u} (Fin d)) S)) :
    Etale (coordinateDeformationMap d s e sq) ∧
    IsSeparated (coordinateDeformationMap d s e sq) ∧
    LocallyOfFiniteType (coordinateDeformationMap d s e sq) ∧
    QuasiCompact (coordinateDeformationMap d s e sq) ∧
    coordinateDeformationMap d s e sq ≫
        affineTraceProjection (AffineSpace (ULift.{u} (Fin 1)) S) d =
      Scheme.Hom.deformationSpaceProj g s ∧
    s.deformationSpaceSection ≫ coordinateDeformationMap d s e sq ≫
        (affineTraceAffineSpaceIso (AffineSpace (ULift.{u} (Fin 1)) S) d).hom =
      AffineSpace.zeroSection (ULift.{u} (Fin d))
        (AffineSpace (ULift.{u} (Fin 1)) S) := by
  have : IsNoetherian (AffineSpace (ULift.{u} (Fin d)) S) := by
    have := LocallyOfFiniteType.isLocallyNoetherian
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
    have := QuasiCompact.compactSpace_of_compactSpace
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
    exact ⟨⟩
  have q := etaleDeformationMap_spec e
    (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
    (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) s sq
  have := q.2.1
  have := q.2.2.1
  have := q.2.2.2.1
  have := q.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold coordinateDeformationMap
    infer_instance
  · unfold coordinateDeformationMap
    infer_instance
  · unfold coordinateDeformationMap
    infer_instance
  · unfold coordinateDeformationMap
    infer_instance
  · unfold coordinateDeformationMap
    have hproj : (affineTraceAffineSpaceIso (AffineSpace (ULift.{u} (Fin 1)) S) d).inv ≫
        affineTraceProjection (AffineSpace (ULift.{u} (Fin 1)) S) d =
        (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) S) ↘ _) := by
      apply (cancel_epi
        (affineTraceAffineSpaceIso (AffineSpace (ULift.{u} (Fin 1)) S) d).hom).1
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      exact (AffineSpace.homOfVector_over _ _).symm
    rw [Category.assoc, Category.assoc, hproj,
      Scheme.Hom.deformationSpaceToAffineSpace_over,
      q.2.2.2.2.2.1, w]
  · simp only [coordinateDeformationMap, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rw [← Category.assoc, q.2.2.2.2.2.2,
      Scheme.Hom.deformationSpaceSection_comp_deformationSpaceToAffineSpace]

/-- The canonical family chart orientation from the pulled-back Tate line.
Source: sk-thm-dnc, coordinate normalization
(blueprint: lem-trf-finite-ring-section-deformation). -/
def familyChartAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {X S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (g : X ⟶ S) (s : S ⟶ X) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [Geometry d g s] (e : X ⟶ AffineSpace (ULift.{u} (Fin d)) S)
    [Etale e] [IsSeparated e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = g)
    (sq : IsPullback s (𝟙 S) e (AffineSpace.zeroSection (ULift.{u} (Fin d)) S)) :
    (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
      (affineLinearBaseCoefficient A N hA S d) ⟶ family A g s := by
  let q := coordinateDeformationMap_spec d g s e w sq
  letI := q.1
  letI := q.2.1
  letI := q.2.2.1
  letI := q.2.2.2.1
  exact (vectorIntegrationBaseCoefficientPullback A N hA t
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) hS d).hom ≫
    chartAdjoint N hN A hA t D (affineTracePullbackInvertible N
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) hS) d
      (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection
      (Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs)
      (coordinateDeformationMap d s e sq) q.2.2.2.2.1

/-- The fixed tower coordinate identification preserves the projection.
Source: sk-thm-dnc, standard coordinates (blueprint: lem-trf-finite-ring-section-deformation).
Proof: the map from the tower to affine space is homOfVector of its projection and its
ordered polynomial coordinates. Its composite with the affine projection is therefore
the tower projection. Cancel its isomorphism and compose with e to obtain this identity. -/
theorem coordinateTower_over {X S : Scheme.{u}} (d : ℕ) (g : X ⟶ S)
    (e : X ⟶ AffineSpace (ULift.{u} (Fin d)) S)
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = g) :
    (e ≫ (affineTraceAffineSpaceIso S d).inv) ≫ affineTraceProjection S d = g := by
  have hproj : (affineTraceAffineSpaceIso S d).inv ≫ affineTraceProjection S d =
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S) := by
    apply (cancel_epi (affineTraceAffineSpaceIso S d).hom).1
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    change affineTraceProjection S d =
      affineTraceToAffineSpace S d ≫
        (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
    exact (AffineSpace.homOfVector_over _ _).symm
  rw [Category.assoc, hproj, w]

/-- The source chart's adjoint orientation through the fixed polynomial coordinate tower.
Source: sk-thm-dnc, chart normalization
(blueprint: lem-trf-finite-ring-section-deformation). -/
def sourceChartAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {X S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (g : X ⟶ S) [HasCompactification g] (s : S ⟶ X) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) [Geometry d g s]
    (e : X ⟶ AffineSpace (ULift.{u} (Fin d)) S) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = g) :
    affineLinearBaseCoefficient A N hA S d ⟶ sectionInvariant A g s :=
  chartAdjoint N hN A hA t D hS d g s hs
    (e ≫ (affineTraceAffineSpaceIso S d).inv) (coordinateTower_over d g e w)

private theorem normalized_comparison
    {B L : Type*} [Category B] [Category L]
    (P : B ⥤ L) (I : L ⥤ B) (J : P ⋙ I ≅ 𝟭 B)
    {X Y : B} {Z : L} (f : P.obj X ≅ Z) (g : X ≅ Y) (θ : I.obj Z ⟶ Y)
    (h : I.map f.hom ≫ θ = J.hom.app X ≫ g.hom) :
    I.map (f.inv ≫ P.map g.hom) ≫ J.hom.app Y = θ := by
  have hn := J.hom.naturality g.hom
  change I.map (P.map g.hom) ≫ J.hom.app Y = J.hom.app X ≫ g.hom at hn
  rw [Functor.map_comp, Category.assoc, hn, ← h,
    ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, I.map_id,
    Category.id_comp]

/-- In each Cartesian-centre coordinate chart kappa is the identity between the two
pullbacks of the specified affine-space dualizing line. Both orientations are the
actual adjoints of the Kummer-normalized coordinate-tower counits.
Source: sk-thm-dnc, chart normalization; orientation-charts Steps 1--4
(blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 15 uses x_j=t*u_j to identify the standard deformation with affine space
over A1. Affine trace base change states equality of the actual counits. Transpose
that equality and compare right adjoints respecting counits; the comparison at one is
then the identity in these orientations. Etale locality commutes with these fibre maps
by the mate-pasting calculation of Step 14. Hence the uncorrected chart comparison is
already normalized at one. Uniqueness identifies it with kappa and yields the displayed
equality. Rank zero uses the literal identity coordinate-tower adjunction. -/
theorem coordinate_normalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {X S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (g : X ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ X) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) [Geometry d g s]
    (e : X ⟶ AffineSpace (ULift.{u} (Fin d)) S) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = g)
    (sq : IsPullback s (𝟙 S) e (AffineSpace.zeroSection (ULift.{u} (Fin d)) S))
    (κ : family A g s ≅ (ordinaryFinitePullback A
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj (sectionInvariant A g s))
    (hκ : Normalized A g s hs κ) :
    IsIso (sourceChartAdjoint N hN A hA t D hS d g s hs e w) ∧
    IsIso (familyChartAdjoint N hN A hA t D hS d g s hs e w sq) ∧
    familyChartAdjoint N hN A hA t D hS d g s hs e w sq ≫ κ.hom =
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).map
        (sourceChartAdjoint N hN A hA t D hS d g s hs e w) := by
  have hC := chartAdjoint_isIso N hN A hA t D hS d g s hs
    (e ≫ (affineTraceAffineSpaceIso S d).inv) (coordinateTower_over d g e w)
  have q := coordinateDeformationMap_spec d g s e w sq
  letI := q.1
  letI := q.2.1
  letI := q.2.2.1
  letI := q.2.2.2.1
  have hF := chartAdjoint_isIso N hN A hA t D
    (affineTracePullbackInvertible N (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) hS) d
    (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection
    (Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs)
    (coordinateDeformationMap d s e sq) q.2.2.2.2.1
  have hFamily : IsIso (familyChartAdjoint N hN A hA t D hS d g s hs e w sq) := by
    as_aux_lemma =>
      exact IsIso.comp_isIso'
        (Iso.isIso_hom (vectorIntegrationBaseCoefficientPullback A N hA t
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) hS d)) hF
  refine ⟨hC, hFamily, ?_⟩
  let P := ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
  let I := ordinaryFinitePullback A (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
  let C := sourceChartAdjoint N hN A hA t D hS d g s hs e w
  let F := familyChartAdjoint N hN A hA t D hS d g s hs e w sq
  let J := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)
  have : IsIso C := hC
  have : IsIso F := hFamily
  have hOne : I.map F ≫ atOne A g s hs =
      J.hom.app (affineLinearBaseCoefficient A N hA S d) ≫ C := by
    as_aux_lemma =>
      have h := coordinateTowerSection_oneFibre N hN A hA t D hS d g s hs e w sq
        (coordinateDeformationMap d s e sq) (by rfl) q.2.2.2.2.1
      dsimp only at h
      simp only [sectionLocality_hom_eq] at h
      change I.map F ≫ atOne A g s hs =
        J.hom.app (affineLinearBaseCoefficient A N hA S d) ≫ C at h
      exact h
  let μ := (asIso F).symm ≪≫ P.mapIso (asIso C)
  have hμ : Normalized A g s hs μ := by
    change I.map μ.hom ≫ J.hom.app (sectionInvariant A g s) = atOne A g s hs
    exact normalized_comparison P I J (asIso F) (asIso C) _ hOne
  obtain ⟨κ₀, _, huniq⟩ := existsUnique_normalized N hN A hA hS d g s hs
  have heq : μ = κ := (huniq μ hμ).trans (huniq κ hκ).symm
  change F ≫ κ.hom = P.map C
  rw [← heq]
  change (asIso F).hom ≫ (asIso F).inv ≫ P.map C = P.map C
  exact Iso.hom_inv_id_assoc _ _
attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

/-- The bundle's chosen compact-support right adjoint, using the already proved bundle
geometry to supply its compactification. Source: sk-thm-dnc, normal-bundle orientation
(blueprint: lem-trf-finite-ring-section-deformation). -/
abbrev bundleRight (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    DerivedCategoryModule A S ⥤
      DerivedCategoryModule A (VectorBundleZeroSection.scheme S d M) :=
  letI := (vectorIntegration_geometry S d M).1
  letI := (vectorIntegration_geometry S d M).2.1
  rightDerivedUpperShriek A (VectorBundleZeroSection.π S d M)

/-- The bundle adjoint orientation is the transpose of the already glued integration.
That integration is defined by its restrictions to every bundle frame, using the specified
affine-space counits. Source: sk-thm-dnc, normal-bundle orientation
(blueprint: lem-trf-finite-ring-section-deformation). -/
def bundleAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    vectorIntegrationCoefficient A N hA S d M ⟶
      (bundleRight A S d M).obj (ordinaryFiniteUnit A S) :=
  (vectorBundlePurityAdjunction A S d M).homEquiv
    (vectorIntegrationCoefficient A N hA S d M) (ordinaryFiniteUnit A S)
    (vectorBundleIntegration N hN A hA S hS d M)

attribute [local irreducible] bundleAdjoint

/-- Restrict the affine-glued bundle adjoint to its zero section. The inverse of this
map is the normal-bundle orientation in the statement.
Source: sk-thm-dnc, normal-bundle orientation
(blueprint: lem-trf-finite-ring-section-deformation). -/
def bundleSectionAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    affineLinearBaseCoefficient A N hA S d ⟶
      (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
        ((bundleRight A S d M).obj (ordinaryFiniteUnit A S)) :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (VectorBundleZeroSection.zero S d M) (VectorBundleZeroSection.π S d M)
    (VectorBundleZeroSection.zero_spec S d M).1).inv.app _ ≫
      (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).map
        (bundleAdjoint N hN A hA S hS d M)

/-- The affine-glued adjoint and its zero-section restriction are invertible for arbitrary
finite A. This asserts only the orientation needed here, independently of the valuation
coefficient restriction in the full vector-bundle-purity theorem.
Source: sk-thm-dnc, normal-bundle orientation
(blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 16 restricts to each linear trivialization. Integration is the specified
affine trace there by VectorIntegrationNormalization. Its adjunct is the affine adjoint
orientation, which is invertible by the affine-space adjunction and uniqueness of right
adjoints respecting counits. Linear trace invariance identifies these orientations on
overlaps; full faithfulness of shifted degree-zero sheaves and sheaf-Hom gluing give
the global orientation. Etale inverse image preserves its inverse, giving the zero-section
assertion. The zero-fold tensor and zero-variable adjunction give the d=0 normalization. -/
theorem bundleAdjoint_isIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    IsIso (bundleAdjoint N hN A hA S hS d M) ∧
    IsIso (bundleSectionAdjoint N hN A hA S hS d M) := by
  let := (vectorIntegration_geometry S d M).1
  let := (vectorIntegration_geometry S d M).2.1
  have h : IsIso (bundleAdjoint N hN A hA S hS d M) := by
    unfold bundleAdjoint vectorBundlePurityAdjunction
    exact integration_unit_adjunct_isIso N hN A hA S hS d M
  refine ⟨h, ?_⟩
  let e := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (VectorBundleZeroSection.zero S d M) (VectorBundleZeroSection.π S d M)
    (VectorBundleZeroSection.zero_spec S d M).1).app
      (affineLinearBaseCoefficient A N hA S d)
  let F := ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)
  let m := bundleAdjoint N hN A hA S hS d M
  letI : IsIso m := h
  exact IsIso.comp_isIso' (Iso.isIso_inv e) (Functor.map_isIso F m)

/-- The normal-bundle orientation, the inverse of the affine-glued adjoint restricted
to zero. Its target is the existing ordered tensor model of A_S(d)[2d], with the empty
tensor equal to A_S. Source: sk-thm-dnc, final orientation
(blueprint: lem-trf-finite-ring-section-deformation). -/
def bundleOrientation (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
        ((bundleRight A S d M).obj (ordinaryFiniteUnit A S)) ≅
      affineLinearBaseCoefficient A N hA S d :=
  letI := (bundleAdjoint_isIso N hN A hA S hS d M).2
  (asIso (bundleSectionAdjoint N hN A hA S hS d M)).symm

/-- The standard zero section in the fixed coordinate-tower presentation.
Source: sk-thm-dnc, bundle frames (blueprint: lem-trf-finite-ring-section-deformation). -/
def standardZero (S : Scheme.{u}) (d : ℕ) : S ⟶ affineTraceTower S d :=
  AffineSpace.zeroSection (ULift.{u} (Fin d)) S ≫ (affineTraceAffineSpaceIso S d).inv

/-- The tower zero is a section of its projection.
Source: sk-thm-dnc, standard pair (blueprint: lem-trf-finite-ring-section-deformation).
Proof: the tower isomorphism preserves the projection by coordinateTower_over. Compose
that equality with the affine zero section, whose composite with the projection is the
identity. This also treats d=0 using the canonical zero-dimensional affine-space map. -/
theorem standardZero_over (S : Scheme.{u}) (d : ℕ) :
    standardZero S d ≫ affineTraceProjection S d = 𝟙 S := by
  unfold standardZero
  apply coordinateTower_over d (𝟙 S)
  exact AffineSpace.zeroSection_comp_over (ULift.{u} (Fin d)) S

attribute [local irreducible] VectorBundleZeroSection.trivializationMap
  affineTraceAffineSpaceIso

/-- Frame coordinates carry the zero section of the standard bundle to the actual zero
section. Source: sk-thm-dnc, orientation gluing
(blueprint: lem-trf-finite-ring-section-deformation).
Proof: the linear frame map is the spectrum of the symmetric-algebra map induced by
the module frame. Both augmentations kill degree-one generators and fix scalars, so they
commute by the symmetric-algebra universal property. Compose with the frame inverse and
the open inclusion used in vectorIntegrationChart to get this equality. -/
theorem bundleFrame_zero (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (W : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d M W) :
    standardZero W.toScheme d ≫ vectorIntegrationChart S d M W e =
      W.ι ≫ VectorBundleZeroSection.zero S d M := by
  have := (VectorBundleZeroSection.trivializationMap_spec S d M W e).1
  have hz := (VectorBundleZeroSection.trivializationMap_spec S d M W e).2.2
  simp only [standardZero, vectorIntegrationChart, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← hz]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact Scheme.Hom.resLE_comp_ι _ _

/-- The zero-section exceptional comparison on a bundle frame, using the actual
Cartesian square and its augmentation-compatible section.
Source: sk-thm-dnc, orientation gluing
(blueprint: lem-trf-finite-ring-section-deformation). -/
def bundleFrameSectionMap (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (W : S.Opens)
    [IsNoetherian W.toScheme]
    (e : VectorBundleZeroSection.Trivialization S d M W) :
    (ordinaryFinitePullback A W.ι).obj
      ((ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
        ((bundleRight A S d M).obj (ordinaryFiniteUnit A S))) ⟶
      sectionInvariant A (affineTraceProjection W.toScheme d) (standardZero W.toScheme d) :=
  letI := (vectorIntegration_geometry S d M).1
  letI := (vectorIntegration_geometry S d M).2.1
  sectionMap A (VectorBundleZeroSection.π S d M) (affineTraceProjection W.toScheme d)
    W.ι (vectorIntegrationChart S d M W e) (vectorIntegrationChart_isPullback S d M W e)
    (VectorBundleZeroSection.zero S d M) (standardZero W.toScheme d)
    (bundleFrame_zero S d M W e)

section FrameCompatibility
-- Match the cached ordinary localization while keeping the large compositors folded.
attribute [local instance 100000] ordinaryFiniteDerivedCategoryInstance
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] Scheme.Modules
attribute [local irreducible] leftDerivedUpperStarComp leftDerivedUpperStarCompSectionIso
attribute [local implicit_reducible] Etale.sheafMonoidalCategory
attribute [local implicit_reducible] Etale.sheafBraidedCategory
attribute [local implicit_reducible] CategoryTheory.catToReflQuiver
attribute [local instance 20002] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
attribute [local semireducible] bundleAdjoint
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
  bundleAdjoint vectorIntegrationCoefficient vectorIntegrationSource dualizingComplex
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- Every bundle frame gives exactly the section restriction of the affine adjoint
orientation; thus the inverse orientation is the specified sheaf gluing and is preserved
by invertible linear frame changes. The displayed map is the canonical exceptional mate.
Source: sk-thm-dnc, normal-bundle orientation; orientation-charts Steps 2--4
(blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 16 uses VectorIntegrationNormalization for the same frame to identify the
actual integration map with the affine coordinate-tower counit after compact-support
exchange. Transposing this equality yields equality of the adjoints; mate pasting commutes
this transpose with restriction to zero. The coefficient and inverse-image section
compositors give precisely the equation below. On overlaps, linear trace invariance
identifies the counits, hence these adjoints. Shift to sheaves and use fully faithful
degree-zero embedding and sheaf-Hom gluing to get the unique common orientation. -/
theorem bundleOrientation_frames (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (W : S.Opens)
    [IsNoetherian W.toScheme] (e : VectorBundleZeroSection.Trivialization S d M W) :
    (ordinaryFinitePullback A W.ι).map (bundleSectionAdjoint N hN A hA S hS d M) ≫
        bundleFrameSectionMap A S d M W e =
      (vectorIntegrationBaseCoefficientPullback A N hA t W.ι hS d).hom ≫
        affineSectionAdjoint N hN A hA t D W.toScheme
          (affineTracePullbackInvertible N W.ι hS) d (standardZero W.toScheme d)
          (standardZero_over W.toScheme d) := by
  change SheafOfModules.{u} S.ringCatSheaf at M
  letI := (vectorIntegration_geometry S d M).1
  letI := (vectorIntegration_geometry S d M).2.1
  have hm := vectorIntegration_frameAdjoint N hN A hA t D S hS d M W e
  have hc := sectionPullback_coefficient_naturality A W.ι
    (VectorBundleZeroSection.π S d M) (affineTraceProjection W.toScheme d)
    (vectorIntegrationChart S d M W e) (VectorBundleZeroSection.zero S d M)
    (standardZero W.toScheme d) (vectorIntegrationChart_isPullback S d M W e).w
    (bundleFrame_zero S d M W e) (VectorBundleZeroSection.zero_spec S d M).1
    (standardZero_over W.toScheme d) (affineLinearBaseCoefficient A N hA S d)
    (affineLinearBaseCoefficient A N hA W.toScheme d)
    (dualizingComplex A (VectorBundleZeroSection.π S d M))
    (dualizingComplex A (affineTraceProjection W.toScheme d))
    (vectorIntegrationBaseCoefficientPullback A N hA t W.ι hS d).hom
    (bundleAdjoint N hN A hA S hS d M)
    ((affineLinearCoefficientDescent A N hA t W.toScheme
        (affineTracePullbackInvertible N W.ι hS) d).inv ≫
      affineAdjoint N hN A hA t D W.toScheme
        (affineTracePullbackInvertible N W.ι hS) d)
    (dualizingComplexBaseChangeMap A (vectorIntegrationChart_isPullback S d M W e)) ?_
  · dsimp only [bundleSectionAdjoint, bundleFrameSectionMap, sectionMap,
      bundleSectionPullbackSquare, affineSectionAdjoint, Iso.trans, Iso.app, Iso.symm,
      sectionInvariant, ordinaryFinitePullback, Functor.id_obj]
        at hc ⊢
    erw [hc]
  · dsimp only [bundleAdjoint, affineAdjoint, vectorIntegrationCoefficient] at hm ⊢
    erw [hm]

end FrameCompatibility

/-- The scalar-unit identification in the source of the full purity mate.
Source: vector-bundle purity at K=A_S (blueprint: lem-trf-finite-ring-section-deformation). -/
abbrev purityUnitCoefficientIso (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S) ≅
      vectorIntegrationCoefficient A N hA S d M :=
  bundleSectionPurityUnitIso N A hA S d M


/-- The actual full-purity mate at the coefficient unit, expressed on its scalar-unit
normalized source. Source: vector-bundle purity, displayed gamma
(blueprint: lem-trf-finite-ring-section-deformation). -/
abbrev purityUnitMate (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (p : (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj (ordinaryFiniteUnit A S)).obj
        (vectorIntegrationSource A N hA S d M)) :
    vectorIntegrationCoefficient A N hA S d M ⟶
      (bundleRight A S d M).obj (ordinaryFiniteUnit A S) :=
  bundleSectionPurityUnitMap N hN A hA S hS d M p

attribute [local semireducible] rightDerivedLowerShriek

attribute [local instance 20002] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory

attribute [local irreducible] vectorIntegrationCoefficient

private theorem normalized_adjunct
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    {X Y : C} (e : X ≅ Y) (c : F.obj Y ⟶ 𝟙_ D)
    (p : F.obj X ≅ (𝟙_ D) ⊗ F.obj Y)
    (h : p.inv ≫ F.map e.hom = (λ_ (F.obj Y)).hom) :
    a.homEquiv _ _ c = e.inv ≫ a.homEquiv _ _
      (p.hom ≫ (𝟙_ D) ◁ c ≫ (ρ_ (𝟙_ D)).hom) := by
  rw [← a.homEquiv_naturality_left]
  apply congrArg (a.homEquiv _ _)
  have he : F.map e.inv ≫ p.hom = (λ_ (F.obj Y)).inv := by
    apply (cancel_mono (λ_ (F.obj Y)).hom).1
    rw [← h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← F.map_comp, e.inv_hom_id, F.map_id]
    rw [h, Iso.inv_hom_id]
  rw [← Category.assoc, he]
  rw [← leftUnitor_inv_naturality_assoc]
  rw [← unitors_equal, Iso.inv_hom_id, Category.comp_id]

private theorem bundleAdjoint_eq (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    : bundleAdjoint N hN A hA S hS d M =
      (vectorBundlePurityAdjunction A S d M).homEquiv
        (vectorIntegrationCoefficient A N hA S d M) (ordinaryFiniteUnit A S)
        (vectorBundleIntegration N hN A hA S hS d M) := by
  unfold bundleAdjoint
  rfl

/-- Agreement with the inverse purity orientation, whenever the full purity theorem
supplies its canonical projection inverse. In particular this applies to all the
valuation-ring quotients in thm-amb-vector-bundle-purity. This records equality of the
actual maps before taking their inverses and restricting to zero.
Source: sk-thm-dnc, final comparison with vector-bundle purity
(blueprint: lem-trf-finite-ring-section-deformation).
Proof: Step 16 observes that vector-bundle purity uses the same integration, characterized
by the same affine traces on every frame. At the coefficient unit, naturality of the
canonical tensor projection map with the unit constraints identifies its normalized
inverse with the compact-support unit constraint. Transposing gives the equality below.
Pull to zero and invert to obtain exactly bundleOrientation, so the orientation agrees
with the zero-section restriction of inverse purity, with no choice of normalization. -/
theorem bundleOrientation_purity (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (p : (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj (ordinaryFiniteUnit A S)).obj
        (vectorIntegrationSource A N hA S d M))
    (hp : p.inv = vectorBundlePurityProjectionMap A N hA S d M (ordinaryFiniteUnit A S)) :
    bundleAdjoint N hN A hA S hS d M = purityUnitMate N hN A hA S hS d M p := by
  let := (vectorIntegration_geometry S d M).1
  let := (vectorIntegration_geometry S d M).2.1
  let C := vectorIntegrationCoefficient A N hA S d M
  let F := vectorBundlePurityLower A S d M
  let e := bundleSectionPurityUnitIso N A hA S d M
  let l := derivedTensorLeftUnitor (ModuleCat.{u + 1} A) S (F.obj C)
  have he : p.inv ≫ F.map e.hom = l.hom := by
    rw [hp]
    exact bundleSectionProjection_unit N A hA S d M
  rw [bundleAdjoint_eq]
  unfold purityUnitMate bundleSectionPurityUnitMap
  exact normalized_adjunct (vectorBundlePurityAdjunction A S d M) e
    (vectorBundleIntegration N hN A hA S hS d M) p he

/-- The line, fibre and unique-comparison conclusions in one proposition, using only
proofs of geometry that the preceding geometric theorem supplies.
Source: sk-thm-dnc, opening paragraph and Gluing
(blueprint: lem-trf-finite-ring-section-deformation). -/
def Conclusions (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) [Geometry d g s] : Prop :=
  IsShiftedLine A S d (sectionInvariant A g s) ∧
  IsShiftedLine A (AffineSpace (ULift.{u} (Fin 1)) S) d (family A g s) ∧
  IsIso (atOne A g s hs) ∧ IsIso (atZero A g s) ∧
  (∃! κ : family A g s ≅ (ordinaryFinitePullback A
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj (sectionInvariant A g s),
    Normalized A g s hs κ) ∧
  ∀ (κ : family A g s ≅ (ordinaryFinitePullback A
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj (sectionInvariant A g s)),
    Normalized A g s hs κ → IsIso (specialization A g s κ)

/-- Normalized section deformation for arbitrary finite etale coefficients, with the
geometric hypotheses of all auxiliary derived constructions asserted as conclusions.
Source: sk-thm-dnc, Local construction and Gluing, finite-ring extension in
sk-thm-smooth-purity (blueprint: lem-trf-finite-ring-section-deformation).
Proof: Steps 1--6 give geometry and the canonical fibre squares. Steps 7--8 give the
shifted lines and invertibility of the counit-defined fibre maps. Steps 9--11 construct,
normalize and glue kappa and its inverse; connected geometric affine-line fibres prove
uniqueness. Its inverse zero restriction is delta. The compatibility and normalization
clauses are stated in baseChange_compatibility, etale_compatibility,
coordinate_normalization and bundleOrientation_purity, with their actual canonical maps.
All of their geometric instances follow from geometry and the displayed pullback squares;
none is an extra assumption on this theorem. -/
theorem finiteRingSectionDeformation (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) :
    ∃ G : Geometry d g s, @Conclusions A _ _ V S d g _ _ s _ hs G := by
  let G : Geometry d g s := geometry d g s hs
  have hlines := lines_and_fibres N hN A hA hS d g s hs
  have hnorm := existsUnique_normalized N hN A hA hS d g s hs
  refine ⟨G, hlines.1, hlines.2.1, hlines.2.2.1, hlines.2.2.2, hnorm, ?_⟩
  intro κ hκ
  exact isIso_specialization N hN A hA hS d g s hs κ hκ

end AlgebraicGeometry.Etale.FiniteRingSectionDeformation
