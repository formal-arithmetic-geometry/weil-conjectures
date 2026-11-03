/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingBundleSectionOrientation
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceLinearTraceInvariance
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.AffineSpace
public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
import WeilConjectures.AlgebraicGeometry.Section.SectionCoordinateTowerOneFibre
import WeilConjectures.AlgebraicGeometry.Coordinate.CoordinateTowerAdjointIsIso
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationFrameAdjoint
import WeilConjectures.AlgebraicGeometry.Section.SectionPullbackCoefficientNaturality
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionProjectionUnit
import all WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
import WeilConjectures.AlgebraicGeometry.AffineLineNormalizedDescent.EtaleShiftedLineNormalizedDescent
import WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import all WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationMate
import all WeilConjectures.AlgebraicGeometry.SectionLocalDualizingComparisons.SectionLocalDualizingComparisons
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.SectionReesNoetherianGeometry.SectionReesNoetherianGeometry
import WeilConjectures.AlgebraicGeometry.SmoothSectionCentredCoordinates.SmoothSectionCentredCoordinates
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

private theorem sectionExceptionalComparison_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B B' : Scheme.{u}} {d : ℕ} {P : ExceptionalSectionPair B d}
    {P' : ExceptionalSectionPair B' d} {v : B' ⟶ B}
    (e : ExceptionalSectionChange P P' v) :
    sectionExceptionalComparison A e = sectionMap A P.map P'.map v e.upper e.square
      P.sect P'.sect e.section_comm := by
  simp only [sectionExceptionalComparison, sectionCoherencePullbackIso, sectionMap,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]

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

attribute [local irreducible] rightDerivedLowerShriek
  rightDerivedUpperShriekAdjunction
  affineLinearCompactComparison affineTraceCounit affineTraceProjection singleFunctorObjUnitIso
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

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

attribute [local irreducible] VectorBundleZeroSection.trivializationMap
  affineTraceAffineSpaceIso

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

end FrameCompatibility

attribute [local semireducible] rightDerivedLowerShriek

attribute [local instance 20002] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory

attribute [local irreducible] vectorIntegrationCoefficient

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

end AlgebraicGeometry.Etale.FiniteRingSectionDeformation
