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

/-- The standard zero section in the fixed coordinate-tower presentation.
Source: sk-thm-dnc, bundle frames (blueprint: lem-trf-finite-ring-section-deformation). -/
def standardZero (S : Scheme.{u}) (d : ℕ) : S ⟶ affineTraceTower S d :=
  AffineSpace.zeroSection (ULift.{u} (Fin d)) S ≫ (affineTraceAffineSpaceIso S d).inv

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

end AlgebraicGeometry.Etale.FiniteRingSectionDeformation
