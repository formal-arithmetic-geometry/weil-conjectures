/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedAdjointCochainCounit
import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps

/-! Normalized tensorators and Koszul symmetries for all finite stages.

The proof uses the ordinary balanced scalar tensorator, the descended pro-etale
finite Verdier scalar comparison, and their representative Koszul braidings.
The construction works for every ring homomorphism, so no finite-stage factorization
or quotient-cofinality argument is needed for these data. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option linter.style.haveILetI false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Etale.ExceptionalCoefficients
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit


private theorem canonicalSymmetry_component
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] (K L : _root_.DerivedCategory C) :
    HEq (((_root_.DerivedCategory.canonicalTensorSymmetry C).hom.app K).app L)
      (DerivedMonoidal.braiding' (_root_.DerivedCategory.Qh (C := C))
        (HomotopyCategory.quasiIso C (.up ℤ)) K L).hom := by
  exact HEq.rfl

private theorem siteSymmetry
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) :
    (∃ b : Etale.derivedTensor A X ≅ (Etale.derivedTensor A X).flip,
      ∀ K L, HEq ((b.hom.app K).app L)
        (DerivedMonoidal.braiding'
          (_root_.DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology A))
          (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (.up ℤ)) K L).hom) ∧
    (∃ b : ProEtale.derivedTensor A X ≅ (ProEtale.derivedTensor A X).flip,
      Sites.IsProKoszulSymmetry A X b) := by
  constructor
  · exact ⟨Etale.derivedTensorSymmetry A X,
      canonicalSymmetry_component (Sheaf X.smallEtaleTopology A)⟩
  · exact ⟨_root_.DerivedCategory.canonicalTensorSymmetry
      (Sheaf (Scheme.ProEt.topology X) A),
      canonicalSymmetry_component (Sheaf (Scheme.ProEt.topology X) A)⟩

/-- The adjoint representative of the localized ordinary unit is the finite Verdier scalar
representative, for abstract adjunctions; stated abstractly so that the kernel does not unfold
the pro-etale sheaf model. -/
private theorem adjointRepresentative_app_eq
    {C : Type v} [Category.{u + 1} C] [Abelian C] [HasDerivedCategory.{u + 1} C]
    {D : Type v} [Category.{u + 1} D] [Abelian D] [HasDerivedCategory.{u + 1} D]
    (L : C ⥤ D) [L.Additive] (R : D ⥤ C) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (ordinary : L ⊣ R) {S : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D}
    (derived : S ⊣ R.mapDerivedCategory) (P : CochainComplex C ℤ) :
    (adjointRepresentative _root_.DerivedCategory.Q _root_.DerivedCategory.Q
      (L.mapHomologicalComplex (.up ℤ)) (R.mapHomologicalComplex (.up ℤ)) S
      R.mapDerivedCategory derived (ordinary.mapHomologicalComplex (.up ℤ))
      R.mapDerivedCategoryFactors.symm).app P =
      finiteVerdierScalarRepresentativeAux L R ordinary derived P := by
  unfold finiteVerdierScalarRepresentativeAux
  rw [← mapComplex_unit_formula]
  rfl

private theorem proTensorNormalized {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    ∃ μ : Sites.TensorComparison true φ X, Sites.NormalizedTensor true φ X μ := by
  let F := finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ
  let U := Sheaf.restrictScalars (Scheme.ProEt.topology X) φ
  let adj : F ⊣ U := finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology X) φ
  letI : F.IsLeftAdjoint := adj.isLeftAdjoint
  letI := φ.toAlgebra
  letI : F.PreservesKFlatQuasiIso := preservesKFlatQuasiIso_sheafExtendScalars A B X
  letI : F.PreservesFlat := preservesFlat_sheafExtendScalars X φ
  letI : F.Monoidal := composeAndSheafifyMonoidal (Scheme.ProEt.topology X)
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)
  let G := pbcFixedScalarExtension.{u} (Scheme.ProEt.topology X) φ
  let ad : G ⊣ U.mapDerivedCategory := Adjunction.ofIsRightAdjoint _
  let b : F.leftDerivedFunctor ⊣ U.mapDerivedCategory :=
    adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let e : G ≅ F.leftDerivedFunctor := ad.leftAdjointUniq b
  let r := adjointRepresentative _root_.DerivedCategory.Q
    _root_.DerivedCategory.Q (F.mapHomologicalComplex (.up ℤ))
    (U.mapHomologicalComplex (.up ℤ)) G U.mapDerivedCategory ad
    (adj.mapHomologicalComplex (.up ℤ)) U.mapDerivedCategoryFactors.symm
  have hr' : r.app = finiteVerdierScalarRepresentative (Scheme.ProEt.topology X) φ :=
    funext fun P ↦ adjointRepresentative_app_eq F U adj ad P
  have hr : ∀ P, r.app P = e.hom.app (_root_.DerivedCategory.Q.obj P) ≫
      F.rightExact_cochainCounit P := by
    intro P
    exact (Adjunction.leftDerivedCochainCounit F U adj ad P).symm
  obtain ⟨μ, hμ, _⟩ := Functor.rightExact_tensorComparison_existsUnique F G e r.app hr
  let δ := productIsoOfFamily (curriedTensor _) (curriedTensor _) G μ hμ.1 hμ.2.1
  have hn : TensorNormalizationAux F G r.app δ := by
    apply tensor_normalization_all_of_flat F G r δ
    exact hμ.2.2
  refine ⟨δ, δ, ?_, HEq.rfl⟩
  rw [← hr']
  exact hn

/-- Normalized tensorators and signed symmetries at finite stages.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--2.
(blueprint: lem-sf-normalized-stage-tensor-symmetry-data).

Proof: On each site, use ordinary scalar extension and its restriction adjunction. The balanced map
sends 1 tensor (x tensor y) to (1 tensor x) tensor (1 tensor y). Apply the normalized derived tensor
comparison to K-flat resolutions in both variables. Naturality extends it through localization,
giving a natural isomorphism for all derived objects and the representative equation in
NormalizedTensor. On the ordinary site this is precisely ExceptionalCoefficients.tensorIso. On the
pro-etale site it is the same generic construction for finiteVerdierOrdinaryExtension and
finiteVerdierScalarRepresentative. Use the descended cochain Koszul swap for each stage. In
bidegrees r,s this is x tensor y mapped to (-1)^(rs) y tensor x; the two signs for the inverse
multiply to one. Its descent is the braiding used in NormalizedSymmetry. Choose these specified
comparisons for every stage and stage arrow, and package their normalization proofs. -/
theorem normalized_stage_tensor_symmetry_data
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ∃ (μ : ∀ (pro : Bool) {s t : Stage l E} (a : Arrow s t),
        Sites.TensorComparison pro a.ringMap X)
      (σ : ∀ (pro : Bool) (s : Stage l E),
        Sites.tensor pro s.ring X ≅ (Sites.tensor pro s.ring X).flip),
      (∀ (pro : Bool) {s t : Stage l E} (a : Arrow s t),
        Sites.NormalizedTensor pro a.ringMap X (μ pro a)) ∧
      (∀ (pro : Bool) (s : Stage l E),
        Sites.NormalizedSymmetry pro s.ring X (σ pro s)) := by
  classical
  have ht (pro : Bool) {s t : Stage l E} (a : Arrow s t) :
      ∃ μ : Sites.TensorComparison pro a.ringMap X,
        Sites.NormalizedTensor pro a.ringMap X μ := by
    cases pro
    · exact ⟨Etale.ExceptionalCoefficients.tensorIso a.ringMap X, HEq.rfl⟩
    · exact proTensorNormalized a.ringMap X
  have hb (pro : Bool) (s : Stage l E) :
      ∃ b : Sites.tensor pro s.ring X ≅ (Sites.tensor pro s.ring X).flip,
        Sites.NormalizedSymmetry pro s.ring X b := by
    cases pro
    · obtain ⟨b, hb⟩ := (siteSymmetry (ModuleCat.{u + 1} s.ring) X).1
      exact ⟨b, hb⟩
    · exact (siteSymmetry (ModuleCat.{u + 1} s.ring) X).2
  exact ⟨fun pro {_ _} a ↦ (ht pro a).choose, fun pro s ↦ (hb pro s).choose,
    fun pro {_ _} a ↦ (ht pro a).choose_spec, fun pro s ↦ (hb pro s).choose_spec⟩

end WeilConjectures.FiniteFreeCoefficients
