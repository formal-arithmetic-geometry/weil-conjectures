/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.Paper.CoordinateLineAdjunctionMaps
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import Sheaf.Paper.AffineLinePurityComparison
public import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
public import Sheaf.Paper.VectorIntegrationSiteComparison
import Sheaf.Paper.CoordinateLineCounitTensor
import Sheaf.Paper.CoordinateLineAugmentationRealization
import Sheaf.Paper.CoordinateLineConjugateExponents
import Sheaf.Paper.AffineSpaceCoordinateBoundaries
import WeilConjectures.Compactification.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Normalized coordinate-line adjunction and its actual counit

Source: main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, first sentences and final paragraph
(blueprint: lem-pur-coordinate-line-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor

namespace AlgebraicGeometry.ProEtale.CoordinateLine
open AffineLinePurity VectorIntegrationSite

variable (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
variable (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)

/-- All normalized counit and transpose clauses in the source's finite-field domain.
Noetherianity is supplied from Geometry; invertibility of N is asserted here.
The positive exponent a is written r+1, covering exactly every a>=1.
Source: main-20261015, first sentences and final comparison paragraph
(blueprint: lem-pur-coordinate-line-adjunction). -/
def NormalizedAdjunction [IsNoetherian T] (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] : Prop :=
  ∃ hT : IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(T, ⊤)),
    NormalizedOrdinary (Ring P) (P.coefficients.l ^ (r + 1)) hA T
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT ∧
    ∀ (K : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
      (Ke : Etale.DerivedCategoryModule (Ring P) T)
      (hKe : Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (Ring P)) T Ke)
      (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj),
      affineLinePurityComparison P T r hA aT K Ke hKe eK =
        comparedConjugate P T r hA hT K Ke eK ∧
      IsIso (affineLinePurityComparison P T r hA aT K Ke hKe eK)

/-- The source's geometric assertions for a single line, in the published models.
Source: polynomial-chart paragraph and proof Step 1
(blueprint: lem-pur-coordinate-line-adjunction). -/
def Geometry : Prop :=
  IsNoetherian T ∧ IsNoetherian (AffineSpace PUnit.{u + 1} T) ∧
    IsNoetherian (ProjectiveLine T) ∧
    (∃ dT dX dP : ℕ, topologicalKrullDim T ≤ (dT : WithBot ℕ∞) ∧
      topologicalKrullDim (AffineSpace PUnit.{u + 1} T) ≤ (dX : WithBot ℕ∞) ∧
      topologicalKrullDim (ProjectiveLine T) ≤ (dP : WithBot ℕ∞)) ∧
    IsSeparated (AffineSpace PUnit.{u + 1} T ↘ T) ∧
    LocallyOfFiniteType (AffineSpace PUnit.{u + 1} T ↘ T) ∧
    QuasiCompact (AffineSpace PUnit.{u + 1} T ↘ T) ∧
    IsOpenImmersion (ProjectiveLine.affineChart T) ∧
    IsProper (ProjectiveLine T ↘ T) ∧
    ProjectiveLine.affineChart T ≫ (ProjectiveLine T ↘ T) =
      (AffineSpace PUnit.{u + 1} T ↘ T)

/-- Canonical exponent comparison through the specified inverse-limit Tate line.
Source: independence of the annihilating exponent, proof Steps 2 and 6
(blueprint: lem-pur-coordinate-line-adjunction). -/
@[irreducible]
def sourceExponentIso (r' : ℕ)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0)
    (hP : IsUnit (P.coefficients.l : Γ(ProjectiveLine T, ⊤)))
    (hX : IsUnit (P.coefficients.l : Γ(AffineSpace PUnit.{u + 1} T, ⊤)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P)))) :
    source P.coefficients.l P.extension (P.level - 1) T r hA K ≅
      source P.coefficients.l P.extension (P.level - 1) T r' hA' K := by
  exact tensorCoefficientIso (Ring P) T _ _
    (coefficientTwistIso P.coefficients.l P.extension (P.level - 1) T r hA hP hX ≪≫
      (coefficientTwistIso P.coefficients.l P.extension (P.level - 1) T r' hA' hP hX).symm) K

/-- All clauses of the coordinate-line statement, including universal Cartier geometry
and the canonical exponent comparison of the actual gamma maps.
Source: main-20261015, source paragraph (blueprint: lem-pur-coordinate-line-adjunction). -/
def CoordinateLineStatement (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] : Prop :=
  Geometry T ∧ (∀ d : ℕ, Geometry (iteratedAffineLine T d)) ∧
    (∀ (B : Scheme.{u}) (d : ℕ),
      iteratedAffineLineProj B (d + 1) =
        (AffineSpace PUnit.{u + 1} (iteratedAffineLine B d) ↘ iteratedAffineLine B d) ≫
          iteratedAffineLineProj B d ∧
      Scheme.Hom.toIteratedAffineLine (𝟙 B) (fun _ : Fin (d + 1) ↦ 0) =
        Scheme.Hom.toIteratedAffineLine (𝟙 B) (fun _ : Fin d ↦ 0) ≫
          AffineSpace.zeroSection PUnit.{u + 1} (iteratedAffineLine B d) ∧
      AffineSpace.zeroSection PUnit.{u + 1} (iteratedAffineLine B d) ≫
        (AffineSpace PUnit.{u + 1} (iteratedAffineLine B d) ↘ iteratedAffineLine B d) =
          𝟙 (iteratedAffineLine B d)) ∧
    (∀ (B : Scheme.{u}) (d : ℕ) (i : Fin d),
      (((iteratedAffineLine B d).zeroLocusSubschemeι
        {iteratedAffineLine.coord B d i}).ker).IsInvertible) ∧
    ((P.coefficients.l ^ P.level : ℕ) : Ring P) = 0 ∧
    (∀ (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0),
      ∀ [IsNoetherian T], NormalizedAdjunction P T r hA aT) ∧
    (∀ (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
      (U : Scheme.{u}) (aU : U ⟶ Spec (.of P.field.k)),
      LocallyOfFiniteType aU → QuasiCompact aU → IsSeparated aU →
      ∃ C : Scheme.Cover.{u} Scheme.etalePrecoverage U, ∀ (i : C.I₀) (m : ℤ),
        Nonempty ((Scheme.finiteEtaleTateSheaf (Ring P) (P.coefficients.l ^ (r + 1)) U hA m).over
          (C.etalePrecoverageToEtale i) ≅
          (constantSheaf (U.smallEtaleTopology.over (C.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} (Ring P))).obj (ModuleCat.of (Ring P) (Ring P)))) ∧
    (∀ (U : Scheme.{u}) (hU : IsUnit (P.coefficients.l : Γ(U, ⊤)))
      (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) (m : ℕ),
      Scheme.IsFiniteTateSiteComparison P.coefficients.l P.extension (P.level - 1) U r hA m
        (twistComparison P.coefficients.l P.extension (P.level - 1) U hU r hA m)) ∧
    ∀ (r r' : ℕ)
      (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
      (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0)
      (hP : IsUnit (P.coefficients.l : Γ(ProjectiveLine T, ⊤)))
      (hX : IsUnit (P.coefficients.l : Γ(AffineSpace PUnit.{u + 1} T, ⊤)))
      (K : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
      (Ke : Etale.DerivedCategoryModule (Ring P) T)
      (hKe : Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (Ring P)) T Ke)
      (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj),
      (sourceExponentIso P T r hA r' hA' hP hX K.obj).hom ≫
        affineLinePurityComparison P T r' hA' aT K Ke hKe eK =
      affineLinePurityComparison P T r hA aT K Ke hKe eK

private theorem geometry_of_finiteType
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] : Geometry T := by
  have : IsNoetherian T := isNoetherian_of_locallyOfFiniteType aT
  have : IsNoetherian (AffineSpace PUnit.{u + 1} T) :=
    isNoetherian_of_locallyOfFiniteType (AffineSpace PUnit.{u + 1} T ↘ T)
  have : IsNoetherian (ProjectiveLine T) :=
    isNoetherian_of_locallyOfFiniteType (ProjectiveLine T ↘ T)
  obtain ⟨dT, hdT⟩ := exists_topologicalKrullDim_le aT
  obtain ⟨dX, hdX⟩ := exists_topologicalKrullDim_le
    ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT)
  obtain ⟨dP, hdP⟩ := exists_topologicalKrullDim_le ((ProjectiveLine T ↘ T) ≫ aT)
  exact ⟨inferInstance, inferInstance, inferInstance,
    ⟨dT, dX, dP, hdT, hdX, hdP⟩, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ProjectiveLine.affineChart_over T⟩

private theorem level_annihilates (P : WeilConjectures.PurityFiniteSetting.{u}) :
    ((P.coefficients.l ^ (P.level) : ℕ) : Ring P) = 0 := by
  let O := Padic.coefficientExtensionIntegers P.coefficients.l P.extension
  let m := Padic.coefficientExtensionMaximalIdeal P.coefficients.l P.extension
  have hDvr := Padic.extension_integers_dvr P.coefficients.l P.extension
    (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension)
    (spectralNorm_extends (K := Padic P.coefficients.l) (L := P.extension))
  have hs := hDvr.choose_spec.choose_spec
  have hm : (P.coefficients.l : O) ∈ m := by
    apply (hs.2.1 (P.coefficients.l : O)).2
    have he := spectralNorm_extends (K := Padic P.coefficients.l) (L := P.extension)
      (P.coefficients.l : Padic P.coefficients.l)
    change spectralNorm (Padic P.coefficients.l) P.extension (P.coefficients.l : P.extension) < 1
    simpa only [map_natCast] using
      he.trans_lt (Padic.norm_p_lt_one (p := P.coefficients.l))
  have hg : Ideal.span ({Padic.coefficientExtensionUniformizer
      P.coefficients.l P.extension} : Set O) = m := by
    exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  apply ULift.down_injective
  change ((P.coefficients.l ^ (P.level) : ℕ) :
    Padic.coefficientExtensionRing P.coefficients.l P.extension ((P.level - 1) + 1)) = 0
  rw [Nat.sub_add_cancel P.level_pos,
    ← map_natCast (Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level)),
    Ideal.Quotient.eq_zero_iff_mem]
  change ((P.coefficients.l ^ (P.level) : ℕ) : O) ∈
    Ideal.span ({Padic.coefficientExtensionUniformizer P.coefficients.l P.extension} : Set O) ^
      P.level
  rw [hg, Nat.cast_pow]
  exact Ideal.pow_mem_pow hm P.level

private theorem specified_transpose_compatible
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).IsLeftAdjoint]
    (M : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (W : Scheme.FixedEtaleOriginWitness X A M)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (Ke : Etale.DerivedCategoryModule A Y)
    (eK : (VectorIntegrationSite.comparison A Y).obj Ke ≅ K.obj)
    (ae : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).obj W.complex.obj ⟶ Ke)
    (ap : (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).obj M.obj ⟶ K.obj)
    (h : (fixedCompactSupportComparisonIso A c).inv.app W.complex ≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).map W.iso.hom ≫ ap =
      (VectorIntegrationSite.comparison A Y).map ae ≫ eK.hom) :
    specifiedExceptionalHomEquiv A c M W K ap =
      W.iso.inv ≫ (VectorIntegrationSite.comparison A X).map
        ((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c)).homEquiv _ Ke ae) ≫
        boundedSiteRho A (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).rightAdjoint Ke ≫
        (sfFiniteExceptionalAt A c).map eK.hom := by
  dsimp only [specifiedExceptionalHomEquiv, Equiv.trans_apply, Iso.homFromEquiv_apply,
    Equiv.ofBijective_apply, Functor.mapIso_symm, Iso.symm_inv]
  change W.iso.inv ≫
    (VectorIntegrationSite.comparison A X).map
      ((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c)).homEquiv _ _
        ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ K.obj
          ((fixedCompactSupportComparisonIso A c).inv.app W.complex ≫
            (rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} A) c).map W.iso.hom ≫ ap))) = _
  rw [h]
  have he : (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ K.obj
      ((VectorIntegrationSite.comparison A Y).map ae ≫ eK.hom) =
      ae ≫ (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app Ke ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) Y).rightDerivedFunctor.map eK.hom := by
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit]
    rw [← Category.assoc]
    congr 1
    exact ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.naturality ae).symm
  rw [he, Adjunction.homEquiv_naturality_right]
  simp only [Functor.map_comp, boundedSiteRho, sfFiniteExceptionalAt,
    Functor.comp_map]

private theorem comparedConjugate_isIso
    [IsNoetherian T]
    (hT : IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj) :
    IsIso (comparedConjugate P T r hA hT K Ke eK) := by
  have hplus : DerivedCategory.TStructure.t.plus Ke := by
    exact hKe.1.1.1
  have := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} (Ring P)) T Ke hplus
  unfold comparedConjugate boundedSiteRho
  infer_instance

private theorem comparison_counit
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hN : 0 < N) (hB : IsUnit (N : Γ(B, ⊤)))
    (K : Etale.DerivedCategoryModule A B) :
    (Etale.affineTraceLineLeft A B).map ((comparison A N hA B hN hB).hom.app K) ≫
      (exceptionalAdjunction A B).counit.app K =
        (adjunction A N hA B hN hB).counit.app K := by
  unfold comparison
  simpa using conjugateEquiv_counit (adjunction A N hA B hN hB)
    (exceptionalAdjunction A B) (𝟙 _) K

private theorem comparison_transpose
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hN : 0 < N) (hB : IsUnit (N : Γ(B, ⊤)))
    (K : Etale.DerivedCategoryModule A B) :
    (comparison A N hA B hN hB).hom.app K =
      (exceptionalAdjunction A B).homEquiv _ K
        ((adjunction A N hA B hN hB).counit.app K) := by
  apply ((exceptionalAdjunction A B).homEquiv _ K).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact comparison_counit A N hA B hN hB K

-- Keep the fixed comparison and the chosen adjunction abstract during unification.
attribute [local irreducible] Adjunction.ofIsLeftAdjoint Adjunction.homEquiv
  Functor.rightAdjoint fixedCompactSupportComparisonIso specifiedExceptionalHomEquiv
  boundedSiteRho derivedComparisonAdjunction

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] sourceWitness exceptionalAdjunction
  affineTraceLineCompactification Etale.affineTraceOpenLeft sfFiniteExceptionalAt

private theorem comparison_realization
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (hT : IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj) :
    affineLinePurityComparison P T r hA aT K Ke hKe eK =
      comparedConjugate P T r hA hT K Ke eK := by
  let M : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology (AffineSpace PUnit.{u + 1} T))
        (ModuleCat.{u + 1} (Ring P))) :=
    ⟨_, source_plus P.coefficients.l P.extension (P.level - 1) T r hA K.obj Ke hKe eK⟩
  let W : Scheme.FixedEtaleOriginWitness (AffineSpace PUnit.{u + 1} T) (Ring P) M :=
    { complex := ⟨etaleSource P.coefficients.l P.extension (P.level - 1) T r hA Ke,
        etaleSource_plus P.coefficients.l P.extension (P.level - 1) T r hA Ke hKe⟩
      iso := sourceComparison P.coefficients.l P.extension (P.level - 1) T r hA K.obj Ke eK }
  let ae : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Ring P)) (affineTraceLineCompactification T)).obj W.complex.obj ⟶
        Ke := ((Etale.affineTraceLineLeft (Ring P) T).map (sourceCoordinates P T r hA Ke).hom ≫
      (adjunction (Ring P) (P.coefficients.l ^ (r + 1)) hA T
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT).counit.app Ke)
  let ap := (augmentation P.coefficients.l P.extension (P.level - 1) T r hA
      (primeUnit P T aT) P.field.k aT K.obj Ke hKe eK)
  have ha := (coordinate_line_augmentation_realization P T aT r hA K Ke hKe eK)
  have hh := specified_transpose_compatible (Ring P) (affineTraceLineCompactification T)
    M W K Ke eK ae ap ha
  have he :
      (exceptionalAdjunction (Ring P) T).homEquiv _ Ke
        ((Etale.affineTraceLineLeft (Ring P) T).map
          (sourceCoordinates P T r hA Ke).hom ≫
          (adjunction (Ring P) (P.coefficients.l ^ (r + 1)) hA T
            (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT).counit.app Ke) =
      (sourceCoordinates P T r hA Ke).hom ≫
        (comparison (Ring P) (P.coefficients.l ^ (r + 1)) hA T
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT).hom.app Ke := by
    rw [Adjunction.homEquiv_naturality_left, comparison_transpose]
  have ht := congrArg (fun z ↦
    (sourceComparison P.coefficients.l P.extension (P.level - 1) T r hA K.obj Ke eK).inv ≫
      (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).map z ≫
      boundedSiteRho (Ring P)
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
          (affineTraceLineCompactification T)).rightAdjoint Ke ≫
      (sfFiniteExceptionalAt (Ring P) (affineTraceLineCompactification T)).map eK.hom) he
  unfold affineLinePurityComparison comparisonFromOrigin comparedConjugate
  dsimp only [sourceWitness]
  exact hh.trans ht

/-- The normalized coordinate-line adjunction, its actual counit, and the precise
pro-etale comparison, at every finite coefficient level and annihilating exponent.
Source: main-20261015, cor-pur-affine-space-zero-section-purity.proof.md,
first sentences and final paragraph (blueprint: lem-pur-coordinate-line-adjunction).

Proof:
1. Polynomial charts give finite-type separated affine projection, standard open
chart and proper projective projection. Finite type over k makes all three schemes
Noetherian of finite dimension. The same applies at every coordinate stage.
2. Write ell=varpi*b in O_E; its level-th power vanishes in A. Any allowed exponent
is invertible on the base. The finite-twist pullback theorem supplies rank-one lines,
their tensor powers and exponent-compatible comparisons with the specified twists.
3. Compose the actual open adjunction with the trace-normalized P1 adjunction.
Exact inverse-image composition and tensor pullback give rightComparison. The
composite-adjunction formula expresses its counit as Rq_* of the open counit,
followed by the normalized projective counit.
4. The open tensor isomorphism identifies the open counit on q*K tensor F with
identity tensor e_F: transpose both maps and use the open triangle identity.
Naturality of the proper projection map with e_F, and factorization of the compact
projection map, then give the displayed inverse-projection tensor integration
formula. Finite Tor of K and bounded constructibility of the Tate line make PF
invertible. Use the specified symmetries; the only shifted line has even shift 2.
5. Conjugate the identity of Rp_! under this adjunction and its Brown right adjoint.
The mates theorem gives a natural isomorphism with component the transpose of the
actual counit; its counit equation fixes the adjunction-preserving normalization.
6. The augmentation-realization lemma carries the actual open/projective counit
through the specified compact-support comparison. Expand the restricted Hom chain;
comparison-adjunction unit naturality and Brown Hom naturality identify its transpose
with comparedConjugate. The comparison unit is invertible on the bounded-below Ke,
so every factor of this map is invertible. This works for each retained representative
in the statement. The exponent lemma identifies the ordinary conjugates in their
actual source coordinates; postcompose with the common unit and representative maps.
The resulting equality is exactly the stipulated exponent compatibility of gamma.
-/
theorem coordinateLineAdjunction (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] :
    CoordinateLineStatement P T aT := by
  have : IsNoetherian T := isNoetherian_of_locallyOfFiniteType aT
  change Geometry T ∧ _
  refine ⟨geometry_of_finiteType P T aT,
    (fun d ↦ geometry_of_finiteType P _ (iteratedAffineLineProj T d ≫ aT)),
    ?_, ?_, level_annihilates P, ?_, ?_, ?_, ?_⟩
  · intro B d
    refine ⟨rfl, ?_, AffineSpace.zeroSection_over _ _⟩
    simp only [Scheme.Hom.toIteratedAffineLine_succ, AffineSpace.zeroSection,
      AffineSpace.comp_homOfVector, Category.comp_id]
    congr 1
    funext i
    exact (map_zero _).symm
  · intro B d i
    exact AffineZeroPurity.coordinate_cartier B d i
  · intro r hA _
    let hT : IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(T, ⊤)) := by
      simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r + 1)
    refine ⟨hT, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact coordinate_line_counit_tensor (Ring P) (P.coefficients.l ^ (r + 1)) hA T
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT
    · exact comparison_counit (Ring P) (P.coefficients.l ^ (r + 1)) hA T
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT
    · exact comparison_transpose (Ring P) (P.coefficients.l ^ (r + 1)) hA T
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT
    · intro K Ke hKe eK
      have he := comparison_realization P T r hA aT hT K Ke hKe eK
      refine ⟨he, ?_⟩
      rw [he]
      exact comparedConjugate_isIso P T r hA hT K Ke hKe eK
  · intro r hA U aU _ _ _
    obtain ⟨_, _, _, h, _⟩ := Scheme.etaleFiniteTwistPullback (Ring P)
      (P.coefficients.l ^ (r + 1)) (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA
    exact h U (by simpa only [Nat.cast_pow] using (primeUnit P U aU).pow (r + 1))
  · exact (twistCompatibility P.coefficients.l P.extension (P.level - 1)).1
  · intro r r' hA hA' hP hX K Ke hKe eK
    let hT : IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(T, ⊤)) := by
      simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r + 1)
    let hT' : IsUnit ((P.coefficients.l ^ (r' + 1) : ℕ) : Γ(T, ⊤)) := by
      simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r' + 1)
    rw [comparison_realization P T r hA aT hT K Ke hKe eK,
      comparison_realization P T r' hA' aT hT' K Ke hKe eK]
    unfold comparedConjugate sourceExponentIso
    have he := coordinate_line_conjugate_exponents P T aT r r' hA hA' hP hX
      K Ke hKe eK
    simpa only [Category.assoc] using congrArg
      (fun z ↦ z ≫ boundedSiteRho (Ring P)
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
          (affineTraceLineCompactification T)).rightAdjoint Ke ≫
        (sfFiniteExceptionalAt (Ring P) (affineTraceLineCompactification T)).map eK.hom) he

end AlgebraicGeometry.ProEtale.CoordinateLine
