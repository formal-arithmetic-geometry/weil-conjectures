/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.PurityDncInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.DiagonalOrientationCharts
public import Sheaf.Paper.VectorBundleDiagonalOrientation
public import Sheaf.Paper.PurityDncFamilyIntrinsic
public import Sheaf.Paper.PurityNormalProjection
public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.PurityDiagonalDualizingObject
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Retagging and normalized coordinate orientations

Source: main-20261015, sec-six-functors/sk-thm-sf-package,
thm-pur-weil-equivariance-of-purity-and-trace.proof.md, Step 1
(blueprint: lem-pur-retagging-coordinate-orientations).

Retagging postcomposes only the structural map with Spec(sigma). All comparisons
use the same underlying compactification and its counit-normalized adjoint. The
finite coefficient setting at the bottom intermediate field is Z/ell^m, m >= 1.
No generator of a Tate line or arbitrary purity isomorphism is an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- The ancillary section/DNC assertion, evaluated below on the relative diagonal.
The displayed family and fibre comparisons are the recorded actual constructions.
The last line selects the unique coordinate-normalized DNC arrow, so no unspecified
isomorphism is chosen. Source: equivariance proof Step 1, diagonal and Rees comparison
(blueprint: lem-pur-retagging-coordinate-orientations). -/
def RetaggingSectionConclusion (P : PurityFiniteSetting.{u})
    (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k)
    {W B : Scheme.{u}} (d : ℕ) (g : W ⟶ B)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ W) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) : Prop :=
  let aBσ := aB ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)
  letI := SmoothOfRelativeDimension.smooth d g
  (purityDncIntrinsicSource P g aBσ s).left =
      (purityDncIntrinsicSource P g aB s).left ∧
  HEq (purityDncIntrinsicMap P g aBσ s).left
      (purityDncIntrinsicMap P g aB s).left ∧
  HEq (purityDncIntrinsicSection P g aBσ s hs).left
      (purityDncIntrinsicSection P g aB s hs).left ∧
  HEq (P.sectionInvariantFinite g aBσ s hs) (P.sectionInvariantFinite g aB s hs) ∧
  HEq (purityDncIntrinsicFamily P g aBσ s hs)
      (purityDncIntrinsicFamily P g aB s hs) ∧
  HEq (Dnc.normalSection P d g aBσ s hs) (Dnc.normalSection P d g aB s hs) ∧
  HEq (Dnc.fibreOne P d g aBσ s hs) (Dnc.fibreOne P d g aB s hs) ∧
  HEq (Dnc.fibreZero P d g aBσ s hs) (Dnc.fibreZero P d g aB s hs) ∧
  HEq (Dnc.existsUnique_dncInvariance P d g aBσ s hs).exists.choose
      (Dnc.existsUnique_dncInvariance P d g aB s hs).exists.choose

/-- The comparison of integration-normalized orientations on a specified bundle.
This predicate is used only on presentations of the diagonal normal bundle below.
It retains the actual integration-adjunction equation on both field presentations.
Source: equivariance proof Step 1 and diagonal orientation of a vector bundle
(blueprint: lem-pur-retagging-coordinate-orientations). -/
def RetaggingVectorOrientationConclusion (P : PurityFiniteSetting.{u})
    (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
  letI : IsNoetherian B := isNoetherian_of_locallyOfFiniteType aB
  letI : IsAffineHom (VectorBundleZeroSection.π B d F) :=
    (Etale.vectorIntegration_geometry B d F).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π B d F) :=
    (Etale.vectorIntegration_geometry B d F).2.1
  letI := vectorBundleDiagonalProjection_smooth B d F
  P.VectorBundleDiagonalOrientationConclusion B aB d F ∧
  P.VectorBundleDiagonalOrientationConclusion B
      (aB ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) d F ∧
  HEq (P.diagonalDualizingObject d (VectorBundleZeroSection.π B d F)
      (aB ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))).hom
    (P.diagonalDualizingObject d (VectorBundleZeroSection.π B d F) aB).hom

/-- Every clause of the local retagging assertion. The map e is an etale V-map;
its displayed equation says exactly that U lies over V. The normal-bundle clause
quantifies over its vector-bundle presentations, not over independent orientations.
The equality is of derived morphisms in the fixed pro-etale coefficient category.
Source: equivariance proof Step 1, local normalized orientation comparison
(blueprint: lem-pur-retagging-coordinate-orientations). -/
def RetaggingCoordinateOrientationsConclusion (P : PurityFiniteSetting.{u})
    (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k)
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
    (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (V : Y.Opens) (_hV : IsAffineOpen V) (U : X.Opens)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.toScheme) [Etale e]
    (_w : e ≫ (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme) ≫ V.ι =
      U.ι ≫ f) : Prop :=
  let aYσ := aY ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI := isNoetherian_of_locallyOfFiniteType aX
  letI : HasCompactification f := inferInstance
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.ι).leftDerivedFunctor.map
      (P.diagonalDualizingObject d f aYσ).hom =
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.ι).leftDerivedFunctor.map
      (P.diagonalDualizingObject d f aY).hom ∧
  P.RetaggingSectionConclusion σ d (pullback.fst f f) aX
    (pullback.diagonal f) (pullback.diagonal_fst f) ∧
  (∀ (F : X.Modules) [F.IsFiniteLocallyFreeOfRank d]
      (φ : VectorBundleZeroSection.scheme X d F ≅ (pullback.diagonal f).ker.normalCone),
      φ.hom ≫ Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f) =
        VectorBundleZeroSection.π X d F →
      P.RetaggingVectorOrientationConclusion σ X aX d F) ∧
  (∀ T : Over (Spec (.of P.field.k)),
    HEq (proEtaleRootsOfUnityTower
        ((Over.map (Spec.map (CommRingCat.ofHom σ.toRingHom))).obj T).left
        P.coefficients.l P.coefficients.prime.out)
      (proEtaleRootsOfUnityTower T.left P.coefficients.l P.coefficients.prime.out))

/-- The normalization uses the structure map only to prove invertibility of the
coefficient exponent. These witnesses are propositions, so the normalization
predicate is unchanged. Transfer the chosen witness and apply uniqueness. -/
private theorem diagonalOrientation_structure_independent (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (a₁ a₂ : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a₁] [QuasiCompact a₁]
    [LocallyOfFiniteType a₂] [QuasiCompact a₂] :
    P.diagonalDualizingObject d f a₁ = P.diagonalDualizingObject d f a₂ := by
  let := isNoetherian_of_locallyOfFiniteType a₁
  let := isNoetherian_of_locallyOfFiniteType (f ≫ a₁)
  let : HasCompactification f := inferInstance
  obtain ⟨e, hn, he⟩ := (P.existsUnique_diagonalDualizingObject d f a₁).exists.choose_spec
  apply (P.existsUnique_diagonalDualizingObject d f a₂).unique
  · refine ⟨e, ?_, he⟩
    exact hn
  · exact (P.existsUnique_diagonalDualizingObject d f a₂).exists.choose_spec

/-- Retag every test base in the normalization equation. The underlying pullback,
family and fibre maps agree definitionally, and the test morphism is still over
the field by associativity. Uniqueness then identifies the chosen DNC arrows. -/
private theorem dnc_retagging (P : PurityFiniteSetting.{u})
    (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k)
    {W B : Scheme.{u}} (d : ℕ) (g : W ⟶ B)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ W) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    HEq (Dnc.existsUnique_dncInvariance P d g
        (aB ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) s hs).exists.choose
      (Dnc.existsUnique_dncInvariance P d g aB s hs).exists.choose := by
  classical
  apply heq_of_eq
  apply (Dnc.existsUnique_dncInvariance P d g aB s hs).unique
  · intro B' aB' _ _ _ b hb C₀ e
    have hbσ : b ≫ (aB ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) =
        aB' ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
      rw [← Category.assoc, hb]
    exact (Dnc.existsUnique_dncInvariance P d g
      (aB ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) s hs).exists.choose_spec
        B' (aB' ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) b hbσ C₀ e
  · exact (Dnc.existsUnique_dncInvariance P d g aB s hs).exists.choose_spec

/-- Retagging identifies the actual normalized diagonal orientations on coordinate charts.
Source: main-20261015, thm-pur-weil-equivariance-of-purity-and-trace.proof.md, Step 1
(blueprint: lem-pur-retagging-coordinate-orientations).

Proof:
1. The defining normalization of diagonalDualizingObject depends on the field
   structure only through proofs of Noetherianity and exponent invertibility.
   Its ordinary normalized witness therefore also satisfies the normalization
   for the retagged structure. Uniqueness identifies the actual isomorphisms.
   Apply derived pullback to their hom equality on U.
2. The underlying Rees source, projection and augmentation are definitionally
   unchanged. Section invariants, the family and both fibre comparisons likewise
   depend on the field structure only through proof-irrelevant domain witnesses.
3. To compare the chosen DNC isomorphisms, evaluate the retagged normalization
   on the retagging of every test base B'. The equation b ≫ aB = aB' remains
   true after postcomposition with Spec(sigma). The unchanged family and fibre
   comparisons give the original normalization, so DNC uniqueness applies.
4. Apply vectorBundleDiagonalOrientation to both field presentations. The first
   uniqueness argument identifies their hom arrows, retaining both actual
   integration-transpose equations. No chosen frame or Tate generator is needed.
5. Retagging leaves the underlying scheme of every Over object definitionally
   unchanged, so its actual roots-of-unity tower, including power transitions,
   is the same. All arguments include empty schemes and rank zero. -/
theorem retagging_coordinate_orientations (P : PurityFiniteSetting.{u})
    (_hE : P.extension = ⊥) (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k)
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
    (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] (_hf : f ≫ aY = aX)
    (V : Y.Opens) (hV : IsAffineOpen V) (U : X.Opens)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.toScheme) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme) ≫ V.ι =
      U.ι ≫ f) :
    P.RetaggingCoordinateOrientationsConclusion σ aX aY d f V hV U e w := by
  classical
  let := isNoetherian_of_locallyOfFiniteType aX
  let := isNoetherian_of_locallyOfFiniteType aY
  dsimp only [RetaggingCoordinateOrientationsConclusion]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact congrArg
      (fun θ ↦ (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        U.ι).leftDerivedFunctor.map θ.hom)
      (diagonalOrientation_structure_independent P d f
        (aY ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) aY)
  · dsimp only [RetaggingSectionConclusion]
    exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl,
      dnc_retagging P σ d (pullback.fst f f) aX
        (pullback.diagonal f) (pullback.diagonal_fst f)⟩
  · intro F _ _φ _hφ
    let : IsAffineHom (VectorBundleZeroSection.π X d F) :=
      (Etale.vectorIntegration_geometry X d F).1
    let : LocallyOfFiniteType (VectorBundleZeroSection.π X d F) :=
      (Etale.vectorIntegration_geometry X d F).2.1
    let := vectorBundleDiagonalProjection_smooth X d F
    dsimp only [RetaggingVectorOrientationConclusion]
    refine ⟨P.vectorBundleDiagonalOrientation _hE X aX d F,
      P.vectorBundleDiagonalOrientation _hE X
        (aX ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) d F, ?_⟩
    exact heq_of_eq (congrArg Iso.hom
      (diagonalOrientation_structure_independent P d (VectorBundleZeroSection.π X d F)
        (aX ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) aX))
  · intro T
    exact HEq.rfl

end WeilConjectures.PurityFiniteSetting
