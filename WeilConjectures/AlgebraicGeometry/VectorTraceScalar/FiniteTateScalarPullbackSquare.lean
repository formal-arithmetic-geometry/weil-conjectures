/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.SmoothPurity.EtaleFiniteTwistPullbackRest
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceNormalization
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DecompositionMapsSupplement
import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
public import WeilConjectures.AlgebraicGeometry.FiniteP1CoefficientSplitting
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.ScalarSingleAdjointInsertion
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows

/-! # The finite Tate scalar line commutes with geometric pullback

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-vector-bundle-purity.proof.md, paragraph 2, coefficient compatibility
(blueprint: lem-pur-finite-tate-scalar-pullback-square).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale.VectorTraceScalar

private def rootInsertion
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    Scheme.finiteEtaleTateLine T N A hA ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine T N B hB) :=
  (ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _
    (balancing φ N hN hA hB T hT 1).hom

private theorem rootInsertion_generator
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤)))
    (W : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf N).obj.obj W) :
    (rootInsertion φ N hN hA hB T hT).hom.app W
      (Scheme.finiteEtaleTateOneGenerator A N T hA W 1 z) =
    Scheme.finiteEtaleTateOneGenerator B N T hB W 1 z := by
  have hb : IsFiniteTateScalarBalancing φ N hA hB T
      (balancing φ N hN hA hB T hT) := by
    unfold balancing
    exact (Classical.choose_spec
      ((finite_tate_scalar_source_normalization φ N hN hA hB T
        (fun x ↦ by
          simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x trivial).hom)).2.exists)).1
  have hh := hb.1 1 W 1 1 (fun _ ↦ z)
  unfold rootInsertion
  rw [Adjunction.homEquiv_unit]
  change ((balancing φ N hN hA hB T hT 1).hom.hom.app W)
      (((purityScalarSheafAdjunction φ T).unit.app
        (Scheme.finiteEtaleTateTwist T N A hA 1)).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A N T hA W 1 z)) = _
  simpa only [one_smul, map_one, one_mul, id_eq,
    Scheme.finiteTateEtalePowerGenerator] using hh

private def rootDerivedMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    (scalarExtension φ T).obj (ordinaryFiniteLine A N hA T) ⟶
      ordinaryFiniteLine B N hB T :=
  purityScalarSingleMap φ T (Scheme.finiteEtaleTateTwist T N A hA 1) ≫
    (DerivedCategory.singleFunctor _ 0).map (balancing φ N hN hA hB T hT 1).hom

private theorem rootDerivedMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    IsIso (rootDerivedMap φ N hN hA hB T hT) := by
  have ht (x : T) : IsUnit (N : T.presheaf.stalk x) := by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x trivial).hom
  have hf := (Scheme.finite_etale_torsion_twist_line T N hN ht A hA 1).2.2.1
  have := ((finite_tate_scalar_source_normalization φ N hN hA hB T ht).1 _
    ((ObjectProperty.flat_iff_preservesFiniteLimits _).2 hf).2).2
  unfold rootDerivedMap
  infer_instance

private theorem rootDerivedMap_insertion
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    rootDerivedMap φ N hN hA hB T hT =
      p1KummerDerivedInsertion φ T (rootInsertion φ N hN hA hB T hT) := by
  exact FiniteSmoothPurity.scalarSingleMap_eq_scalarInsertion φ T _ _ _

private theorem line_eq_shifted_root
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    line φ N hN hA hB T hT =
      (FiniteSmoothPurity.scalarShiftIso φ T (2 : ℤ)).hom.app _ ≫
        (rootDerivedMap φ N hN hA hB T hT)⟦(2 : ℤ)⟧' := by
  rfl

private theorem rootInsertion_pullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsUnit (N : Γ(X, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB) :
    (upperStar (ModuleCat.{u + 1} A) f).map (rootInsertion φ N hN hA hB Y hY) ≫
        (upperStarRestrictScalarsIsoSheaf φ f).hom.app _ ≫
        (Sheaf.restrictScalars X.smallEtaleTopology φ).map (tB.line f hY).hom =
      (tA.line f hY).hom ≫ rootInsertion φ N hN hA hB X hX := by
  have hr : (tA.roots f hY).hom = (tB.roots f hY).hom := by
    apply (cancel_mono (kernel.ι (N • 𝟙 X.gmSheaf))).mp
    exact (tA.roots_normalization f hY).symm.trans (tB.roots_normalization f hY)
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, restriction_pullback_adjunct,
    Adjunction.homEquiv_naturality_right]
  apply (Scheme.lineHomEquiv Y N A hA _).injective
  ext W z
  simp only [Scheme.lineHomEquiv_generator]
  change (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).homEquiv _ _
      (tB.line f hY).hom).hom.app W)
      ((rootInsertion φ N hN hA hB Y hY).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A N Y hA W 1 z)) =
    (rootInsertion φ N hN hA hB X hX).hom.app
      ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).op.obj W)
      ((((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
        (tA.line f hY).hom).hom.app W)
          (Scheme.finiteEtaleTateOneGenerator A N Y hA W 1 z))
  rw [rootInsertion_generator, tB.line_normalization, tA.line_normalization,
    rootInsertion_generator, hr]

/-- The actual normalized scalar line map commutes with root-normalized shifted
geometric pullback. The transport structures contain the roots-in-G_m and pure-root
normalizations, so they encode the canonical transport without choosing a generator.

Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2; Stacks 0G7E and 07A4
(blueprint: lem-pur-finite-tate-scalar-pullback-square).

Proof:
1. Transpose the published degree-one balancing along the ordinary scalar
   adjunction. Its source-normalization formula sends the root generator
   1 tensor z to 1 tensor z. Flatness of the source Tate line makes the
   derived scalar/single comparison invertible, even when B is not A-flat.
2. Compare the ordinary insertion/pullback maps by the geometric adjunction
   and the root-line Hom equivalence. Both send every root generator to its
   root pullback. The root pullback maps in the two transport structures
   agree after their monomorphism into G_m, hence agree themselves.
3. Identify the degree-zero derived scalar map with the scalar adjunct
   insertion. Apply the proved insertion_pullback calculation of the finite
   P1 coefficient splitting to the ordinary square of Step 2.
4. The actual published line is the scalar shift comparison followed by
   the shifted degree-zero scalar map. Its geometric pullback has the same
   canonical shift/single presentation. Apply the proved shifted_cube
   identity, using scalar_pullback_shift, and cancel the scalar/pullback
   isomorphism. This gives the displayed equality. No boundedness,
   Noetherianity, trace or flatness assumption on B over A was used. -/
theorem finite_tate_scalar_pullback_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsUnit (N : Γ(X, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (scalarExtension φ X).map (ordinaryFiniteShiftedLinePullback A N hA tA f hY).hom ≫
        line φ N hN hA hB X hX =
      (scalarPullbackIso φ f).inv.app ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePullback B f).map (line φ N hN hA hB Y hY) ≫
        (ordinaryFiniteShiftedLinePullback B N hB tB f hY).hom := by
  let : (ordinaryFinitePullback A f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  let : (ordinaryFinitePullback B f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} B) f
  let : (scalarExtension φ Y).CommShift ℤ := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)).leftAdjointCommShift ℤ
  let : (scalarExtension φ X).CommShift ℤ := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).leftAdjointCommShift ℤ
  let : L(upperStar (ModuleCat.{u + 1} A) f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  let : L(upperStar (ModuleCat.{u + 1} B) f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} B) f
  let := scalar_pullback_shift φ f
  let := rootDerivedMap_isIso φ N hN hA hB Y hY
  let := rootDerivedMap_isIso φ N hN hA hB X hX
  have hc := insertion_pullback φ f
    (rootInsertion φ N hN hA hB Y hY) (rootInsertion φ N hN hA hB X hX)
    (asIso (rootDerivedMap φ N hN hA hB Y hY))
    (asIso (rootDerivedMap φ N hN hA hB X hX))
    (rootDerivedMap_insertion φ N hN hA hB Y hY)
    (rootDerivedMap_insertion φ N hN hA hB X hX)
    (tA.line f hY).hom (tB.line f hY).hom
    (rootInsertion_pullback φ N hN hA hB f hX hY tA tB)
  have hs := NatTrans.shift_app_comm (scalarPullbackIso φ f).hom (2 : ℤ)
    (ordinaryFiniteLine A N hA Y)
  simp only [Functor.commShiftIso_comp_hom_app] at hs
  have hh := shifted_cube (scalarExtension φ Y) (ordinaryFinitePullback A f)
    (ordinaryFinitePullback B f) (scalarExtension φ X) (scalarPullbackIso φ f)
    (rootDerivedMap φ N hN hA hB Y hY)
    ((ordinaryFiniteSinglePullbackIso B f).hom.app _ ≫
      (ordinaryFiniteSingleFunctor B X).map (tB.line f hY).hom)
    ((ordinaryFiniteSinglePullbackIso A f).hom.app _ ≫
      (ordinaryFiniteSingleFunctor A X).map (tA.line f hY).hom)
    (rootDerivedMap φ N hN hA hB X hX) 2 hc.symm (by
      simpa only [ordinaryFinitePullback, Category.assoc] using hs)
  have hx : (scalarExtension φ X).commShiftIso (2 : ℤ) =
      FiniteSmoothPurity.scalarShiftIso φ X (2 : ℤ) := rfl
  have hy : (scalarExtension φ Y).commShiftIso (2 : ℤ) =
      FiniteSmoothPurity.scalarShiftIso φ Y (2 : ℤ) := rfl
  apply (cancel_epi ((scalarPullbackIso φ f).hom.app
    ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧))).mp
  simpa only [ordinaryFiniteShiftedLinePullback_eq, line_eq_shifted_root,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, hx, hy, ordinaryFiniteLine, ordinaryFiniteSingleFunctor_eq,
    ordinaryFiniteDegreeZero, ordinaryFinitePullback,
    Iso.hom_inv_id_app_assoc] using hh.symm

end AlgebraicGeometry.Etale.VectorTraceScalar
