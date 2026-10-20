/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.ProEtaleTateTwistsOfUniverses
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
public import Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.TateTwistLocallyFree
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Sheaf.Paper.PurInverseImageCompatibleFreeTower
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-! # Cartesian coefficients and Tate twists

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`sk-prop-sfb-cartesian-coefficients-twists.md`
(blueprint: det-prop-sfb-cartesian-coefficients-twists).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

private theorem comparisonIntoPreservedLimit
    {A B C D J : Type*} [Category A] [Category B] [Category C] [Category D]
    [Category J]
    (U : A ⥤ C) (V : B ⥤ D) (F : C ⥤ D)
    (a : J ⥤ A) (b : J ⥤ B) [HasLimit a] [HasLimit b]
    [PreservesLimit b V] (α : a ⋙ U ⋙ F ⟶ b ⋙ V) :
    ∃! c : F.obj (U.obj (limit a)) ⟶ V.obj (limit b),
      ∀ j, c ≫ V.map (limit.π b j) = F.map (U.map (limit.π a j)) ≫ α.app j := by
  let s : Cone (b ⋙ V) :=
    { pt := F.obj (U.obj (limit a))
      π :=
        { app := fun j ↦ F.map (U.map (limit.π a j)) ≫ α.app j
          naturality := by
            intro i j g
            dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
            rw [Category.id_comp, Category.assoc, ← α.naturality g, ← Category.assoc]
            simp only [Functor.comp_map]
            rw [← F.map_comp, ← U.map_comp, limit.w] } }
  exact (isLimitOfPreserves V (limit.isLimit b)).existsUnique s

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Roots of unity commute with inverse image along every scheme morphism where ell
is invertible, including exponent zero. Source: blueprint Roots of unity paragraph
(blueprint: det-prop-sfb-cartesian-coefficients-twists).
Proof: represent roots by t^(ell^n)-1 over Z[1/ell]. Its derivative is invertible,
so the representing scheme is etale and belongs to the small site. The inverse-image
adjunction, subcanonicity and Yoneda identify its pullback with the corresponding
root scheme over X. This is precisely the adjoint of pullback of units. Multiplication
and power maps commute with base change, giving group and Kummer compatibility.
At n=0 the representing equation is t-1 and both abelian sheaves are zero. -/
theorem spRoots_cartesian (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] (n : ℕ) :
    IsIso (Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ n)) := by
  sorry

/-- The ring-sheaf encoding of alpha is uniquely fixed by its abelian adjunct.
Source: blueprint coefficient compatibility, lem-sfb-alpha-iso
(blueprint: det-prop-sfb-cartesian-coefficients-twists).
Proof: reconstruct section rings from the internal multiplication. The coefficient
adjunct is a ring homomorphism since condensedPullbackHom is monoidal. Lift the
abelian adjunction to ring objects. Its adjunct determines the map uniquely, and
alpha is invertible by lem-sfb-alpha-iso; forgetting reflects isomorphisms. -/
theorem spCoefficientIso_existsUnique
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    ∃! c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology Y)
          (condensedRingObj Λ Y)) ≅
        InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (condensedRingObj Λ X),
      ∀ (V : Y.ProEtᵒᵖ) (a : (condensedRingObj Λ Y).obj.obj V),
        (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
          c.hom).hom.app V a = (condensedPushforwardHom Λ f).hom.app V a := by
  sorry

/-- Alpha, in commutative ring sheaves, selected by its unique adjunct normalization.
Source: blueprint coefficient compatibility
(blueprint: det-prop-sfb-cartesian-coefficients-twists). -/
def spCoefficientIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  Classical.choose (spCoefficientIso_existsUnique f Λ)

private def integralLevelComparison (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} f).obj (spIntegralTwistLevel Y ℓ E n).X ⟶
      (spIntegralTwistLevel X ℓ E n).X :=
  Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f) _ _ ≫
    (condensedPullbackHom (spEllPointRingObj.{u} ℓ E n) f ⊗ₘ
      Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ (n + 1)))

private def integralComparisonSystem (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    spIntegralTwistSystem Y ℓ E ⋙ Mod.forget _ ⋙ upperStar AddCommGrpCat.{u + 1} f ⟶
      spIntegralTwistSystem X ℓ E ⋙ Mod.forget _ :=
    NatTrans.ofOpSequence (integralLevelComparison f ℓ E) (by
      intro n
      simp only [Functor.comp_map, spIntegralTwistSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      change (upperStar AddCommGrpCat.{u + 1} f).map (spIntegralLevelTransition Y ℓ E n).hom ≫ _ =
        _ ≫ (spIntegralLevelTransition X ℓ E n).hom
      have hY := (spIntegralLevelTransition_existsUnique Y ℓ E n).exists.choose_spec
      have hX := (spIntegralLevelTransition_existsUnique X ℓ E n).exists.choose_spec
      change (spIntegralLevelTransition Y ℓ E n).hom = _ at hY
      change (spIntegralLevelTransition X ℓ E n).hom = _ at hX
      rw [hY, hX]
      unfold integralLevelComparison
      rw [← Functor.OplaxMonoidal.δ_natural_assoc (upperStar AddCommGrpCat.{u + 1} f)]
      simp only [Category.assoc]
      apply congrArg (fun k ↦ Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f) _ _ ≫ k)
      simp only [MonoidalCategory.tensorHom_comp_tensorHom]
      apply congrArg₂ (fun a b ↦ a ⊗ₘ b)
      · exact map_coefficientMap_comp_condensedPullbackHom _ _
      · exact (Scheme.proEtaleRootsOfUnityInverseImageIso f).1 _ _ _ _ _)

private theorem integralComparisonSystem_app (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    (integralComparisonSystem f ℓ E).app (op n) = integralLevelComparison f ℓ E n := rfl

/-- The integral comparison is uniquely determined by every finite root projection.
Source: blueprint Integral twist paragraph
(blueprint: det-prop-sfb-cartesian-coefficients-twists).
Proof: tensor the canonical coefficient comparison with the canonical root map,
using the strong monoidal inverse image. These maps commute with reductions and
Kummer transitions. They give a cone on the finite-level system. The forgetful
functor creates its limit, hence the cone has exactly one induced abelian map.
This characterization does not assert preservation of arbitrary inverse limits. -/
theorem spIntegralComparison_existsUnique (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃! c : (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (spIntegralTwist.{u} Y ℓ E).X ⟶ (spIntegralTwist.{u} X ℓ E).X,
      ∀ n : ℕ,
        c ≫ (limit.π (spIntegralTwistSystem X ℓ E) (op n)).hom =
          (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
            (limit.π (spIntegralTwistSystem Y ℓ E) (op n)).hom ≫
          (Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f)
            (condensedRingObj (spEllPointRingObj.{u} ℓ E n) Y)
            (Scheme.proEtaleRootsOfUnitySheaf Y (ℓ ^ (n + 1)))) ≫
          (condensedPullbackHom (spEllPointRingObj.{u} ℓ E n) f ⊗ₘ
            Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ (n + 1))) := by
  let F := upperStar AddCommGrpCat.{u + 1} f
  let UY := Mod.forget (C := Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
    (D := Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) Y)
  let UX := Mod.forget (C := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (D := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) X)
  obtain ⟨c, hc, hu⟩ :=
    comparisonIntoPreservedLimit UY UX F (spIntegralTwistSystem Y ℓ E)
      (spIntegralTwistSystem X ℓ E) (integralComparisonSystem f ℓ E)
  refine ⟨c, ?_, ?_⟩
  · intro n
    change c ≫ UX.map (limit.π (spIntegralTwistSystem X ℓ E) (op n)) =
      F.map (UY.map (limit.π (spIntegralTwistSystem Y ℓ E) (op n))) ≫
        integralLevelComparison f ℓ E n
    rw [← integralComparisonSystem_app]
    exact hc (op n)
  · intro c' hc'
    apply hu c'
    rintro ⟨n⟩
    rw [integralComparisonSystem_app]
    exact hc' n

/-- The integral comparison, with all finite-level projections specified.
Source: blueprint Integral twist paragraph
(blueprint: det-prop-sfb-cartesian-coefficients-twists). -/
def spIntegralComparison (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
      (spIntegralTwist.{u} Y ℓ E).X ⟶ (spIntegralTwist.{u} X ℓ E).X :=
  Classical.choose (spIntegralComparison_existsUnique f ℓ E)

/-- Rational comparison is fixed by the scalar-extension quotient map.
Source: blueprint Rational and algebraically closed coefficients paragraph
(blueprint: det-prop-sfb-cartesian-coefficients-twists).
Proof: the integral comparison is semilinear by its finite projection formulas.
Tensor it with alpha for E. The coefficient square makes the result balanced,
so it descends through the scalar-extension coequalizer. Its epimorphic projection
and preservation of epimorphisms by inverse image give uniqueness. -/
theorem spRationalComparison_existsUnique (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃! c : (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (spRationalTwist.{u} Y ℓ E).X ⟶ (spRationalTwist.{u} X ℓ E).X,
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist.{u} Y ℓ E)) ≫ c =
        Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f)
          (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) Y)
          (spIntegralTwist.{u} Y ℓ E).X ≫
        (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f ⊗ₘ
          spIntegralComparison f ℓ E) ≫
        Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist.{u} X ℓ E) := by
  sorry

/-- The derived twist functor is tensor with the recorded signed line in degree zero.
Its object function is spComplexTwistOfUniverses. Source: blueprint derived consequence
(blueprint: det-prop-sfb-cartesian-coefficients-twists). -/
def spTwistFunctor (Z : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Z) CommRingCat.{u + 1})
    (L : Scheme.proEtaleRingModules Z R) (d : ℤ) :=
  Scheme.tateTensorRight
    (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology Z) R)
    ((DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2}
      (Scheme.proEtaleRingModules Z R) 0).obj
        (WeilConjectures.coefficientTwistLine Z (R := R) L d))

/-- The signed comparisons with their coefficient, tensor and evaluation normalizations.
Here the unit section is the canonical unit of the module pullback adjunction;
thus the formulas determine maps on all inverse-image generators, not just global
sections. Negative powers are normalized by evaluation of the pulled-back functional
on the pulled-back section. Source: blueprint Powers and duals paragraph
(blueprint: det-prop-sfb-cartesian-coefficients-twists). -/
structure SpSignedComparison
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (L : Scheme.proEtaleRingModules Y R) (M : Scheme.proEtaleRingModules X S) where
  signed : ∀ d : ℤ,
    (Scheme.proEtaleRingModulePullback f R S c).obj
        (WeilConjectures.coefficientTwistLine Y (R := R) L d) ≅
      WeilConjectures.coefficientTwistLine X (R := S) M d
  zero : ∀ (V : Y.ProEt) (a : R.obj.obj (op V)),
    (signed 0).hom.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
      (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app
        (WeilConjectures.coefficientTwistLine Y (R := R) L 0)).val.app (op V) a) =
      (Scheme.proEtaleRingDirectImageMap f R S c).hom.app (op V) a
  positive : ∀ (n : ℕ) (V : Y.ProEt) (a : L.val.obj (op V))
    (b : (WeilConjectures.coefficientTwistPower Y L (n + 1)).val.obj (op V)),
    (signed (n + 2)).hom.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
      (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app
        (WeilConjectures.coefficientTwistPower Y L (n + 2))).val.app (op V)
          (SheafOfModules.siteSheafTensorTmul
            (WeilConjectures.coefficientTwistPower Y L (n + 1)) L (op V) b a)) =
      SheafOfModules.siteSheafTensorTmul
        (WeilConjectures.coefficientTwistPower X M (n + 1)) M
        (op ((Scheme.proEtaleBaseChange f).obj V))
        ((signed (n + 1)).hom.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
          (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app
            (WeilConjectures.coefficientTwistPower Y L (n + 1))).val.app (op V) b))
        ((signed 1).hom.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
          (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app L).val.app (op V) a))
  negative : ∀ (n : ℕ) (V : Y.ProEt)
    (φ : (WeilConjectures.coefficientTwistLine Y (R := R) L (Int.negSucc n)).val.obj (op V))
    (a : (WeilConjectures.coefficientTwistPower Y L (n + 1)).val.obj (op V)),
    (((signed (Int.negSucc n)).hom.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
      (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app
        (WeilConjectures.coefficientTwistLine Y (R := R) L (Int.negSucc n))).val.app
          (op V) φ)).app (op (Over.mk (𝟙 ((Scheme.proEtaleBaseChange f).obj V)))))
      ((signed (n + 1)).hom.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app
          (WeilConjectures.coefficientTwistPower Y L (n + 1))).val.app (op V) a)) =
      (Scheme.proEtaleRingDirectImageMap f R S c).hom.app (op V)
        (φ.app (op (Over.mk (𝟙 V))) a)
  derived : ∀ d : ℤ,
    spTwistFunctor Y R L d ⋙ Scheme.proEtaleRingDerivedPullback f R S c ≅
      Scheme.proEtaleRingDerivedPullback f R S c ⋙ spTwistFunctor X S M d

/-- The finite signed comparison is normalized on root tensors, and commutes with
all annihilating-exponent Kummer identifications. Source: blueprint Finite coefficients
and Powers and duals paragraphs
(blueprint: det-prop-sfb-cartesian-coefficients-twists).
Proof: tensor the root comparison with the constant coefficient comparison. The
map sends u tensor a to the pulled-back u tensor the pulled-back a. Pure tensors
locally generate, so this determines it uniquely. The Kummer square is the root
power square. Tensor this comparison for positive powers and use alpha in degree
zero. For negative powers pull back evaluation; finite local freeness makes the
dual comparison invertible. Apply the unbounded derived tensor comparison with
one factor the signed line in degree zero. This gives the natural derived
isomorphism for every K, without any boundedness or constructibility restriction. -/
theorem spFiniteTwists_cartesian (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)]
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∃ β : ∀ (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* A),
      SpSignedComparison f (Scheme.tateFiniteCoefficient Y A)
        (Scheme.tateFiniteCoefficient X A)
        (StrictTower.constantRingIso A f)
        (Scheme.tateFiniteLine Y ℓ A r a) (Scheme.tateFiniteLine X ℓ A r a),
      (∀ (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* A) (V : Y.ProEt)
        (b : (Scheme.tateFiniteCoefficient Y A).obj.obj (op V))
        (z : (Scheme.proEtaleRootsOfUnitySheaf Y (ℓ ^ (r + 1))).obj.obj (op V)),
        (((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _)
          ((β r a).signed 1).hom).val.app (op V)
            (Scheme.tateFiniteTensor Y ℓ A r a V b z) =
          Scheme.tateFiniteTensor X ℓ A r a ((Scheme.proEtaleBaseChange f).obj V)
            ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
              (CommRingCat.of A)).hom.app (op V) b)
            ((Scheme.proEtaleRootsOfUnityDirectImageMap f (ℓ ^ (r + 1))).hom.app
              (op V) z)) ∧
      (∀ (r n : ℕ) (h : r ≤ n) (a : ZMod (ℓ ^ (r + 1)) →+* A),
        (Scheme.proEtaleRingModulePullback f _ _ _).map
          (spFiniteKummer Y ℓ A r n h a) ≫ ((β r a).signed 1).hom =
        ((β n (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ h))
          (ZMod (ℓ ^ (r + 1)))))).signed 1).hom ≫ spFiniteKummer X ℓ A r n h a) := by
  sorry

/-- A comparison over alpha in the internal and sectionwise module encodings.
The signed first comparison has exactly the given abelian adjunct, which fixes
its linear lift; the module isomorphisms encode semilinearity over alpha at every
signed degree. Source: blueprint compatibility with alpha and module structures
(blueprint: det-prop-sfb-cartesian-coefficients-twists). -/
def SpInternalCartesian
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}) (condensedRingObj Λ Y))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) (condensedRingObj Λ X))
    (τ : (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj L.X ⟶ M.X) : Prop :=
  IsIso τ ∧
    ∃ β : SpSignedComparison f
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology Y)
          (condensedRingObj Λ Y))
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (condensedRingObj Λ X)) (spCoefficientIso f Λ)
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) (condensedRingObj Λ Y)).functor.obj L)
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (condensedRingObj Λ X)).functor.obj M),
      ∀ (V : Y.ProEtᵒᵖ) (m : L.X.obj.obj V),
        (((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _)
          (β.signed 1).hom).val.app V m =
        (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _) τ).hom.app
          V m

/-- Inverse image of all non-finite coefficient twists, including integral and rational
Q_ell as the bottom finite subextension, and the algebraic-closure sheafified colimit.
Together with spRoots_cartesian and spFiniteTwists_cartesian this states every
coefficient case in the source. Source: blueprint Inverse image of Tate twists,
Integral twist, Rational and algebraically closed coefficients, Powers and duals,
and Derived consequence paragraphs
(blueprint: det-prop-sfb-cartesian-coefficients-twists).
Proof:
1. The roots comparison is the base change of the etale root scheme; Yoneda fixes
   its adjunct. It commutes with all powers and Kummer transitions.
2. For finite coefficients tensor this root comparison with alpha. Its pure-tensor
   formula commutes with reduction and the annihilating-exponent identifications.
3. Write O_E as the limit of its finite ell-power quotients. The integral coefficient
   limit and coefficient pullback comparisons identify its canonical map with alpha.
   The ell-power and uniformizer-power towers are cofinal since ell=v*pi^e, e>0.
4. A common pro-etale cover with compatible root generators gives compatible free
   bases at every finite quotient. Apply lem-pur-inverse-image-compatible-free-tower
   on its localized site, using lem-weil-proetale-weakly-etale-localization. This makes
   the uniquely projection-normalized integral comparison invertible. The finite
   formulas also give semilinearity over alpha and compatibility with E inclusions.
5. Invert ell by the sequential scalar-multiplication colimit. Inverse image preserves
   it. Thus the uniquely balanced rational comparison is invertible and semilinear.
   Its localization formula gives compatibility with all finite field inclusions.
6. Take the specified sheafified colimit over finite subextensions. The rational
   compatibilities give the colimit comparison, which is invertible because inverse
   image preserves colimits. The common-stage scalar-action formula gives linearity
   over the finite-subextension condensed Qbar coefficient ring, not the full
   continuous-function ring on the topological algebraic closure.
7. At degree zero use alpha. Tensor the first comparison for positive degrees. For
   negative degrees pull back evaluation of the positive line into the coefficient
   unit. The common compatible-generator cover makes each line free of rank one,
   so lem-pur-ringed-site-finite-free-dual-pullback makes this comparison invertible.
   The tensor and evaluation formulas specify the signed comparisons canonically.
8. Since alpha is invertible, module pullback is exact. Its termwise functor on
   unbounded derived categories is f^*. Apply the canonical unbounded derived tensor
   comparison to K and the signed line in degree zero. The result is natural in
   every K and requires no boundedness, constructibility, or finite-Tor condition. -/
theorem spTwists_cartesian (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] :
    ∃ (ρ : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
        (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
          (spRationalTwist.{u} Y ℓ E).X ⟶ (spRationalTwist.{u} X ℓ E).X)
      (κ : (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
          (spQbarTwist.{u} Y ℓ).X ⟶ (spQbarTwist.{u} X ℓ).X),
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist.{u} Y ℓ E)) ≫
        ρ E =
      Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f)
        (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) Y)
        (spIntegralTwist.{u} Y ℓ E).X ≫
      (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f ⊗ₘ
        spIntegralComparison f ℓ E) ≫
      Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist.{u} X ℓ E)) ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (colimit.ι (spRationalTwistDiagram Y ℓ) E) ≫ κ =
        ρ E ≫ colimit.ι (spRationalTwistDiagram X ℓ) E) ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      SpInternalCartesian f (Profinite.padicIntegersRingObj.{u} ℓ E.1)
        (spIntegralTwist.{u} Y ℓ E) (spIntegralTwist.{u} X ℓ E) (spIntegralComparison f ℓ E) ∧
      SpInternalCartesian f (Profinite.continuousMapRingObj.{u} E.1)
        (spRationalTwist.{u} Y ℓ E) (spRationalTwist.{u} X ℓ E) (ρ E)) ∧
    SpInternalCartesian f (Profinite.padicAlgClRingObj.{u} ℓ)
      (spQbarTwist.{u} Y ℓ) (spQbarTwist.{u} X ℓ) κ ∧
    (∀ (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (spIntegralTwistMap Y ℓ h) ≫ spIntegralComparison f ℓ F =
        spIntegralComparison f ℓ E ≫ spIntegralTwistMap X ℓ h) ∧
    (∀ (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (spRationalTwistMap Y ℓ h) ≫ ρ F =
        ρ E ≫ spRationalTwistMap X ℓ h) ∧
    (∀ (n m : ℕ) (h : n ≤ m),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
        (Scheme.proEtaleRootsOfUnityTransition Y (ℓ ^ n) (ℓ ^ m)
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ h)) ≫ Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ n) =
      Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ m) ≫
        Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ n) (ℓ ^ m)
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ h)) := by
  sorry

end AlgebraicGeometry.ProEtale
