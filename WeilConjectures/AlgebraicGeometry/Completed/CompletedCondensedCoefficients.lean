/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Types.Filtered
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.EssentiallySmall
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.Topology.Algebra.Ring.Compact
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import all WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import all Mathlib.Topology.Category.Profinite.AsLimit
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import all WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all Mathlib.Algebra.Ring.Subring.Basic
import all Mathlib.Algebra.Ring.Pi
import all Mathlib.Topology.Homeomorph.Defs
import all Mathlib.Topology.Connected.TotallyDisconnected
import all Mathlib.Topology.Compactness.Compact
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.Topology.Homeomorph.Lemmas
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import all Mathlib.AlgebraicGeometry.Limits
import all Mathlib.CategoryTheory.FintypeCat
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.CategoryTheory.Limits.Presheaf
import all Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.CategoryTheory.Sites.LocallySurjective
import all Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.SixFunctors.IntegralModelsGenerators

/-!
# Comparison with completed condensed coefficients

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-sfb-qlbar-colimit-x, the three comparisons and inverse-image compatibility
(blueprint: sk-prop-sfb-qlbar-colimit-x).

The comparisons are expressed by universal properties of the specified reduction maps
and localization cocone. Thus no choice of an unrelated isomorphism is involved.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

/-- Pull back an actual condensed ring homomorphism, including all its ring structure.
Source: blueprint comparison with completed coefficients, its canonical maps
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedCoefficientMap (X : Scheme.{u})
    {R S : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}} (f : R ⟶ S) :
    completedCoefficient X R ⟶ completedCoefficient X S :=
  (sfbPullbackFromPoint X).mapMon.map
    (Mon.Hom.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map f))

/-- The existing finite-field diagram, bundled with its ring homomorphisms.
Source: blueprint comparison with completed coefficients, third comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedPointSubfieldDiagram (l : ℕ) [Fact l.Prime] :
    PadicAlgCl.FiniteIntermediateField l ⥤
      Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) where
  obj E := Mon.mk (Profinite.continuousMapRingObj E)
  map f := Mon.Hom.mk (Profinite.padicSubfieldRingObjMap l (leOfHom f))
  map_id E := Mon.Hom.ext (Profinite.padicSubfieldRingObjMap_id l E)
  map_comp f g := Mon.Hom.ext (Profinite.padicSubfieldRingObjMap_comp l
    (leOfHom f) (leOfHom g))

/-- The existing canonical algebraic-closure cocone, bundled in ring objects.
Source: blueprint comparison with completed coefficients, third comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedPointSubfieldCocone (l : ℕ) [Fact l.Prime] :
    Cocone (completedPointSubfieldDiagram.{u} l) where
  pt := Mon.mk (Profinite.padicAlgClRingObj l)
  ι := {
    app E := Mon.Hom.mk (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
    naturality _E _F f := Mon.Hom.ext
      ((Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl l (leOfHom f)).trans
        (Category.comp_id _).symm) }

/-- The canonical ring cocone on a scheme is the image of the point cocone under p_X^*.
Source: blueprint comparison with completed coefficients, third comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedSubfieldCocone (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] :=
  (sfbPullbackFromPoint X).mapMon.mapCocone (completedPointSubfieldCocone l)

open CategoryTheory.MonObj CategoryTheory.MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def siftedRingCoconeIsColimit
    {C : Type*} [Category C] [MonoidalCategory C]
    {J : Type*} [Category J] [IsSifted J]
    {D : J ⥤ Mon C} (c : Cocone D)
    (hc : IsColimit ((Mon.forget C).mapCocone c))
    [PreservesColimit₂ (D ⋙ Mon.forget C) (D ⋙ Mon.forget C) (curriedTensor C)] :
    IsColimit c := by
  let desc (s : Cocone D) : c.pt ⟶ s.pt := by
    let d : c.pt.X ⟶ s.pt.X := hc.desc ((Mon.forget C).mapCocone s)
    have hd (j : J) : (c.ι.app j).hom ≫ d = (s.ι.app j).hom :=
      hc.fac ((Mon.forget C).mapCocone s) j
    have : IsMonHom d := by
      constructor
      · obtain ⟨j⟩ := IsSifted.nonempty (C := J)
        rw [← IsMonHom.one_hom (c.ι.app j).hom, Category.assoc, hd j]
        exact IsMonHom.one_hom (s.ι.app j).hom
      · apply (hc.tensor hc).hom_ext
        intro j
        change ((c.ι.app j).hom ⊗ₘ (c.ι.app j).hom) ≫ μ[c.pt.X] ≫ d =
          ((c.ι.app j).hom ⊗ₘ (c.ι.app j).hom) ≫ (d ⊗ₘ d) ≫ μ[s.pt.X]
        rw [← IsMonHom.mul_hom_assoc, hd j,
          tensorHom_comp_tensorHom_assoc, hd j]
        exact IsMonHom.mul_hom (s.ι.app j).hom
    exact Mon.Hom.mk d
  refine { desc := desc, fac := ?_, uniq := ?_ }
  · intro s j
    apply Mon.Hom.ext
    exact hc.fac ((Mon.forget C).mapCocone s) j
  · intro s m hm
    apply Mon.Hom.ext
    apply hc.hom_ext
    intro j
    exact (congrArg Mon.Hom.hom (hm j)).trans
      (hc.fac ((Mon.forget C).mapCocone s) j).symm

namespace CondensedRing
attribute [local irreducible] pointUpperStarLowerStarAdjunction
  ProEtale.upperStarLowerStarAdjunction
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

section

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

private noncomputable abbrev coefficientPresheaf (R : Type) [TopologicalSpace R]
    [Ring R] [IsTopologicalRing R] : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  Profinite.continuousMapRingPresheaf R ⋙ forget₂ RingCat Ab

private noncomputable abbrev integralPresheafMap :
    coefficientPresheaf.{u} (continuousIntegers ℓ E) ⟶ coefficientPresheaf E :=
  Functor.whiskerRight
    (Profinite.continuousMapRingPresheafMap (continuousIntegers ℓ E).subtype
      continuous_subtype_val) (forget₂ RingCat Ab)

private noncomputable def localizationLegHom (n : ℕ) :
    coefficientPresheaf.{u} (continuousIntegers ℓ E) ⟶ coefficientPresheaf E where
  app S := AddCommGrpCat.ofHom
    { toFun x := ULift.up
        (⟨fun s ↦ (x.down s : E) / (ℓ : E) ^ n,
          (continuous_subtype_val.comp x.down.continuous).div_const _⟩ : C(S.unop, E))
      map_zero' := by apply ULift.ext; ext; simp
      map_add' x y := by
        apply ULift.ext
        ext s
        change ((x.down s : E) + (y.down s : E)) / (ℓ : E) ^ n =
          (x.down s : E) / (ℓ : E) ^ n + (y.down s : E) / (ℓ : E) ^ n
        exact add_div _ _ _ }
  naturality _ _ _ := rfl

private noncomputable def localizationLeg (n : ℕ) :
    Mod.regular (coefficientPresheaf.{u} (continuousIntegers ℓ E)) ⟶
      (Mod.comap (integralPresheafMap ℓ E)).obj (Mod.regular (coefficientPresheaf E)) :=
  Mod.homMk (localizationLegHom ℓ E n) (by
    ext S : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro a b
    apply ULift.ext
    ext x
    change ((a.down x : E) * (b.down x : E)) / (ℓ : E) ^ n =
      (a.down x : E) * ((b.down x : E) / (ℓ : E) ^ n)
    exact mul_div_assoc _ _ _)

private noncomputable abbrev localizationSequence :
    ℕ ⥤ Mod (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
      (coefficientPresheaf (continuousIntegers ℓ E)) :=
  Functor.ofSequence (fun _ ↦ ℓ • 𝟙 (Mod.regular
    (coefficientPresheaf (continuousIntegers ℓ E))))

private noncomputable def localizationCocone : Cocone (localizationSequence.{u} ℓ E) where
  pt := (Mod.comap (integralPresheafMap ℓ E)).obj (Mod.regular (coefficientPresheaf E))
  «ι» := NatTrans.ofSequence (localizationLeg ℓ E) (by
    intro n
    simp only [localizationSequence, Functor.ofSequence_map_homOfLE_succ,
      Functor.const_obj_map]
    apply Mod.hom_ext
    ext S x
    apply ULift.ext
    ext s
    change (continuousIntegers ℓ E).subtype (ℓ • x.down s) / (ℓ : E) ^ (n + 1) =
      (x.down s : E) / (ℓ : E) ^ n
    rw [map_nsmul, nsmul_eq_mul, pow_succ]
    field_simp [ell_ne_zero ℓ E]
    rfl)

private noncomputable def localizationCoconeIsColimit :
    IsColimit (localizationCocone.{u} ℓ E) := by
  let := Functor.functorCategoryMonoidalClosed Profinite.{u}ᵒᵖ Ab.{u + 1}
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  have : ReflectsColimitsOfShape ℕ (forget Ab.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : ReflectsColimitsOfShape ℕ
      (Mod.forget (D := Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
        (coefficientPresheaf (continuousIntegers ℓ E))) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (Mod.forget (D := Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
    (coefficientPresheaf (continuousIntegers ℓ E)))
  refine evaluationJointlyReflectsColimits _ fun S ↦
    isColimitOfReflects (forget Ab.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    let φ := (continuousIntegers ℓ E).subtype.compLeftContinuous S.unop continuous_subtype_val
    let := φ.toAlgebra
    have hloc := continuousIntegralFunctions_isLocalization ℓ E S.unop
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj
      (ContinuousMap.const S.unop (ℓ : continuousIntegers ℓ E)) x.down
    refine ⟨n, ULift.up a, ?_⟩
    apply ULift.ext
    ext s
    change x.down s = (a s : E) / (ℓ : E) ^ n
    have ha' := congrArg (fun f : C(S.unop, E) ↦ f s) ha
    change x.down s * (ℓ : E) ^ n = (a s : E) at ha'
    exact (eq_div_iff (pow_ne_zero n (ell_ne_zero ℓ E))).2 ha'
  · intro n x y h
    have hxy : x = y := by
      apply ULift.ext
      apply ContinuousMap.ext
      intro s
      apply Subtype.ext
      have h' := congrArg (fun f : ULift.{u + 1} C(S.unop, E) ↦ f.down s) h
      change (x.down s : E) / (ℓ : E) ^ n = (y.down s : E) / (ℓ : E) ^ n at h'
      exact (div_left_inj' (pow_ne_zero n (ell_ne_zero ℓ E))).mp h'
    subst y
    exact ⟨n, 𝟙 n, rfl⟩

private noncomputable def pointCoefficientIso (R : Type) [TopologicalSpace R]
    [Ring R] [IsTopologicalRing R] :
    (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (coefficientPresheaf R) ≅ Profinite.continuousMapRingObj R :=
  Sheaf.sheafifyRingPresheafIso (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheaf R)

private noncomputable abbrev schemeCoefficientFunctor (X : Scheme.{u}) :=
  presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ upperStarFromPoint X

private noncomputable def schemeCoefficientIso (X : Scheme.{u})
    (R : Type) [TopologicalSpace R] [Ring R] [IsTopologicalRing R] :
    (schemeCoefficientFunctor X).obj (coefficientPresheaf R) ≅
      condensedRingObj (Profinite.continuousMapRingObj R) X :=
  (upperStarFromPoint X).mapIso (pointCoefficientIso R)

end

attribute [local irreducible] localizationCoconeIsColimit

attribute [local irreducible] schemeCoefficientIso pointCoefficientIso

end CondensedRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- The underlying limit determines the unit and multiplication of every lift.

-- Positive quotient levels avoid any special convention at the trivial level.

-- Compact nested fibres give existence; joint injectivity gives uniqueness.

-- Preserve the represented tower, rather than arbitrary limits of inverse images.

-- Use the explicit constant-function map to retain naturality in coefficient maps.

/-- The canonical finite-subextension cocone is a colimit in ring objects.
Source: blueprint comparison with completed coefficients, third display
(blueprint: sk-prop-sfb-qlbar-colimit-x).

Proof: A section of the condensed algebraic closure belongs to some finite subfield.
A compatible family of additive maps therefore glues uniquely, independently of the
chosen field because two fields lie in a common finite compositum. Pullback from the
point preserves this colimit, being a left adjoint. The descended map preserves the
unit at the base field. For multiplication, tensor preserves colimits in each variable;
compare on E_X tensor F_X and pass to a common finite compositum H. Both restrictions
are multiplicative there. Additive uniqueness then proves uniqueness as a ring map.
These are steps 3--5 of the node's proof.
-/
theorem completedCondensedAlgebraicClosure (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] :
    Nonempty (IsColimit (completedSubfieldCocone X l)) := by
  have : IsSifted (PadicAlgCl.FiniteIntermediateField l) := IsFiltered.isSifted
  refine ⟨siftedRingCoconeIsColimit _ ?_⟩
  change IsColimit (padicAlgClRingObjCocone X l)
  exact isColimitPadicAlgClRingObjCocone X l

end AlgebraicGeometry.ProEtale
