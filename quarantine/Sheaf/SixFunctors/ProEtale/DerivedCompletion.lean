/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.DerivedNakayamaResolution
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import Sheaf.CategoryTheory.SheafTensorStructure
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Algebra.Homology.KFlatRoosRepresentativeInvariance
import Sheaf.Paper.ProfinitePointPullback
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Topology.ProfiniteCondensedRing

/-!
# Derived completion for pulled-back continuous integral coefficients

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-def-pe-derived-completion/_section.md` (blueprint: sk-def-pe-derived-completion).

The coefficient objects are the continuous condensed rings of DerivedNakayama,
pulled back by the published strong monoidal inverse image from the point.
Positive level n is indexed by n-1. Completion uses the explicit augmented Roos
complex on a K-flat representative, with zero homotopy in its second coordinate.
Normalization uses extension of scalars over the successive finite coefficient rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.AdicCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The continuous integral coefficient ring pulled back from the point.
Source: blueprint, coefficient sheaves (blueprint: sk-def-pe-derived-completion). -/
abbrev ring (X : Scheme.{u}) := condensedRingObj (DerivedNakayama.integerRing l E) X

/-- Internal modules over the completed continuous coefficient ring.
Source: blueprint, ambient category (blueprint: sk-def-pe-derived-completion). -/
abbrev Modules (X : Scheme.{u}) := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (ring l E X)

/-- The continuous finite quotient ring at the positive level n+1.
Source: blueprint, finite coefficient sheaves (blueprint: sk-def-pe-derived-completion). -/
abbrev finiteRing (X : Scheme.{u}) (n : ℕ) :=
  condensedRingObj (DerivedNakayama.quotientRing l E (n + 1)) X

/-- Commutativity of the continuous finite quotient ring, before pullback.
Source: blueprint, coefficient sheaves (blueprint: sk-def-pe-derived-completion). -/
instance quotientRing_isCommMonObj (n : ℕ) :
    IsCommMonObj (DerivedNakayama.quotientRing l E n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.isCommMonObj_continuousCoefficientRingObj _

/-- The actual quotient morphism pulled back from the point.
Source: blueprint, reduction cone (blueprint: sk-def-pe-derived-completion). -/
abbrev quotient (X : Scheme.{u}) (n : ℕ) : ring l E X ⟶ finiteRing l E X n :=
  (upperStarFromPoint X).map (DerivedNakayama.reductionRing l E (n + 1))

/-- The quotient topology induced by the spectral topology on the finite extension.
Source: blueprint, continuous coefficient rings (blueprint: sk-def-pe-derived-completion). -/
abbrev finiteTopology (n : ℕ) : TopologicalSpace (Padic.coefficientExtensionRing l E n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  inferInstance

/-- The quotient transition is continuous for the quotient topologies.
Source: blueprint, reduction identities (blueprint: sk-def-pe-derived-completion).
Proof: the quotient map O_E to O_E/pi^(n+2) is a quotient map. Its composite
with the displayed factor is the continuous quotient map to O_E/pi^(n+1),
so the quotient universal property proves continuity. -/
theorem continuous_transition (n : ℕ) :
    @Continuous _ _ (finiteTopology l E (n + 2)) (finiteTopology l E (n + 1))
      (Padic.coefficientExtensionTransition l E (n + 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact continuous_quot_lift _ continuous_quot_mk

/-- Continuous postcomposition with the specified quotient transition.
Source: blueprint, canonical transitions (blueprint: sk-def-pe-derived-completion). -/
def transitionRingSheaf (n : ℕ) :
    DerivedNakayama.quotientRingSheaf l E (n + 2) ⟶
      DerivedNakayama.quotientRingSheaf l E (n + 1) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ⟨{
    app := fun _ ↦ RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (((Padic.coefficientExtensionTransition l E (n + 1)).compLeftContinuous _
        (continuous_transition l E n)).comp ULift.ringEquiv.toRingHom))
    naturality := fun _ _ _ ↦ rfl }⟩

/-- The same quotient transition as a morphism of internal condensed rings.
Source: blueprint, canonical transitions (blueprint: sk-def-pe-derived-completion). -/
abbrev transitionRing (n : ℕ) :
    DerivedNakayama.quotientRing l E (n + 2) ⟶
      DerivedNakayama.quotientRing l E (n + 1) :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (transitionRingSheaf l E n)

/-- The transition between the pulled-back finite ring objects.
Source: blueprint, canonical transitions (blueprint: sk-def-pe-derived-completion). -/
abbrev transition (X : Scheme.{u}) (n : ℕ) : finiteRing l E X (n + 1) ⟶
    finiteRing l E X n := (upperStarFromPoint X).map (transitionRing l E n)

private theorem restricted_linear {C : Type*} [Category C] [MonoidalCategory C]
    {R S T : C} [MonObj S] [MonObj T] (q : R ⟶ S) (r : R ⟶ T)
    (f : S ⟶ T) [IsMonHom f] (h : q ≫ f = r) :
    (q ▷ S ≫ μ[S]) ≫ f = R ◁ f ≫ (r ▷ T ≫ μ[T]) := by
  simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_def']
  rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc, h]

/-- Quotient and transition maps preserve the scalar action on the regular module.
Source: blueprint, construction of the reduction cone
(blueprint: sk-def-pe-derived-completion).
Proof: a ring homomorphism sends ab to its image product. In the transition equation,
the composite O_E to the smaller quotient equals the direct quotient. Apply these
identities to continuous functions pointwise; naturality and inverse image preserve them. -/
theorem coefficient_linearity :
    (∀ n : ℕ, Mod.act (Mod.regular (DerivedNakayama.integerRing l E)).X ≫
        DerivedNakayama.reductionRing l E (n + 1) =
      DerivedNakayama.integerRing l E ◁ DerivedNakayama.reductionRing l E (n + 1) ≫
        Mod.act (DerivedNakayama.quotientModule l E (n + 1)).X) ∧
    (∀ n : ℕ, Mod.act (DerivedNakayama.quotientModule l E (n + 2)).X ≫
        transitionRing l E n =
      DerivedNakayama.integerRing l E ◁ transitionRing l E n ≫
        Mod.act (DerivedNakayama.quotientModule l E (n + 1)).X) := by
  constructor
  · intro n
    change μ[DerivedNakayama.integerRing l E] ≫
      DerivedNakayama.reductionRing l E (n + 1) =
      DerivedNakayama.integerRing l E ◁ DerivedNakayama.reductionRing l E (n + 1) ≫
        (DerivedNakayama.reductionRing l E (n + 1) ▷
          DerivedNakayama.quotientRing l E (n + 1) ≫ μ[_])
    simpa only [tensorHom_def', Category.assoc] using
      (IsMonHom.mul_hom (DerivedNakayama.reductionRing l E (n + 1)))
  · intro n
    exact restricted_linear (DerivedNakayama.reductionRing l E (n + 2))
      (DerivedNakayama.reductionRing l E (n + 1)) (transitionRing l E n) (by rfl)

/-- The actual unit quotient map as an integral-module morphism on the point.
Source: blueprint, unit of the reduction cone (blueprint: sk-def-pe-derived-completion). -/
def quotientUnit (n : ℕ) : Mod.regular (DerivedNakayama.integerRing l E) ⟶
    DerivedNakayama.quotientModule l E (n + 1) :=
  Mod.homMk (DerivedNakayama.reductionRing l E (n + 1))
    ((coefficient_linearity l E).1 n)

/-- The actual transition as an integral-module morphism on the point.
Source: blueprint, canonical transitions (blueprint: sk-def-pe-derived-completion). -/
def quotientStep (n : ℕ) : DerivedNakayama.quotientModule l E (n + 2) ⟶
    DerivedNakayama.quotientModule l E (n + 1) :=
  Mod.homMk (transitionRing l E n) ((coefficient_linearity l E).2 n)

/-- The pulled-back finite coefficient module with its integral scalar action.
Source: blueprint, finite coefficient sheaves (blueprint: sk-def-pe-derived-completion). -/
abbrev finiteModule (X : Scheme.{u}) (n : ℕ) : Modules l E X :=
  (DerivedNakayama.pullback l E X).obj (DerivedNakayama.quotientModule l E (n + 1))

/-- The coefficient quotient map from the monoidal unit, with the canonical action transport.
Source: blueprint, tensor units (blueprint: sk-def-pe-derived-completion). -/
def finiteUnit (X : Scheme.{u}) (n : ℕ) : 𝟙_ (Modules l E X) ⟶ finiteModule l E X n :=
  (DerivedNakayama.regularPullbackIso l E X).inv ≫
    (DerivedNakayama.pullback l E X).map (quotientUnit l E n)

/-- Ordinary tensor reduction of a complex, used only on K-flat representatives.
Source: blueprint, K-flat construction of reductions
(blueprint: sk-def-pe-derived-completion). -/
abbrev level (X : Scheme.{u}) (n : ℕ) :
    CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ :=
  (tensorRight (finiteModule l E X n)).mapHomologicalComplex (.up ℤ)

/-- The strict transition P tensor B_(n+2) to P tensor B_(n+1).
Source: blueprint, canonical transitions (blueprint: sk-def-pe-derived-completion). -/
def levelStep (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    (level l E X (n + 1)).obj P ⟶ (level l E X n).obj P :=
  (NatTrans.mapHomologicalComplex
    ((tensoringRight (Modules l E X)).map
      ((DerivedNakayama.pullback l E X).map (quotientStep l E n))) (.up ℤ)).app P

/-- The chain map p to p tensor 1 at each positive level.
Source: blueprint, canonical reduction cone (blueprint: sk-def-pe-derived-completion). -/
def levelUnit (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    P ⟶ (level l E X n).obj P :=
  (NatTrans.mapHomologicalComplex
    ((rightUnitorNatIso (Modules l E X)).inv ≫
      (tensoringRight (Modules l E X)).map (finiteUnit l E X n)) (.up ℤ)).app P

/-- The termwise product of the strict reduction tower of P.
Source: blueprint, Roos model (blueprint: sk-def-pe-derived-completion). -/
abbrev product (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :=
  ∏ᶜ fun n : ℕ ↦ (level l E X n).obj P

/-- The specified 1 minus shift on the strict reduction product.
Source: Stacks 08TC, blueprint Roos model (blueprint: sk-def-pe-derived-completion). -/
def oneSubShift (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :
    product l E X P ⟶ product l E X P :=
  towerTransitionEndomorphism (levelStep l E X P)

/-- The two coordinates (x,y) of the reduction Roos complex in degree i.
Source: blueprint, Roos model (blueprint: sk-def-pe-derived-completion). -/
def roosX (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) (i : ℤ) :=
  (product l E X P).X i ⊞ (product l E X P).X (i - 1)

/-- The differential (dx,(1-s)x-dy) of the reduction Roos complex.
Source: blueprint, Roos model (blueprint: sk-def-pe-derived-completion). -/
def roosD (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) (i : ℤ) :
    roosX l E X P i ⟶ roosX l E X P (i + 1) :=
  biprod.lift (biprod.fst ≫ (product l E X P).d i (i + 1))
    (biprod.fst ≫ (oneSubShift l E X P).f i ≫
      eqToHom (congrArg (product l E X P).X (Int.add_sub_cancel i 1).symm) -
      biprod.snd ≫ (product l E X P).d (i - 1) ((i + 1) - 1))

/-- The specified Roos differential squares to zero.
Source: blueprint, Roos construction (blueprint: sk-def-pe-derived-completion).
Proof: the first coordinate is d squared. In the second coordinate the two mixed
terms cancel because 1-s is a chain map; the remaining d squared term is zero. -/
theorem roosD_sq (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) (i : ℤ) :
    roosD l E X P i ≫ roosD l E X P (i + 1) = 0 := by
  dsimp only [roosD, roosX]
  apply biprod.hom_ext
  · simp
  · suffices biprod.fst ≫ (product l E X P).d i (i + 1 + 1 - 1) ≫
        (oneSubShift l E X P).f (i + 1 + 1 - 1) -
        biprod.fst ≫ eqToHom (congrArg (product l E X P).X
          (Int.add_sub_cancel i 1).symm) ≫
          (product l E X P).d (i + 1 - 1) (i + 1 + 1 - 1) ≫
          (oneSubShift l E X P).f (i + 1 + 1 - 1) = 0 by simpa using this
    have hd := (product l E X P).eqToHom_comp_d
      (i := i) (i' := i + 1 - 1) (j := i + 1 + 1 - 1)
      (by change i + 1 = i + 1 + 1 - 1; omega)
      (by change i + 1 - 1 + 1 = i + 1 + 1 - 1; omega)
    rw [reassoc_of% hd, sub_self]

/-- The explicit homotopy inverse limit of the strict derived reductions of a K-flat P.
Source: Stacks 08TC, blueprint Roos model (blueprint: sk-def-pe-derived-completion). -/
def roos (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :
    CochainComplex (Modules l E X) ℤ :=
  CochainComplex.of (roosX l E X P) (roosD l E X P) (roosD_sq l E X P)

/-- The product of the specified tensor-unit maps.
Source: blueprint, strict reduction augmentation (blueprint: sk-def-pe-derived-completion). -/
def unitProduct (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :
    P ⟶ product l E X P := Pi.lift (levelUnit l E X P)

private theorem quotientUnit_step (n : ℕ) :
    quotientUnit l E (n + 1) ≫ quotientStep l E n = quotientUnit l E n := by
  apply Mod.hom_ext
  rfl

private theorem finiteUnit_step (X : Scheme.{u}) (n : ℕ) :
    finiteUnit l E X (n + 1) ≫
      (DerivedNakayama.pullback l E X).map (quotientStep l E n) = finiteUnit l E X n := by
  dsimp only [finiteUnit]
  rw [Category.assoc, ← Functor.map_comp, quotientUnit_step]

private theorem levelUnit_step (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ)
    (n : ℕ) : levelUnit l E X P (n + 1) ≫ levelStep l E X P n = levelUnit l E X P n := by
  apply HomologicalComplex.hom_ext
  intro i
  change ((ρ_ (P.X i)).inv ≫ P.X i ◁ finiteUnit l E X (n + 1)) ≫
    P.X i ◁ (DerivedNakayama.pullback l E X).map (quotientStep l E n) =
    (ρ_ (P.X i)).inv ≫ P.X i ◁ finiteUnit l E X n
  rw [Category.assoc, ← whiskerLeft_comp, finiteUnit_step]

private theorem unitProduct_oneSubShift (X : Scheme.{u})
    (P : CochainComplex (Modules l E X) ℤ) :
    unitProduct l E X P ≫ oneSubShift l E X P = 0 := by
  apply Pi.hom_ext
  intro n
  simp [oneSubShift, towerTransitionEndomorphism, towerProductShift, unitProduct,
    levelUnit_step]

/-- The map with coordinates (unit,0) is a chain map.
Source: blueprint, canonical reduction comparison (blueprint: sk-def-pe-derived-completion).
Proof: the tensor units commute with d. Quotient transitions preserve 1 and commute
with the quotient maps, so (1-s) unit = 0. These are exactly the two chain-map equations. -/
theorem augmentation_comm (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ)
    (i : ℤ) :
    biprod.lift ((unitProduct l E X P).f i) 0 ≫ (roos l E X P).d i (i + 1) =
      P.d i (i + 1) ≫ biprod.lift ((unitProduct l E X P).f (i + 1)) 0 := by
  have hz (j : ℤ) : (unitProduct l E X P).f j ≫ (oneSubShift l E X P).f j = 0 :=
    congrArg (fun f ↦ f.f j) (unitProduct_oneSubShift l E X P)
  simp only [roos, CochainComplex.of_d]
  dsimp only [roosD, roosX]
  apply biprod.hom_ext
  · simp
  · simpa using hz (i + 1 - 1)

/-- The canonical completion comparison, with the specified zero shifted-product component.
Source: blueprint, canonical reduction comparison (blueprint: sk-def-pe-derived-completion). -/
def augmentation (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :
    P ⟶ roos l E X P :=
  CochainComplex.ofHom (fun i ↦ biprod.lift ((unitProduct l E X P).f i) 0)
    (augmentation_comm l E X P)

end AlgebraicGeometry.ProEtale.AdicCompletion

namespace AlgebraicGeometry.ProEtale

/-- Derived completeness in the unbounded internal-module category of the continuous
pulled-back integral coefficients. A K-flat representative computes the derived reductions;
the specified augmentation, with zero nullhomotopy, must be invertible after localization.
Source: blueprint definition and its Roos construction
(blueprint: sk-def-pe-derived-completion). -/
def IsDerivedComplete (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K : DerivedCategory (AdicCompletion.Modules l E X)) : Prop :=
  ∃ P : CochainComplex (AdicCompletion.Modules l E X) ℤ,
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E X) (.up ℤ)).kFlat P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
        IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.AdicCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The quotient maps factor through each consecutive quotient, as ring-object morphisms.
Source: blueprint, canonical coefficient tower (blueprint: sk-def-pe-derived-completion).
Proof: quotient factor after quotient is the smaller quotient homomorphism.
This identity holds pointwise on continuous functions, and inverse image preserves composition. -/
theorem quotient_transition (n : ℕ) :
    quotient l E X (n + 1) ≫ transition l E X n = quotient l E X n := by
  rw [← Functor.map_comp]
  congr 1

/-- The derived category over the positive finite coefficient level n+1.
Source: blueprint, normalized complexes (blueprint: sk-def-pe-derived-completion). -/
abbrev FiniteDerived (n : ℕ) := DerivedCategory
  (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (finiteRing l E X n))

/-- Canonical derived extension from the integral coefficients to positive level n+1.
Source: blueprint, K_n (blueprint: sk-def-pe-derived-completion). -/
abbrev derivedReduction (n : ℕ) : DerivedCategory (Modules l E X) ⥤ FiniteDerived l E X n :=
  (Mod.extendScalars (quotient l E X n)).leftDerivedFunctor

/-- Exact derived restriction from level n+1 back to the integral ring.
Source: blueprint, reduction tower (blueprint: sk-def-pe-derived-completion). -/
abbrev restrict (n : ℕ) : FiniteDerived l E X n ⥤ DerivedCategory (Modules l E X) :=
  (Mod.comap (quotient l E X n)).mapDerivedCategory

/-- Consecutive derived base change over B_(n+2), rather than over the integral ring.
Source: blueprint, reduction identities (blueprint: sk-def-pe-derived-completion). -/
abbrev finiteExtend (n : ℕ) : FiniteDerived l E X (n + 1) ⥤ FiniteDerived l E X n :=
  (Mod.extendScalars (transition l E X n)).leftDerivedFunctor

/-- Exact restriction along B_(n+2) to B_(n+1).
Source: blueprint, normalization (blueprint: sk-def-pe-derived-completion). -/
abbrev finiteRestrict (n : ℕ) : FiniteDerived l E X n ⥤ FiniteDerived l E X (n + 1) :=
  (Mod.comap (transition l E X n)).mapDerivedCategory

/-- Canonical composition of exact restriction, including the quotient-factor identity.
Source: blueprint, coherent reductions (blueprint: sk-def-pe-derived-completion). -/
def restrictComp (n : ℕ) :
    finiteRestrict l E X n ⋙ restrict l E X (n + 1) ≅ restrict l E X n :=
  (Functor.mapDerivedCategoryCompIso
    (Mod.comap (transition l E X n)) (Mod.comap (quotient l E X (n + 1)))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp (quotient l E X (n + 1)) (transition l E X n)).symm ≪≫
        Mod.comapCongr (quotient_transition l E X n))

/-- The derived reduction identity determined by the canonical adjunction units and counits.
This is the canonical association (P tensor B_(n+2)) tensor B_(n+1) = P tensor B_(n+1).
Source: blueprint, normalization (blueprint: sk-def-pe-derived-completion). -/
def reductionComp (n : ℕ) :
    derivedReduction l E X (n + 1) ⋙ finiteExtend l E X n ≅ derivedReduction l E X n :=
  (((Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X (n + 1))).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (transition l E X n))).ofNatIsoRight
        (restrictComp l E X n)).leftAdjointUniq
    (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n))

/-- Transition between the derived reductions, given by the consecutive unit and association.
Source: blueprint, canonical transition maps (blueprint: sk-def-pe-derived-completion). -/
def derivedStep (K : DerivedCategory (Modules l E X)) (n : ℕ) :
    (derivedReduction l E X (n + 1)).obj K ⟶
      (finiteRestrict l E X n).obj ((derivedReduction l E X n).obj K) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction (transition l E X n)).unit.app
      ((derivedReduction l E X (n + 1)).obj K) ≫
    (finiteRestrict l E X n).map ((reductionComp l E X n).hom.app K)

/-- A compatible tower of finite-coefficient complexes is normalized when the actual
transition-induced derived reduction comparisons are invertible. Successive comparisons
suffice: compose their adjunction mates to get every longer reduction identity.
This imposes no ordinary-tensor condition on the cohomology sheaves.
Source: blueprint, definition of normalized tower (blueprint: sk-def-pe-derived-completion). -/
def IsNormalized (M : ∀ n : ℕ, FiniteDerived l E X n)
    (t : ∀ n : ℕ, M (n + 1) ⟶ (finiteRestrict l E X n).obj (M n)) : Prop :=
  ∀ n : ℕ, IsIso
    (((Mod.derivedExtendMapDerivedCategoryAdjunction (transition l E X n)).homEquiv
      (M (n + 1)) (M n)).symm (t n))

private theorem isIso_mate_unit {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : C} {B : D} (e : F.obj A ≅ B) :
    IsIso ((adj.homEquiv A B).symm (adj.unit.app A ≫ G.map e.hom)) := by
  rw [← adj.homEquiv_unit, Equiv.symm_apply_apply]
  infer_instance

/-- The derived reduction tower is normalized with its specified transitions.
Source: blueprint, derived reduction identities (blueprint: sk-def-pe-derived-completion).
Proof: reductionComp is the canonical natural isomorphism supplied by uniqueness
of left adjoints to the same restriction functor. By definition, derivedStep is its
component transported by the finite scalar-extension adjunction: it is the unit
followed by the restricted isomorphism. Applying the inverse adjunction homEquiv
therefore recovers that isomorphism component, which is invertible. This proves
normalization at each consecutive positive level. -/
theorem derivedReduction_isNormalized (K : DerivedCategory (Modules l E X)) :
    IsNormalized l E X (fun n ↦ (derivedReduction l E X n).obj K)
      (derivedStep l E X K) := by
  intro n
  exact isIso_mate_unit
    (Mod.derivedExtendMapDerivedCategoryAdjunction (transition l E X n))
    ((reductionComp l E X n).app K)

/-- The canonical comparison on any specified K-flat representative of K.
Source: blueprint, canonical completion map (blueprint: sk-def-pe-derived-completion). -/
def completionMap (K : DerivedCategory (Modules l E X))
    (P : CochainComplex (Modules l E X) ℤ) (e : DerivedCategory.Q.obj P ≅ K) :
    K ⟶ DerivedCategory.Q.obj (roos l E X P) :=
  e.inv ≫ DerivedCategory.Q.map (augmentation l E X P)

/-- Completeness can be checked on any K-flat representative, retaining the actual
augmentation rather than merely an isomorphism between the two objects.
Source: blueprint, representative independence (blueprint: sk-def-pe-derived-completion).
Proof: use lem-pe-internal-section-tensor-comparison to identify internal and sectionwise
modules, total tensor and K-flatness. Refine representatives by flat-term K-flat
resolutions and use lem-pe-kflat-roos-representative-invariance for those refinements.
For a quasi-isomorphism between arbitrary K-flat representatives, derived change of
rings gives a quasi-isomorphism on each tensor reduction without a flat-term assumption.
Exact countable products and the cone triangle then give a Roos quasi-isomorphism.
The induced product map on both coordinates intertwines (unit,0). A common K-flat
refinement of a derived roof therefore gives an invertible augmented comparison.
Thus one specified augmentation is invertible exactly when every such augmentation is. -/
theorem isDerivedComplete_iff (K : DerivedCategory (Modules l E X))
    (P : CochainComplex (Modules l E X) ℤ)
    (_hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
    (e : DerivedCategory.Q.obj P ≅ K) :
    IsDerivedComplete l E X K ↔ IsIso (completionMap l E X K P e) := by
  sorry

end AlgebraicGeometry.ProEtale.AdicCompletion

namespace AlgebraicGeometry.ProEtale.AdicCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The derived reduction at level n+1, regarded as an integral-coefficient complex.
Source: blueprint, inverse system (blueprint: sk-def-pe-derived-completion). -/
abbrev integralLevel (K : DerivedCategory (Modules l E X)) (n : ℕ) :=
  (restrict l E X n).obj ((derivedReduction l E X n).obj K)

/-- The canonical transition after exact restriction to the common integral category.
Source: blueprint, compatible reduction tower (blueprint: sk-def-pe-derived-completion). -/
def integralStep (K : DerivedCategory (Modules l E X)) (n : ℕ) :
    integralLevel l E X K (n + 1) ⟶ integralLevel l E X K n :=
  (restrict l E X (n + 1)).map (derivedStep l E X K n) ≫
    (restrictComp l E X n).hom.app ((derivedReduction l E X n).obj K)

/-- The full inverse-system functor of canonical derived reductions.
Source: blueprint, derived inverse limit (blueprint: sk-def-pe-derived-completion). -/
def derivedTower (K : DerivedCategory (Modules l E X)) :
    ℕᵒᵖ ⥤ DerivedCategory (Modules l E X) :=
  Functor.ofOpSequence (integralStep l E X K)

private theorem composed_unit_compatible
    {C D A : Type*} [Category C] [Category D] [Category A]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ A} {I : A ⥤ D}
    {L : C ⥤ A} {R : A ⥤ C}
    (a : F ⊣ G) (b : H ⊣ I) (c : L ⊣ R) (e : I ⋙ G ≅ R) (K : C) :
    let t := ((a.comp b).ofNatIsoRight e).leftAdjointUniq c
    a.unit.app K ≫ (G.map (b.unit.app (F.obj K) ≫ I.map (t.hom.app K)) ≫
      e.hom.app (L.obj K)) = c.unit.app K := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app ((a.comp b).ofNatIsoRight e) c K
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Adjunction.comp_unit_app, Category.assoc, Functor.whiskerLeft_app] at h
  rw [← e.hom.naturality ((((a.comp b).ofNatIsoRight e).leftAdjointUniq c).hom.app K)] at h
  simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using h

/-- The coherent tensor-unit maps to the derived reductions.
Source: blueprint, reduction cone (blueprint: sk-def-pe-derived-completion).
Proof: reductionComp is formed by left-adjoint uniqueness, which identifies the
composite unit with the direct unit. Composing this identity with restrictComp
is exactly the displayed compatibility of the positive consecutive units. -/
theorem reductionUnit_compatible (K : DerivedCategory (Modules l E X)) (n : ℕ) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X (n + 1))).unit.app K ≫
        integralStep l E X K n =
      (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n)).unit.app K := by
  exact composed_unit_compatible
    (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X (n + 1)))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (transition l E X n))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n))
    (restrictComp l E X n) K

/-- The specified augmented Roos model is the derived inverse limit of the canonical
reductions; its evaluations compose with the explicit completionMap to the tensor units.
The extra product instance is the usual categorical choice of product, not a hypothesis
on K, and no choice of a triangulated lift is used to define the comparison.
Source: blueprint, Roos interpretation, Stacks 08TC
(blueprint: sk-def-pe-derived-completion).
Proof: on a K-flat P, ordinary tensor with B_n computes relative derived extension.
The scalar-extension counit gives the level identifications, compatibly with quotient
transitions and tensor units. Exact countable products of module sheaves identify the
product of the localized levels with the localized termwise product. The signed
interchange of the two coordinates identifies roos with Cone(1-s)[-1]. Its cone triangle
gives the asserted distinguished triangle. Its first arrow is the first-coordinate
projection, whose composite with (unit,0) is the product of the canonical units.
The strict augmentation clause of lem-weil-strict-roos-comparison identifies this
specified map with the total-derived-limit comparison, including its zero homotopy. -/
theorem roos_isDerivedLimit (K : DerivedCategory (Modules l E X))
    (P : CochainComplex (Modules l E X) ℤ)
    (_hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
    (e : DerivedCategory.Q.obj P ≅ K)
    [HasProduct (integralLevel l E X K)] :
    ∃ (p : DerivedCategory.Q.obj (roos l E X P) ⟶ ∏ᶜ (integralLevel l E X K))
      (δ : ∏ᶜ (integralLevel l E X K) ⟶
        (DerivedCategory.Q.obj (roos l E X P))⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle (integralStep l E X K) _ p δ ∧
        completionMap l E X K P e ≫ p = Pi.lift (f := integralLevel l E X K)
          (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction
            (quotient l E X n)).unit.app K) := by
  sorry

end AlgebraicGeometry.ProEtale.AdicCompletion
