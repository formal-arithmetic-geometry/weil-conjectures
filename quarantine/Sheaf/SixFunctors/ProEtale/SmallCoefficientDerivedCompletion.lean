/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q16 and NW
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.RingTheory.Finiteness.Small
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Mathlib.Algebra.Homology.HomologicalComplexLimits


/-!
# Derived completion with an independent finite-extension universe

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-def-pe-derived-completion/_section.md` (blueprint:
def-sfb-small-coefficient-derived-completion).

The coefficients use the same continuous condensed ring construction as DerivedNakayama,
with the canonical small field presentation, pulled back by the published strong monoidal
inverse image from the point.
Positive level n is indexed by n-1. Completion uses the explicit augmented Roos
complex on a K-flat representative, with zero homotopy in its second coordinate.
Normalization uses extension of scalars over the successive finite coefficient rings.
This generalizes the recorded interface using the same small coefficient presentation
as integralHeartCoefficientRingObj; the site universe remains independent of E.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.SmallAdicCompletion.Coefficients

variable (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical small presentation of the finite extension.
Source: finite-dimensional smallness (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev field : Type :=
  letI : Small.{0} E := Module.Finite.small (Padic l) E
  Shrink.{0} E

/-- Transported field structure on the small presentation.
Source: Shrink.field (blueprint: def-sfb-small-coefficient-derived-completion). -/
instance fieldField : Field (field l E) :=
  letI : Small.{0} E := Module.Finite.small (Padic l) E
  inferInstanceAs (Field (Shrink.{0} E))

/-- Transported coefficient algebra on the small presentation.
Source: Shrink.algebra (blueprint: def-sfb-small-coefficient-derived-completion). -/
instance fieldAlgebra : Algebra (Padic l) (field l E) :=
  letI : Small.{0} E := Module.Finite.small (Padic l) E
  inferInstanceAs (Algebra (Padic l) (Shrink.{0} E))

/-- Finite dimension transported by the canonical algebra equivalence.
Source: Shrink.algEquiv (blueprint: def-sfb-small-coefficient-derived-completion). -/
instance fieldFinite : FiniteDimensional (Padic l) (field l E) :=
  letI : Small.{0} E := Module.Finite.small (Padic l) E
  (Shrink.algEquiv (Padic l) E).symm.toLinearEquiv.finiteDimensional

/-- The coefficient DVR in the canonical small presentation.
Source: the integral coefficient setup (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev integers := Padic.coefficientExtensionIntegers l (field l E)

/-- The spectral topology used by the integral-heart coefficient construction.
Source: the integral coefficient setup (blueprint: def-sfb-small-coefficient-derived-completion). -/
instance fieldNorm : NormedField (field l E) := spectralNorm.normedField (Padic l) (field l E)

/-- The same condensed ring used by the integral-heart constructibility predicate.
Source: pulled-back coefficients (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev integerRing : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI : Small.{0} E := Module.Finite.small (Padic l) E
  letI : FiniteDimensional (Padic l) (Shrink.{0} E) :=
    (Shrink.algEquiv (Padic l) E).symm.toLinearEquiv.finiteDimensional
  letI := spectralNorm.normedField (Padic l) (Shrink.{0} E)
  Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers l (Shrink.{0} E))

/-- The existing multiplication on the small coefficient object, cached as an instance.
Source: pulled-back coefficients (blueprint: def-sfb-small-coefficient-derived-completion). -/
instance integerRingMonObj : MonObj (integerRing.{u} l E) :=
  inferInstanceAs (MonObj (Profinite.continuousMapRingObj (integers l E)))

/-- The existing commutativity on the small coefficient object.
Source: pulled-back coefficients (blueprint: def-sfb-small-coefficient-derived-completion). -/
instance integerRingComm : IsCommMonObj (integerRing.{u} l E) :=
  inferInstanceAs (IsCommMonObj (Profinite.continuousMapRingObj (integers l E)))

/-- The continuous finite quotient ring at the point.
Source: finite coefficients (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev quotientRingSheaf (n : ℕ) : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  Profinite.continuousMapRingSheaf (Padic.coefficientExtensionRing l (field l E) n)

/-- The internal finite quotient ring at the point.
Source: finite coefficients (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev quotientRing (n : ℕ) : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (quotientRingSheaf l E n)

/-- The actual continuous quotient morphism.
Source: finite coefficient reduction (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev reductionRing (n : ℕ) : integerRing.{u} l E ⟶ quotientRing l E n :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.continuousMapRingSheafMap
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l (field l E) n))
      continuous_quot_mk)

/-- The finite quotient with its canonical integral action.
Source: finite coefficients (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev quotientModule (n : ℕ) :=
  (Mod.comap (reductionRing.{u} l E n)).obj (Mod.regular (quotientRing l E n))

/-- The exact pulled-back module functor.
Source: pulled-back coefficients (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev pullback (X : Scheme.{u}) := (upperStarFromPoint X).mapMod (integerRing l E)

/-- The regular-module identification for the strong monoidal inverse image.
Source: tensor unit normalization (blueprint: def-sfb-small-coefficient-derived-completion).
Proof: the transported regular action is the transported multiplication; both
underlying objects are p_X^* of the same ring, so module extensionality applies. -/
theorem pullback_regular (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    (pullback l E X).obj (Mod.regular (integerRing l E)) =
      Mod.regular (condensedRingObj (integerRing l E) X) := by
  rfl

/-- The normalized regular-module comparison.
Source: tensor unit normalization (blueprint: def-sfb-small-coefficient-derived-completion). -/
def regularPullbackIso (X : Scheme.{u}) :
    (pullback l E X).obj (Mod.regular (integerRing l E)) ≅
      Mod.regular (condensedRingObj (integerRing l E) X) :=
  eqToIso (pullback_regular l E X)

end AlgebraicGeometry.ProEtale.SmallAdicCompletion.Coefficients

namespace AlgebraicGeometry.ProEtale.SmallAdicCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The continuous integral coefficient ring pulled back from the point.
Source: blueprint, coefficient sheaves (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev ring (X : Scheme.{u}) := condensedRingObj (Coefficients.integerRing.{u} l E) X

/-- Internal modules over the completed continuous coefficient ring.
Source: blueprint, ambient category (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev Modules (X : Scheme.{u}) := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (ring l E X)

/-- The continuous finite quotient ring at the positive level n+1.
Source: blueprint, finite coefficient sheaves (blueprint:
def-sfb-small-coefficient-derived-completion). -/
abbrev finiteRing (X : Scheme.{u}) (n : ℕ) :=
  condensedRingObj (Coefficients.quotientRing.{u} l E (n + 1)) X

/-- Commutativity of the continuous finite quotient ring, before pullback.
Source: blueprint, coefficient sheaves (blueprint: def-sfb-small-coefficient-derived-completion). -/
instance quotientRing_isCommMonObj (n : ℕ) :
    IsCommMonObj (Coefficients.quotientRing.{u} l E n) :=
  Profinite.isCommMonObj_continuousMapRingObj _

/-- The actual quotient morphism pulled back from the point.
Source: blueprint, reduction cone (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev quotient (X : Scheme.{u}) (n : ℕ) : ring l E X ⟶ finiteRing l E X n :=
  (upperStarFromPoint X).map (Coefficients.reductionRing.{u} l E (n + 1))

/-- The quotient topology induced by the spectral topology on the finite extension.
Source: blueprint, continuous coefficient rings (blueprint:
def-sfb-small-coefficient-derived-completion). -/
abbrev finiteTopology (n : ℕ) :
    TopologicalSpace (Padic.coefficientExtensionRing l (Coefficients.field l E) n) :=
  inferInstance

/-- The quotient transition is continuous for the quotient topologies.
Source: blueprint, reduction identities (blueprint: def-sfb-small-coefficient-derived-completion).
Proof: the quotient map O_E to O_E/pi^(n+2) is a quotient map. Its composite
with the displayed factor is the continuous quotient map to O_E/pi^(n+1),
so the quotient universal property proves continuity. -/
theorem continuous_transition (n : ℕ) :
    @Continuous _ _ (finiteTopology l E (n + 2)) (finiteTopology l E (n + 1))
      (Padic.coefficientExtensionTransition l (Coefficients.field l E) (n + 1)) := by
  exact (QuotientRing.isOpenQuotientMap_mk
    (Padic.coefficientExtensionIdeal l (Coefficients.field l E) (n + 2))).isQuotientMap
      |>.continuous_iff.mpr continuous_quot_mk

/-- Continuous postcomposition with the specified quotient transition.
Source: blueprint, canonical transitions (blueprint: def-sfb-small-coefficient-derived-completion).
-/
def transitionRingSheaf (n : ℕ) :
    Coefficients.quotientRingSheaf.{u} l E (n + 2) ⟶
      Coefficients.quotientRingSheaf.{u} l E (n + 1) :=
  ⟨{
    app := fun _ ↦ RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (((Padic.coefficientExtensionTransition l (Coefficients.field l E)
          (n + 1)).compLeftContinuous _
        (continuous_transition l E n)).comp ULift.ringEquiv.toRingHom))
    naturality := fun _ _ _ ↦ rfl }⟩

/-- The same quotient transition as a morphism of internal condensed rings.
Source: blueprint, canonical transitions (blueprint: def-sfb-small-coefficient-derived-completion).
-/
abbrev transitionRing (n : ℕ) :
    Coefficients.quotientRing.{u} l E (n + 2) ⟶
      Coefficients.quotientRing.{u} l E (n + 1) :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (transitionRingSheaf l E n)

/-- The transition between the pulled-back finite ring objects.
Source: blueprint, canonical transitions (blueprint: def-sfb-small-coefficient-derived-completion).
-/
abbrev transition (X : Scheme.{u}) (n : ℕ) : finiteRing l E X (n + 1) ⟶
    finiteRing l E X n := (upperStarFromPoint X).map (transitionRing l E n)

private theorem reduction_transition (n : ℕ) :
    Coefficients.reductionRing.{u} l E (n + 2) ≫ transitionRing l E n =
      Coefficients.reductionRing.{u} l E (n + 1) := by
  ext S x
  rfl

/-- Quotient and transition maps preserve the scalar action on the regular module.
Source: blueprint, construction of the reduction cone
(blueprint: def-sfb-small-coefficient-derived-completion).
Proof: a ring homomorphism sends ab to its image product. In the transition equation,
the composite O_E to the smaller quotient equals the direct quotient. Apply these
identities to continuous functions pointwise; naturality and inverse image preserve them. -/
theorem coefficient_linearity :
    (∀ n : ℕ, Mod.act (Mod.regular (Coefficients.integerRing.{u} l E)).X ≫
        Coefficients.reductionRing.{u} l E (n + 1) =
      Coefficients.integerRing.{u} l E ◁ Coefficients.reductionRing.{u} l E (n + 1) ≫
        Mod.act (Coefficients.quotientModule.{u} l E (n + 1)).X) ∧
    (∀ n : ℕ, Mod.act (Coefficients.quotientModule.{u} l E (n + 2)).X ≫
        transitionRing l E n =
      Coefficients.integerRing.{u} l E ◁ transitionRing l E n ≫
        Mod.act (Coefficients.quotientModule.{u} l E (n + 1)).X) := by
  constructor
  · intro n
    change μ[Coefficients.integerRing.{u} l E] ≫ _ =
      _ ≫ Coefficients.reductionRing.{u} l E (n + 1) ▷ _ ≫
        μ[Coefficients.quotientRing.{u} l E (n + 1)]
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc]
  · intro n
    change (Coefficients.reductionRing.{u} l E (n + 2) ▷ _ ≫
      μ[Coefficients.quotientRing.{u} l E (n + 2)]) ≫ _ =
      _ ≫ Coefficients.reductionRing.{u} l E (n + 1) ▷ _ ≫
        μ[Coefficients.quotientRing.{u} l E (n + 1)]
    rw [Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def, Category.assoc,
      whisker_exchange_assoc, ← comp_whiskerRight_assoc, reduction_transition]

/-- The actual unit quotient map as an integral-module morphism on the point.
Source: blueprint, unit of the reduction cone (blueprint:
def-sfb-small-coefficient-derived-completion). -/
def quotientUnit (n : ℕ) : Mod.regular (Coefficients.integerRing.{u} l E) ⟶
    Coefficients.quotientModule.{u} l E (n + 1) :=
  Mod.homMk (Coefficients.reductionRing.{u} l E (n + 1))
    ((coefficient_linearity.{u} l E).1 n)

/-- The actual transition as an integral-module morphism on the point.
Source: blueprint, canonical transitions (blueprint: def-sfb-small-coefficient-derived-completion).
-/
def quotientStep (n : ℕ) : Coefficients.quotientModule.{u} l E (n + 2) ⟶
    Coefficients.quotientModule.{u} l E (n + 1) :=
  Mod.homMk (transitionRing l E n) ((coefficient_linearity.{u} l E).2 n)

/-- The pulled-back finite coefficient module with its integral scalar action.
Source: blueprint, finite coefficient sheaves (blueprint:
def-sfb-small-coefficient-derived-completion). -/
abbrev finiteModule (X : Scheme.{u}) (n : ℕ) : Modules l E X :=
  (Coefficients.pullback.{u} l E X).obj (Coefficients.quotientModule.{u} l E (n + 1))

/-- The coefficient quotient map from the monoidal unit, with the canonical action transport.
Source: blueprint, tensor units (blueprint: def-sfb-small-coefficient-derived-completion). -/
def finiteUnit (X : Scheme.{u}) (n : ℕ) : 𝟙_ (Modules l E X) ⟶ finiteModule l E X n :=
  (Coefficients.regularPullbackIso.{u} l E X).inv ≫
    (Coefficients.pullback.{u} l E X).map (quotientUnit l E n)

private theorem finiteUnit_step (X : Scheme.{u}) (n : ℕ) :
    finiteUnit l E X (n + 1) ≫
      (Coefficients.pullback.{u} l E X).map (quotientStep l E n) = finiteUnit l E X n := by
  unfold finiteUnit
  rw [Category.assoc, ← Functor.map_comp]
  congr 1

/-- Ordinary tensor reduction of a complex, used only on K-flat representatives.
Source: blueprint, K-flat construction of reductions
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev level (X : Scheme.{u}) (n : ℕ) :
    CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ :=
  (tensorRight (finiteModule l E X n)).mapHomologicalComplex (.up ℤ)

/-- The strict transition P tensor B_(n+2) to P tensor B_(n+1).
Source: blueprint, canonical transitions (blueprint: def-sfb-small-coefficient-derived-completion).
-/
def levelStep (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    (level l E X (n + 1)).obj P ⟶ (level l E X n).obj P :=
  (NatTrans.mapHomologicalComplex
    ((tensoringRight (Modules l E X)).map
      ((Coefficients.pullback.{u} l E X).map (quotientStep l E n))) (.up ℤ)).app P

/-- The chain map p to p tensor 1 at each positive level.
Source: blueprint, canonical reduction cone (blueprint:
def-sfb-small-coefficient-derived-completion). -/
def levelUnit (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    P ⟶ (level l E X n).obj P :=
  (NatTrans.mapHomologicalComplex
    ((rightUnitorNatIso (Modules l E X)).inv ≫
      (tensoringRight (Modules l E X)).map (finiteUnit l E X n)) (.up ℤ)).app P

private theorem levelUnit_step (X : Scheme.{u})
    (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    levelUnit l E X P (n + 1) ≫ levelStep l E X P n = levelUnit l E X P n := by
  apply HomologicalComplex.Hom.ext
  funext i
  change ((ρ_ (P.X i)).inv ≫ P.X i ◁ finiteUnit l E X (n + 1)) ≫
    P.X i ◁ (Coefficients.pullback.{u} l E X).map (quotientStep l E n) =
      (ρ_ (P.X i)).inv ≫ P.X i ◁ finiteUnit l E X n
  rw [Category.assoc, ← MonoidalCategory.whiskerLeft_comp, finiteUnit_step]

/-- The termwise product of the strict reduction tower of P.
Source: blueprint, Roos model (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev product (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :=
  ∏ᶜ fun n : ℕ ↦ (level l E X n).obj P

/-- The specified 1 minus shift on the strict reduction product.
Source: Stacks 08TC, blueprint Roos model (blueprint: def-sfb-small-coefficient-derived-completion).
-/
def oneSubShift (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :
    product l E X P ⟶ product l E X P :=
  towerTransitionEndomorphism (levelStep l E X P)

/-- The two coordinates (x,y) of the reduction Roos complex in degree i.
Source: blueprint, Roos model (blueprint: def-sfb-small-coefficient-derived-completion). -/
def roosX (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) (i : ℤ) :=
  (product l E X P).X i ⊞ (product l E X P).X (i - 1)

/-- The differential (dx,(1-s)x-dy) of the reduction Roos complex.
Source: blueprint, Roos model (blueprint: def-sfb-small-coefficient-derived-completion). -/
def roosD (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) (i : ℤ) :
    roosX l E X P i ⟶ roosX l E X P (i + 1) :=
  biprod.lift (biprod.fst ≫ (product l E X P).d i (i + 1))
    (biprod.fst ≫ (oneSubShift l E X P).f i ≫
      eqToHom (congrArg (product l E X P).X (Int.add_sub_cancel i 1).symm) -
      biprod.snd ≫ (product l E X P).d (i - 1) ((i + 1) - 1))

/-- The specified Roos differential squares to zero.
Source: blueprint, Roos construction (blueprint: def-sfb-small-coefficient-derived-completion).
Proof: the first coordinate is d squared. In the second coordinate the two mixed
terms cancel because 1-s is a chain map; the remaining d squared term is zero. -/
theorem roosD_sq (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (P : CochainComplex (SmallAdicCompletion.Modules l E X) ℤ) (i : ℤ) :
    roosD l E X P i ≫ roosD l E X P (i + 1) = 0 := by
  dsimp only [roosD, roosX]
  apply biprod.hom_ext
  · simp [Category.assoc]
  · simp only [Category.assoc, biprod.lift_snd, Preadditive.comp_sub,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc, Preadditive.sub_comp,
      add_sub_cancel_right, ComplexShape.up_Rel, HomologicalComplex.eqToHom_comp_d,
      HomologicalComplex.Hom.comm, HomologicalComplex.d_comp_d, comp_zero, sub_zero,
      zero_comp]
    have transport (j k : ℤ) (h : j = k) :
        (product l E X P).d i j ≫ (oneSubShift l E X P).f j ≫
            eqToHom (congrArg (product l E X P).X h) =
          (product l E X P).d i k ≫ (oneSubShift l E X P).f k := by
      subst k
      simp
    rw [transport _ _ (by omega)]
    exact sub_self _

/-- The explicit homotopy inverse limit of the strict derived reductions of a K-flat P.
Source: Stacks 08TC, blueprint Roos model (blueprint: def-sfb-small-coefficient-derived-completion).
-/
def roos (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :
    CochainComplex (Modules l E X) ℤ :=
  CochainComplex.of (roosX l E X P) (roosD l E X P) (roosD_sq l E X P)

/-- The product of the specified tensor-unit maps.
Source: blueprint, strict reduction augmentation (blueprint:
def-sfb-small-coefficient-derived-completion). -/
def unitProduct (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :
    P ⟶ product l E X P := Pi.lift (levelUnit l E X P)

private theorem unitProduct_oneSubShift (X : Scheme.{u})
    (P : CochainComplex (Modules l E X) ℤ) :
    unitProduct l E X P ≫ oneSubShift l E X P = 0 := by
  unfold oneSubShift towerTransitionEndomorphism
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero]
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, towerProductShift, unitProduct, Pi.lift_π, Pi.lift_π_assoc]
  exact (levelUnit_step l E X P n).symm

/-- The map with coordinates (unit,0) is a chain map.
Source: blueprint, canonical reduction comparison (blueprint:
def-sfb-small-coefficient-derived-completion).
Proof: the tensor units commute with d. Quotient transitions preserve 1 and commute
with the quotient maps, so (1-s) unit = 0. These are exactly the two chain-map equations. -/
theorem augmentation_comm (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (P : CochainComplex (SmallAdicCompletion.Modules l E X) ℤ) (i : ℤ) :
    biprod.lift ((unitProduct l E X P).f i) 0 ≫ (roos l E X P).d i (i + 1) =
      P.d i (i + 1) ≫ biprod.lift ((unitProduct l E X P).f (i + 1)) 0 := by
  dsimp only [roos]
  rw [CochainComplex.of_d]
  dsimp only [roosD]
  apply biprod.hom_ext
  · simp [Category.assoc]
  · have h := congrArg (fun f ↦ f.f i) (unitProduct_oneSubShift l E X P)
    simpa [Category.assoc, Preadditive.comp_sub] using
      congrArg (fun f ↦ f ≫
        eqToHom (congrArg (product l E X P).X (Int.add_sub_cancel i 1).symm)) h

/-- The canonical completion comparison, with the specified zero shifted-product component.
Source: blueprint, canonical reduction comparison (blueprint:
def-sfb-small-coefficient-derived-completion). -/
def augmentation (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ) :
    P ⟶ roos l E X P :=
  CochainComplex.ofHom (fun i ↦ biprod.lift ((unitProduct l E X P).f i) 0)
    (augmentation_comm l E X P)

end AlgebraicGeometry.ProEtale.SmallAdicCompletion

namespace AlgebraicGeometry.ProEtale.SmallAdicCompletion

/-- Derived completeness in the unbounded internal-module category of the continuous
pulled-back integral coefficients. A K-flat representative computes the derived reductions;
the specified augmentation, with zero nullhomotopy, must be invertible after localization.
Source: blueprint definition and its Roos construction
(blueprint: def-sfb-small-coefficient-derived-completion). -/
def IsDerivedComplete (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K : DerivedCategory (SmallAdicCompletion.Modules l E X)) : Prop :=
  ∃ P : CochainComplex (SmallAdicCompletion.Modules l E X) ℤ,
    (HomologicalComplex.quasiIso (SmallAdicCompletion.Modules l E X) (.up ℤ)).kFlat P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
        IsIso (DerivedCategory.Q.map (SmallAdicCompletion.augmentation l E X P))

end AlgebraicGeometry.ProEtale.SmallAdicCompletion

namespace AlgebraicGeometry.ProEtale.SmallAdicCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The quotient maps factor through each consecutive quotient, as ring-object morphisms.
Source: blueprint, canonical coefficient tower (blueprint:
def-sfb-small-coefficient-derived-completion).
Proof: quotient factor after quotient is the smaller quotient homomorphism.
This identity holds pointwise on continuous functions, and inverse image preserves composition. -/
theorem quotient_transition (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (n : ℕ) :
    quotient l E X (n + 1) ≫ transition l E X n = quotient l E X n := by
  rw [quotient, transition, ← Functor.map_comp]
  exact congrArg (upperStarFromPoint X).map (reduction_transition l E n)

/-- The derived category over the positive finite coefficient level n+1.
Source: blueprint, normalized complexes (blueprint: def-sfb-small-coefficient-derived-completion).
-/
abbrev FiniteDerived (n : ℕ) := DerivedCategory
  (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (finiteRing l E X n))

/-- Canonical derived extension from the integral coefficients to positive level n+1.
Source: blueprint, K_n (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev derivedReduction (n : ℕ) : DerivedCategory (Modules l E X) ⥤ FiniteDerived l E X n :=
  (Mod.extendScalars (quotient l E X n)).leftDerivedFunctor

/-- Exact derived restriction from level n+1 back to the integral ring.
Source: blueprint, reduction tower (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev restrict (n : ℕ) : FiniteDerived l E X n ⥤ DerivedCategory (Modules l E X) :=
  (Mod.comap (quotient l E X n)).mapDerivedCategory

/-- Consecutive derived base change over B_(n+2), rather than over the integral ring.
Source: blueprint, reduction identities (blueprint: def-sfb-small-coefficient-derived-completion).
-/
abbrev finiteExtend (n : ℕ) : FiniteDerived l E X (n + 1) ⥤ FiniteDerived l E X n :=
  (Mod.extendScalars (transition l E X n)).leftDerivedFunctor

/-- Exact restriction along B_(n+2) to B_(n+1).
Source: blueprint, normalization (blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev finiteRestrict (n : ℕ) : FiniteDerived l E X n ⥤ FiniteDerived l E X (n + 1) :=
  (Mod.comap (transition l E X n)).mapDerivedCategory

/-- Canonical composition of exact restriction, including the quotient-factor identity.
Source: blueprint, coherent reductions (blueprint: def-sfb-small-coefficient-derived-completion). -/
def restrictComp (n : ℕ) :
    finiteRestrict l E X n ⋙ restrict l E X (n + 1) ≅ restrict l E X n :=
  (Functor.mapDerivedCategoryCompIso
    (Mod.comap (transition l E X n)) (Mod.comap (quotient l E X (n + 1)))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp (quotient l E X (n + 1)) (transition l E X n)).symm ≪≫
        Mod.comapCongr (quotient_transition l E X n))

/-- The derived reduction identity determined by the canonical adjunction units and counits.
This is the canonical association (P tensor B_(n+2)) tensor B_(n+1) = P tensor B_(n+1).
Source: blueprint, normalization (blueprint: def-sfb-small-coefficient-derived-completion). -/
def reductionComp (n : ℕ) :
    derivedReduction l E X (n + 1) ⋙ finiteExtend l E X n ≅ derivedReduction l E X n :=
  (((Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X (n + 1))).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (transition l E X n))).ofNatIsoRight
        (restrictComp l E X n)).leftAdjointUniq
    (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n))

/-- Transition between the derived reductions, given by the consecutive unit and association.
Source: blueprint, canonical transition maps (blueprint:
def-sfb-small-coefficient-derived-completion). -/
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
Source: blueprint, definition of normalized tower (blueprint:
def-sfb-small-coefficient-derived-completion). -/
def IsNormalized (M : ∀ n : ℕ, FiniteDerived l E X n)
    (t : ∀ n : ℕ, M (n + 1) ⟶ (finiteRestrict l E X n).obj (M n)) : Prop :=
  ∀ n : ℕ, IsIso
    (((Mod.derivedExtendMapDerivedCategoryAdjunction (transition l E X n)).homEquiv
      (M (n + 1)) (M n)).symm (t n))

private theorem isIso_mate_unit {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : C} {B : D}
    (f : F.obj A ⟶ B) [IsIso f] :
    IsIso ((adj.homEquiv A B).symm (adj.unit.app A ≫ G.map f)) := by
  rw [← adj.homEquiv_unit, Equiv.symm_apply_apply]
  infer_instance

/-- The derived reduction tower is normalized with its specified transitions.
Source: blueprint, derived reduction identities (blueprint:
def-sfb-small-coefficient-derived-completion).
Proof: choose a K-flat representative P. Extension to B_(n+2) remains K-flat by
lem-pur-kflat-change-of-rings. Associativity of balanced tensor sends
(p tensor a) tensor b to p tensor image(a)b; its inverse sends p tensor b to
(p tensor 1) tensor b. They are inverse chain maps. The reductionComp construction
is this isomorphism by uniqueness of the left adjoint to the same exact restriction.
Under the adjunction homEquiv, derivedStep is precisely its component; hence it is
invertible. For three levels both associations multiply the same coefficient images,
so their composites agree and give all longer reduction identities. -/
theorem derivedReduction_isNormalized (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K : DerivedCategory (SmallAdicCompletion.Modules l E X)) :
    IsNormalized l E X (fun n ↦ (derivedReduction l E X n).obj K)
      (derivedStep l E X K) := by
  intro n
  exact isIso_mate_unit
    (Mod.derivedExtendMapDerivedCategoryAdjunction (transition l E X n))
    ((reductionComp l E X n).hom.app K)

end AlgebraicGeometry.ProEtale.SmallAdicCompletion
