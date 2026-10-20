/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.Paper.IntegralTwistDerivedScalarCanonical
public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.Paper.PbcDescentFunctors
public import Sheaf.Paper.IntegralCompactSupportUniformRestriction
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
import Sheaf.Paper.PbcIdempotentCompleteTriangulation
import Sheaf.Paper.IntegralResidueTor
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.FiniteFieldFiber
import Sheaf.Paper.FiniteTorAmplitude
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfDerivedComplete
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.PbcScalarExtension
import Sheaf.CategoryTheory.SemilinearScalarLocalization
import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.Paper.PbcFiniteStageKaroubian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.EtaleCohomology.Purity.Smooth.Rational
import Sheaf.Paper.RationalSmoothPurityCanonical

/-! # Coefficient transitivity and retracts of PBC smooth purity

Source: main-20261015, sec-smooth-purity/sk-lem-sp-field-extension,
prop-pur-rational-purity-transitivity-summands, proof Steps 1--7.
(blueprint: prop-pur-rational-purity-transitivity-summands).

The functors below have the actual PBC integral and rational categories as their
source and target. Twisted pullback is completed pullback followed by the published
Tate tensor and the shift [2d]. Compact support is Rp_* j_! at a compactification,
with the published completed coefficient inverse-image identifications. Exceptional
inverse image is specified by its adjunction to that particular compact support.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option linter.all false
set_option linter.unusedVariables false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeilConjectures
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The completed coefficient system already used by PBC, with its actual pullback maps.
Source: proof Step 1 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityCoefficients : PurCompactSupport.Coefficients.{u} where
  ring W := pbcAdicCompletion W (pbcIntegralDatum l E)
  pull g := cbcCompletedCoefficientIso g (pbcIntegralDatum l E)

/-- The actual proper/open compact-support composite, before restricting its domain.
Source: proof Step 1 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityCompactAmbient {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    PbcCompletedDerived X (pbcIntegralDatum l E) ⥤
      PbcCompletedDerived Y (pbcIntegralDatum l E) :=
  PurCompactSupport.image (pbcPurityCoefficients l E) c

/-- The actual completed inverse image followed by Tate tensor and [2d].
Source: proof Step 1, H_E (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityTwistedAmbient {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] :
    PbcCompletedDerived Y (pbcIntegralDatum l E) ⥤
      PbcCompletedDerived X (pbcIntegralDatum l E) :=
  pbcActualCompletedPull f (pbcIntegralDatum l E) ⋙
    pbcTateAmbient l X E (d : ℤ) ⋙ shiftFunctor _ (2 * (d : ℤ))

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The geometric bounds and invertibility used in the PBC category notation follow
from the fixed setting, including for the empty scheme.
Source: proof Step 1 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: finite type over the field gives Noetherianity and finite dimension by
lem-weil-pbc-finite-type-over-noetherian and lem-kun-dimension-finite-type. The
image of l is invertible in k since l differs from p; map its inverse to each stalk. -/
theorem pbcPurityGeometricBounds (hl : l ≠ D.p) (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))] :
    IsNoetherian W ∧ (∃ n : ℕ, topologicalKrullDim W ≤ (n : WithBot ℕ∞)) ∧
      ∀ x : W, IsUnit (l : W.presheaf.stalk x) := by
  sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) (W : Scheme.{u})
    [IsNoetherian W]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim W ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]

/-- The coefficient transport puts a PBC lattice in the recorded intrinsic category.
Source: proof Step 1 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: the bounded-predicate clause of purCoefficientModel identifies the two
constructible complete predicates. Invertibility in every stalk implies the same
for the global section l, by the local criterion for invertibility. Apply that
clause to the lattice's membership proof. -/
theorem pbcPurityModel_mem
    (K : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)) :
    sfIntegralConstructible l E W ((purCoefficientModel l E W).functor.obj K.obj) := by
  sorry

/-- The ordinary Tate transport round trip, fixed by identity section functions.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: expand the transported Tate tensor. The final two coefficient restrictions
are along mutually inverse ring isomorphisms. The identity section functions are
linear, natural and inverse; sectionwise faithfulness proves uniqueness. -/
theorem pbcPurityOrdinaryTateModel_existsUnique (m : ℤ) :
    ∃! e : pbcTateSheafTensor l W E m ⋙ purOrdinaryCoefficientModel l E W ≅
        purOrdinaryCoefficientModel l E W ⋙ integralSheafTwist l E W m,
      ∀ (M : pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E)))
        (U : W.ProEtᵒᵖ)
        (x : ((pbcTateSheafTensor l W E m ⋙
          purOrdinaryCoefficientModel l E W).obj M).val.obj U),
        (e.hom.app M).val.app U x = x := by
  sorry

/-- The identity-on-sections Tate transport used before derived localization.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityOrdinaryTateModel (m : ℤ) :=
  (pbcPurityOrdinaryTateModel_existsUnique l E W m).exists.choose

/-- Derived Tate transport, using exactly the ordinary identity-section comparison.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityTateModel (m : ℤ) :
    pbcTateAmbient l W E m ⋙ (purCoefficientModel l E W).functor ≅
      (purCoefficientModel l E W).functor ⋙
        (integralSheafTwist l E W m).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (pbcTateSheafTensor l W E m)
    (purOrdinaryCoefficientModel l E W)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pbcPurityOrdinaryTateModel l E W m) ≪≫
      Functor.mapDerivedCategoryCompIso (purOrdinaryCoefficientModel l E W)
        (integralSheafTwist l E W m)

/-- Identify the two published ordinary scalar models on their tensor generators.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: both coefficient maps have the same finite quotient projections, hence are
equal. Both ordinary models are the sheafified balanced tensor. Sending b tensor x
to b tensor x is balanced and natural; these local generators prove uniqueness. -/
theorem pbcPurityOrdinaryScalarModel_existsUnique :
    ∃! e : integralOrdinaryScalar l E F i W ≅
        completedOrdinaryScalarExtension l E F i W,
      ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
        (b : (completedIntegralCommRingSheafUnrestricted l F W).obj.obj U)
        (x : M.val.obj U),
        (e.hom.app M).val.app U (integralOrdinaryTensorSection l E F i W M U b x) =
          completedScalarTensorSection l E F i W M U b x := by
  sorry

/-- The ordinary tensor-generator identity between the two published presentations.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityOrdinaryScalarModel :=
  (pbcPurityOrdinaryScalarModel_existsUnique l E F i W).exists.choose

/-- The derived scalar-model identification is fixed by the universal counits.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: finite free scalar extension is exact. Its termwise derived functor is
therefore also a total left derived functor. Conjugate the two universal counits
by the ordinary generator identity. Universality gives the unique natural iso;
the same computation on every representative gives the displayed equation. -/
theorem pbcPurityDerivedScalarModel_existsUnique :
    ∃! e : integralOrdinaryDerivedScalar l E F i W ≅
        completedDerivedScalarExtension l E F i W,
      ∀ P : CochainComplex (integralTowerModules l E W) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E F i W P =
          (integralOrdinaryScalar l E F i W).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (pbcPurityOrdinaryScalarModel l E F i W)
                (.up ℤ)).hom.app P) := by
  sorry

/-- The universal-counit normalized derived scalar-model identification.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityDerivedScalarModel :=
  (pbcPurityDerivedScalarModel_existsUnique l E F i W).exists.choose

/-- Tate/scalar comparison transported from the published pure-tensor normalized beta.
The model functor is fully faithful, so preimageIso retains that precise map.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityTateScalarComponent (m : ℤ)
    (K : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l E F i W).obj ((pbcTateAmbient l W E m).obj K.obj) ≅
      (pbcTateAmbient l W F m).obj ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj) :=
  (purCoefficientModel l F W).functor.preimageIso
    ((purScalarModel l E F i W).app ((pbcTateAmbient l W E m).obj K.obj) ≪≫
      (pbcPurityDerivedScalarModel l E F i W).app
        ((purCoefficientModel l E W).functor.obj ((pbcTateAmbient l W E m).obj K.obj)) ≪≫
      (completedDerivedScalarExtension l E F i W).mapIso
        ((pbcPurityTateModel l E W m).app K.obj) ≪≫
      (integralTwistOrdinaryBeta l E F i W m).app
        ⟨(purCoefficientModel l E W).functor.obj K.obj, pbcPurityModel_mem l E W K⟩ ≪≫
      (integralSheafTwist l F W m).mapDerivedCategory.mapIso
        (((pbcPurityDerivedScalarModel l E F i W).app
          ((purCoefficientModel l E W).functor.obj K.obj)).symm ≪≫
          ((purScalarModel l E F i W).app K.obj).symm) ≪≫
      ((pbcPurityTateModel l F W m).app
        ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj)).symm)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f) (d : ℕ)
    [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- Completed pullback preserves the actual integral lattice category.
Source: proof Step 1 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: reduction commutes with completed pullback by its quotient augmentation.
Finite pullback is exact and preserves constructible finite stalks, so it preserves
the common support interval and etale origins. The strict reduction-tower formula
supplies the intrinsic completeness condition, including the zero object. -/
theorem pbcPurityPull_mem
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((pbcActualCompletedPull f (pbcIntegralDatum l E)).obj K.obj) := by
  sorry

/-- The two actual ambient functors preserve lattices and their scalar action.
Source: proof Steps 1--2 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: pbcPurityPull_mem, Tate tensor preservation and shift preservation give the
first assertion. For compact support use exact extension by zero followed by
proper direct image and integral-stratified-perfect-characterization. Both preserve
the uniform reduction interval and compatible etale origins. On chain maps both
functors are additive and commute with the canonical constant scalar action;
these equations descend through the derived localization. -/
theorem pbcPurityAmbientProperties [QuasiCompact f] :
    (∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
        ((pbcPurityTwistedAmbient l E f d).obj K.obj)) ∧
    (∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
        ((pbcPurityCompactAmbient l E c).obj K.obj)) ∧
    (pbcPurityTwistedAmbient l E f d).Additive ∧
    (pbcPurityTwistedAmbient l E f d).Linear (PbcIntegralRing l E) ∧
    (pbcPurityCompactAmbient l E c).Additive ∧
    (pbcPurityCompactAmbient l E c).Linear (PbcIntegralRing l E) := by
  sorry

/-- Lf^*(-)(d)[2d] on the actual raw PBC rational category.
Source: proof Step 2 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityTwisted [QuasiCompact f] :
    PbcRationalDerivedCategory l E Y dY.out iY.out ⥤
      PbcRationalDerivedCategory l E X dX.out iX.out :=
  letI := (pbcPurityAmbientProperties l E f c d).2.2.1
  letI := (pbcPurityAmbientProperties l E f c d).2.2.2.1
  pbcConditionalRational (pbcIntegralDatum l E) (pbcPurityTwistedAmbient l E f d)
    (pbcPurityAmbientProperties l E f c d).1 (pbcUniformizer l E)

/-- Rp_* j_! on the same raw PBC rational categories.
Source: proof Step 2 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityCompact [QuasiCompact f] :
    PbcRationalDerivedCategory l E X dX.out iX.out ⥤
      PbcRationalDerivedCategory l E Y dY.out iY.out :=
  letI := (pbcPurityAmbientProperties l E f c d).2.2.2.2.1
  letI := (pbcPurityAmbientProperties l E f c d).2.2.2.2.2
  pbcConditionalRational (pbcIntegralDatum l E) (pbcPurityCompactAmbient l E c)
    (pbcPurityAmbientProperties l E f c d).2.1 (pbcUniformizer l E)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F)

/-- The published completed coefficient inclusion commutes with pullback.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: compose with each finite projection. Both paths restrict the same locally
constant function and apply the same residue-ring inclusion. Limit projections
are jointly monic, giving the equality, including ramified extensions. -/
theorem pbcPurityCoefficientChange_square {U V : Scheme.{u}} (g : U ⟶ V) :
    ((pbcPurityCoefficients l E).pull g).hom ≫ pbcScalarCoefficientMap l E F i U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (pbcScalarCoefficientMap l E F i V) ≫ ((pbcPurityCoefficients l F).pull g).hom := by
  sorry

/-- The actual coefficient change, with no comparison map chosen independently.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityCoefficientChange :
    PurCompactSupport.Change (pbcPurityCoefficients l E) (pbcPurityCoefficients l F) where
  map W := pbcScalarCoefficientMap l E F i W
  square g := pbcPurityCoefficientChange_square l E F i g

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f) (d : ℕ)
    [QuasiCompact f] [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- The actual pullback/tensor/twist/shift coefficient comparison at a lattice.
Its three factors are shift/scalar interchange, the pure-tensor Tate comparison,
and the inverse of the published completed-pullback scalar comparison.
Source: proof Step 3, a (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityTwistedScalarComponent
    (K : PbcRationalDerivedCategory l E Y dY.out iY.out) :
    (pbcRationalScalarExtension l E F i X dX.out iX.out).obj
        ((pbcPurityTwisted l E f c d).obj K) ≅
      (pbcPurityTwisted l F f c d).obj
        ((pbcRationalScalarExtension l E F i Y dY.out iY.out).obj K) :=
  letI : (pbcEmbeddingAmbientTensor l E F i X).CommShift ℤ :=
    PurCompactSupport.scalarCommShift (pbcScalarCoefficientMap l E F i X)
  (pbcRationalization X (pbcIntegralDatum l F) (pbcUniformizer l F)).mapIso
    (ObjectProperty.isoMk (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l F))
      (((pbcEmbeddingAmbientTensor l E F i X).commShiftIso (2 * (d : ℤ))).app
          ((pbcTateAmbient l X E (d : ℤ)).obj
            ((pbcActualCompletedPull f (pbcIntegralDatum l E)).obj K.obj.obj)) ≪≫
        (shiftFunctor _ (2 * (d : ℤ))).mapIso
          (pbcPurityTateScalarComponent l E F i X (d : ℤ)
            ⟨(pbcActualCompletedPull f (pbcIntegralDatum l E)).obj K.obj.obj,
              pbcPurityPull_mem l E f K.obj⟩) ≪≫
        (shiftFunctor _ (2 * (d : ℤ))).mapIso
          ((pbcTateAmbient l X F (d : ℤ)).mapIso
            (((pbcScalarCompletedPullIso l E F i f).app K.obj.obj).symm))))

/-- The specified coefficient maps extend naturally to every rational morphism.
Source: proof Steps 2--3 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: each integral factor is natural and semilinear for the integer-ring inclusion.
Extend this equality to every pure tensor a tensor u in the localized Hom modules.
These generate each Hom, so the equality holds with arbitrary denominators. -/
theorem pbcPurityTwistedScalar_naturality
    {K L : PbcRationalDerivedCategory l E Y dY.out iY.out} (u : K ⟶ L) :
    (pbcPurityTwisted l E f c d ⋙
        pbcRationalScalarExtension l E F i X dX.out iX.out).map u ≫
        (pbcPurityTwistedScalarComponent l E F i f c d L).hom =
      (pbcPurityTwistedScalarComponent l E F i f c d K).hom ≫
        (pbcRationalScalarExtension l E F i Y dY.out iY.out ⋙
          pbcPurityTwisted l F f c d).map u := by
  sorry

/-- The canonical a comparison, defined from the actual three normalized factors.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityTwistedScalar :
    pbcPurityTwisted l E f c d ⋙ pbcRationalScalarExtension l E F i X dX.out iX.out ≅
      pbcRationalScalarExtension l E F i Y dY.out iY.out ⋙ pbcPurityTwisted l F f c d :=
  NatIso.ofComponents (pbcPurityTwistedScalarComponent l E F i f c d)
    (fun u ↦ pbcPurityTwistedScalar_naturality l E F i f c d u)

/-- Rationalization of the actual proper/open compact-support scalar mate.
Source: proof Step 3, c (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityCompactScalarComponent
    (K : PbcRationalDerivedCategory l E X dX.out iX.out) :
    (pbcRationalScalarExtension l E F i Y dY.out iY.out).obj
        ((pbcPurityCompact l E f c d).obj K) ⟶
      (pbcPurityCompact l F f c d).obj
        ((pbcRationalScalarExtension l E F i X dX.out iX.out).obj K) :=
  (pbcRationalization Y (pbcIntegralDatum l F) (pbcUniformizer l F)).map
    (ObjectProperty.homMk
      ((PurCompactSupport.comparison (pbcPurityCoefficientChange l E F i) c).app K.obj.obj))

/-- Naturality and invertibility of the specified compact-support scalar mate.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: integral coefficient comparison is natural. Finite freeness makes that
comparison invertible on complete inputs; restrict it to the actual lattice
categories and rationalize its inverse. The fraction formula gives naturality on
all rational arrows and preserves the two inverse equations. -/
theorem pbcPurityCompactScalar_properties :
    (∀ (K : PbcRationalDerivedCategory l E X dX.out iX.out),
      IsIso (pbcPurityCompactScalarComponent l E F i f c d K)) ∧
    ∀ {K L : PbcRationalDerivedCategory l E X dX.out iX.out} (u : K ⟶ L),
      (pbcPurityCompact l E f c d ⋙
          pbcRationalScalarExtension l E F i Y dY.out iY.out).map u ≫
          pbcPurityCompactScalarComponent l E F i f c d L =
        pbcPurityCompactScalarComponent l E F i f c d K ≫
          (pbcRationalScalarExtension l E F i X dX.out iX.out ⋙
            pbcPurityCompact l F f c d).map u := by
  sorry

/-- The canonical compact-support scalar isomorphism, with its mate normalization.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityCompactScalar :
    pbcPurityCompact l E f c d ⋙ pbcRationalScalarExtension l E F i Y dY.out iY.out ≅
      pbcRationalScalarExtension l E F i X dX.out iX.out ⋙ pbcPurityCompact l F f c d :=
  NatIso.ofComponents
    (fun K ↦ by
      letI := (pbcPurityCompactScalar_properties l E F i f c d).1 K
      exact asIso (pbcPurityCompactScalarComponent l E F i f c d K))
    (fun u ↦ (pbcPurityCompactScalar_properties l E F i f c d).2 u)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) [IsNoetherian W]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim W ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]

/-- Compare actual rational tensor with the literal-unit normalized stage transition.
The component is specified by the recorded integral comparison, including repeated
stages. No scalar extension or associator is supplied as a free variable.
Source: proof Steps 3--4 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: the two completed coefficient inclusions agree on every finite quotient,
hence agree. Their derived tensors and raw localizations agree. Conjugate by the
recorded integral comparison; its normalization at equal stages is multiplication
by one. Extend its integral naturality to every tensor-Hom fraction. Components
on all integral representatives determine a natural isomorphism uniquely. -/
theorem pbcPurityScalarNormalization_existsUnique
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    ∃! n : pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) W hDim.out hInv.out ≅
        (pbcScalarSystem l Ω W hDim.out hInv.out).T h,
      ∀ K : pbcIntegralStage l Ω W E,
        HEq (n.hom.app (ScalarLocalization.mk K))
          ((pbcScalarIntegralComparison l Ω W hDim.out hInv.out h).inv.app K) := by
  sorry

/-- The canonical normalization of rational scalar transitions.
Source: proof Steps 3--4 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityScalarNormalization
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :=
  (pbcPurityScalarNormalization_existsUnique l Ω W h).exists.choose

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f) (d : ℕ)
    [QuasiCompact f] [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- The actual twisted inverse image at a finite coefficient stage of Qbar.
Source: proof Step 2 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityStageTwisted (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω Y E ⥤ pbcStageCategory l Ω X E :=
  pbcPurityTwisted l (pbcFiniteField.{u} l Ω E) f c d

/-- The actual proper/open compact support at that same finite stage.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityStageCompact (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω X E ⥤ pbcStageCategory l Ω Y E :=
  pbcPurityCompact l (pbcFiniteField.{u} l Ω E) f c d

/-- The specified a comparison in the normalized stage coordinates.
Source: proof Steps 3--4 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityStageA {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcPurityStageTwisted l Ω f c d E ⋙ (pbcScalarSystem l Ω X dX.out iX.out).T h ≅
      (pbcScalarSystem l Ω Y dY.out iY.out).T h ⋙ pbcPurityStageTwisted l Ω f c d F :=
  Functor.isoWhiskerLeft _ (pbcPurityScalarNormalization l Ω X h).symm ≪≫
    pbcPurityTwistedScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
      (pbcFiniteFieldInclusion l Ω h) f c d ≪≫
    Functor.isoWhiskerRight (pbcPurityScalarNormalization l Ω Y h) _

/-- The compact-support comparison in normalized stage coordinates.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityStageC {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcPurityStageCompact l Ω f c d E ⋙ (pbcScalarSystem l Ω Y dY.out iY.out).T h ≅
      (pbcScalarSystem l Ω X dX.out iX.out).T h ⋙ pbcPurityStageCompact l Ω f c d F :=
  Functor.isoWhiskerLeft _ (pbcPurityScalarNormalization l Ω Y h).symm ≪≫
    pbcPurityCompactScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
      (pbcFiniteFieldInclusion l Ω h) f c d ≪≫
    Functor.isoWhiskerRight (pbcPurityScalarNormalization l Ω X h) _

/-- The actual pullback/tensor comparisons obey the tensor associator equation.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: on flat-term K-flat representatives the two composites multiply the same
two scalar factors and send the root line by the same twistScalarMaps. Tensor
associativity, root-line transitivity and canonical shift interchange identify
them. Universal counits descend that equality, then scalar localization preserves
it. Conjugation by the fixed unit normalizations gives the displayed equation. -/
theorem pbcPurityStageA_coherence {E F L : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (k : F ≤ L) (K : pbcStageCategory l Ω Y E) :
    ((pbcScalarSystem l Ω X dX.out iX.out).T k).map
        ((pbcPurityStageA l Ω f c d h).hom.app K) ≫
      (pbcPurityStageA l Ω f c d k).hom.app
        (((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj K) ≫
      (pbcPurityStageTwisted l Ω f c d L).map
        (((pbcScalarSystem l Ω Y dY.out iY.out).assoc h k).hom.app K) =
    ((pbcScalarSystem l Ω X dX.out iX.out).assoc h k).hom.app
        ((pbcPurityStageTwisted l Ω f c d E).obj K) ≫
      (pbcPurityStageA l Ω f c d (h.trans k)).hom.app K := by
  sorry

/-- The actual twisted inverse-image family with its specified comparison maps.
Source: proof Steps 3--5 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityTwistedSystem :
    StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out) where
  Φ := pbcPurityStageTwisted l Ω f c d
  β := pbcPurityStageA l Ω f c d
  coh := pbcPurityStageA_coherence l Ω f c d

/-- Exceptional inverse image is right adjoint to the actual proper/open compact
support. Its b comparison is the adjoint transpose of inverse c followed by the
old counit. The counit equation fixes every component uniquely, so a sign change
of b cannot satisfy this normalization.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def PbcPurityExceptionalSpec
    (G : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out)) : Prop :=
  ∃ adj : ∀ E : Padic.FiniteCoefficientFields l Ω,
      pbcPurityStageCompact l Ω f c d E ⊣ G.Φ E,
    ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
      (K : pbcStageCategory l Ω Y E),
      (pbcPurityStageCompact l Ω f c d F).map ((G.β h).hom.app K) ≫
          (adj F).counit.app (((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj K) =
        (pbcPurityStageC l Ω f c d h).inv.app ((G.Φ E).obj K) ≫
          ((pbcScalarSystem l Ω Y dY.out iY.out).T h).map ((adj E).counit.app K)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f) (d : ℕ)
    [QuasiCompact f] [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- Step 4's pasted-square equation, retaining the actual tensor associators at both
ends. The middle expression is successive extension; the first and last use direct
extension. This is an equality of maps, not merely existence of compositors.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def PbcPurityTransitivity
    (G : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out))
    (γ : ∀ E : Padic.FiniteCoefficientFields l Ω,
      pbcPurityStageTwisted l Ω f c d E ≅ G.Φ E) : Prop :=
  ∀ {E F L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) (k : F ≤ L)
    (K : pbcStageCategory l Ω Y E),
    (((pbcScalarSystem l Ω X dX.out iX.out).assoc h k).hom.app
          ((pbcPurityStageTwisted l Ω f c d E).obj K) ≫
        ((pbcScalarSystem l Ω X dX.out iX.out).T (h.trans k)).map ((γ E).hom.app K) ≫
        (G.β (h.trans k)).hom.app K =
      ((pbcScalarSystem l Ω X dX.out iX.out).T k).map
          (((pbcScalarSystem l Ω X dX.out iX.out).T h).map ((γ E).hom.app K)) ≫
        ((pbcScalarSystem l Ω X dX.out iX.out).T k).map ((G.β h).hom.app K) ≫
        (G.β k).hom.app (((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj K) ≫
        (G.Φ L).map (((pbcScalarSystem l Ω Y dY.out iY.out).assoc h k).hom.app K)) ∧
    (((pbcScalarSystem l Ω X dX.out iX.out).assoc h k).hom.app
          ((pbcPurityStageTwisted l Ω f c d E).obj K) ≫
        ((pbcScalarSystem l Ω X dX.out iX.out).T (h.trans k)).map ((γ E).hom.app K) ≫
        (G.β (h.trans k)).hom.app K =
      ((pbcScalarSystem l Ω X dX.out iX.out).assoc h k).hom.app
          ((pbcPurityStageTwisted l Ω f c d E).obj K) ≫
        (pbcPurityStageA l Ω f c d (h.trans k)).hom.app K ≫
        (γ L).hom.app (((pbcScalarSystem l Ω Y dY.out iY.out).T (h.trans k)).obj K))

/-- Descent on the actual PBC Qbar categories, including the common-stage naturality
square and both component formulas. Morphism classes and enlargement independence
are those of the recorded StageSystem descent functors themselves.
Source: proof Step 5 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def PbcPurityDescent
    (G : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out))
    (γ : ∀ E : Padic.FiniteCoefficientFields l Ω,
      pbcPurityStageTwisted l Ω f c d E ≅ G.Φ E)
    (γQ : (pbcPurityTwistedSystem l Ω f c d).functor ≅ G.functor) : Prop :=
  StageSystem.Morphism.DescentSpec (pbcPurityTwistedSystem l Ω f c d) ∧
  StageSystem.Morphism.DescentSpec G ∧
  (∀ K : pbcQbarCategory l Ω Y,
    γQ.hom.app K = (Functor.whiskerRight (γ K.stage).hom
      ((pbcScalarSystem l Ω X dX.out iX.out).ι K.stage)).app K.obj ∧
    γQ.inv.app K = (Functor.whiskerRight (γ K.stage).inv
      ((pbcScalarSystem l Ω X dX.out iX.out).ι K.stage)).app K.obj) ∧
  ∀ {E F M : Padic.FiniteCoefficientFields l Ω} (hE : E ≤ M) (hF : F ≤ M)
    (K : pbcStageCategory l Ω Y E) (L : pbcStageCategory l Ω Y F)
    (u : ((pbcScalarSystem l Ω Y dY.out iY.out).T hE).obj K ⟶
      ((pbcScalarSystem l Ω Y dY.out iY.out).T hF).obj L),
    ((G.β hE).hom.app K ≫ (G.Φ M).map u ≫ (G.β hF).inv.app L) ≫
        ((pbcScalarSystem l Ω X dX.out iX.out).T hF).map ((γ F).inv.app L) =
      ((pbcScalarSystem l Ω X dX.out iX.out).T hE).map ((γ E).inv.app K) ≫
        ((pbcPurityStageA l Ω f c d hE).hom.app K ≫
          (pbcPurityStageTwisted l Ω f c d M).map u ≫
          (pbcPurityStageA l Ω f c d hF).inv.app L)

/-- The complete coefficient-square, associator, descent and retract assertion.
All categories, scalar transitions and a comparisons are specified constructions.
The exceptional family is pinned to actual compact support by its adjunction and
counit-mate normalization. No arbitrary pair of functors can instantiate this.
Source: proof Steps 1--7 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def PbcPurityCoefficientConclusion : Prop :=
  ∃ G : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out),
    PbcPurityExceptionalSpec l Ω f c d G ∧
    ∃ γ : ∀ E : Padic.FiniteCoefficientFields l Ω,
        pbcPurityStageTwisted l Ω f c d E ≅ G.Φ E,
      (∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
        (K : pbcStageCategory l Ω Y E),
        ((pbcScalarSystem l Ω X dX.out iX.out).T h).map ((γ E).hom.app K) ≫
            (G.β h).hom.app K =
          (pbcPurityStageA l Ω f c d h).hom.app K ≫
            (γ F).hom.app (((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj K)) ∧
      PbcPurityTransitivity l Ω f c d G γ ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : pbcStageCategory l Ω Y E) (e : K ⟶ K) (he : e ≫ e = e),
        IsIso (((Idempotents.functorExtension₂
          (pbcStageCategory l Ω Y E) (pbcStageCategory l Ω X E)).map (γ E).hom).app
            ⟨K, e, he⟩)) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω) {J K : pbcStageCategory l Ω Y E}
        (i : J ⟶ K) (r : K ⟶ J) (_hi : i ≫ r = 𝟙 J),
        (pbcPurityStageTwisted l Ω f c d E).map i ≫ (γ E).hom.app K ≫
            (G.Φ E).map r = (γ E).hom.app J ∧
        (G.Φ E).map i ≫ (γ E).inv.app K ≫
            (pbcPurityStageTwisted l Ω f c d E).map r = (γ E).inv.app J) ∧
      ∃ γQ : (pbcPurityTwistedSystem l Ω f c d).functor ≅ G.functor,
        PbcPurityDescent l Ω f c d G γ γQ ∧
        (∀ (K : pbcQbarCategory l Ω Y) (e : K ⟶ K) (he : e ≫ e = e),
          IsIso (((Idempotents.functorExtension₂
            (pbcQbarCategory l Ω Y) (pbcQbarCategory l Ω X)).map γQ.hom).app ⟨K, e, he⟩)) ∧
        ∀ {J K : pbcQbarCategory l Ω Y} (i : J ⟶ K) (r : K ⟶ J)
          (_hi : i ≫ r = 𝟙 J),
          (pbcPurityTwistedSystem l Ω f c d).functor.map i ≫ γQ.hom.app K ≫
              G.functor.map r = γQ.hom.app J ∧
          G.functor.map i ≫ γQ.inv.app K ≫
              (pbcPurityTwistedSystem l Ω f c d).functor.map r = γQ.inv.app J

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
    [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
    [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
    [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
    [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
    [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
    (d : ℕ) [fsm : SmoothOfRelativeDimension d f]

/-- Supply the source-implied PBC category bounds without extra geometric assumptions.
Source: proof Step 1 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def PbcRationalPurityConclusion : Prop := by
  letI := (pbcPurityGeometricBounds l D hl X).1
  letI := (pbcPurityGeometricBounds l D hl Y).1
  letI : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞)) :=
    ⟨(pbcPurityGeometricBounds l D hl X).2.1⟩
  letI : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞)) :=
    ⟨(pbcPurityGeometricBounds l D hl Y).2.1⟩
  letI : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x)) :=
    ⟨(pbcPurityGeometricBounds l D hl X).2.2⟩
  letI : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :=
    ⟨(pbcPurityGeometricBounds l D hl Y).2.2⟩
  exact ∀ c : Compactification f, PbcPurityCoefficientConclusion l Ω f c d

include Xbase Ybase Xsep Ysep Xft Xqc Yft Yqc fbase fsep fft fqc fsm hl in
/-- The actual rational purity isomorphisms admit their normalized coefficient square,
its tensor-associator transitivity equation, compatible Qbar descent and restriction
to every rational or Qbar idempotent summand.

Source: main-20261015, sec-smooth-purity/sk-lem-sp-field-extension,
prop-pur-rational-purity-transitivity-summands, proof Steps 1--7
(blueprint: prop-pur-rational-purity-transitivity-summands).

Proof:
1. In the fixed smooth separated finite-type setting, use Noetherianity, finite
   dimension and stalkwise invertibility supplied by pbcPurityGeometricBounds.
   Integral-stratified-perfect-characterization and integral-residue-tor put every
   actual PBC lattice in the finite-Tor domain of the simultaneous natural adic
   purity construction of lem-pur-adic-purity-scalar-naturality. Its exceptional
   functor is the constructible right adjoint of the specified proper/open image.
2. Rational-transport extends that entire integral construction and its natural
   transformations, not independently chosen objectwise lifts. Tensor-Hom
   localization gives naturality for every fraction u/varpi^r, including rational
   idempotents with no integral idempotent representative. Rationalizing both
   inverse equations proves that each gamma is an isomorphism.
3. Semilinear scalar localization carries the integral coefficient square to the
   square with the actual a and b. The a defined above is precisely completed
   pullback, pure-tensor Tate comparison and shift interchange. The b is fixed by
   the inverse compact-support comparison followed by the old counit. The
   normalization bridges agree on tensor generators and universal counits.
4. Apply the second extension to the first square and paste with the next square.
   Substitute both canonical associator equations, and use associator naturality
   at gamma. The two equalities in PbcPurityTransitivity are exactly this
   calculation. Identity extensions use the stipulated tensor multiplication unit.
5. Apply pbcDescentFunctors to the two exact coherent families. The purity square
   gives a compatible transformation and its inverse. Descend both maps and their
   inverse identities. On a common-stage arrow the two squares and naturality at
   that stage give PbcPurityDescent's representative equation. Descended objects
   and arrows are in the actual pbcQbarCategory, with no change of category.
6. Naturality at every idempotent gives the sandwich of gamma with its projectors.
   In Karoubi its inverse is the corresponding sandwich of gamma inverse. Their
   composites are the projectors, the identities of those Karoubi objects. This
   applies at each rational stage and after descent. The exact Karoubi equivalence
   of pbcIdempotentCompleteTriangulation interprets these as the actual summands,
   independently of any chosen splitting or finite-stage representative.
7. For any actual retract i:J to K and r:K to J, naturality identifies
   H(i) followed by gamma_K followed by G(r) with gamma_J, since i followed
   by r is identity. The same calculation identifies the inverse restriction.
   Another splitting is related by its canonical inverse splitting maps, so
   naturality identifies its restriction too. Every coefficient functor preserves
   the splitting equations; the square and Step 4 at J therefore give the
   coefficient and transitivity statements for the restriction. After descent
   the same calculation uses actual common-stage morphism classes and the
   Step 5 representative independence. -/
theorem rationalPurityTransitivitySummands :
    PbcRationalPurityConclusion l Ω D hl f d := by
  sorry

end AlgebraicGeometry.Scheme
