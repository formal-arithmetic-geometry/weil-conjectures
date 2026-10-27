module

public import Sheaf.Paper.SystemCompactSupportTransitions
public import Sheaf.Paper.SystemCompactSupportEvaluation
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.EtaleSupportProjectionShiftUnit
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CoefficientSystemDerivedComparison
public import Sheaf.CategoryTheory.SystemLevelLeftExtension
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
import Sheaf.SixFunctors.EtaleOpenTensor

/-! # Unbounded compact support and projection on strict étale systems

Source: Stacks Tags 0B56, 0F0G, 0GL1 and 0GL6; the ordinary strict-system
refinement of the integral exceptional-adjoint argument
(blueprint: lem-coef-system-compact-support-projection).

All presentations below are conclusion data. The coefficient index n means n+1.
Tensor comparisons are normalized on ordinary pure tensors and signed total complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures.SemilinearSections
open scoped TensorProduct

namespace AlgebraicGeometry.Etale.SystemCompactSupport
open SystemProjection

/-- The actual positive DVR quotient tower, without a normalization condition on modules.
Source: coefficient-extension convention (blueprint: lem-coef-system-compact-support-projection). -/
def quotientTower (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ℕᵒᵖ ⥤ CommRingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n ↦ CommRingCat.of
    (Padic.coefficientExtensionRing l E (n + 1)))
    (fun n ↦ CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)))

/-- Ordinary unbounded compact support on strict etale systems, with the actual
system projection, the canonical finite-coefficient evaluation, and the quotient
projection and transition equations. All presentation data occur in the conclusion;
there is no flatness, normalization, cartesianness or boundedness premise.

Source: Zheng Constructions 4.1, 5.14--5.15, Lemma 5.16; Stacks 0B56, 0F0G, 0GL1,
0GL6; integral exceptional-adjoint argument, second proof paragraph
(blueprint: lem-coef-system-compact-support-projection).

Proof: Regard strict systems as module sheaves on the ringed vertical sequence site.
Its ordinary inverse images and open extensions are exact, and their adjunctions
localize to the ordinary unbounded derived categories. Derive proper direct image
with K-injective resolutions on that category. The semilinear derived-sections
comparisons give the normalized evaluations of these functors and adjunctions.
Compose open extension and derived proper image to obtain F. Exact localization
and the right-derived triangulated-functor theorem make F triangulated. The DVR
quotients are finite and the finite-type schemes are Noetherian. Thus the finite-ring
proper-image coproduct theorem, together with the open-extension adjunction, proves
coproduct preservation after every evaluation. Componentwise coproducts and joint
conservativity prove preservation on systems, including the empty coproduct.
Construct the proper tensor projection as the transpose of tensor pullback followed
by the geometric counit. Compute open extension tensor on flat-term K-flat complexes:
on each signed total-complex summand it is the ordinary sheaf open tensor identity.
The transpose normalization in ProjectionData records exactly this map. Compose its
inverse with the proper projection to obtain the natural transformation pi. The
pure-tensor and total-complex normalizations of TensorEvaluation and ImageTensor
identify its evaluated word with the published ordinary finite projection. This is
invertible by the unbounded finite-ring proper projection theorem and the open
tensor theorem. Joint conservative evaluation makes pi invertible on systems.
For a quotient A_m to A_n use the published compactScalarMap: its proper factor is
the changed-ring counit projection and its open factor is the termwise tensor
balancing comparison. Both are isomorphisms on all unbounded objects; proper finite
coefficient extension requires no flatness. Mate pasting and tensor reassociation
prove the displayed quotient cocycle as an equality of the specified natural maps.
Finally localize the actual sectionwise strict transition and take its scalar
adjunct, as in TransitionEvaluation.reduction. Compatibility of the geometric
adjunctions with those transitions gives the displayed reduction equation. These
are constructions and equalities before evaluation, not conclusions from equality
of evaluated derived morphisms. -/
theorem systemCompactSupportProjection
    (k : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hlp : l ≠ k.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (X Y : Over (Spec (CommRingCat.of k.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) :
    ∃ d : ProjectionData c Y.hom (quotientTower l E),
    ∃ e : ProjectionEvaluation d,
    ∃ tx : TransitionEvaluation X.left (quotientTower l E) e.ex,
    ∃ ty : TransitionEvaluation Y.left (quotientTower l E) e.ey,
    ∃ pi : d.source ⟶ d.target,
      (∃ (_ : d.support.F.CommShift ℤ), d.support.F.IsTriangulated) ∧
      (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) d.support.F) ∧
      (∀ (P : Derived (Spec (CommRingCat.of k.k)) (quotientTower l E))
        (M : Derived X.left (quotientTower l E)), pi.app (P, M) = d.word P M) ∧
      IsIso pi ∧ e.projectionLaw pi ∧
      (∀ (m n : ℕ) (h : n ≤ m),
        IsIso (compactScalarMap (quotientMap (quotientTower l E) h) c)) ∧
      (∀ (r m n : ℕ) (h : n ≤ m) (h' : m ≤ r),
        compactScalarMap
            (((quotientTower l E).map (homOfLE h').op) ≫
              ((quotientTower l E).map (homOfLE h).op)).hom c =
          singlePath ((quotientTower l E).map (homOfLE h').op)
            ((quotientTower l E).map (homOfLE h).op) c) ∧
      (∀ (m n : ℕ) (h : n ≤ m) (M : Derived X.left (quotientTower l E)),
        ty.reduction h (d.support.F.obj M) ≫ (e.support n).iso.hom.app M =
          (scalarExtension (quotientMap (quotientTower l E) h) Y.left).map
              ((e.support m).iso.hom.app M) ≫
            (compactScalarMap (quotientMap (quotientTower l E) h) c).app
              ((e.ex m).E.obj M) ≫
            (rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} ((quotientTower l E).obj (op n))) c).map
                (tx.reduction h M)) := by
  sorry

end AlgebraicGeometry.Etale.SystemCompactSupport
