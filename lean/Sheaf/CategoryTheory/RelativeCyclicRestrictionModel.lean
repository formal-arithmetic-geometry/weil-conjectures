/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution
public import Sheaf.CategoryTheory.CondensedDerivedInvariantBar
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.CategoryTheory.CondensedProductActionInflation
import Sheaf.CategoryTheory.InternalActionSitePresentation
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.CategoryTheory.BoundedBelowDerivedMateModel
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import Sheaf.CategoryTheory.ActionToposGeometricRestriction
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.DerivedAdjunctionShift

public import Sheaf.CategoryTheory.RelativeDerivedInvariants
public import Sheaf.CategoryTheory.RelativeCyclicTotal
public import Sheaf.CategoryTheory.RelativeInvariantForgetting
public import Sheaf.CategoryTheory.RelativeCoefficientComparison
public import Sheaf.CategoryTheory.RelativeBarData
public import Sheaf.CategoryTheory.RelativeTrivialCyclicMap
public import Sheaf.CategoryTheory.RelativeLatticeBridge

/-! # Relative cyclic restriction model and forgetting the residual action

Source: main-20261015, six-functors direct-images proof, paragraph (3),
agent-formulated relative rank-one input (exact combined reference wanted).
(blueprint: lem-sfb-relative-cyclic-restriction-model)

## Main definitions and statements

The primary declaration is `relative_cyclic_restriction_model`.
The accompanying definitions fix the canonical maps, coordinates and normalization equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (inflate ProductInvariants)
namespace CategoryTheory.RelativeCyclic
variable (A : CondensedBar.Ring.{u}) (G J : Type u)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {A' : CondensedBar.Ring.{u}}
variable {J}
variable {A G}

set_option backward.isDefEq.respectTransparency false in
/-- The bar evaluation identity for the actual relative cyclic restriction map, in the
ordinary derived category, for every compatible nonnegative injective resolution.
Source: paragraph (3), steps 15--18
(blueprint: lem-sfb-relative-cyclic-restriction-model).
Proof: on the compatible double complex define E to be identity on column zero, evaluation
at v(1) on column one, and zero on all higher columns. The only horizontal equation is
(d_h m)(v(1)) = (T-1)m. Vertical evaluation commutes with d_I, with the same signs in both
totals. Hence E is a cochain map, and E b_H is the invariant inclusion into the cyclic
total. The beta model equation and theta alpha = Qb give c = Q(K(Va)) inverse after
Q(E b_H). The bar comparison eta is Qb_H after the normalized resolution comparison.
Cancel Qb_H and note that E applied to j equals K(Va) after epsilon: this is a in degree
zero, a after evaluation at v(1) in degree one, and zero in higher degrees. Cancellation
of the quasi-isomorphism K(Va) gives the stated identity; beta is never inverted. -/
theorem barEvaluation [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    {K : TotalModel A PUnit.{u + 1}}
    (C : HasComparison A PUnit.{u + 1} K) (v : Z.{u} →ₜ* H)
    (M : BarModel A H) (b : BarNormalization M)
    (I : InjectiveResolution (CondensedDerivedRestriction.regularTrivial A H)) :
    DerivedCategory.Q.map (HomologicalComplex.extendMap
        (barAugmentation (barFunctions M) (barDiagram M)
          (CondensedDerivedRestriction.regularTrivial A H) I) ComplexShape.embeddingUpNat) ≫
      (barEta M b (CondensedDerivedRestriction.regularTrivial A H) I).inv ≫
      trivialCyclicMap C v =
    DerivedCategory.Q.map (HomologicalComplex.extendMap
      (evaluation (barFunctions M) (barDiagram M) v) ComplexShape.embeddingUpNat) := by
  sorry

variable (A G)

/-- The relative cyclic total descends to a triangulated functor and computes ordinary
relative derived invariants with the invariant-inclusion normalization.
Source: main-20261015 direct-images proof, paragraph (3), agent-formulated relative input
(blueprint: lem-sfb-relative-cyclic-restriction-model).

Proof, following the node's eighteen steps:
1. Use the section-module equivalence and action-site presentation for G, H, G times H,
   and G times the discrete integers. Their module categories are Grothendieck abelian.
2. Fixed sections after every base change give projection invariants with the normalized
   adjunction to exact trivial-second-factor inflation, retaining the first action.
3. Forgetting is exact and conservative on modules. Cohomology and cone triangles show
   that the induced ordinary derived functors are also conservative, without boundedness.
4. Free induction R[G] tensor - is an exact left adjoint to forgetting, by flatness of
   represented free modules (03EV). Consequently forgetting preserves injectives.
5. Derive the identity inflation square to define beta, with its invariant-inclusion unit
   equation. Shift-compatible units and counits make beta preserve triangle boundaries.
6. Forget an equivariant injective resolution; it remains injective and computes the same
   invariant submodule. Resolution naturality gives forgetDerived and forgetBeta.
7. The differential on N^n plus N^(n-1) squares to zero since d_N commutes with T. Maps
   act on both coordinates and a homotopy totalizes as (h,-h). Column comparison gives
   preservation of quasi-isomorphisms; shift a common lower bound to zero and re-sign.
8. The shift is (x,y) maps to (x,(-1)^s y). Reordering the summands of the cone and
   multiplying its source summand in column a by (-1)^a identifies the cone triangles,
   including their negative cone-projection boundary. Thus the descent is triangulated.
9. Forget a relative injective module to a scalar cyclic injective. The rank-one lattice
   theorem and its invariant normalization make its row augmentation a quasi-isomorphism;
   conservativity reflects this back to the residual-action category.
10. Total row comparison makes the augmentation Gamma(I) -> K(I) a quasi-isomorphism
    for a bounded-below injective complex. The derived universal property gives theta
    with theta alpha = Qb. On injectives it is invertible, hence everywhere on D+.
11. Define lambda = theta inverse. For a resolution a:N -> I its formula is alpha_I
    after Q(b_I) inverse after Q(K a), transported back along RG(Qa). This fixes all
    choices and makes lambda compatible with the shifts and cone triangles of step 8.
12. Forgetting leaves K, b and these resolutions unchanged, giving the scalar rank-one
    comparison and the composite c = lambda inverse after beta.
13. The commuting scalar/projection square of action topoi gives the ordinary derived
    scalar comparison, without flatness. Both coefficient-beta transposes are V(f)
    after V of the H-counit, so mate pasting identifies the actual derived arrows.
14. Restricted injectives need not be injective, but their augmented cyclic rows stay
    acyclic by exact scalar restriction. The scalar mate model and theta alpha = Qb on
    this common acyclic model give coefficientLambda and coefficient naturality of c.
15. In a compatible nonnegative equivariant injective resolution, use the recorded bar
    total and augmentation. Its invariant-inclusion comparison is eta; a into the
    resolution-zero row is j, without any assertion that the underived bar is acyclic.
16. Evaluation E on column zero is identity, on column one is evaluation at v(1), and
    on higher columns is zero. Its only horizontal equation is d_h(m)(v(1)) = (T-1)m;
    the vertical signs agree. E b_H is the cyclic invariant inclusion.
17. The beta model equation followed by theta alpha = Qb represents c by Q(K(Va))
    inverse after Q(E b_H), with no injectivity assumption on the restricted resolution.
18. Cancel the bar augmentation and use E j = K(Va) epsilon. This gives barEvaluation.
    At no stage is beta asserted invertible. Trivial groups and the zero ring are included.
-/
theorem relative_cyclic_restriction_model :
    ∃ K : TotalModel A G, HasComparison A G K := by
  sorry



variable {A G}

/-- The actual scalar cyclic input obtained by restriction to the second factor.
Source: paragraph (3) (blueprint: lem-sfb-relative-cyclic-restriction-model). -/
def scalarCyclicInput (N : CochainComplex.Plus (Equivariant A (G × Z.{u}))) :
    CochainComplex.Plus (Equivariant A Z.{u}) :=
  (forgetResidual A G Z).mapCochainComplexPlus.obj N

/-- The same scalar input with the trivial residual group reinserted.
Source: paragraph (3) (blueprint: lem-sfb-relative-cyclic-restriction-model). -/
def trivialResidualCyclicInput (N : CochainComplex.Plus (Equivariant A (G × Z.{u}))) :
    CochainComplex.Plus (Equivariant A (PUnit.{u + 1} × Z.{u})) :=
  (addTrivialResidual A).mapCochainComplexPlus.obj (scalarCyclicInput N)

/-- Forgetting the residual group identifies the full bounded-below cyclic comparison
with the scalar comparison, realized by the trivial residual group. Both coordinates
fix the comparison of totals. Its module restriction is the recorded rank-one comparison
by latticeCompatibility below.
Source: paragraph (3), steps 6--12
(blueprint: lem-sfb-relative-cyclic-restriction-model).
Proof: adding a trivial residual action and then forgetting it is the identity normalized
by unitResidualIso. The two totals have exactly the same underlying coordinates and
matrix differential, hence the unique displayed coordinate-preserving chain isomorphism.
On an equivariant K-injective resolution, forgetting preserves K-injectives by exact
free induction. Both comparisons are computed by the same invariant augmentation and
satisfy theta alpha = Qb. Cancel the augmentation quasi-isomorphisms to obtain the
square on every bounded-below complex. Coordinate uniqueness and the diagonal map formula
also give naturality; the signed shift coordinates identify the canonical boundaries. -/
theorem forgetLambda {K : TotalModel A G} (C : HasComparison A G K)
    {K₀ : TotalModel A PUnit.{u + 1}} (C₀ : HasComparison A PUnit.{u + 1} K₀)
    (N : CochainComplex.Plus (Equivariant A (G × Z.{u}))) :
    ∃! k : ((CondensedBar.forgetAction (A := A) (G := G)).mapHomologicalComplex
        (.up ℤ)).obj (K.functor.obj N.obj) ≅
      ((CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapHomologicalComplex
        (.up ℤ)).obj (K₀.functor.obj (trivialResidualCyclicInput N).obj),
      (∀ n : ℤ,
        (k.hom.f n ≫ (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).map
            ((K₀.coordinates (trivialResidualCyclicInput N).obj n).hom ≫ biprod.fst) =
          (CondensedBar.forgetAction (A := A) (G := G)).map
            ((K.coordinates N.obj n).hom ≫ biprod.fst)) ∧
        (k.hom.f n ≫ (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).map
            ((K₀.coordinates (trivialResidualCyclicInput N).obj n).hom ≫ biprod.snd) =
          (CondensedBar.forgetAction (A := A) (G := G)).map
            ((K.coordinates N.obj n).hom ≫ biprod.snd))) ∧
      DerivedCategory.Q.map k.hom ≫
          (forgottenLambda A PUnit.{u + 1} C₀ (trivialResidualCyclicInput N)).hom ≫
          (CondensedDerivedRestriction.derived A Z).map
            (DerivedCategory.Q.map (scalarizationIso A (scalarCyclicInput N)).hom) =
        (forgottenLambda A G C N).hom := by
  sorry

/-- The rank-one lattice comparison and the forgotten relative lambda can be chosen to be
exactly the same normalized row-augmentation comparison. This asserts equality of the actual
derived arrows, with both action and universe transports fixed by their computation units.
Source: paragraph (3), steps 9--12
(blueprint: lem-sfb-relative-cyclic-restriction-model).
Proof: a discrete cyclic condensed action is determined by the constant positive generator;
locally constant sections act by gluing its powers, giving DiscreteBridge and its exact
inverse. Its invariant-limit comparison is the identity on fixed sections. Derive that
comparison, using the canonical universe-localization transport, to obtain the displayed
unit-normalized derived bridge. Construct the scalar lattice witness by the same row
augmentation as the relative total, with G forgotten. The two finite-subset coordinates
in degrees zero and one are its two columns, with differential T-1. On each bounded-below
injective resolution all units, row inclusions and inverse quasi-isomorphisms agree.
This gives the displayed equality for modules; no uniqueness from H-zero alone is used. -/
theorem latticeCompatibility {K : TotalModel A G}
    (C : HasComparison A G K) :
    ∃ (B : DiscreteBridge A) (E : DiscreteDerivedBridge A B)
      (L : Profinite.DiscreteLattice.KoszulModel A.toMon 1)
      (c : Profinite.DiscreteLattice.Comparison A.toMon 1 L),
    ∀ M : Equivariant A (G × Z.{u}),
      ∃ k : ((CondensedBar.forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).obj
          (K.functor.obj (single A (G × Z) M).obj) ≅
        L.functor.obj (B.equivalence.functor.obj ((forgetResidual A G Z).obj M)),
      (k.hom.f 0 ≫
          (L.coordinates (B.equivalence.functor.obj ((forgetResidual A G Z).obj M)) 0).hom ≫
          biproduct.π _ ⟨∅, rfl⟩ ≫ B.underlying.hom.app ((forgetResidual A G Z).obj M) =
        zeroCoordinate K M) ∧
      (k.hom.f 1 ≫
          (L.coordinates (B.equivalence.functor.obj ((forgetResidual A G Z).obj M)) 1).hom ≫
          biproduct.π _ ⟨{0}, by simp⟩ ≫ B.underlying.hom.app ((forgetResidual A G Z).obj M) =
        oneCoordinate K M) ∧
      DerivedCategory.Q.map k.hom ≫
          (lowerQ A).inv.app
            (L.functor.obj (B.equivalence.functor.obj ((forgetResidual A G Z).obj M))) ≫
          (lowerDerived A).map
            (c.iso.hom.app (B.equivalence.functor.obj ((forgetResidual A G Z).obj M))) ≫
          (lowerDerived A).map ((Profinite.DiscreteLattice.derivedInvariants A.toMon 1).map
            ((B.equivalence.functor.mapDerivedCategorySingleFunctor 0).inv.app
              ((forgetResidual A G Z).obj M))) ≫
          E.iso.hom.app ((DerivedCategory.singleFunctor _ 0).obj
            ((forgetResidual A G Z).obj M)) =
        (forgottenLambda A G C (single A (G × Z) M)).hom ≫
          (CondensedDerivedRestriction.derived A Z).map
            (DerivedCategory.Q.map
              ((HomologicalComplex.singleMapHomologicalComplex (forgetResidual A G Z)
                (.up ℤ) 0).hom.app M)) := by
  sorry

/-- The canonical scalar/action-forgetting square, localized from the recorded underlying
scalar-action comparison, with no preservation-of-injectives assumption for scalar change.
Source: paragraph (3) (blueprint: lem-sfb-relative-cyclic-restriction-model). -/
def scalarForgetDerived (a : A ⟶ A') :
    CondensedDerivedRestriction.scalarDerived a G ⋙
        (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory ≅
      (CondensedBar.forgetAction (A := A') (G := G)).mapDerivedCategory ⋙
        CondensedDerivedRestriction.scalarBase a :=
  (Functor.mapDerivedCategoryCompIso
    (CondensedDerivedRestriction.scalarAction (G := G) a).functor
    (CondensedBar.forgetAction (A := A) (G := G))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (CondensedDerivedRestriction.scalarAction (G := G) a).underlying ≪≫
    Functor.mapDerivedCategoryCompIso
      (CondensedBar.forgetAction (A := A') (G := G)) (Mod.comap a.hom.hom)

/-- The relative-to-scalar invariant identifications are natural in arbitrary coefficients,
as actual derived arrows and compatibly with canonical shifts and triangle boundaries.
Source: paragraph (3), step 13
(blueprint: lem-sfb-relative-cyclic-restriction-model).
Proof: use the same commuting scalar/projection square with forgetting. The two normalized
derived-composition comparisons have the same composite underived invariant inclusion and
the same computation-unit equation. Derived mate pasting identifies the composites. All
units, counits and scalar comparisons commute with shifts, hence with triangle boundaries. -/
theorem forgetCoefficient (a : A ⟶ A')
    {N : DerivedCategory.{u + 1} (Equivariant A (G × J))}
    {N' : DerivedCategory.{u + 1} (Equivariant A' (G × J))}
    (f : N ⟶ (CondensedDerivedRestriction.scalarDerived a (G × J)).obj N') :
    (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory.map
        (coefficientMap a f) ≫
      (scalarForgetDerived (G := G) a).hom.app ((derived A' G J).obj N') ≫
      (CondensedDerivedRestriction.scalarBase a).map
        ((forgetDerived A' G (J := J)).hom.app N') =
    (forgetDerived A G (J := J)).hom.app N ≫
      CondensedDerivedRestriction.coefficientMap a
        ((forgetResidual A G J).mapDerivedCategory.map f ≫
          (CondensedDerivedRestriction.scalarGroupDerived a
            (ContinuousMonoidHom.inr G J)).hom.app N') := by
  sorry



end CategoryTheory.RelativeCyclic
