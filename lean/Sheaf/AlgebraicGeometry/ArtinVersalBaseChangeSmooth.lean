module

public import Sheaf.AlgebraicGeometry.ArtinRepresentableDiagonalCriterion
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.AlgebraicGeometry.Thickening

import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Jacobson.Ring
import Sheaf.AlgebraicGeometry.SmoothFixedResidueArtinianTest
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource

/-! # Smooth representable base changes of a versal family

Source: Stacks Project, Artin's Axioms, Tag 0CXM, limit-preserving case, and
Tag 0CXU, the section defined by a first order thickening
(blueprint: lem-sfb-artin-versal-base-change-smooth).

The four helpers unpack notions introduced in this node. Families are functors from
representable fibred groupoids; evaluation at the identity gives their fibre objects.
All comparison isomorphisms and both projections of the triples space are retained.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ArtinCriterion AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.ArtinCriterion

/-- Evaluation of a family at the identity of its base. This is the usual object
corresponding to a morphism from a representable fibred groupoid by 2-Yoneda.
Source: Stacks, Tag 0CXM, the objects x and y
(blueprint: lem-sfb-artin-versal-base-change-smooth). -/
def familyObject {F : BasedCategory.{v, w} (Over Base.{u})} {U : Scheme.{u}}
    (x : BasedFunctor (discreteModuli (yoneda.obj (integerScheme U))) F) :
    Object F (integerScheme U) :=
  ⟨x.obj (CostructuredArrow.mk (𝟙 (yoneda.obj (integerScheme U)))), x.w_obj _⟩

/-- Square-zero gluing for arbitrary base algebras, with no Artinian or finite-type
restriction. For a fibred groupoid the total-category pushout universal property
expresses equivalence with the fibre product of groupoids, including all arrows.
The scheme pushout is Spec of the ring fibre product; quantifying over its pushout
presentations makes no choice of a ring model.
Source: Stacks, Artin's Axioms, (RS*) and Tag 0CXM
(blueprint: lem-sfb-artin-versal-base-change-smooth). -/
def HasSquareZeroGluing (F : BasedCategory.{v, w} (Over Base.{u})) : Prop :=
  ∀ (A B B' : CommRingCat.{u}) (f : A ⟶ B) (g : B' ⟶ B),
    Function.Surjective g.hom → RingHom.ker g.hom ^ 2 = ⊥ →
    ∀ (P : Over Base.{u}) (i : integerScheme (Spec A) ⟶ P)
      (j : integerScheme (Spec B') ⟶ P),
      IsPushout (overMap (Spec.map f)) (overMap (Spec.map g)) i j →
      ∀ (a : Object F (integerScheme (Spec B)))
        (b : Object F (integerScheme (Spec A)))
        (b' : Object F (integerScheme (Spec B')))
        (s : Lift (overMap (Spec.map f)) a b)
        (t : Lift (overMap (Spec.map g)) a b'),
        ∃ (c : Object F P) (s' : Lift i b c) (t' : Lift j b' c),
          IsPushout s.val t.val s'.val t'.val

/-- A finite type algebraic-space point has a closed lift on an etale scheme chart.
No residue field is assigned to a point class and no scheme source for Z is assumed.
Source: Stacks, Morphisms of Spaces, definition-finite-type-point, used in Tag 0CXM
(blueprint: lem-sfb-artin-versal-base-change-smooth). -/
def SpaceFiniteTypePoint {S : Scheme.{u}} (Z : AlgebraicSpace S)
    (z : Point Z.obj.obj) : Prop :=
  ∃ (W : Over S) (e : yoneda.obj W ⟶ Z.obj.obj), AlgebraicSpace.IsEtale e ∧
    ∃ a : W.left, IsClosed ({a} : Set W.left) ∧ schemePointMap e a = z

/-- Smoothness on an open subspace containing the specified point, tested on every
etale scheme chart of that open subspace.
Source: Stacks, Tag 0CXM and the chart definition of smoothness for spaces
(blueprint: lem-sfb-artin-versal-base-change-smooth). -/
def SpaceSmoothNear {S : Scheme.{u}} (Z : AlgebraicSpace S) (V : Over S)
    (q : Z.obj.obj ⟶ yoneda.obj V) (z : Point Z.obj.obj) : Prop :=
  ∃ O : OpenSubspace Z, z ∈ pointImage O.val.ι ∧
    ∀ (W : Over S) (a : yoneda.obj W ⟶ O.val.toFunctor), AlgebraicSpace.IsEtale a →
      Smooth ((yoneda.preimage (a ≫ O.val.ι ≫ q)).left)

/-- A limit-preserving fibred groupoid with representable diagonal has a triples
space, smooth near every finite type point above a finite type versal point. The
section associated with a first order thickening preserves finite type points and
has the same smooth-neighbourhood conclusion.

Source: Stacks, Tags 0CXM and 0CXU
(blueprint: lem-sfb-artin-versal-base-change-smooth).

Proof:
1. Apply lem-sfb-limit-preserving-isom-space-lft: the diagonal gives the triples
   space and its locally finite type projections. V is locally Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian and pqf-def-locnoeth. Choose an etale
   chart W with a closed lift w of z, then an affine neighbourhood of w.
2. The closed point gives a finite type residue-field map by
   lem-trf-closed-point-residue-immersion. Compose with W to U using
   lem-sfb-stack-finite-type-calculus and cancel the map Spec kappa(u) to U by
   lemma-nagata-finite-type-to-separated-target. The chart residue field L is
   finite over kappa(u) by lem-weil-pbc-zariski-lemma. Apply
   lem-sfb-artin-pointwise-versal-field-extension to this finite extension and the
   square-zero gluing hypothesis, retaining the prescribed reduction isomorphism.
3. For a small extension B' to B and maps a:Spec B to W, b':Spec B' to V,
   apply that lifting property to eta=b'^*y with reduction alpha inverse.
   It gives c':Spec B' to U and theta:eta isomorphic to c'^*x restricting to
   alpha inverse. The triple (c',b',theta inverse) lifts the original triple.
   By lem-sfb-etale-space-infinitesimal-lifting lift it uniquely to W. Its second
   projection is b', giving the tests of lem-sfb-smooth-fixed-residue-artinian-test.
4. That test yields a smooth open neighbourhood N of w in W. Its etale image O
   is open by lem-a1-space-etale-open-image. For any chart T to O, use
   lem-trf-space-fibre-products-etale-covers to cover T by T times_O N.
   Smoothness of its map to V follows from
   lem-sfb-stack-chartwise-smooth-etale-calculus and descends by
   lem-trf-etale-source-smoothness. Thus O to V is smooth on all charts.
5. The section is the triple (id,j,sigma). Both projection equations follow from
   this triple. Since p i=id, lem-sfb-space-lft-cancellation makes i locally of
   finite type. Compose with the finite type residue-field map of u using
   lem-sfb-stack-finite-type-calculus; then
   lem-sfb-space-finite-type-point-characterization gives that i(u) is a finite
   type point in the closed-chart sense. The first assertion now applies at i(u).
-/
theorem versal_base_change_smooth
    (F : BasedCategory.{v, w} (Over Base.{u}))
    (hFibred : IsFibredInGroupoids F) (hDiagonal : HasAlgebraicSpaceDiagonal F)
    (hGluing : HasSquareZeroGluing F) (hLimits : IsLimitPreserving F)
    (U V : Scheme.{u})
    (hU : LocallyOfFiniteType (specULiftZIsTerminal.from U))
    (hV : LocallyOfFiniteType (specULiftZIsTerminal.from V))
    (x : BasedFunctor (discreteModuli (yoneda.obj (integerScheme U))) F)
    (y : BasedFunctor (discreteModuli (yoneda.obj (integerScheme V))) F) :
    ∃ (Z : AlgebraicSpace Base.{u})
      (p : Z.obj.obj ⟶ yoneda.obj (integerScheme U))
      (q : Z.obj.obj ⟶ yoneda.obj (integerScheme V))
      (e : BasedFunctor (discreteModuli Z.obj.obj) (moduliTwoFiberProduct x y)),
      e.toFunctor.IsEquivalence ∧
      Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst x y)) (discreteModuliMap p)) ∧
      Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberSnd x y)) (discreteModuliMap q)) ∧
      (∀ (u₀ : U), FiniteTypePoint U u₀ → IsVersalAt F U (familyObject x) u₀ →
        ∀ (z₀ : Point Z.obj.obj), SpaceFiniteTypePoint Z z₀ →
          mapPoint p z₀ = schemePointMap (𝟙 (yoneda.obj (integerScheme U))) u₀ →
          SpaceSmoothNear Z (integerScheme V) q z₀) ∧
      ∀ (j : U ⟶ V), IsFirstOrderThickening j →
        ∀ σ : x ≅ (discreteModuliMap (yoneda.map (overMap j))).comp y,
        ∃ i : yoneda.obj (integerScheme U) ⟶ Z.obj.obj,
          i ≫ p = 𝟙 (yoneda.obj (integerScheme U)) ∧ i ≫ q = yoneda.map (overMap j) ∧
          Nonempty (ModuliTwoIso ((discreteModuliMap i).comp e)
            (moduliTwoFiberLift
              (BasedFunctor.id (discreteModuli (yoneda.obj (integerScheme U))))
              (discreteModuliMap (yoneda.map (overMap j))) σ)) ∧
          ∀ u₀ : U, FiniteTypePoint U u₀ →
            SpaceFiniteTypePoint Z (schemePointMap i u₀) ∧
            (IsVersalAt F U (familyObject x) u₀ →
              SpaceSmoothNear Z (integerScheme V) q (schemePointMap i u₀)) := by
  sorry

end AlgebraicGeometry.ArtinCriterion
