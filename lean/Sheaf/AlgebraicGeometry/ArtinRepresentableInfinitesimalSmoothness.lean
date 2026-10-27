module

public import Sheaf.AlgebraicGeometry.FibredGroupoidLimitPreserving
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import WeilConjectures.AlgebraicGeometry.Thickening

/-! # Representable infinitesimal smoothness over a limit preserving fibred groupoid

Source: Stacks Project, Artin's Axioms, Tag 07XX, lemma-implies-smooth, specialized
using Tag 07XN to the representable source of finite type over a Noetherian affine base
(blueprint: lem-sfb-artin-representable-infinitesimal-smoothness).

The object over U is encoded by its associated based functor from h_U. All deformation
isomorphisms are retained as cartesian arrows, and their extension is an equality of
arrows, rather than an existence assertion about isomorphism classes.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory

/-- A representable map from a finite type scheme to a limit preserving fibred groupoid
is smooth if every marked Artinian local deformation diagram lifts.

Source: Stacks Project, Artin's Axioms, Tag 07XX and equation-smooth; Tag 07XN
(blueprint: lem-sfb-artin-representable-infinitesimal-smoothness).

Here x encodes its value at id_U, with values at a obtained by pullback. A surjective
residue augmentation rho identifies B/m_B with K; rho composed with the surjection q
identifies the residue field of B' with the same K. The arrow c is precisely the given
isomorphism between the restriction of z and a*x, written in the inverse orientation.
The arrow b lies over Spec(q), so its comma square says a' restricts to a. The vertical
arrow d is an isomorphism because F is fibred in groupoids; x.map b followed by d = c
is exactly extension of the supplied deformation isomorphism.

Proof following the seven steps of the node:
1. The affine base is locally Noetherian (pqf-def-locnoeth). Finite type of U gives
   local finite presentation by pqf-lem-lft-fp-locnoeth. The limit test
   lem-sfb-lfp-space-scheme-limit-test therefore makes h_U limit preserving, as it
   does h_V for every affine finitely presented V over the base.
2. In Z = h_U times_F h_V, descend the U and V maps to a common stage, then their
   isomorphism by fullness in the limit hypothesis. Equalities of the scheme maps
   and of the isomorphisms descend by faithfulness. Thus Z is limit preserving.
   It is an algebraic space by representability, hence an algebraic stack; apply
   lem-sfb-stack-limit-preserving-lfp to get local finite presentation over the base.
3. Choose an etale surjective scheme chart W of Z. The composition law of
   lem-sfb-stack-chartwise-smooth-etale-calculus gives local finite presentation
   of W over the base. Apply lem-sfb-space-lft-cancellation to W -> V -> S to see
   that W -> V is locally of finite type; V is locally Noetherian.
4. For the finite type Artinian tests of lem-sfb-scheme-artinian-smoothness-finite-type-tests,
   the bottom map makes the residue field finite type over R: an open neighbourhood
   of the closed point of a local spectrum is the entire spectrum. Apply hlift to
   the triple (a,c,theta) in Z. The compatibility equality gives its actual lift.
5. A small extension has square-zero kernel (def-sbc-first-order-thickening).
   Lift the triple through W -> Z by lem-sfb-etale-space-infinitesimal-lifting.
6. Apply lem-sfb-scheme-artinian-smoothness-finite-type-tests to W -> V, then
   lem-sfb-scheme-etale-source-target-properties and
   lem-sfb-space-etale-presentation-property-criterion to get smoothness of Z -> V
   on every etale chart.
7. Smoothness is stable under scheme base change by
   lem-sfb-stack-chartwise-smooth-etale-calculus. It is Zariski local on the target:
   open immersions are etale (lem-weil-pbc-open-immersion-etale), and the same
   calculus gives composition and source-open locality. Apply
   lem-sfb-limit-test-representable-property to conclude for arbitrary T and y.
-/
theorem artin_representable_infinitesimal_smoothness
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (F : BasedCategory.{v, w} (Over (Spec R))) (hF : IsFibredInGroupoids F)
    (hLimits : FibredGroupoidLimit.IsLimitPreserving F)
    (U : Over (Spec R)) [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (x : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (hrep : IsRepresentableByAlgebraicSpaces x)
    (hlift : ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.FiniteType R K]
      (B' B : Type u) [CommRing B'] [CommRing B] [Algebra R B'] [Algebra R B]
      [IsLocalRing B'] [IsLocalRing B] [IsArtinianRing B'] [IsArtinianRing B]
      (q : B' →ₐ[R] B), Function.Surjective q →
      ∀ (rho : B →ₐ[R] K), Function.Surjective rho →
      RingHom.ker rho.toRingHom = IsLocalRing.maximalIdeal B →
      ∀ (alpha : (algSpec R).obj (op (CommAlgCat.of R K)) ⟶ U)
        (a : (algSpec R).obj (op (CommAlgCat.of R B)) ⟶ U),
        (algSpec R).map (CommAlgCat.ofHom rho).op ≫ a = alpha →
        ∀ (z : F.obj) (c : x.obj (CostructuredArrow.mk (yoneda.map a)) ⟶ z),
          F.p.IsHomLift ((algSpec R).map (CommAlgCat.ofHom q).op) c →
          ∃ (a' : (algSpec R).obj (op (CommAlgCat.of R B')) ⟶ U)
            (b : CostructuredArrow.mk (yoneda.map a) ⟶
              CostructuredArrow.mk (yoneda.map a'))
            (d : x.obj (CostructuredArrow.mk (yoneda.map a')) ⟶ z),
            (discreteModuli (yoneda.obj U)).p.IsHomLift
              ((algSpec R).map (CommAlgCat.ofHom q).op) b ∧
            F.p.IsHomLift (𝟙 ((algSpec R).obj (op (CommAlgCat.of R B')))) d ∧
            x.map b ≫ d = c) :
    ModuliSpaceTest @Smooth x := by
  sorry

end CategoryTheory
