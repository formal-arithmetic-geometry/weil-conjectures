/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.ModuliInertia
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
import Sheaf.AlgebraicGeometry.AffineGroupoidInvariantNorm
import Sheaf.AlgebraicGeometry.AffineGroupoidInvariantRankStrata
import Sheaf.AlgebraicGeometry.AdequateModuliEtaleLocality
import Sheaf.AlgebraicGeometry.AffineGroupoidQuasiCoherentAlgebraDescent
import Sheaf.AlgebraicGeometry.FiniteFlatAffineGroupoidModuli
import Mathlib.LinearAlgebra.Determinant
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Finite inertia gives an adequate coarse moduli space

Source: Stacks Project, Tags 0DUT and 0DUY; Alper, arXiv:1005.2398v3,
Theorem 8.1.1 and Proposition 8.2.1
(blueprint: lem-sfb-finite-inertia-adequate-coarse-space).

Universality is unique factorization up to a 2-isomorphism, that is, equality of
morphism classes. Geometric points use the actual induced functor on fibre skeletons.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A finite-type algebraic stack with finite inertia admits a surjective adequate
coarse moduli space. A finite stack diagonal makes the coarse space separated.
No étaleness, smoothness or prime-to-characteristic condition on inertia is assumed.
Source: Stacks Project, Tags 0DUT and 0DUY; Alper, arXiv:1005.2398v3,
Theorem 8.1.1 and Proposition 8.2.1
(blueprint: lem-sfb-finite-inertia-adequate-coarse-space).

Proof:
1. Apply lem-sfb-finite-inertia-etale-affine-charts to obtain jointly surjective,
   representable separated étale stabilizer-preserving charts presented by finite
   locally free affine groupoids, all over k.
2. Apply lem-sfb-finite-flat-affine-groupoid-moduli on each chart. Its equalizer
   spectrum is uniform categorical, qcqs, a universal homeomorphism, has the required
   geometric-point bijections, and has the canonical structure-sheaf isomorphism.
3. Apply lem-sfb-etale-stabilizer-preserving-affine-moduli to both overlap projections.
   Categoricality gives inverse comparison maps between the two overlap moduli spaces:
   their composites are identities by uniqueness. Transport the second cartesian
   overlap square across this isomorphism.
4. Apply lem-sfb-etale-local-moduli-gluing to the resulting compatible squares. The
   étale equivalence relation on the local moduli spaces has an algebraic-space
   quotient Q. The descended q is qcqs, a universal homeomorphism and surjective,
   and has the geometric-point bijections and cartesian chart comparisons.
5. After every flat base change Q' to Q, uniform categoricality gives the unique
   local factorizations to any algebraic space T. On overlaps, the base changes
   remain flat; categorical uniqueness identifies the two restrictions. Étale
   sheaf descent glues them uniquely. Take Q'=Q for the asserted universality.
6. By lem-a1-affine-groupoid-invariant-rank-strata, split each affine groupoid into
   finitely many invariant clopen pieces of positive constant rank n. Both arrow
   maps are coordinatewise, so their equalizer ring is the product of the piece
   equalizers. Empty charts have no pieces. Adequacy can be checked on these pieces
   by lem-sfb-adequate-moduli-etale-locality.
7. On a piece, lem-sfb-affine-groupoid-quasicoherent-algebra-descent identifies a
   quasi-coherent algebra surjection with an equivariant surjection A to B, and
   global sections with invariants. Lift an invariant b to a in A. Pulling back
   the descent datum gives the action groupoid on Spec A, finite locally free of
   degree n, with arrow algebra A tensor_E L and its descent structural maps.
8. Apply lem-a1-affine-groupoid-invariant-norm to obtain the invariant norm of the
   transported a. Modulo A to B its multiplication matrix is b times the identity,
   since b is invariant. The determinant therefore reduces to b^n on every free
   chart. This is the required invariant lift, without dividing by n.
9. The affine global-power criterion of lem-sfb-adequate-moduli-etale-locality and
   the local structure-sheaf isomorphism give adequacy on each rank piece, then
   on each chart and finally on Q. Quantification includes all quasi-coherent
   algebras on every étale base change.
10. If the stack diagonal is finite, lem-weil-pbc-finite-proper makes it proper,
   hence universally closed by def-weil-proper-morphism. Apply
   lem-sfb-stack-universal-homeomorphism-separated-target to q to obtain the
   closed-immersion diagonal of Q, as in relative Tag 0DUY. -/
theorem finiteInertia_exists_adequate_coarse_space (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
    (hF : IsAlgebraicModuliStack F)
    (hft : ∃ (U : Over (Spec (CommRingCat.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a ∧ LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom)
    (hI : IsRepresentableFiniteModuliMap (moduliInertiaProjection F)) :
    ∃ (Q : AlgebraicSpace (Spec (CommRingCat.of k)))
      (q : BasedFunctor F (discreteModuli Q.obj.obj)),
      Function.Surjective (moduliPointMap q) ∧
      IsAdequateModuliSpace F hF Q q ∧
      (∀ (T : AlgebraicSpace (Spec (CommRingCat.of k)))
        (f : BasedFunctor F (discreteModuli T.obj.obj)),
        ∃! g : Q.obj.obj ⟶ T.obj.obj,
          Nonempty (ModuliTwoIso (q.comp (discreteModuliMap g)) f)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (j : k →+* Ω),
        Function.Bijective
          ((moduliFiberMap q (Over.mk (Spec.map (CommRingCat.ofHom j)))).mapSkeleton.obj)) ∧
      (HasFiniteModuliDiagonal F →
        AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
          (prod.lift (𝟙 Q.obj.obj) (𝟙 Q.obj.obj))) := by
  sorry

end CategoryTheory
