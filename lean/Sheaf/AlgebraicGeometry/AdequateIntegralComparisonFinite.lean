/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets

/-! # Finiteness over an integral map of adequate moduli spaces

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
arXiv:1005.2398v3, Lemma 8.3.1, printed p.39, and Section 2 conventions
(blueprint: lem-sfb-adequate-integral-comparison-finite).

Smooth atlases express finite type for general algebraic stacks. The point topology
is the existing smooth-atlas topology. All space and scheme tests retain their projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A representable quasi-finite separated map preserving closed points is finite over
an integral map of adequate moduli spaces. Quasi-finiteness includes local finite type
on every étale scheme chart and quasi-compactness of each algebraic-space test.
The scheme `LocallyQuasiFinite` predicate alone does not impose local finite type.
Source: Alper, arXiv:1005.2398v3, Lemma 8.3.1 and Section 2
(blueprint: lem-sfb-adequate-integral-comparison-finite).

Proof:
1. Apply lem-sfb-stack-quasifinite-relative-normalization to f, obtaining the open
immersion j into the relative spectrum N of the integral-closure algebra A inside
f_* O_U, followed by an integral h : N → V. Keep this actual algebra.
2. The section formula of def-sfb-stack-quasi-coherent-algebra, the specified square,
and the structure isomorphism in def-sfb-adequate-moduli-space identify
(qf)_* O_U with g_* O_P. Thus q_* A is a subalgebra of g_* O_P. On an affine étale
test T = Spec R → Q, integrality of g gives P_T = Spec B integral over R. Every
b in B satisfies a monic polynomial over R; on every smooth affine chart of V_T
its restriction therefore belongs to the integral-closure algebra A. These sections
glue, since they are restrictions of the same section. Hence q_* A = g_* O_P,
compatibly with restrictions (def-weil-finite-integral-morphism).
3. Apply lem-sfb-adequate-relative-spectrum to q and A. Its adequate moduli target
Spec_Q(q_* A) identifies with P by step 2 and integrality of g. Evaluation on each
affine étale test identifies the composite with j with p. This uses no assertion
that arbitrary base change preserves an adequate moduli space.
4. By lem-sfb-integral-stack-closed-point-topology, h is closed and points over
closed points are closed. Every nonempty closed subset of N has closed image in V,
which contains a closed point by lem-sfb-finite-type-stack-closed-specialization.
A point above it is closed in N. The closed-point hypothesis on f also implies
that j sends closed points of U to closed points of N.
5. If the complement of j(U) is nonempty, choose a closed point x there by step 4.
By lem-sfb-smooth-presentation-closed-subsets its singleton is a reduced closed
substack. By lem-sfb-adequate-moduli-topological-images its image y in P is closed.
Surjectivity of p and lem-sfb-finite-type-stack-closed-specialization give a closed
u in U above y. Both x and j(u) are closed in N. The intersection-of-closed-images
clause of lem-sfb-adequate-moduli-topological-images applied to their reduced singleton
substacks forces x = j(u), a contradiction.
6. Thus j is a surjective open immersion and an isomorphism, so f is integral.
On each scheme test it is integral and locally of finite type; apply
pqf-lem-integral-lft-finite, namely IsFinite.iff_isIntegralHom_and_locallyOfFiniteType.
Every scheme test is finite, which is IsRepresentableFiniteModuliMap f. -/
theorem adequate_integral_comparison_finite (k : Type u) [Field k]
    (U : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (V : BasedCategory.{v₂, w₂} (Over (Spec (.of k))))
    (hU : IsAlgebraicModuliStack U) (hV : IsAlgebraicModuliStack V)
    (hUft : ∃ (T : Over (Spec (.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj T)) U),
      IsSmoothModuliAtlas U T a ∧ LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom)
    (hVft : ∃ (T : Over (Spec (.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj T)) V),
      IsSmoothModuliAtlas V T a ∧ LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom)
    (P Q : AlgebraicSpace (Spec (.of k)))
    (p : BasedFunctor U (discreteModuli P.obj.obj))
    (q : BasedFunctor V (discreteModuli Q.obj.obj))
    (hp : IsAdequateModuliSpace U hU P p) (hq : IsAdequateModuliSpace V hV Q q)
    (f : BasedFunctor U V) (g : P ⟶ Q)
    (square : ModuliTwoIso (f.comp q) (p.comp (discreteModuliMap g.hom.hom)))
    (hf : ∀ (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) V),
      ∃ (Z : AlgebraicSpace (Spec (.of k))) (a : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange f T t Z a ∧ AlgebraicSpace.MapIsQuasiCompact a ∧
        AlgebraicSpace.MapToSchemeIsLocally
          (fun _ _ b ↦ LocallyOfFiniteType b ∧ LocallyQuasiFinite b) Z T a ∧
        AlgebraicSpace.MapToSchemeIsSeparated Z T a)
    (hg : AlgebraicSpace.IsRepresentableWith (fun _ _ a ↦ IsIntegralHom a.left)
      g.hom.hom)
    (hclosed : ∀ x : ModuliPoints U,
      IsClosed ({x} : Set (ModuliPoints U)) →
      IsClosed ({moduliPointMap f x} : Set (ModuliPoints V)))
    (hUdiag : ∀ (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T))
        (moduliTwoFiberProduct (moduliBaseStructure U) (moduliBaseStructure U))),
      ∃ (Z : AlgebraicSpace (Spec (.of k))) (a : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange (moduliRelativeDiagonal (moduliBaseStructure U)) T t Z a ∧
        AlgebraicSpace.MapIsQuasiCompact a ∧ AlgebraicSpace.MapToSchemeIsSeparated Z T a)
    (hVdiag : ∀ (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T))
        (moduliTwoFiberProduct (moduliBaseStructure V) (moduliBaseStructure V))),
      ∃ (Z : AlgebraicSpace (Spec (.of k))) (a : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange (moduliRelativeDiagonal (moduliBaseStructure V)) T t Z a ∧
        AlgebraicSpace.MapIsQuasiCompact a ∧ AlgebraicSpace.MapToSchemeIsSeparated Z T a) :
    IsRepresentableFiniteModuliMap f := by
  sorry

end CategoryTheory
