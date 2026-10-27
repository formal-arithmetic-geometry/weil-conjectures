/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.ModuliInertia
public import Sheaf.AlgebraicGeometry.ModuliIsoClassSheaf
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Algebraic-space quotient of a stack with flat inertia

Source: Stacks Project, Tags 06QJ, 06QD, 0DN8 and 0AHD
(blueprint: lem-sfb-flat-inertia-algebraic-space-quotient).

The natural map is the quotient to fibrewise isomorphism classes followed by the
sheafification unit. Its smoothness is tested on a smooth source atlas, without
requiring the stack-to-space map itself to be representable.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry

/-- Flat locally finitely presented inertia gives an algebraic-space quotient, a
smooth surjective natural map, and descent of smoothness over the base.
Source: Stacks Project, Tags 06QJ, 06QD, 0DN8 and 0AHD
(blueprint: lem-sfb-flat-inertia-algebraic-space-quotient).

Proof:
1. Choose a smooth surjective scheme atlas U of F. By
   lem-sfb-etale-smooth-atlas-fppf-descent, F is also an fppf stack. The diagonal
   represents R = U ×_F U; its source and target are smooth surjective by
   lem-sfb-stack-chartwise-smooth-etale-calculus. Its stabilizer G is the pullback
   of inertia along U, hence is flat and locally finitely presented.
2. Precomposition with inverse automorphisms is a free left G-action on R.
   Apply lem-sfb-free-flat-group-space-quotient to obtain the algebraic space
   A = R/G and the flat locally finitely presented surjective quotient map.
3. Identify A with h_U ×_Q h_U: two isomorphisms with the same endpoints differ
   by a unique stabilizer element. Equality in the sheafification is fppf-local
   equality of classes by lem-weil-pbc-site-sheafification-sections-local.
   Local isomorphisms therefore give compatible local sections of A and glue.
4. The two maps A → U are smooth: on étale scheme charts of A and R, apply
   lem-sbc-smooth-flat-surjective-source-descent to the flat surjective quotient
   chart followed by a smooth source or target map of R. Identity arrows give
   sections of both maps A → U, so both are surjective. The quotient map R → A
   is not assumed smooth.
5. Sections of Q fppf-locally come from objects of F. Pull back the atlas along
   these objects and use lem-sfb-smooth-space-cover-etale-sections to lift further
   to U. The étale refinements are fppf covers by the chartwise calculus.
6. Each h_T ×_Q h_U is locally T_j ×_U A on those covers. Apply
   lem-sfb-fppf-local-algebraic-space and
   lem-sfb-space-smooth-surjective-fppf-locality to represent it by a smooth
   surjective space over T. A cover of size at most the points of T and
   lem-weil-pbc-scheme-coproduct-family supply the size bound.
7. Thus h_U → Q is representable by spaces, smooth and surjective. Apply
   lem-sfb-fppf-space-atlas-bootstrap to obtain algebraicity of Q. Since Q has
   representable diagonal, the scheme tests of h_U → Q are now schemes.
   Its identification with the atlas composite gives exactly the smoothness
   and surjectivity of the natural map F → Q, allowing nontrivial stabilizers.
8. If F is smooth over S, choose U smooth over S. On an étale scheme chart
   V → Q, the scheme W = U ×_Q V is smooth over S and smooth surjective over V.
   Scheme source descent (lem-sbc-smooth-flat-surjective-source-descent) gives
   V smooth over S. This is the étale-chart test for Q → S. -/
theorem flat_inertia_algebraic_space_quotient {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F)
    (hI : HasFlatLocallyPresentedModuliInertia F) (Q : ModuliIsoClassSheaf F) :
    AlgebraicSpace.IsAlgebraicSpace Q.sheaf ∧
      (∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
        (b : yoneda.obj U ⟶ Q.sheaf.obj),
        IsSmoothModuliAtlas F U a ∧
          Nonempty (ModuliTwoIso (a.comp Q.projection) (discreteModuliMap b)) ∧
          AlgebraicSpace.IsRepresentableWith
            (fun _ _ p ↦ Smooth p.left ∧ Surjective p.left) b) ∧
      (IsSmoothModuliStack F → ∀ (V : Over S) (b : yoneda.obj V ⟶ Q.sheaf.obj),
        AlgebraicSpace.IsEtale b → Smooth V.hom) := by
  sorry

end AlgebraicGeometry
