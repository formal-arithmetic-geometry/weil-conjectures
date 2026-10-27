/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.ModuliInertia
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.StackPointTopology
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Pointwise affine finite locally free groupoid charts

Source: Stacks Project, stacks-morphisms.tex, Tag 0DU4,
`lemma-etale-local-quasi-DM-at-x`, specialized to finite inertia using Tag 0CL0
(blueprint: lem-sfb-finite-inertia-pointwise-groupoid-chart).

The quotient is specified by the existing fppf groupoid presentation. Stabilizer
identification is tested on every scheme over the field representative, including
nonreduced schemes. Thus it identifies group schemes, rather than only field points.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- An algebraic stack with finite inertia has a pointed representable etale chart
presented by an affine finite locally free scheme groupoid, identifying the stabilizer.
Source: Stacks Project, Tag 0DU4, using Tag 0CL0(1),(5) and Tags 01WN, 02NU
(blueprint: lem-sfb-finite-inertia-pointwise-groupoid-chart).

`z` is a field-valued object of the quotient and its image represents `x`. For every
scheme `T` over its field scheme, every arrow `b -> z` over `T -> base(z)` is a
cartesian pullback arrow, since the quotient is fibred in groupoids. The final
bijection is the canonical map on automorphism groups of this pullback object.
These bijections on all schemes are natural by functoriality of `h`, and preserve
the group operations. By Yoneda they express an isomorphism of stabilizer group
schemes over the common representing field. The original groupoid law predicate
and the presentation's groupoid field impose the same laws, with the same operations.

Proof, following the five steps of the DAG node:
1. Apply lem-sfb-finite-inertia-flat-quasifinite-presentation at x. This gives a
   flat locally finitely presented locally quasi-finite scheme presentation near x
   with separated relation. Its stabilizer fibre is the base change of the inertia
   projection, hence finite.
2. Apply lem-sfb-etale-groupoid-affine-stabilizer-splitting. After an elementary
   etale neighbourhood of the chosen point, an open subgroupoid P is finite, flat
   and locally finitely presented and contains the entire stabilizer fibre. The
   restricted relation is the self 2-fibre product of the new presentation: both
   have triples of two new objects and an isomorphism between their images.
3. By lem-sfb-stack-chartwise-smooth-etale-calculus and
   lem-sfb-stack-point-topology-flat-lfp-open, the new presentation has open image.
   On a smooth atlas this image is invariant. Apply
   lem-sfb-invariant-open-substack-descent to obtain the open substack W; the map
   factors through W and is surjective there by the common-field-extension point
   criterion. Clause (2) of lem-sfb-fppf-groupoid-stack-presentations identifies
   the quotient by the whole relation with W.
4. By lem-sfb-open-subgroupoid-etale-quotient the quotient by P maps representably
   etale to W. The open immersion W -> X is etale by
   lem-weil-pbc-open-immersion-etale; composition uses the chartwise calculus.
   Its object scheme is affine by construction, and its arrow scheme is affine
   by lem-weil-pbc-finite-morphism-permanence(b). Both projections are finite
   locally free in the recorded finite-flat-locally-finitely-presented sense.
5. Take z to be the image of the chosen point. Clause (1) of
   lem-sfb-fppf-groupoid-stack-presentations identifies the stabilizer map with
   P_(z,z) -> R_(z,z). This open immersion contains the entire stabilizer fibre,
   so it is an isomorphism, including its nilpotents. Composition is inherited
   from R, so the isomorphism respects multiplication, unit and inverse. The
   equivalence with the full open substack W preserves these automorphisms. -/
theorem exists_finiteInertia_pointwise_groupoid_chart
    (k : Type u) [Field k]
    (X : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hX : IsAlgebraicModuliStack X)
    (hfinite : IsRepresentableFiniteModuliMap (moduliInertiaProjection X))
    (x : ModuliPoints X) :
    ∃ (U R : Over (Spec (.of k))) (s t : R ⟶ U)
      (e : U.left ⟶ R.left) (i : R.left ⟶ R.left)
      (c : pullback s.left t.left ⟶ R.left),
      IsAffine U.left ∧ IsAffine R.left ∧ IsGroupoidScheme s.left t.left e i c ∧
      s.left.IsFiniteLocallyFree ∧ t.left.IsFiniteLocallyFree ∧
      ∃ (V : BasedCategory.{u + 1, u + 1} (Over (Spec (.of k))))
        (a : BasedFunctor (discreteModuli (yoneda.obj U)) V),
        Nonempty (SchemeGroupoidQuotientPresentation s t e i c V a) ∧
        IsAlgebraicModuliStack V ∧
        ∃ h : BasedFunctor V X,
          IsRepresentableByAlgebraicSpaces h ∧ IsEtaleModuliMap h ∧
          ∃ z : ModuliFieldObject V, moduliPointMap h (Quot.mk _ z) = x ∧
            ∀ (T : Over (V.p.obj z.val).left)
              (b : Functor.Fiber V.p (Over.mk (T.hom ≫ (V.p.obj z.val).hom)))
              (β : b.val ⟶ z.val),
              V.p.IsHomLift
                (Over.homMk T.hom rfl :
                  Over.mk (T.hom ≫ (V.p.obj z.val).hom) ⟶ V.p.obj z.val) β →
                Function.Bijective
                  ((moduliFiberMap h (Over.mk (T.hom ≫ (V.p.obj z.val).hom))).mapAut
                    (X := b)) := by
  sorry

end CategoryTheory
