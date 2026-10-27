/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.StablePointedCurve
import Sheaf.AlgebraicGeometry.MarkedNodalInfinitesimalFields
import Sheaf.AlgebraicGeometry.NodalCurveLCICriterion
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular

/-! # Projective coarse moduli of unpointed stable curves

Source: Stacks Project, moduli-curves.tex, Tag 0E9C; Mumford, ICM Nice (1970),
p. 462; Morrison, arXiv:0810.2340, §§3.3--3.4
(blueprint: lem-sfb-unpointed-stable-coarse-projective).

The open-substack clause uses its functor-of-points characterization on every
stable family. Density is tested on a surjective étale atlas, rather than on an
arbitrary family. The same atlas has smooth structure morphism to the field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Stable unpointed genus-`g` curves form a smooth DM stack, with finite-type
H-projective coarse moduli scheme, and the smooth families form a dense open.
Source: Stacks Tag 0E9C; Mumford, ICM Nice (1970), p. 462; Morrison §§3.3--3.4
(blueprint: lem-sfb-unpointed-stable-coarse-projective).

Proof:
1. The nodal curve stack is smooth (`lem-sfb-nodal-curve-stack-smooth`). The
stable-family open locus (`lem-sfb-stable-and-smooth-family-open-loci`) identifies
our scheme families, including their projective-bundle condition, with an open
substack. Restrict its smooth atlas to obtain smoothness over the field.
2. Apply `lem-sfb-marked-nodal-infinitesimal-fields` with zero markings. Component
stability makes all normalization vector fields vanish: rational components have
at least three special points, genus-one components at least one, and components
of higher genus have negative-degree tangent bundle. Thus infinitesimal
identity-reducing automorphisms vanish. The criterion
`lem-sfb-curve-stack-infinitesimal-dm-locus` makes this open a DM stack, with no
restriction on characteristic or on orders of finite automorphism groups.
3. The smooth-family locus is open by the same open-locus theorem. For density,
`lem-trf-nodal-curve-lci-criterion` makes each geometric stable curve lci, and
`lem-trf-nodal-family-fitting-singular` makes its singular set finite. Apply
`lem-sfb-isolated-lci-curve-smoothing` over the power-series trait. The stable
open contains the closed point, hence the whole trait, and its generic point is
smooth. Every geometric stable point is therefore a specialization of a smooth
one. Pulling back to an étale atlas gives the dense open asserted below.
4. `lem-sfb-ten-canonical-hilbert-parameter`, with `r = 19(g-1)` and Hilbert
polynomial `20(g-1)m+1-g`, identifies this exact groupoid with the quotient of
the stable Hilbert locus by PGL. Its projective-frame torsors allow base line
bundle twists and retain all automorphisms.
5. `lem-sfb-gieseker-ten-canonical-hilbert-stability` places this locus entirely
inside the stable locus and as a closed subscheme of the semistable locus for
a positive power of the Hilbert--Pluecker polarization, in every characteristic.
6. `lem-sfb-projective-pgl-stable-quotient` gives a finite-type projective scheme
quotient, universal for invariant maps to algebraic spaces. A Veronese embedding
of its invariant section algebra gives precisely `IsHProjective`.
7. Descend the quotient map along projective-frame torsors. Maps from the quotient
groupoid to an algebraic space are exactly invariant maps from the Hilbert locus,
which proves the initial property. Over an algebraically closed field frames
exist and their PGL orbits are exactly curve isomorphism classes; the geometric
quotient bijection is therefore the geometric-isomorphism-class bijection of
`IsCoarseModuliScheme`. Combine with the smooth atlas and open-locus conclusions. -/
theorem unpointed_stable_coarse_projective (k : Type u) [Field k] (g : ℕ) (hg : 2 ≤ g) :
    IsDeligneMumfordModuliStack
      (BasedCategory.ofFunctor (StablePointedModuli.forget (Spec (.of k)) g 0)) ∧
    (∃ (Q : Over (Spec (.of k)))
      (π : BasedFunctor
        (BasedCategory.ofFunctor (StablePointedModuli.forget (Spec (.of k)) g 0))
        (discreteModuli (yoneda.obj Q))),
      IsCoarseModuliScheme
        (BasedCategory.ofFunctor (StablePointedModuli.forget (Spec (.of k)) g 0)) Q π ∧
      LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom ∧ IsHProjective Q.hom) ∧
    (∀ X : StablePointedModuli (Spec (.of k)) g 0,
      ∃ V : X.base.left.Opens,
        ∀ (T : Over (Spec (.of k))) (b : T ⟶ X.base),
          Smooth (pullback.snd X.projection b.left) ↔ Set.range b.left ⊆ (V : Set X.base.left)) ∧
    (∃ (U : Over (Spec (.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U))
        (BasedCategory.ofFunctor (StablePointedModuli.forget (Spec (.of k)) g 0))),
      Smooth U.hom ∧
      (∀ (T : Over (Spec (.of k)))
        (t : BasedFunctor (discreteModuli (yoneda.obj T))
          (BasedCategory.ofFunctor (StablePointedModuli.forget (Spec (.of k)) g 0))),
        ∃ (Z : AlgebraicSpace (Spec (.of k))) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange a T t Z p ∧ SpaceMapIsEtale Z T p ∧
            SpaceMapIsSurjective Z T p) ∧
      ∃ V : U.left.Opens, Dense (V : Set U.left) ∧
        ∀ (T : Over (Spec (.of k))) (b : T ⟶ U),
          Smooth (a.toFunctor.obj (CostructuredArrow.mk (yoneda.map b))).projection ↔
            Set.range b.left ⊆ (V : Set U.left)) := by
  sorry

end AlgebraicGeometry
