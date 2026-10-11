/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Sheaves.Functors

/-!
# Zariski degree-zero comparison for a proper scheme over a henselian pair

Source: Stacks Project, Etale Cohomology, Lemma 59.91.1, Tag 0A0B
(blueprint: lem-weil-pbc-zariski-h0-proper-henselian-pair).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open TopologicalSpace

namespace AlgebraicGeometry

/-- For a proper scheme over a henselian pair, sections of any sheaf of sets are
unchanged on the closed fibre.
Source: Stacks Project, Etale Cohomology, Lemma 59.91.1, Tag 0A0B
(blueprint: lem-weil-pbc-zariski-h0-proper-henselian-pair).

Proof (the six steps of the node):
1. The quotient spectrum map is a closed immersion, as is its base change
   (`lem-weil-pbc-spec-quotient-closed-immersion`,
   `lem-weil-pbc-closed-immersion-base-change`). Fibre-product points identify its image
   with the inverse image of V(I) (`lem-weil-pbc-fibre-product-points`). Properness over
   an affine base makes X quasi-compact and quasi-separated, hence spectral
   (`lem-weil-pbc-qcqs-over-affine`, `lem-weil-pbc-qcqs-scheme-spectral`, Tag 094L).
2. The spectral restriction criterion (`lem-weil-pbc-h0-spectral-closed-restriction`,
   Tag 09ZG) reduces bijectivity to connectedness of the closed fibre intersected with
   the closure of every point of X.
3. Realize that closure as an irreducible closed subscheme Y
   (`lem-weil-pbc-closed-subset-closed-subscheme`). Its composite map to Spec A is proper
   (`lem-weil-pbc-proper-fp-permanence`), and its closed fibre is homeomorphic to the
   required intersection.
4. Factor Y through Spec B by Stein factorization
   (`def-weil-pbc-stein-factorization`, `lem-weil-pbc-stein-factorization-affine`, Tag 03H2).
   The first map is proper with connected nonempty fibres, A to B is integral, and
   (B, IB) is henselian (`lem-weil-pbc-integral-over-henselian-pair`, Tag 09XK).
5. The image of Y in Spec B is closed and irreducible, hence V(q) for a prime q
   (`lem-weil-pbc-scheme-sober`). Its intersection with V(IB) is V(q + IB), connected
   and nonempty (`lem-weil-pbc-henselian-pair-prime-connected`, Tag 09Y6).
6. The closed fibre of Y maps surjectively and closedly onto V(q + IB), with connected
   fibres. This gives a quotient map, so its source is connected
   (`lem-weil-pbc-connected-fibres-quotient-preimage-connected`, Tag 0377).
   Step 3 identifies the intersection, and Step 2 proves the assertion.

The displayed map is the global component of the unit of the inverse-image adjunction
`TopCat.Sheaf.pullbackPushforwardAdjunction` (STATE INVERSE IMAGE, Type u), the form of
`lem-weil-pbc-h0-spectral-closed-restriction`: the colimit coprojection followed by
sheafification, the restriction map specified in the node.
-/
theorem zariski_h0_proper_henselian_pair
    (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsProper f] :
    ∀ (𝓕 : TopCat.Sheaf (Type u) X),
      Function.Bijective
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
          (pullback.fst f
            (Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)).op)).base).unit.app
              𝓕).hom.app (op ⊤)) := by
  sorry

end AlgebraicGeometry
