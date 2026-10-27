module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Topology.Irreducible

import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Nonempty clopen restrictions of finite étale morphisms

Source: Stacks Project, Schemes Tag 01IQ; Morphisms Tags 035C, 01WK, 02GP, 02GN,
01WN, 03WT; Topology Tag 004V.
(blueprint: lem-sfb-finite-etale-clopen-restriction)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Over an irreducible target, a nonempty clopen source restriction of a finite
étale morphism is finite étale and surjective; its source inclusion is closed.

Source: Stacks Project, Schemes Tag 01IQ; Morphisms Tags 035C, 01WK, 02GP, 02GN,
01WN, 03WT; Topology Tag 004V.
(blueprint: lem-sfb-finite-etale-clopen-restriction)

Proof:
1. The inclusion `U.ι` is an open immersion, hence an immersion by factoring it
   through the identity closed immersion. Its range is the closed subset `U`.
   Apply lem-weil-pbc-immersion-closed-image-closed-immersion (Tag 01IQ) to conclude
   that it is a closed immersion.
2. By lem-weil-pbc-closed-immersion-finite (Tag 035C), the inclusion is finite.
   Compose with `p` using lem-weil-pbc-finite-composition (Tag 01WK). The inclusion
   is étale by clause (1) of lem-weil-pbc-etale-composition-cancellation (Tag 02GP);
   clause (2) of that node (Tag 02GN) makes the composite étale.
3. Set `A` equal to the image of `U.ι ≫ p`. Clause (1) of
   lem-weil-pbc-finite-closed-map-finite-fibres (Tag 01WN), applied to the whole
   source, makes `A` closed. The node lem-weil-pbc-etale-morphism-open-map
   (Tag 03WT), applied to the whole source, makes `A` open. The hypothesis that
   `U` is nonempty gives a point in `A`.
4. Both `A` and its complement are closed and cover `X`. Irreducibility
   (def-weil-irreducible-components, Tag 004V) forces one to be all of `X`.
   Nonemptiness of `A` excludes its complement, so `A = X`, which is surjectivity
   (def-weil-surjective-morphism). No normality or Noetherian assumption is used. -/
theorem Scheme.finiteEtale_clopen_restriction_surjective
    {X Y : Scheme.{u}} [IrreducibleSpace X]
    (p : Y ⟶ X) [IsFinite p] [Etale p]
    (U : Y.Opens) (hU : IsClosed (U : Set Y)) (hne : (U : Set Y).Nonempty) :
    IsClosedImmersion U.ι ∧ IsFinite (U.ι ≫ p) ∧ Etale (U.ι ≫ p) ∧
      Surjective (U.ι ≫ p) := by
  sorry

end AlgebraicGeometry
