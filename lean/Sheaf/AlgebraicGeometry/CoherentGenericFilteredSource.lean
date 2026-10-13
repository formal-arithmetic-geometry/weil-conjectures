/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentIntegralFiltration
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # A filtered source surjecting at a generic stalk

Source: Stacks Project, Tags 01YE and 01YF, generic ideal inclusion and its source filtration.
(blueprint: lem-pc-s3-coherent-generic-filtered-source)
-/

@[expose] public section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Construct only the filtered source of the generic inclusion, without constructing
its cokernel or asserting anything about the target's support.

Source: Stacks Project, Tag 01YE (`lemma-prepare-filter-irreducible`), and Tag 01YF
(`lemma-coherent-filter`), final paragraph.
(blueprint: lem-pc-s3-coherent-generic-filtered-source)

Proof: apply the generic-point ideal inclusion to i and F, obtaining a coherent ideal
I on Z, a finite number r of copies, and a monomorphism from their pushforward to F
which is invertible on an open neighbourhood of i(genericPoint Z). The stalk at this
point is nonzero by hx. If I were zero, its finite sum and pushforward would be zero,
contradicting hx via the bijective generic stalk map. Thus I is nonzero. Finite-sum
coherence and finite closed-pushforward coherence make A coherent. Filter A by the first k summands,
for k = 0,...,r. Each consecutive quotient is the pushforward of I from the integral
closed subscheme Z, so the ideal-sum filtration theorem gives the required coherent
integral filtration. The isomorphism on the neighbourhood induces a bijective stalk
map, and in particular a surjective one. This constructs A and its map; no cokernel,
short exact sequence, support containment, or support induction is used here.

Edge cases: hx excludes a zero target stalk and therefore excludes I = 0 and r = 0.
No assertion that F is supported on the image of i is required: the construction
concerns only its generic stalk, and sections away from that image remain in F. -/
theorem coherent_generic_filtered_source
    {X Z : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hx : ¬ Subsingleton (F.presheaf.stalk (i.base (genericPoint Z))))
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal
      (X.presheaf.stalk (i.base (genericPoint Z))),
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint Z))).obj F, a • m = 0) :
    ∃ (A : X.Modules) (f : A ⟶ F), Mono f ∧
      RingedSpace.IsCoherent X.toRingedSpace A ∧ HasCoherentIntegralFiltration A ∧
      Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint Z))).map f) := by sorry

end AlgebraicGeometry.Scheme.Modules
