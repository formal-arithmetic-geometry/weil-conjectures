/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleToposPointFiberComparison

/-!
# Bijectivity of the geometric comparison

Affine splitting and descent upgrade a natural geometric comparison with the
correct support to a natural bijection.
(blueprint: lem-trf-etale-topos-point-comparison-bijective)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every natural comparison with the correct support is bijective on each
étale object. The comparison itself is supplied separately by coherent choice.
Source: Stacks Project, Etale Cohomology, Tag 04HU, last paragraph and the
affine-cover argument omitted there; Étale Morphisms, Tag 04HM.
(blueprint: lem-trf-etale-topos-point-comparison-bijective)

Proof: choose an affine open A containing s. Finite-limit preservation and the
cover condition give subterminal values on opens and disjoint-union values on
disjoint unions. The support condition makes the value on A a singleton.
For affine U étale over A, use an affine pointed splitting neighborhood V.
The decomposition U × V = (coprod_i V) coproduct W has W-value empty by support.
In the fiber over c_V(v), its copy sections enumerate the value of U without
repetitions. The same sections enumerate all geometric lifts into U. Naturality
identifies their images with c_U, so c_U is bijective, including the empty fiber.

For arbitrary T, replace it by T × A. Both geometric lifts and point values are
unchanged: A is an open neighborhood of s with singleton value. Cover T × A by
affine opens. Joint surjectivity and affine bijectivity imply surjectivity of c.
For injectivity, put two lifts with the same image in affine opens B1 and B2.
Finite-limit preservation gives a paired value on B1 ×_T B2. Lift this value
along an affine cover of that fiber product. Affine bijectivity supplies a
geometric lift into the covering affine C. Naturality and injectivity on B1
and B2 identify its projections with the original lifts, whose composites to
T therefore agree. The overlap itself need not be affine. ULift transports
these bijections to the stated universe. -/
theorem etale_point_comparison_bijective (S : Scheme.{u})
    (p : GeometricMorphism (Type (u + 1))
      (Sheaf S.smallEtaleTopology (Type (u + 1))))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S)
    (c : ((pointSmallEtale s).fiber ⋙ uliftFunctor.{u + 1}) ⟶ etalePointFiberFunctor S p)
    (hsupport : ∀ U : S.Etale,
      Nonempty ((etalePointFiberFunctor S p).obj U) ↔ s default ∈ Set.range U.hom) :
    ∀ U : S.Etale, Function.Bijective (c.app U) := by
  sorry

end AlgebraicGeometry.Scheme
