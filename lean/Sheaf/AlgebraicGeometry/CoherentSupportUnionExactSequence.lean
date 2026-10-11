/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.AlgebraicGeometry.Coherent
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Splitting the support of a coherent module into two closed pieces

Source: Stacks Project, Cohomology of Schemes, Lemma 30.12.1, Tag 01YD
(blueprint: lem-weil-pbc-coherent-support-union-exact-sequence).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module with support `Z ∪ Z'` has a coherent submodule supported on `Z'`
and coherent quotient supported on `Z`. The inclusion is a monomorphism `i`, and the
quotient is its canonical cokernel. Support uses the inline nonzero-stalk convention.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.12.1, Tag 01YD
(blueprint: lem-weil-pbc-coherent-support-union-exact-sequence).

Proof:
1. Let I be the ideal of the reduced induced closed subscheme on Z, using
   lem-weil-pbc-reduced-induced-closed-subscheme. Its zero set is Z by
   lem-weil-pbc-quasi-coherent-ideal-zero-set-affine, so I_x = O_{X,x} outside Z.
2. Set G'_n = I^n F and G_n = F/I^n F (def-weil-pbc-coherent-formal-module), with
   G'_0 = F and G_0 = 0. The ideal powers and their products with F are quasi-coherent
   by lem-weil-pbc-ideal-times-quasi-coherent-affine-sections and pqf-def-coherent.
   They and the quotients are coherent by lem-weil-pbc-coherent-kernel-cokernel-locnoeth.
3. The inclusion and its cokernel form a short exact sequence, checked on stalks by
   lem-weil-pbc-module-stalk-exact. For n = 0 this is the identity sequence.
4. Every quotient G_n has zero stalk outside Z: I_x is the unit ideal there, so its
   power times F_x is F_x, by lem-weil-pbc-ideal-module-product-stalk.
5. The open V = X minus Z' is Noetherian by
   lem-weil-pbc-noetherian-open-subscheme-noetherian. Restriction preserves coherence
   (lem-weil-pbc-coherent-module-local-on-open-cover) and quasi-coherent ideals
   (lem-weil-pbc-module-restriction-open-immersion-colimits). Stalks of restrictions
   agree with the original stalks (def-weil-pbc-module-stalk). Thus F restricted to V
   is supported in the zero set of I restricted to V. By
   lem-weil-pbc-coherent-support-power-ideal-kills, some power t kills this restriction.
6. Restriction commutes with ideal products and powers by
   lem-weil-pbc-ideal-times-quasi-coherent-affine-sections, including power zero.
   Hence G'_t vanishes on V and has support in Z'.
7. Take G' = G'_t and G = G_t. Steps 2–6 give coherence, the canonical quotient,
   short exactness, and both support inclusions. -/
theorem exists_coherent_submodule_of_support_union
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (Z Z' : Set X) (hZ : IsClosed Z) (hZ' : IsClosed Z')
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = Z ∪ Z') :
    ∃ (G' : X.Modules) (i : G' ⟶ F),
      RingedSpace.IsCoherent X.toRingedSpace G' ∧
      RingedSpace.IsCoherent X.toRingedSpace (cokernel i) ∧
      (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact ∧
      {x : X | ¬ Subsingleton (G'.presheaf.stalk x)} ⊆ Z' ∧
      {x : X | ¬ Subsingleton ((cokernel i).presheaf.stalk x)} ⊆ Z := by
  sorry

end AlgebraicGeometry.Scheme.Modules
