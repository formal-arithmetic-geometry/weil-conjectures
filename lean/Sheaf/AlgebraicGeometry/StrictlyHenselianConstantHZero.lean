/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections

/-!
# Degree-zero constant étale cohomology over a strictly henselian local ring

Source: blueprint, `sec-smooth-base-change/sk-rem-rest`, degree-zero clause of
`sbc-lem-strict-henselian-constant-cohomology`; Stacks Project, Tags 03QO, 03P5 and 05TD
(blueprint: lem-sbc-strict-henselian-constant-hzero).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Degree-zero cohomology of constant abelian étale sheaves on `Spec R` is naturally the
coefficient group. The natural isomorphism is in `AddCommGrpCat`, so its components are
additive equivalences and its naturality covers every homomorphism of coefficient groups.
Source: the degree-zero clause of `sbc-lem-strict-henselian-constant-cohomology`, and
Stacks Project Tags 03QO, 03P5 and 05TD
(blueprint: lem-sbc-strict-henselian-constant-hzero).

Proof:
1. Apply `lem-weil-pbc-cohomology-pullback-degree-zero`, clause (1), to identify derived
   degree-zero global sections with sections of the constant sheaf, naturally in that sheaf
   and compatibly with every K-injective resolution.
2. The local ring has a proper maximal ideal, hence a point of its spectrum. Every prime
   is contained in that maximal ideal, so any nonempty closed subset contains the closed
   point. In a clopen partition the part containing the closed point is therefore the
   whole spectrum. Thus the spectrum is connected and nonempty
   (`def-weil-connected-scheme`, `def-weil-affine-spectrum`, henselian terminology).
3. Apply `lem-weil-pbc-constant-sheaf-sections-connected`: the constant-section map from
   the coefficient group to sections is an additive isomorphism. Compose its inverse
   with the inverse of the degree-zero comparison from step 1.
4. For a coefficient homomorphism, the constant-presheaf map sends a constant section
   to the corresponding constant section. Naturality of the sheafification unit
   (`def-weil-pbc-constant-sheaf`, `def-weil-pbc-sheafification`) and the comparison in
   step 1 then gives naturality of the composite additive isomorphism. -/
theorem nonempty_constantSheaf_cohomology_zero_iso
    (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R] :
    Nonempty
      ((constantSheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u + 1}) ⋙
          DerivedCategory.singleFunctor
            (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
          cohomology AddCommGrpCat.{u + 1} (Spec (CommRingCat.of R)) 0 ≅
        𝟭 AddCommGrpCat.{u + 1}) := by
  sorry

end AlgebraicGeometry.Etale
