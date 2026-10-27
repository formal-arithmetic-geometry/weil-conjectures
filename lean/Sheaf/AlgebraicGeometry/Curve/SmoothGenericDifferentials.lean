/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Kaehler.Basic

import Sheaf.AlgebraicGeometry.Curve.SmoothCotangentGenericIsomorphism
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Generic differentials of a smooth integral curve

Source: Stacks Project, Curves, Tag 0C1C, proof of lemma-generically-etale;
Algebra, Tag 00RT (2), lemma-differentials-localize
(blueprint: lem-sfb-smooth-curve-generic-differentials).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The generic stalk of the differential sheaf of a smooth integral curve is uniquely
isomorphic to the differentials of its function field, compatibly with every differential
of a regular function. Both spaces have dimension one and are nonzero. The equality `hk`
specifies the canonical base-field action on the function field, rather than an unrelated
algebra structure. The generic point is Mathlib's canonical representative.

Source: Stacks Project, Curves, Tag 0C1C, proof of lemma-generically-etale; Algebra,
Tag 00RT (2), lemma-differentials-localize
(blueprint: lem-sfb-smooth-curve-generic-differentials).

Proof:
1. Apply lem-a1-smooth-curve-cotangent-generic-isomorphism to the identity of Z. Its
   last assertion for W = Z and x the generic point gives a nonzero free rank-one
   generic stalk, hence dimension one over the generic stalk field.
2. Choose a nonempty affine open U = Spec A. By
   lem-sc-integral-function-field-affine-fraction, its germ algebra identifies the
   function field with Frac A. The generic point corresponds to the zero prime:
   its closure is all Spec A, so its prime is contained in every prime, hence is zero.
3. By def-sc-relative-differential-sheaf the restriction to U is the associated
   sheaf of the module of differentials of A over k, compatibly with derivations.
   Apply lem-weil-pbc-spec-module-tilde-sections and
   lem-sbc-affine-module-germ-localization at the zero prime. They identify the
   generic stalk with the localization of that module at the nonzero elements of A.
   Neighbourhoods contained in U are cofinal, so this is also the ambient stalk
   (def-weil-pbc-module-stalk).
4. Apply lem-weil-pbc-kahler-differentials-localization. Composing its localized
   isomorphism with step 3 yields the desired map and the formula on functions in A.
5. For a section a on any nonempty W, shrink inside U intersect W to a principal
   open D(s) containing the generic point. By
   lem-weil-pbc-spec-module-tilde-sections, there a is b/s^n. The quotient rule
   from def-weil-pbc-kahler-differentials and restriction compatibility of
   def-sc-relative-differential-sheaf extend the formula to a. Differentials db
   generate the affine differential module, hence their germs span its localization;
   therefore the normalization determines the linear isomorphism uniquely. Transfer
   dimension one and nonvanishing across it to the function-field differentials.
-/
theorem Scheme.Hom.smooth_curve_generic_differentials
    {k : Type u} [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [IsIntegralCurve p] [Smooth p]
    [Algebra k Z.functionField]
    (hk : algebraMap k Z.functionField =
      (Z.presheaf.germ ⊤ (genericPoint Z) trivial).hom.comp
        (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)) :
    (∃! α :
        (RingedSpace.moduleStalkFunctor Z.toRingedSpace (genericPoint Z)).obj
          p.relativeDifferentials ≃ₗ[Z.functionField] Ω[Z.functionField⁄k],
      ∀ (W : Z.Opens) (hW : genericPoint Z ∈ W) (a : Γ(Z, W)),
        α (p.relativeDifferentials.presheaf.germ W (genericPoint Z) hW
          (p.relativeDifferentialsDerivation.d (X := op W) a)) =
            KaehlerDifferential.D k Z.functionField
              (Z.presheaf.germ W (genericPoint Z) hW a)) ∧
    Module.finrank Z.functionField
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace (genericPoint Z)).obj
        p.relativeDifferentials) = 1 ∧
    Module.finrank Z.functionField Ω[Z.functionField⁄k] = 1 ∧
    Nontrivial ((RingedSpace.moduleStalkFunctor Z.toRingedSpace (genericPoint Z)).obj
      p.relativeDifferentials) ∧
    Nontrivial Ω[Z.functionField⁄k] := by
  sorry

end AlgebraicGeometry
