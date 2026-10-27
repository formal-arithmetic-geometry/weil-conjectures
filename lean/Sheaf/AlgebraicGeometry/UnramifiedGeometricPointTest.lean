/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import Sheaf.AlgebraicGeometry.UnramifiedLocusBaseChange

/-! # Unramifiedness tested at rational points of geometric fibres

Source: Stacks Project, Morphisms, Tag 0475; Schemes, Tag 01J9
(blueprint: lem-sfb-unramified-geometric-point-test).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A locally finite type morphism is unramified exactly when each rational point of each
geometric fibre has an unramified source neighbourhood. Every source point lifts to such
an Omega-point with Omega the algebraic closure of its residue field. The test fields may
be transcendental over the residue field of the image in the base.
Source: Stacks Project, Morphisms, Tag 0475; Schemes, Tag 01J9
(blueprint: lem-sfb-unramified-geometric-point-test).

Proof plan:
1. For z in X take Omega = AlgebraicClosure (X.residueField z), as in
   `def-weil-algebraic-closure`. By `lem-weil-pbc-morphism-from-spec-field`, the residue
   field embedding gives a : Spec Omega to X with image z. Set s = a followed by f.
   The universal property in `def-pc-fibre-product` applied to (a, identity) gives the
   section x of the geometric fibre, and its first projection has image z. This proves
   the lifting clause, without requiring Omega algebraic over the base residue field.
2. By `lem-weil-pbc-lft-base-change`, each fibre morphism p_s is locally of finite type.
   The equality in `lem-trf-unramified-locus-base-change` says that its unramified locus
   is the inverse image of the unramified locus of f. If f is unramified, X itself is an
   unramified source neighbourhood, so this equality supplies the desired neighbourhood
   at every test point.
3. Conversely, lift each z using Step 1. The test hypothesis puts the lifted point in
   the unramified locus of p_s. The same base-change equality puts z in the unramified
   locus of f. Thus every point of X has an unramified source neighbourhood.
4. The affine-cover characterization in `def-weil-unramified-morphism` glues these
   neighbourhoods to unramifiedness of f: collect their affine unramified charts. For
   the empty source the empty affine cover suffices, and both pointwise clauses are
   vacuous. No flatness, finite presentation, quasi-compactness or Noetherian assumption
   is used. -/
theorem unramified_iff_geometricPoint_test
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    (IsUnramified f ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
        (x : Spec (.of Ω) ⟶ pullback f s),
        x ≫ pullback.snd f s = 𝟙 (Spec (.of Ω)) →
          ∃ U : (pullback f s).Opens, x (IsLocalRing.closedPoint Ω) ∈ U ∧
            IsUnramified (U.ι ≫ pullback.snd f s)) ∧
    (∀ z : X,
      ∃ (s : Spec (.of (AlgebraicClosure (X.residueField z))) ⟶ S)
        (x : Spec (.of (AlgebraicClosure (X.residueField z))) ⟶ pullback f s),
        x ≫ pullback.snd f s = 𝟙 (Spec (.of (AlgebraicClosure (X.residueField z)))) ∧
          pullback.fst f s
            (x (IsLocalRing.closedPoint (AlgebraicClosure (X.residueField z)))) = z) := by
  sorry

end AlgebraicGeometry
