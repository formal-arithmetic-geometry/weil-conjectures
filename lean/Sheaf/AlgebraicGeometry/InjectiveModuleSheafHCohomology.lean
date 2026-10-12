/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
import Sheaf.AlgebraicGeometry.ModuleSheafConstantRingEquivalence

/-! # Abelian sheaf cohomology of injective module sheaves

Source: Stacks Project, Tag 03FD, second paragraph of the proof.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- The underlying abelian sheaf of an injective module sheaf is acyclic for H.
This concerns an injective on its own site, without a closed immersion or torsion.

Source: Stacks Project, Tag 03FD, second paragraph of the proof.
(blueprint: lem-weil-pbc-injective-module-sheaf-H-acyclic)

Proof: regard a sheaf with values in ModuleCat as a sheaf of modules over the
constant ring sheaf using `AlgebraicGeometry.moduleSheaf_constantRing_equivalence`
(lem-weil-pbc-module-sheaf-constant-ring-equivalence). Its natural isomorphism of
underlying-abelian forgetful functors identifies the additive sheaves, and the
category equivalence preserves injectivity. The free module Cech complex of any
covering is exact in positive homological degrees. Applying Hom into the injective
module sheaf gives zero positive Cech cohomology. Forgetting coefficients does
not change these complexes. The Cech vanishing criterion therefore gives vanishing
of positive right-derived evaluation on every object of the small etale site (03FD).
Evaluation at its terminal object X computes global sections. Apply the
right-derived-functor identification (lem-sp-derived-functor-single-identification)
to identify these rightDerived groups with the homology of derived global sections
of the degree-zero single complex. The existing Ext comparison
(lem-weil-pbc-sheafH-ext-derived-comparison) then identifies these groups with
Sheaf.H, giving the asserted subsingleton. All abelian sheaves and groups have
universe u+1 on X : Scheme.{u}; no replacement of X by a larger-universe scheme is
used. This does not claim that forgetting coefficients preserves injectivity.
The empty scheme and the zero ring also satisfy the argument.
-/
theorem Etale.subsingleton_H_underlying_of_injective_module
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Injective J] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J) q) := by
  sorry

end AlgebraicGeometry
