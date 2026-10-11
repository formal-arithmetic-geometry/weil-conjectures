/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.AlgebraicGeometry.EtaleSheaves
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Local lifts in a short exact sequence of etale module sheaves

Source: the Weil conjectures blueprint, `sec-proper-base-change/sk-thm-properbasechange`,
`lemma-constructible-flc-serre`, extension paragraph, the assertion that a surjection of
sheaves is locally surjective on sections (blueprint: lem-constructible-shortexact-local-lift).
-/

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Every section of the quotient in a short exact sequence of etale sheaves of modules
lifts over an etale covering. The coefficients are the constant ring sheaf of the
commutative ring `Λ` ("ring" in the Stacks sense, as in `def-weil-pbc-etale-sheaves`);
`ULift` only places the ring in the universe of the sheaf values. A covering is encoded by
its generated sieve, equivalently a jointly surjective family by
`ofArrows_mem_smallEtaleTopology_iff`.

Source: blueprint `lemma-constructible-flc-serre`, extension paragraph
(blueprint: lem-constructible-shortexact-local-lift).

Proof: `def-weil-pbc-exact-sequence` makes the quotient map an epimorphism. By
`lem-weil-pbc-module-sheaves-colimits-forgetful` (1), forgetting module structure preserves
cokernels, so this is also an epimorphism of abelian sheaves. Apply
`lem-weil-pbc-abelian-sheaf-epi-locally-surjective` to the given section to obtain a covering
and a lift on each member. This only lifts individual sections and requires no splitting
of the sequence. -/
theorem exists_etale_local_lift_of_shortExact (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (S : ShortComplex (SheafOfModules.{u + 1}
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} Λ)))))
    (hS : S.ShortExact) (U : X.Etale) (t : S.X₃.val.obj (op U)) :
    ∃ (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U)
      (s : ∀ i : I, S.X₂.val.obj (op (V i))),
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U ∧
        ∀ i : I, S.g.val.app (op (V i)) (s i) = S.X₃.val.map (f i).op t :=
  sorry

end AlgebraicGeometry.Scheme
