/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Weakly étale morphisms are Zariski local on the source

A morphism of schemes `f : U ⟶ X` is weakly étale if and only if its restrictions to the members
of a Zariski open covering of `U` are
(`AlgebraicGeometry.weaklyEtale_iff_of_iSup_eq_top`, blueprint `lemma-stability--3`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Let `f : U ⟶ X` be a morphism of schemes and `U = ⋃ᵢ Uᵢ` a Zariski open covering. Then `f`
is weakly étale if and only if every restriction `Uᵢ ⟶ X` is weakly étale.
(blueprint: `lemma-stability--3`) -/
theorem weaklyEtale_iff_of_iSup_eq_top {U X : Scheme.{u}} (f : U ⟶ X) {ι : Type*}
    (V : ι → U.Opens) (hV : iSup V = ⊤) :
    WeaklyEtale f ↔ ∀ i, WeaklyEtale ((V i).ι ≫ f) :=
  IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @WeaklyEtale) V hV

end AlgebraicGeometry
