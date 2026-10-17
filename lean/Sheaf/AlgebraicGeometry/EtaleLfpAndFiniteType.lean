/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Etale morphisms and finite type over a field

Source: the Weil conjectures blueprint, chapter `sec-smooth-purity`, unit
`sk-prop-sf-kunneth-ordinary`, lemma `lem-kun-etale-lfp`
(blueprint: lem-kun-etale-lfp).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An etale morphism is locally of finite presentation. If it is quasi-compact and its
 target is of finite type over a field, its source is of finite type over the same field.
Finite type is written as quasi-compactness and local finite type.

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`,
lemma `lem-kun-etale-lfp` (blueprint: lem-kun-etale-lfp).

Proof: Mathlib provides a locally finite presentation instance for an etale morphism.
For the second conjunct, install the explicit quasi-compactness hypothesis on `f` and the
quasi-compactness and locally finite type hypotheses on `g` as local instances. Mathlib's
`AlgebraicGeometry.quasiCompact_comp` and
`AlgebraicGeometry.locallyOfFiniteType_comp` then provide the corresponding properties
for `f ≫ g`. -/
theorem etale_lfp_and_finiteType_over_field {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] :
    LocallyOfFinitePresentation f ∧
      ∀ (K : Type u) [Field K] (g : X ⟶ Spec (CommRingCat.of K)),
        QuasiCompact f → (QuasiCompact g ∧ LocallyOfFiniteType g) →
          QuasiCompact (f ≫ g) ∧ LocallyOfFiniteType (f ≫ g) := by
  constructor
  · infer_instance
  · intro K _ g hf hg
    let _ : QuasiCompact f := hf
    let _ : QuasiCompact g := hg.1
    let _ : LocallyOfFiniteType g := hg.2
    exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
