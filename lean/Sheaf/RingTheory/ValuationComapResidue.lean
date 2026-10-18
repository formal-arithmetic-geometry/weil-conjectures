/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.FieldTheory.AbhyankarInequality

/-!
# Residue extension of a restricted valuation ring

Source: Temkin, *Stable modification of relative curves*, §2.1, valued field extensions,
and Proposition 4.3.1, proof, p. 28 (blueprint: def-trf-valuation-comap-residue).

## Main definitions

- `ValuationSubring.comapResidueAlgebra`: its residue-field algebra structure.

The restricted inclusion, its locality theorem and its induced quotient map are
reused from `Sheaf.FieldTheory.AbhyankarInequality`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ValuationSubring

/-- The residue-field algebra structure from the canonical residue-field embedding.
Source: Temkin, §2.1 and Proposition 4.3.1, proof, p. 28.
(blueprint: def-trf-valuation-comap-residue) -/
@[instance_reducible]
noncomputable def comapResidueAlgebra {K : Type u} {L : Type v} [Field K] [Field L]
    (O : ValuationSubring L) (f : K →+* L) :
    Algebra (IsLocalRing.ResidueField (O.comap f)) (IsLocalRing.ResidueField O) :=
  (O.comapResidueFieldMap f).toAlgebra

end ValuationSubring
