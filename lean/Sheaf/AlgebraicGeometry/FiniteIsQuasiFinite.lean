/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism

/-!
# Finite morphisms are quasi-finite

Source: the Weil conjectures blueprint, chapter `sec-abelian-varieties`, unit
`sk-prop-av-pqf-finite`, node `pqf-lem-finite-qf` (blueprint: pqf-lem-finite-qf).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite morphism of schemes is quasi-finite in the Stacks sense, including finite type.
Source: the Weil conjectures blueprint, `sec-abelian-varieties/sk-prop-av-pqf-finite`,
node `pqf-lem-finite-qf` (blueprint: pqf-lem-finite-qf).

Proof: by clause (1) of `lem-weil-pbc-finite-closed-map-finite-fibres`, a finite morphism
is proper, hence of finite type. By `def-weil-pbc-scheme-conventions`, it is therefore
quasi-compact and locally of finite type. By clause (2) of
`lem-weil-pbc-finite-closed-map-finite-fibres`, every fibre is finite. The reverse
implication of `pqf-lem-qf-finitefibres` now gives quasi-finiteness. -/
theorem isQuasiFinite_of_isFinite {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.IsFinite f] : f.IsQuasiFinite := by
  sorry

end AlgebraicGeometry.Scheme.Hom
