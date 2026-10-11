/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Sheaf.AlgebraicGeometry.SmoothProjectiveCurve
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Well-definedness of the genus

Source: blueprint `sec-picard-framework/sk-thm-picard-rr/lem-pc-genus-well-defined.md`,
node `lem-pc-genus-well-defined`; Stacks Project, Morphisms, Tags 02H2, 01WF,
01K5, 01W4 and Varieties, Tags 056T, 01ON.

## Main statements

* `genus_well_defined`: the first cohomology of the structure sheaf of a smooth
  projective geometrically irreducible curve is finite-dimensional over its base field.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The genus is well-defined as a finite-dimensional vector space.
Source: blueprint `lem-pc-genus-well-defined` (Stacks Project, Morphisms, Tags
02H2, 01WF, 01K5, 01W4; Varieties, Tags 056T and 01ON).

The structure sheaf is `SheafOfModules.unit X.ringCatSheaf`; its first cohomology is
`Scheme.Modules.scalarCohomology` (the recorded O_X-module cohomology
`RingedSpace.moduleCohomology` with scalars restricted along k → Γ(X, O_X)), and
finite-dimensionality over k renders `dim_k H^1(X, \mathcal O_X) < \infty`.

Proof: let k̄ be an algebraic closure of k and X_k̄ the base change. X_k̄ is again a
smooth projective curve over k̄: smoothness and projectivity are preserved by base change,
it has dimension 1, it is separated of finite type, reduced (X is smooth, hence
geometrically reduced) and irreducible (geometric irreducibility), hence integral. By
coherent finiteness on smooth projective curves over an algebraically closed field,
H^1(X_k̄, O_{X_k̄}) is finite-dimensional over k̄. Since X is proper over k and k → k̄ is
flat, flat base change gives H^1(X, O_X) ⊗_k k̄ ≅ H^1(X_k̄, O_{X_k̄}). A k-vector space V with
V ⊗_k k̄ finite-dimensional over k̄ is finite-dimensional over k, since linearly
independent families stay independent after extending scalars.
(blueprint: lem-pc-genus-well-defined)
-/
theorem genus_well_defined (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))]
    [Scheme.Hom.IsSmoothProjectiveCurve (X ↘ Spec (.of k))]
    [GeometricallyIrreducible (X ↘ Spec (.of k))] :
    FiniteDimensional k
      (Scheme.Modules.scalarCohomology (f := X ↘ Spec (.of k))
        (SheafOfModules.unit X.ringCatSheaf) 1) := by
  sorry

end AlgebraicGeometry
