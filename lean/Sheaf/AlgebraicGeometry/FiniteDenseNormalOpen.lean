/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Sheaf.AlgebraicGeometry.NormalScheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# A finite-type integral scheme contains a normal open

Source: Blueprint, `sec-smooth-purity/sk-prop-a1-kummer/lem-fin-dense-normal-open`
(blueprint: lem-fin-dense-normal-open).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Every integral finite-type scheme over a field has a nonempty open subscheme whose local
    rings are integrally closed (the normal-open conclusion of the blueprint).

    (blueprint: lem-fin-dense-normal-open)

    Choose a nonempty affine open `Spec B` in `X`. Since `X` is integral, `B` is a domain.
    Its integral closure `C` in `Frac B` is finite over `B` by
    `lem-fin-normalization-extension-finite`. Write finite module generators of `C` as fractions
    over `B` and multiply their nonzero denominators to obtain `b`. Then `C_b = B_b`.
    The integral closure is a normal domain by
    `lem-weil-pbc-integral-closure-finite-extension-normal`, and localization preserves
    normality by `lem-weil-pbc-localization-normal-domain`. Thus `Spec(B_b)` is a normal open
    in `X`. It is nonempty because `b` is nonzero, and dense because every nonempty open of an
    integral scheme is dense. -/
theorem exists_nonempty_normal_open (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsIntegral X] :
    ∃ U : X.Opens, Nonempty U ∧ ∀ x : X, x ∈ U → IsIntegrallyClosed (X.presheaf.stalk x) := by
  sorry

end AlgebraicGeometry
