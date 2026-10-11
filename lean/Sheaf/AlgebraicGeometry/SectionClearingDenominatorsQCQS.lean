/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import Sheaf.AlgebraicGeometry.Ample

/-! # Clearing denominators of sections on a nonvanishing locus

Source: Stacks Project, Properties, Lemma 01PW, proof of part (2)
(blueprint: lem-sc-p1-section-clearing-denominators-qcqs).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- On a quasi-compact and quasi-separated scheme, sections on the nonvanishing locus of a
section of an invertible module become restrictions of global sections after a tensor power.
Here `U` is an open with underlying set `X_s = nonvanishingLocus L s` and the right side is
`t ⊗ (s|_U)^{⊗ m}`.
Source: Stacks Project, Properties, Lemma 01PW, proof of part (2)
(blueprint: lem-sc-p1-section-clearing-denominators-qcqs).

Proof:
1. Using `def-sc-invertible-module` and `pqf-def-coherent`, choose affine neighbourhoods
   with a basis for `L` and a module presentation for `F`. Refine their intersections by
   principal opens; `lem-weil-pbc-spec-module-tilde-sections` preserves the presentations.
   By `def-weil-pbc-quasi-compact-scheme`, take a finite cover `Vᵢ = Spec Aᵢ`. Write
   `s = fᵢ eᵢ` on each chart. Its residue-field value is nonzero precisely on `D(fᵢ)`.
   The same affine-sections lemma identifies sections there with localized modules.
   Write the given section locally as `vᵢ / fᵢ ^ aᵢ`, take a common exponent `a`, and
   form `wᵢ = fᵢ ^ (a - aᵢ) vᵢ ⊗ eᵢ ^ a`. Its restriction is the given section times
   `s ^ a`.
2. Quasi-separatedness makes each overlap `Wᵢⱼ = Vᵢ ∩ Vⱼ` quasi-compact. It is also
   quasi-separated, since its affine opens are affine opens of `X`. The twisted module
   is quasi-coherent by `lem-sc-invertible-tensor-qcoherent`. The difference of the two
   local lifts vanishes on `Wᵢⱼ ∩ X_s`. Apply `lem-sc-p1-section-restriction-s-torsion`
   on this qcqs overlap to kill that difference by some power `s ^ bᵢⱼ`.
3. Take a common exponent `b` for the finitely many pairs. After multiplying each lift
   by `s ^ b` and identifying the tensor powers, the resulting sections agree on every
   overlap. Glue them by the sheaf axiom to a global section of `F ⊗ L ^ (a + b)`.
   On the principal opens covering `X_s` it equals the given section times `s ^ (a + b)`.
   Thus `m = a + b` has the required property.
-/
theorem exists_tensorPowSection_eq_restrict_qcqs [CompactSpace X]
    [QuasiSeparatedSpace X] (L : X.Modules) [L.IsInvertible]
    (s : Γ(L, ⊤)) (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    (U : X.Opens) (hU : (U : Set X) = nonvanishingLocus L s) (t : Γ(F, U)) :
    ∃ (m : ℕ) (u : Γ(F ⊗ L.tensorPow m, ⊤)),
      (F ⊗ L.tensorPow m).presheaf.map (homOfLE le_top).op u =
        tmulSection t (tensorPowSectionOne (homOfGlobalSection L s) m U) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
