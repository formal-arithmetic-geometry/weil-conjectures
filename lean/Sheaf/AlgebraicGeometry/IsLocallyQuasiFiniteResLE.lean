/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism

/-!
# Restriction of locally quasi-finite morphisms to open subschemes

Source: Stacks Project, Morphisms of Schemes, Tags 01TD and 01TH (4), as invoked in
Tag 03JA (blueprint: lem-weil-pbc-lqf-restriction-to-opens).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- Restricting a locally quasi-finite morphism to open subschemes preserves local
quasi-finiteness in the Stacks sense, including the finite-type requirement.
Source: Stacks Project, Morphisms of Schemes, Tags 01TD and 01TH (4), as used in Tag 03JA
(blueprint: lem-weil-pbc-lqf-restriction-to-opens).

The open immersions are `U.ι` and `V.ι`. The canonical restriction `f.resLE V U e` satisfies
`f.resLE V U e ≫ V.ι = U.ι ≫ f` by `resLE_comp_ι`; uniqueness follows since `V.ι` is mono.

Proof:
1. By `lem-weil-pbc-lqf-locally-finite-type`, local quasi-finiteness implies that `f` is
   locally of finite type (the remark following Stacks 01TD).
2. For a point `x` of `U`, choose affine opens `V'` around `f x` inside `V`, and `U'` around
   `x` inside `U ∩ f⁻¹(V')`, using `lem-weil-pbc-affine-opens-basis` (Stacks 01IT).
3. By `lem-weil-pbc-quasi-finite-at-point-isolated`, `x` is isolated in its fibre. Apply
   `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs` to this affine pair to get
   a finite-type ring map quasi-finite at the prime corresponding to `x` (Stacks 01TH).
4. Open subschemes have the restricted structure sheaf, so the same affine pair has the
   same rings of sections, induced ring map, and prime for `f.resLE V U e`. It therefore
   witnesses `IsQuasiFiniteAtPoint (f.resLE V U e) x` by `pqf-def-quasifinite` (Stacks 01TD).
5. Since `x` was arbitrary, `pqf-def-quasifinite` gives local quasi-finiteness. -/
theorem isLocallyQuasiFinite_resLE {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (hf : IsLocallyQuasiFinite f) (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    IsLocallyQuasiFinite (f.resLE V U e) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
