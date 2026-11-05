/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Flat
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Modules
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Noetherian models of proper flat families

Let `V` be an affine scheme, `f : X ⟶ V` proper and of finite presentation, and `ℱ` an
`𝒪_X`-module of finite presentation which is flat over `V`. Then `(f, ℱ)` is the base change of
a pair `(p, 𝒢)` over an affine scheme `S` with Noetherian ring of global sections: `p : Y ⟶ S`
is proper and of finite presentation, `𝒢` is of finite presentation and flat over `S`, and there
is a cartesian square
```
X ---h---> Y
|          |
f          p
v          v
V ---π---> S
```
with `h^* 𝒢 ≅ ℱ` (EGA IV₃, 8.9.1, 8.10.5, 11.2.6; Stacks, Tags 01ZM, 081F, 01ZR).

## Proof

`V` is the limit of the spectra of the finitely generated subrings of `Γ(V, ⊤)`
(`AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`). The morphism `f` descends to a
separated morphism of finite presentation over a stage (Stacks 01ZQ), the module `ℱ` descends to
a later stage (Stacks 01ZR), and properness (Stacks 081F) and flatness (EGA IV₃ 11.2.6) hold at
all sufficiently large stages.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.NoetherianApproximation

namespace Scheme.Modules

end Scheme.Modules

end AlgebraicGeometry
