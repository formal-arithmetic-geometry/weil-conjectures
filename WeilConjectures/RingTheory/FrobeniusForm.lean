/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Frobenius forms of finite free extensions of principal ideal domains

Let `R ⟶ S` be a ring morphism of domains which makes `S` a finite free `R`-module,
with `S` a principal ideal domain. Then the `R`-linear dual `Hom_R(S, R)`, an `S`-module through
`(s • λ)(x) = λ(s * x)`, is free of rank one over `S`. A generator `λ` is a *Frobenius form*:
every `R`-linear form on `S` is `λ(s * -)` for a unique `s ∈ S`
(`Module.exists_bijective_comp_mulLeft`).

This is the input that makes extension and coextension of scalars along `R ⟶ S` isomorphic,
for instance for the inclusion `𝒪_E ⟶ 𝒪_L` of rings of integers of finite extensions of `ℚ_ℓ`.

## Proof

The dual `Hom_R(S, R)` is a finitely generated `S`-module, and it is torsion free: if
`λ(s * -) = 0` with `s ≠ 0`, some nonzero `r ∈ R` is a multiple `r = s * t` (`S` is integral
over `R`), so `r * λ(x) = λ(s * t * x) = 0` for all `x`. Over the principal ideal domain `S`
it is therefore free, and comparing ranks over `R` in the tower `R ⟶ S ⟶ Hom_R(S, R)` gives
`rank_R S * rank_S Hom_R(S, R) = rank_R Hom_R(S, R) = rank_R S`, so its rank over `S` is one.
-/

@[expose] public section

namespace Module

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

namespace FrobeniusForm

attribute [local instance] dualModule

variable {R S} [IsDomain R] [IsDomain S] [Module.Finite R S]

variable [IsPrincipalIdealRing S] [Module.Free R S]

end FrobeniusForm

end Module
