/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Sylow

/-!
# Galois subextensions of prime degree and degrees of Galois extensions

* `IsGalois.exists_isGalois_finrank_eq_prime_le_of_finrank_eq_prime_pow`: in a finite Galois
  extension `E/K` of degree `p ^ k`, every intermediate field `M ≠ K` contains an intermediate
  field `M'` which is Galois of degree `p` over `K` (`p`-group reduction).
* `IntermediateField.exists_isGalois_finrank_eq_prime_le`: the same inside an algebraically closed
  field `Ω`, assuming every finite Galois subextension of `Ω/L` has `p`-power degree.
* `IsGalois.exists_not_pow_eq_of_prime_dvd_finrank`: if `K` contains a primitive `ℓ`-th root of
  unity and `ℓ` divides the degree of a finite Galois extension `E/K`, some intermediate field of
  `E/K` contains an element that is not an `ℓ`-th power in it (Sylow + Kummer theory).
* `IntermediateField.mem_of_prime_dvd_finrank`: consequently, if every finite subextension of
  `Ω/L` is `ℓ`-divisible and `L` contains the `ℓ`-th roots of unity for all primes `ℓ ∉ S`, the
  prime factors of the degrees of finite Galois subextensions of `Ω/L` lie in `S`.
-/

@[expose] public section

open Module Polynomial IntermediateField

namespace IsGalois

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

end IsGalois

namespace IntermediateField

variable {L Ω : Type*} [Field L] [Field Ω] [Algebra L Ω]

end IntermediateField
