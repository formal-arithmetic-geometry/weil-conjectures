/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.BoundedHom
public import WeilConjectures.SixFunctors.Etale.Derived.FieldStagePointers
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Uniformizer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible

/-!
# The uniform `Ext` bound for constructible `𝒪_E`-sheaves

Blueprint `sk-lem-int-ext` (2). Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of
integers `𝒪_E`, uniformizer `ϖ` and residue field `𝔽_E`, and let `X` be a separated scheme of finite
type over a field `k` of characteristic prime to `ℓ` with `cd_ℓ(k) < ∞`. For every constructible
`𝒪_{E,X}`-module `M` there is `d` with `Ext^q(M, B) = 0` for `q > d` and every constructible `B`
(`hasUniformConstructibleExtBound_padicIntegersRingObj_of_hasFiniteCohomologicalDimension`).

The proof avoids derived limits:

* *Torsion targets.* By the triangle `B --ϖ--> B ⟶ B ⊗ᴸ 𝔽_E ⟶`
  (`ProEtale.exists_distinguished_regularEndCenter_derivedExtendScalars`) and the adjunction
  between derived extension and restriction of scalars along `𝒪_E ⟶ 𝔽_E`,
  `Ext^q_{𝒪_E}(M, B ⊗ᴸ 𝔽_E) = Ext^q_{𝔽_E}(M ⊗ᴸ 𝔽_E, B ⊗ᴸ 𝔽_E)`. The source is a constructible
  complex of `𝔽_E`-sheaves and the target has constructible cohomology sheaves (of étale origin) in
  degrees `[-1, 0]`, so these groups vanish for `q` large, uniformly in `B`
  (`exists_forall_eq_zero_of_constructibleFiniteTor_of_generation`, which uses `cd_ℓ(k) < ∞`).
* *Inverting `ϖ`.* Hence, for `q` large, multiplication by `ϖ` is bijective on
  `V = Hom(M, B[q])`.
* *Completeness.* On the countable power of `B`, `(xₙ) ↦ (xₙ - ϖ x_{n+1})` is an isomorphism
  (`ProEtale.isIso_sub_powShift_padicIntegersCenter_of_isConstructible`); applying `Hom(M, -[q])`,
  which commutes with products, `(xₙ) ↦ (xₙ - ϖ x_{n+1})` is injective on `V^ℕ`. For `v ∈ V` the
  sequence `xₙ = ϖ^{-n} v` lies in its kernel, so `v = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

section Reduction

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

end Reduction

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {k : Type u} [Field k]
  [Fact (ringChar k ≠ ℓ)]

end AlgebraicGeometry.ProEtale
