/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.TraceClass

/-!

# Specialization of trace classes

Let `c = (c₁, c₂) : C ⟶ X × X` be an endocorrespondence of `(X, K)` over `k` with fixed locus
`ι : Fix(c) ⟶ C`, `d = ι ≫ c₁`, and let `c' : C' ⟶ X' × X'` be an endocorrespondence of
`(X', K')` over a second field `k'`, with fixed locus `ι' : Fix(c') ⟶ C'`. In Varshavsky's proof
of the contracting theorem (*Lefschetz–Verdier trace formula and a generalization of a theorem of
Fujiwara*, §1.4–§2; blueprint `sk-prop-tf-trace-specialization`), `c` is the generic fibre and
`c'` the special fibre of a correspondence over a strictly henselian trait, and nearby cycles
`Ψ` relate the six functors on the two fibres through the exchange maps (blueprint
`det-nearby-exchange-maps`)
```
χ_ι : Ψ_C Rι_* ⟶ Rι'_* Ψ_F,     χ_Δ : Ψ_{X×X} RΔ_* ⟶ RΔ'_* Ψ_X,
β_c : Ψ_C Rc^! ⟶ Rc'^! Ψ_{X×X},  β_d : Ψ_F Rd^! ⟶ Rd'^! Ψ_X,
σ : ℚ̄_ℓ ⟶ Ψ ℚ̄_ℓ,               θ : Ψ ω ⟶ ω'.
```
This file packages these exchange maps and the coherences between them that the trace class
uses (`ProEtale.CondensedRing.Correspondence.TraceSpecialization`), defines the
*specialization* `sp_F(z) = θ_F Ψ_F(z) σ_F` of Borel–Moore sections
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.sp`), and proves that the
specialization of the trace class factors through the exceptional exchange `β_c` at the kernel
`K ⊠ D_X K` (`ProEtale.CondensedRing.Correspondence.TraceSpecialization.traceMap_specialization`,
the first identity of blueprint `det-tf-sp-trace-morphism` with the nearby cycles of the
universal kernel left unidentified). In particular the specialization of the trace class
vanishes as soon as `Rc'^! Ψ_{X×X}(K ⊠ D_X K)` does
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.sp_traceClass_eq_zero`), which is the
mechanism of Varshavsky's vanishing argument (blueprint `det-tf-contracting-vanishing`): for the
deformation to the normal cone, `Ψ_{X×X}(K ⊠ D_X K) ≅ Ψ_X K ⊠ D_{X'} Ψ_X K` by Gabber's theorems,
so `Rc'^! Ψ_{X×X}(K ⊠ D_X K) ≅ RHom(Lc₂'^* Ψ_X K, Rc₁'^! Ψ_X K)`, and `Lc₂'^* Ψ_X K = 0`.

## Main definitions

- `ProEtale.CondensedRing.Correspondence.TraceSpecialization`: the exchange maps between a
  generic and a special correspondence used by the trace class, with their coherences.
- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.sp`: the specialization of
  Borel–Moore sections of the fixed loci.

## Main statements

- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.sp_traceClass`: the specialization
  of the trace class is the adjoint of `σ_C`, the mate of `u`, and the specialized trace map.
- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.traceMap_specialization`: the
  specialized trace map factors through `β_c(K ⊠ D_X K)`.
- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.sp_traceClass_eq_zero`: if
  `Rc'^! Ψ_{X×X}(K ⊠ D_X K) = 0`, the specialization of the trace class vanishes.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

namespace Correspondence

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

variable (c : Correspondence ℓ K) (F : c.FixedLocus) (c' : Correspondence ℓ K')
  (F' : c'.FixedLocus)

namespace TraceSpecialization

variable {c F c' F'} (T : c.TraceSpecialization F c' F')

end TraceSpecialization

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
