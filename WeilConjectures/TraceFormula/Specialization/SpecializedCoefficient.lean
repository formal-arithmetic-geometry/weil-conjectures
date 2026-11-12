/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Basic

/-!

# The specialized coefficient map

Let `T` be specialization data from a correspondence `c` of `(X, K)` with fixed locus `F` to a
correspondence `c'` with fixed locus `F'`
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization`), and put `K' = Ψ_X K`. Given the
pullback exchange `α_{c₂} : Lc₂'^* Ψ_X ⟶ Ψ_C Lc₂^*` and the exceptional exchange
`β_{c₁} : Ψ_C Rc₁^! ⟶ Rc₁'^! Ψ_X`, the coefficient map `u : Lc₂^* K ⟶ Rc₁^! K` of `c` specializes
to the composite (blueprint `proposition-specialization-trace-class--1`)
```
u_s : Lc₂'^* K' --α_{c₂}--> Ψ_C Lc₂^* K --Ψ_C u--> Ψ_C Rc₁^! K --β_{c₁}--> Rc₁'^! K'
```
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.specializedCoeff`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace Correspondence.TraceSpecialization

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K} {F : c.FixedLocus} {c' : Correspondence ℓ K'} {F' : c'.FixedLocus}
  (T : c.TraceSpecialization F c' F')

/-- The *specialized coefficient map* (blueprint `proposition-specialization-trace-class--1`):
for `K' = Ψ_X K`, the pullback exchange `α_{c₂} : Lc₂'^* Ψ_X ⟶ Ψ_C Lc₂^*` and the exceptional
exchange `β_{c₁} : Ψ_C Rc₁^! ⟶ Rc₁'^! Ψ_X`, the composite
`u_s = β_{c₁} ∘ Ψ_C(u) ∘ α_{c₂} : Lc₂'^* K' ⟶ Rc₁'^! K'` of the coefficient map `u` of `c`. -/
noncomputable def specializedCoeff
    (α : T.ΨX ⋙ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c'.c₂ ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂ ⋙ T.ΨC)
    (β : boundedConstructibleUpperShriek ℓ c.c₁ ⋙ T.ΨC ⟶
      T.ΨX ⋙ boundedConstructibleUpperShriek ℓ c'.c₁) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c'.c₂).obj (T.ΨX.obj K) ⟶
      (boundedConstructibleUpperShriek ℓ c'.c₁).obj (T.ΨX.obj K) :=
  α.app K ≫ T.ΨC.map c.u ≫ β.app K

end Correspondence.TraceSpecialization

end AlgebraicGeometry.ProEtale.CondensedRing
