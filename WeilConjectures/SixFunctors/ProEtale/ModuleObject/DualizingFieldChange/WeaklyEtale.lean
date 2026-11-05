/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Closed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale

/-!

# Exceptional inverse images of closed immersions and weakly étale base change

Let `k₁` and `k₂` be fields and `i : Z ⟶ P` a closed immersion of separated `k₁`-schemes of finite
type with a cartesian square
```
Z' --πZ--> Z
 |i'       |i
 v         v
P' --πP--> P
```
where `i' : Z' ⟶ P'` is a closed immersion of separated `k₂`-schemes of finite type. If `πP` is
weakly étale, the base change map `γ : πZ^* Ri^! ⟶ Ri'^! πP^*` of the exceptional inverse image
(`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`) is an isomorphism on bounded constructible
`ℚ̄_ℓ`-complexes (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_weaklyEtale`).
This applies for instance to the inclusion of the generic point of `𝔸¹_k`, which changes the
base field from `k` to `k(t)`.

## Proof

As in `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_fieldExtension`: complete
the unit `M ⟶ Rj_* j^* M` (`j : V ⟶ P` the open complement of `i`) to a distinguished triangle;
its pullback along `πP` is distinguished, and its third term `πP^* Rj_* j^* M` is
`Rj'_* πV^* j^* M` by weakly étale base change
(`ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale`, for the weakly étale restriction
`πV = πP ∣_ V`), which receives no maps from `Ri'_*`. Unlike the case of a field extension, no
finiteness condition on `M` is needed for this base change.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The coefficient ring `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {P Z : Over (Spec (.of k₁))} [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
  [IsSeparated P.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {P' Z' : Over (Spec (.of k₂))} [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom]
  [IsSeparated P'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {i : Z ⟶ P} {i' : Z' ⟶ P'} [IsClosedImmersion i.left] [IsClosedImmersion i'.left]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left}

end AlgebraicGeometry.ProEtale.CondensedRing
