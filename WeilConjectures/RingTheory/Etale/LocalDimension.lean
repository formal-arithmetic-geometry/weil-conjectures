/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Unramified.LocalStructure
import WeilConjectures.RingTheory.QuasiFiniteLocalDimension
import WeilConjectures.RingTheory.RingKrullDimLeOfFaithfullyFlatOfIsLocalHom

/-!
# Local dimension under an étale ring map

For an étale ring map `A → B` and a prime `q` of `B` lying over `p`, the local rings `A_p` and
`B_q` have the same Krull dimension.

## Implementation details

The induced map `A_p → B_q` is flat and local, hence faithfully flat, which gives
`dim A_p ≤ dim B_q` by going down. Conversely, an étale map is of finite type and quasi-finite
at `q`, so the local dimension inequality gives `dim B_q ≤ dim A_p`.

## References

* Stacks Project, More on Algebra, Lemma Tag 07QP
-/

@[expose] public section

universe u v

namespace RingHom.Etale

/-- Localizing an étale ring map at a prime and its contraction preserves Krull dimension. -/
theorem ringKrullDim_localization_eq {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Etale) (q : Ideal B) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime (Ideal.comap f q)) =
      ringKrullDim (Localization.AtPrime q) := by
  let := f.toAlgebra
  have : Algebra.Etale A B := hf
  apply le_antisymm
  · let g := Localization.localRingHom (Ideal.comap f q) q f rfl
    have hg : g.Flat := (Etale.iff_flat_and_formallyUnramified.mp hf).1.localRingHom
      q (Ideal.comap f q) rfl
    let := g.toAlgebra
    have : IsLocalHom (algebraMap (Localization.AtPrime (Ideal.comap f q))
        (Localization.AtPrime q)) := show IsLocalHom g from inferInstance
    have : Module.Flat (Localization.AtPrime (Ideal.comap f q))
        (Localization.AtPrime q) := hg
    have hgfaithful : g.FaithfullyFlat :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact RingHom.ringKrullDim_le_of_faithfullyFlat_of_isLocalHom g hgfaithful
  · have hq : Algebra.IsQuasiFiniteAtPrime A B ⟨q, inferInstance⟩ := by
      unfold Algebra.IsQuasiFiniteAtPrime
      exact isOpen_discrete _
    exact Algebra.ringKrullDim_le_of_isQuasiFiniteAtPrime A B ⟨q, inferInstance⟩ hq

end RingHom.Etale
