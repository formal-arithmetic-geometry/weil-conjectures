/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.MatrixComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Minimal matrix complexes over a local ring

Let `S` be a commutative local ring with maximal ideal `𝔪`. A matrix complex over `S` is
*minimal* (`MatrixComplex.IsMinimal`) if all the entries of its matrices lie in `𝔪`; its
associated complex is then minimal in the sense of `CochainComplex.IsMinimal`.

## Main results

- `MatrixComplex.exists_iso_Q_obj_of_isPerfect`: every perfect object of `D(S)` is the image of
  a minimal matrix complex with bounded ranks.
- `MatrixComplex.exists_isIso_Q_map_eq`: a morphism between images of bounded minimal matrix
  complexes in `D(S)` which is an isomorphism is the image of an isomorphism of complexes.
- `MatrixComplex.exists_map_eq_isUnit_det`: invertible matrices lift along surjective morphisms
  of local rings.
- `MatrixComplex.conj`: the conjugate of a matrix complex by invertible matrices, isomorphic to
  it (`MatrixComplex.conjHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

section SmulTop

variable {S : Type u} [CommRing S] (I : Ideal S)

end SmulTop

namespace MatrixComplex

variable {r r' : ℤ → ℕ} {S : Type u} [CommRing S]

/-! ### Matrix complexes from complexes of free modules -/

section OfLinearEquiv

variable (N : CochainComplex (ModuleCat.{u} S) ℤ) (e : ∀ i, N.X i ≃ₗ[S] (Fin (r i) → S))

end OfLinearEquiv

/-! ### Conjugation by invertible matrices -/

section Conj

variable (M : MatrixComplex r S) (b : ∀ i, Matrix (Fin (r i)) (Fin (r i)) S)
  (hb : ∀ i, IsUnit (b i).det)

end Conj

variable [IsLocalRing S]

/-! ### Minimal matrix complexes -/

variable [HasDerivedCategory.{u} (ModuleCat.{u} S)]

end MatrixComplex
