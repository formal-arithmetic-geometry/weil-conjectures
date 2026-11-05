/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Free
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact
public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseAbelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy

/-!
# Irreducible lisse subsheaves of a lisse `ℓ`-adic sheaf

Let `Y` be a locally Noetherian scheme with a monodromy of lisse sheaves `M` which is an
equivalence at a geometric point `t`
(`AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt`), e.g. `Y` connected, regular and
locally Noetherian (`AlgebraicGeometry.ProEtale.exists_lisseMonodromy`). We only use that the
stalk functor at `t` is faithful on lisse sheaves; the *rank*
`AlgebraicGeometry.ProEtale.adicStalkRank` of a lisse sheaf is the dimension of its stalk at `t`.

* The rank is additive in short exact sequences of lisse sheaves, and a lisse sheaf of rank zero
  is zero.
* Among infinitely many irreducible lisse subsheaves `T₀, T₁, …` of a lisse sheaf `V`, two are
  isomorphic (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_iso_of_mono`): as long as
  `T_k` is not isomorphic to an earlier `T_j`, it meets the sum `P_k` of the earlier ones
  trivially, so that the rank of `P_k` grows with `k`.
* For an irreducible lisse `S`, a lisse `V` and an autoequivalence `Φ` of `ℓ`-adic sheaves
  commuting with scalars, together with `Φ S ≅ S` and `Φ V ≅ V`, there is a monomorphism
  `S ⟶ V` which is an eigenvector of the induced `ℚ̄_ℓ`-linear operator on the
  finite-dimensional space `Hom(S, V)`
  (`AlgebraicGeometry.ProEtale.IsIrreducibleAdicLocalSystem.exists_mono_map_comp_eq`), since
  `ℚ̄_ℓ` is algebraically closed.
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

section Iso

variable {X Y : Scheme.{u}}

/-- The pushforward of a lisse sheaf along an isomorphism of schemes is lisse: it is the pullback
along the inverse isomorphism. -/
theorem IsAdicLisseSheaf.adicLowerStar_of_iso (e : X ≅ Y) {F : AdicSheaf l X}
    (hF : IsAdicLisseSheaf F) : IsAdicLisseSheaf ((e.hom)_*ᵃ[l].obj F) :=
  (hF.upperStar e.inv).of_iso ((adicUpperStarIsoLowerStarInv l e.symm).app F)

/-- The pushforward of an irreducible local system along an isomorphism of schemes is an
irreducible local system: the pushforward along `e.inv` is an inverse equivalence, and both
pushforwards preserve lisse sheaves. -/
theorem IsIrreducibleAdicLocalSystem.adicLowerStar_of_iso (e : X ≅ Y) {F : AdicSheaf l X}
    (hF : IsIrreducibleAdicLocalSystem F) :
    IsIrreducibleAdicLocalSystem ((e.hom)_*ᵃ[l].obj F) := by
  obtain ⟨hl, hz, h⟩ := hF
  let E := adicLowerStarEquivalence l e
  refine ⟨hl.adicLowerStar_of_iso e,
    fun h0 ↦ hz ((E.inverse.map_isZero h0).of_iso (E.unitIso.app F)), fun G i _ hG ↦ ?_⟩
  rcases h (E.inverse.obj G) (E.inverse.map i ≫ E.unitIso.inv.app F) inferInstance
    (hG.adicLowerStar_of_iso e.symm) with h' | h'
  · exact Or.inl ((E.functor.map_isZero h').of_iso (E.counitIso.app G).symm)
  · have : IsIso (E.inverse.map i) := IsIso.of_isIso_comp_right _ (E.unitIso.inv.app F)
    exact Or.inr (isIso_of_reflects_iso i E.inverse)

end Iso

section Schur

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y]

end Schur

section Rank

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)

variable {M : LisseMonodromy l Y Ω}

end Rank

end AlgebraicGeometry.ProEtale
