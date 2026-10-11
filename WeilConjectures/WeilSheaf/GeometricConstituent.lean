/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisse
public import WeilConjectures.WeilSheaf.Category

/-!
# The trivial geometric constituent of an irreducible Weil sheaf

Let `X` be a `k₀`-scheme whose geometric fiber `X̄` is irreducible, and `F` a nonzero irreducible
lisse Weil sheaf on `X`. If the trivial sheaf `ℚ̄_ℓ` is a geometric constituent of `F`, that is
a quotient of a lisse subsheaf of the underlying sheaf `F̄` on `X̄`, then `F̄` is constant: a
finite direct sum of copies of `ℚ̄_ℓ`
(`AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.exists_iso_biproduct_unit`).

This is the sheaf-theoretic form of Clifford's theorem for the normal subgroup `π₁(X̄)` of the
Weil group. The lisse sheaves on the irreducible `X̄` form an abelian category in which every
object has finite length, measured by the dimension of a geometric stalk
(`WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisse`), and the Frobenius pullback
`Fr^*` is an autoequivalence of it.

- Let `S ⊆ F̄` be a lisse subsheaf of minimal positive rank; it is irreducible. Its Frobenius
  translates `S_n = φ(Fr^* S_{n-1})` are irreducible lisse subsheaves of `F̄`.
- The sums `S_0 + ⋯ + S_N` increase and stabilise; the stable sum `T` is carried into itself by
  `φ ∘ Fr^*`, hence onto itself by rank, so it is a Weil subsheaf, and `T = F̄` by the
  irreducibility of `F`. Thus `F̄` is a quotient of `S_0 ⊕ ⋯ ⊕ S_N`.
- A subquotient `ℚ̄_ℓ` of `S_0 ⊕ ⋯ ⊕ S_N` forces some `S_n ≅ ℚ̄_ℓ`, by induction on `N`; then
  `S ≅ ℚ̄_ℓ` and every `S_n ≅ Fr^{*n} ℚ̄_ℓ ≅ ℚ̄_ℓ`.
- A lisse quotient of a finite sum of copies of the irreducible `ℚ̄_ℓ` is again such a sum.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The Frobenius pullback of a lisse sheaf is lisse: it is the pullback along the geometric
Galois Frobenius. -/
theorem isAdicLisseSheaf_frobeniusPullback_obj
    {H : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} (hH : IsAdicLisseSheaf H) :
    IsAdicLisseSheaf ((frobeniusPullback k₀ l X).obj H) :=
  (hH.upperStar _).of_iso
    ((adicUpperStarIsoLowerStarInv l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius).app H)

/-- A sheaf whose Frobenius pullback is lisse is lisse. -/
theorem isAdicLisseSheaf_of_frobeniusPullback_obj
    {H : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hH : IsAdicLisseSheaf ((frobeniusPullback k₀ l X).obj H)) : IsAdicLisseSheaf H :=
  let Fr := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
  (hH.upperStar Fr.inv).of_iso ((adicUpperStarIsoLowerStarInv l Fr.symm).app _ ≪≫
    ((adicLowerStarEquivalence l Fr.symm).unitIso.app H).symm)

/-- The Frobenius pullback of the constant sheaf `ℚ̄_ℓ` is `ℚ̄_ℓ`. -/
noncomputable def frobeniusPullbackUnitIso :
    (frobeniusPullback k₀ l X).obj
        (AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≅
      AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  adicLowerStarUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm


variable {K : Type u} [Field K] [IsAlgClosed K]

/-- The Frobenius pullback of a lisse sheaf has the same rank: its stalk at `s` is the stalk of
the sheaf at `s ≫ Fr`. -/
theorem finrank_geometricStalkFunctor_frobeniusPullback_obj
    [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    {H : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} (hH : IsAdicLisseSheaf H)
    (s : Spec (.of K) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((geometricStalkFunctor l s).obj ((frobeniusPullback k₀ l X).obj H))) =
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((geometricStalkFunctor l s).obj H)) := by
  let Fr := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
  let e : (s)^*ᵃ[l].obj ((frobeniusPullback k₀ l X).obj H) ≅ (s ≫ Fr.hom)^*ᵃ[l].obj H :=
    (s)^*ᵃ[l].mapIso ((adicUpperStarIsoLowerStarInv l Fr).app H).symm ≪≫
      ((adicUpperStarComp l s Fr.hom).app H).symm
  rw [← hH.finrank_geometricStalkFunctor_eq (s ≫ Fr.hom) s]
  exact ((AdicSheaf.forget _ ⋙ Sheaf.Γ _ _ ⋙ WeilCoefficients.toModuleCat l).mapIso
    e).toLinearEquiv.finrank_eq

/-- The Frobenius pullback of an irreducible local system is irreducible: it is an
autoequivalence preserving lisse sheaves in both directions. -/
theorem IsIrreducibleAdicLocalSystem.frobeniusPullback_obj
    {H : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hH : IsIrreducibleAdicLocalSystem H) :
    IsIrreducibleAdicLocalSystem ((frobeniusPullback k₀ l X).obj H) := by
  let eqv := adicLowerStarEquivalence l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm
  change IsIrreducibleAdicLocalSystem (eqv.functor.obj H)
  refine ⟨isAdicLisseSheaf_frobeniusPullback_obj hH.1, fun hz ↦ hH.2.1 ?_,
    fun A j _ hA ↦ ?_⟩
  · exact (eqv.inverse.map_isZero hz).of_iso (eqv.unitIso.app H)
  · have hA' : IsAdicLisseSheaf (eqv.inverse.obj A) :=
      isAdicLisseSheaf_of_frobeniusPullback_obj (hA.of_iso (eqv.counitIso.app A).symm)
    rcases hH.2.2 _ (eqv.inverse.map j ≫ (eqv.unitIso.app H).inv) inferInstance hA' with h | h
    · exact Or.inl ((eqv.functor.map_isZero h).of_iso (eqv.counitIso.app A).symm)
    · have : IsIso (eqv.inverse.map j) := by
        have := IsIso.comp_isIso' h (inferInstance : IsIso (eqv.unitIso.app H).hom)
        simpa using this
      exact Or.inr (isIso_of_reflects_iso j eqv.inverse)

end AlgebraicGeometry.WeilSheaf
