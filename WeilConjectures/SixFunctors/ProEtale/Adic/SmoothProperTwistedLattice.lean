/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeAdic
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.CompactOpenLattice
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.GLValues
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Transition
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedModule

/-!
# Smooth proper direct images of lisse sheaves with a lattice

Let `K` be a field, `Y` locally of finite type over `K`, `g : T ⟶ Y` smooth and proper and `F`
a lisse `ℓ`-adic sheaf on `T`, trivialised on a pro-étale cover `f₀ : V ⟶ T` with transition
cocycle `γ : V ×_T V → GL_n(E)` for a finite extension `E` of `ℚ_ℓ`. A *lattice* of `F` is a
twisted section of the cocycle `γ` acting on the discrete set of `ℤ_ℓ`-lattices in `Eⁿ`, its
compact open subgroups (`PadicAlgCl.CompactOpenLattice`). If `F` has a lattice, every `Hᵏ(Rg_* F[0])` is lisse
(`AlgebraicGeometry.ProEtale.isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_isTwistedSection`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open PadicAlgCl AdicSheaf

variable {l : ℕ} [Fact l.Prime]

/-- **Lisse direct images of lisse sheaves with a lattice.** -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_isTwistedSection
    {K : Type u} [Field K] (hK : ringChar K ≠ l) {T Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aY] (g : T ⟶ Y) [Smooth g] [IsProper g] {F : AdicSheaf l T}
    {V : Scheme.{u}} [IsAffine V] (f₀ : V ⟶ T) [WeaklyEtale f₀] [Surjective f₀]
    [QuasiCompact f₀] {n : ℕ} (ε : (f₀)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l V)
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E]
    (γ : ↥(pullback f₀ f₀) → GL (Fin n) E)
    (hγ : ∀ z, ((γ z : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map
      (algebraMap E (PadicAlgCl l)) = (transitionMatrix ε (pullback.snd f₀ f₀)
        (pullback.fst f₀ f₀) pullback.condition.symm).map (locallyFiniteFunctionsEval z))
    (σ : ↥(pullback f₀ (𝟙 T)) → CompactOpenLattice E n)
    (hσ : IsTwistedSection f₀ (fun z L ↦ γ z • L) (𝟙 T) σ) (k : ℤ) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ k).obj
      ((g)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F))) :=
  sorry

end AlgebraicGeometry.ProEtale
