/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import WeilConjectures.WeilSheaf.StalkCharpoly
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.AlgebraicGeometry.Regular

/-!
# The Frobenius twist of subsheaves of a Weil sheaf

Let `F` be a Weil sheaf on a `k₀`-scheme `X`, with underlying `ℓ`-adic sheaf `F̄` on the geometric
fiber `X̄` and Weil structure `φ : Fr^* F̄ ≅ F̄`. A subsheaf `P ⊆ F̄` (a subobject in the category
of `ℓ`-adic sheaves, with no Weil structure) has a *Frobenius twist* `T P = φ (Fr^* P) ⊆ F̄`
(`AlgebraicGeometry.WeilSheaf.frobeniusTwist`); `T` is an order automorphism of the lattice of
subobjects of `F̄`, and its `n`-th iterate is `P ↦ φ_n ((Frⁿ)^* P)` for the iterated Weil
structure `φ_n` (`AlgebraicGeometry.WeilSheaf.frobeniusTwist_iterate_mk`).

The subsheaves fixed by `T` are the Weil subsheaves; those fixed by `T^N` are the subsheaves
defined over the extension of degree `N` of `k₀`: such a subsheaf carries the structure of an
algebra for the `N`-th Frobenius pullback (`AlgebraicGeometry.WeilSheaf.stableIsoAlgebra`),
compatibly with the iterated structure `φ_N` of `F` (`AlgebraicGeometry.WeilSheaf.powIsoAlgebra`).

This is the sheaf-theoretic side of the geometric constituents of a Weil sheaf (blueprint
`lem-zl-geometric-constituents-any-base`): an irreducible lisse Weil sheaf has a geometrically
irreducible subsheaf defined over a finite extension
(`AlgebraicGeometry.WeilSheaf.exists_isIrreducibleAdicLocalSystem_frobeniusTwist_iterate_eq`),
and its Frobenius conjugates span the whole sheaf
(`AlgebraicGeometry.WeilSheaf.iSup_frobeniusTwist_iterate_eq_top`).

On geometric stalks, the twist moves the stalk of `P` at `t ≫ Frᵃ` to the stalk of `Tᵃ P` at `t`
(`AlgebraicGeometry.WeilSheaf.stalkSubspace_frobeniusTwist_iterate`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section Twist

variable (F : WeilSheaf k₀ l X)

/-- The *Frobenius twist* `P ↦ φ (Fr^* P)` of subobjects of the underlying `ℓ`-adic sheaf `F̄` of
a Weil sheaf, where `φ : Fr^* F̄ ≅ F̄` is the Weil structure: the transport of subobjects along
the autoequivalence `Fr^* = (Fr⁻¹)_*`, followed by `φ`. -/
noncomputable def frobeniusTwist : Subobject F.obj.carrier ≃o Subobject F.obj.carrier :=
  (Subobject.lowerEquivalence
      (MonoOver.congr F.obj.carrier (frobeniusPullback k₀ l X).asEquivalence)).toOrderIso.trans
    (Subobject.mapIsoToOrderIso F.obj.str)

/-- The Frobenius twist of the subobject given by a monomorphism `u : A ⟶ F̄` is given by the
monomorphism `φ ∘ Fr^* u`. -/
theorem frobeniusTwist_mk {A : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (u : A ⟶ F.obj.carrier) [Mono u] :
    F.frobeniusTwist (Subobject.mk u) =
      Subobject.mk ((frobeniusPullback k₀ l X).map u ≫ F.obj.str.hom) := by
  sorry

/-- The `n`-th iterate of the Frobenius twist of the subobject given by `u : A ⟶ F̄` is given by
the monomorphism `φ_n ∘ (Frⁿ)^* u`, for the iterated Weil structure `φ_n`
(`AlgebraicGeometry.WeilSheaf.frobeniusPowIso`). -/
theorem frobeniusTwist_iterate_mk {A : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (u : A ⟶ F.obj.carrier) [Mono u] (n : ℕ) :
    (⇑F.frobeniusTwist)^[n] (Subobject.mk u) =
      Subobject.mk
        ((((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).inv)_*ᵃ[l].map u ≫
          (F.frobeniusPowIso n).hom) := by
  sorry

/-- The Frobenius twist of a subsheaf which is an irreducible local system is an irreducible
local system: it is isomorphic to the pullback along the automorphism `Fr`. -/
theorem isIrreducibleAdicLocalSystem_frobeniusTwist_iterate {P : Subobject F.obj.carrier}
    (hP : IsIrreducibleAdicLocalSystem (Subobject.underlying.obj P)) (n : ℕ) :
    IsIrreducibleAdicLocalSystem (Subobject.underlying.obj ((⇑F.frobeniusTwist)^[n] P)) := by
  sorry

/-- The Frobenius twist of a lisse subsheaf is lisse. -/
theorem isAdicLisseSheaf_frobeniusTwist_iterate {P : Subobject F.obj.carrier}
    (hP : IsAdicLisseSheaf (Subobject.underlying.obj P)) (n : ℕ) :
    IsAdicLisseSheaf (Subobject.underlying.obj ((⇑F.frobeniusTwist)^[n] P)) := by
  sorry

end Twist

section IsoAlgebra

variable (F : WeilSheaf k₀ l X)

/-- The underlying `ℓ`-adic sheaf of a Weil sheaf with its iterated Weil structure
`φ_N : (Fr^N)^* F̄ ≅ F̄`, an algebra for the `N`-th Frobenius pullback. -/
noncomputable def powIsoAlgebra (N : ℕ) :
    IsoAlgebra ((((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).inv)_*ᵃ[l]) :=
  IsoAlgebra.mk F.obj.carrier (F.frobeniusPowIso N)

/-- A subsheaf `P ⊆ F̄` fixed by the `N`-th iterate of the Frobenius twist, with the structure of
an algebra for the `N`-th Frobenius pullback induced by `φ_N`: the isomorphism
`(Fr^N)^* P ≅ P` through which `φ_N ∘ (Fr^N)^* P.arrow` factors. -/
noncomputable def stableIsoAlgebra {N : ℕ} (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) :
    IsoAlgebra ((((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).inv)_*ᵃ[l]) :=
  IsoAlgebra.mk (Subobject.underlying.obj P)
    ((Subobject.underlyingIso _).symm ≪≫
      Subobject.isoOfEq _ _ ((F.frobeniusTwist_iterate_mk P.arrow N).symm.trans
        ((congrArg (⇑F.frobeniusTwist)^[N] (Subobject.mk_arrow P)).trans hP)))

/-- The inclusion `P ⟶ F̄` of a subsheaf fixed by the `N`-th iterate of the Frobenius twist is a
morphism of algebras for the `N`-th Frobenius pullback. -/
noncomputable def stableIsoAlgebraι {N : ℕ} (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) :
    F.stableIsoAlgebra P hP ⟶ F.powIsoAlgebra N :=
  ObjectProperty.homMk ⟨P.arrow, by
    sorry⟩

@[simp]
lemma stableIsoAlgebraι_hom_f {N : ℕ} (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) :
    (F.stableIsoAlgebraι P hP).hom.f = P.arrow :=
  rfl

/-- A lisse subsheaf `P ⊆ F̄` fixed by the Frobenius twist underlies a lisse Weil subsheaf of
`F`. -/
theorem exists_mono_of_frobeniusTwist_eq {P : Subobject F.obj.carrier}
    (hP : F.frobeniusTwist P = P) (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) :
    ∃ (G : WeilSheaf k₀ l X) (i : G ⟶ F), Mono i ∧ G.IsLisse ∧
      ∃ _ : Mono i.hom.hom.f, Subobject.mk i.hom.hom.f = P := by
  sorry

end IsoAlgebra

section Constituents

variable (F : WeilSheaf k₀ l X)

/-- **Geometric constituents** (blueprint: `lem-zl-geometric-constituents-any-base`, sheaf
form). A nonzero lisse Weil sheaf `F` on `X`, with `X̄` connected, regular and locally Noetherian,
has a subsheaf `P ⊆ F̄` which is an irreducible local system and is fixed by some positive
iterate of the Frobenius twist, i.e. is defined over a finite extension of `k₀`. -/
theorem exists_isIrreducibleAdicLocalSystem_frobeniusTwist_iterate_eq
    [ConnectedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [IsRegular (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [IsLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    (hF : F.IsLisse) (hF0 : ¬ IsZero F) :
    ∃ P : Subobject F.obj.carrier, IsIrreducibleAdicLocalSystem (Subobject.underlying.obj P) ∧
      ∃ N : ℕ, 0 < N ∧ (⇑F.frobeniusTwist)^[N] P = P := by
  sorry

/-- **The Frobenius conjugates of a geometric constituent span** (blueprint:
`thm-zl-real-mixed-by-curves`, descent of the constant extension). Let `F` be an irreducible
lisse Weil sheaf and `P ⊆ F̄` a nonzero lisse subsheaf fixed by `T^M`, `M > 0`, for the
Frobenius twist `T`. Then `P, T P, …, T^{M-1} P` span `F̄`: their sum is fixed by `T`, hence
underlies a nonzero lisse Weil subsheaf of `F`, which is `F`. -/
theorem iSup_frobeniusTwist_iterate_eq_top
    [IsLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    (hF : F.IsIrreducibleLisse) {P : Subobject F.obj.carrier}
    (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) (hP0 : P ≠ ⊥) {M : ℕ} (hM : 0 < M)
    (hP : (⇑F.frobeniusTwist)^[M] P = P) :
    (Finset.univ : Finset (Fin M)).sup (fun n ↦ (⇑F.frobeniusTwist)^[n] P) = ⊤ := by
  sorry

end Constituents

section Stalk

variable (F : WeilSheaf k₀ l X)

/-- The geometric stalk `P_t ⊆ F_t` of a subsheaf `P ⊆ F̄` at a geometric point `t`: the image of
the stalk of `P` in the stalk of `F`. -/
noncomputable def stalkSubspace
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (P : Subobject F.obj.carrier) :
    Submodule (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj (F.stalkObj t)) :=
  LinearMap.range ((WeilCoefficients.toModuleCat l).map ((Sheaf.Γ _ _).map
    ((t)^*[WeilCoefficients.{u} l].map ((ProEtale.AdicSheaf.forget _).map P.arrow)))).hom

/-- The stalk of the whole sheaf is the whole stalk. -/
theorem stalkSubspace_top
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    F.stalkSubspace t ⊤ = ⊤ := by
  sorry

/-- If finitely many subsheaves span `F̄`, their stalks span the stalk of `F`: the stalk functor
is exact. -/
theorem iSup_stalkSubspace_eq_top
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    {M : ℕ} (Q : Fin M → Subobject F.obj.carrier) (hQ : (Finset.univ : Finset (Fin M)).sup Q = ⊤) :
    ⨆ n, F.stalkSubspace t (Q n) = ⊤ := by
  sorry

/-- The stalk at `t` of the `a`-th Frobenius twist of `P` is the image of the stalk of `P` at
`t ≫ Frᵃ` under the identification `F_{t ≫ Frᵃ} ≅ F_t` induced by `φ_a`
(`AlgebraicGeometry.WeilSheaf.stalkObjFrobeniusPowIso`). -/
theorem stalkSubspace_frobeniusTwist_iterate
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (P : Subobject F.obj.carrier) (a : ℕ) :
    F.stalkSubspace t ((⇑F.frobeniusTwist)^[a] P) =
      (F.stalkSubspace (t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).hom)
        P).map (WeilCoefficients.linearEquivOfIso (F.stalkObjFrobeniusPowIso a t)).toLinearMap := by
  sorry

/-- The reparametrisation `F_{σᵃ ≫ t} ≅ F_t` of a geometric point by a power of the Frobenius
of `k̄` (`AlgebraicGeometry.WeilSheaf.stalkObjSpecFrobeniusPowIso`) carries the stalk of `P` at
`σᵃ ≫ t` to its stalk at `t`. -/
theorem stalkSubspace_specGeometricFrobenius_pow
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (P : Subobject F.obj.carrier) (a : ℕ) :
    (F.stalkSubspace ((specGeometricFrobenius k₀ ^ a).hom ≫ t) P).map
        (WeilCoefficients.linearEquivOfIso (F.stalkObjSpecFrobeniusPowIso a t)).toLinearMap =
      F.stalkSubspace t P := by
  sorry

/-- The stalk at `t` of a subsheaf fixed by `T^N` is stable under the Frobenius relative to
`𝔽_{q^N}` of the stalk of `F` at a geometric point `t` fixed by `Fr^N` up to reparametrisation. -/
theorem frobenius_mem_stalkSubspace
    {t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {N : ℕ} (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).hom =
      (specGeometricFrobenius k₀ ^ N).hom ≫ t)
    {P : Subobject F.obj.carrier} (hP : (⇑F.frobeniusTwist)^[N] P = P)
    {v : (F.stalkAt t N ht).carrier} (hv : v ∈ F.stalkSubspace t P) :
    (F.stalkAt t N ht).frobenius v ∈ F.stalkSubspace t P := by
  sorry

/-- The identification `F_{t ≫ Frᵃ} ≅ F_t` induced by `φ_a` intertwines the Frobenius relative to
`𝔽_{q^N}` at the two geometric points. -/
theorem stalkObjFrobeniusPowIso_frobenius
    {t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {N : ℕ} (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).hom =
      (specGeometricFrobenius k₀ ^ N).hom ≫ t) (a : ℕ)
    (ht' : (t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).hom) ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).hom =
        (specGeometricFrobenius k₀ ^ N).hom ≫
          t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).hom)
    (v : (F.stalkAt _ N ht').carrier) :
    WeilCoefficients.linearEquivOfIso (F.stalkObjFrobeniusPowIso a t)
        ((F.stalkAt _ N ht').frobenius v) =
      (F.stalkAt t N ht).frobenius
        (WeilCoefficients.linearEquivOfIso (F.stalkObjFrobeniusPowIso a t) v) := by
  sorry

/-- The reparametrisation `F_{σᵃ ≫ t} ≅ F_t` intertwines the Frobenius relative to `𝔽_{q^N}`. -/
theorem stalkObjSpecFrobeniusPowIso_frobenius
    {t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {N : ℕ} (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).hom =
      (specGeometricFrobenius k₀ ^ N).hom ≫ t) (a : ℕ)
    (ht' : ((specGeometricFrobenius k₀ ^ a).hom ≫ t) ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).hom =
        (specGeometricFrobenius k₀ ^ N).hom ≫ (specGeometricFrobenius k₀ ^ a).hom ≫ t)
    (v : (F.stalkAt _ N ht').carrier) :
    WeilCoefficients.linearEquivOfIso (F.stalkObjSpecFrobeniusPowIso a t)
        ((F.stalkAt _ N ht').frobenius v) =
      (F.stalkAt t N ht).frobenius
        (WeilCoefficients.linearEquivOfIso (F.stalkObjSpecFrobeniusPowIso a t) v) := by
  sorry

/-- A subsheaf which is an irreducible local system has a nonzero stalk at every geometric point,
when the geometric fiber is connected, regular and locally Noetherian. -/
theorem stalkSubspace_ne_bot
    [ConnectedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [IsRegular (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [IsLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    {P : Subobject F.obj.carrier}
    (hP : IsIrreducibleAdicLocalSystem (Subobject.underlying.obj P)) :
    F.stalkSubspace t P ≠ ⊥ := by
  sorry

end Stalk

end AlgebraicGeometry.WeilSheaf
