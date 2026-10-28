/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.DeligneLaumon.ConstantFieldRestriction
import Sheaf.DeligneLaumon.GeometricPowerOrbit
import Sheaf.DeligneLaumon.GeometricPowerOrbitStalk
import WeilConjectures.TraceFormula.ModelExtension

/-! # Descent of geometric simple summands under a Frobenius power

Source: the geometric-socle step in `sk-i-dl-general-real`.
(blueprint: lem-zl-semisimple-frobenius-orbit-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.WeilSheaf
open ProEtale

private theorem lisse_lowerStar_iso {l : ℕ} [Fact l.Prime] {Y Z : Scheme.{u}}
    (e : Y ≅ Z) {H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H) :
    IsAdicLisseSheaf ((e.hom)_*ᵃ[l].obj H) :=
  (hH.upperStar e.inv).of_iso ((adicUpperStarIsoLowerStarInv l e.symm).app H)

private theorem irreducible_lowerStar_iso {l : ℕ} [Fact l.Prime]
    {Y Z : Scheme.{u}} (e : Y ≅ Z) {H : AdicSheaf l Y}
    (hH : IsIrreducibleAdicLocalSystem H) :
    IsIrreducibleAdicLocalSystem ((e.hom)_*ᵃ[l].obj H) := by
  let E := adicLowerStarEquivalence l e
  change IsIrreducibleAdicLocalSystem (E.functor.obj H)
  refine ⟨lisse_lowerStar_iso e hH.1, fun hz ↦ hH.2.1 ?_, fun A j _ hA ↦ ?_⟩
  · exact (E.inverse.map_isZero hz).of_iso (E.unitIso.app H)
  · have hA' : IsAdicLisseSheaf (E.inverse.obj A) := lisse_lowerStar_iso e.symm hA
    rcases hH.2.2 _ (E.inverse.map j ≫ (E.unitIso.app H).inv) inferInstance hA' with h | h
    · exact Or.inl ((E.functor.map_isZero h).of_iso (E.counitIso.app A).symm)
    · have : IsIso (E.inverse.map j) := by
        have := IsIso.comp_isIso' h (inferInstance : IsIso (E.unitIso.app H).hom)
        simpa using this
      exact Or.inr (isIso_of_reflects_iso j E.inverse)

/-- Descend a supplied geometric semisimple decomposition after a finite
constant extension, retaining the transitive Frobenius orbit of the summands.

Source: blueprint `sec-deligne-laumon-general/sk-i-dl-general-real`, first unit step
(geometric socle, isotypic blocks and multiplicity eigenline).
(blueprint: lem-zl-semisimple-frobenius-orbit-descent).

Proof: Group the given geometric simple summands by isomorphism class. The Weil
isomorphism permutes the isotypic blocks, and there is a single orbit, since an
orbit sum descends to a Weil subobject. Choose a positive power fixing every
block. On one block write the return as T tensor B, using Schur's lemma on its
simple factor. An eigenline of B exists over the algebraically closed coefficient
field. Its translates around the orbit form a nonzero Weil subobject of V.
Arithmetic simplicity makes it all of V, so every block has multiplicity one.
Take the constant extension of this power's degree and its actual cartesian base
change. Transport the original sheaf by its iterated Weil isomorphism through the
canonical isomorphism of geometric fibers. Each preserved simple summand has the
induced return map and hence is a constructible source Weil sheaf S_a; the
geometric direct-sum isomorphism is equivariant and gives v. These constructions
can also be obtained by the geometric-constituents filtration theorem applied to
the multiplicity spaces. For a pair of summands, a power of the original
Frobenius sends one to the other. It induces a deck automorphism of the constant
extension model. Apply that automorphism to a closed point t. Its image under c
is unchanged, its residue field is isomorphic to the old one, and the original
Weil map identifies the two local return maps. This gives the stated equivalence
of Frobenius modules at t and t'. No choice of eigenvalues of local Frobenius or
reality hypothesis is involved. -/
theorem exists_semisimple_frobenius_orbit_descent
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    (V : WeilSheaf k₀ l X) (hV : V.IsIrreducibleLisse)
    (N : ℕ) (T : Fin N → AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hT : ∀ i, IsIrreducibleAdicLocalSystem (T i)) (vT : V.obj.carrier ≅ ⨁ T) :
    ∃ (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : Algebra k₀ k₁)
      (_ : Algebra.IsAlgebraic k₀ k₁) (_ : Fact (ringChar k₁ ≠ l))
      (r : ℕ) (_ : 0 < r) (hr : Nat.card k₁ = Nat.card k₀ ^ r)
      (C : Scheme.{u}) (_ : C.Over (Spec (CommRingCat.of k₁))) (c : C ⟶ X)
      (hc : IsPullback c (C ↘ Spec (CommRingCat.of k₁)) (X ↘ Spec (CommRingCat.of k₀))
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))))
      (n : ℕ) (S : Fin n → WeilSheaf k₁ l C),
      Nonempty ((constantFieldRestrictionOfSquare hc r hr).obj V ≅ ⨁ S) ∧
      (∀ a, (S a).IsGeometricallyIrreducible) ∧
      ∀ (t : C.finitePoints) (a b : Fin n), ∃ t' : C.finitePoints,
        c t'.1 = c t.1 ∧
        (C ↘ Spec (CommRingCat.of k₁)).residueCard t'.1 =
          (C ↘ Spec (CommRingCat.of k₁)).residueCard t.1 ∧
        Nonempty (((S b).stalk t).Equiv ((S a).stalk t')) := by
  classical
  obtain ⟨r, hrpos, n, W, v, hW, horbit⟩ :=
    exists_geometric_power_orbit V hV N T hT vT
  obtain ⟨K, hK, hr⟩ := ProEtale.CondensedRing.exists_intermediateField_natCard_eq_pow
    k₀ (AlgebraicClosure k₀) hrpos.ne'
  let k₁ : Type u := K
  have : Finite k₁ := hK
  have : Algebra.IsAlgebraic k₀ k₁ := inferInstance
  have : Fact (ringChar k₁ ≠ l) := ⟨by
    rw [← Algebra.ringChar_eq k₀ k₁]
    exact Fact.out⟩
  let f := X ↘ Spec (CommRingCat.of k₀)
  let g := Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))
  let C := pullback f g
  let c : C ⟶ X := pullback.fst f g
  let : C.Over (Spec (CommRingCat.of k₁)) := ⟨pullback.snd f g⟩
  have hc : IsPullback c (C ↘ Spec (CommRingCat.of k₁)) f g :=
    IsPullback.of_hasPullback f g
  let θ := Scheme.Hom.geometricFiberBaseChangeIso hc
  let hθ := Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius hc r hr
  let Ψ := Endofunctor.IsoAlgebra.mapOfNatIso
    (ProEtaleWeilSheaf.transportCommIso (l := l) θ r hθ)
  let S : Fin n → WeilSheaf k₁ l C := fun a ↦
    ⟨Ψ.obj (W a), (lisse_lowerStar_iso θ (hW a).1).isAdicConstructibleSheaf⟩
  let I : WeilSheaf k₁ l C ⥤ ProEtaleWeilSheaf k₁ l C :=
    (WeilSheaf.objectProperty k₁ l C).ι
  have : HasFiniteBiproducts (WeilSheaf.objectProperty k₁ l C).FullSubcategory :=
    inferInstanceAs (HasFiniteBiproducts (WeilSheaf k₁ l C))
  have : I.Additive := ⟨rfl⟩
  have : PreservesFiniteBiproducts I := Functor.preservesFiniteBiproductsOfAdditive I
  have vs : (constantFieldRestrictionOfSquare hc r hr).obj V ≅ ⨁ S :=
    (WeilSheaf.objectProperty k₁ l C).isoMk
      (Ψ.mapIso v ≪≫ Ψ.mapBiproduct W ≪≫ (I.mapBiproduct S).symm)
  refine ⟨k₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    r, hrpos, hr, C, inferInstance, c, hc, n, S, ⟨vs⟩, ?_, ?_⟩
  · intro a
    exact irreducible_lowerStar_iso θ (hW a)
  · intro t a b
    obtain ⟨j, e, he⟩ := horbit a b
    exact exists_stalk_equiv_of_power_orbit hc r hrpos hr V (W a) (W b)
      (biproduct.ι W a ≫ v.inv) (biproduct.ι W b ≫ v.inv) j e he (S a) (S b) rfl rfl t

end AlgebraicGeometry.WeilSheaf
