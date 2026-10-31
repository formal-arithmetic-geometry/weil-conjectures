/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Transport
public import WeilConjectures.WeilSheaf.BaseChangeField.Geometric
public import WeilConjectures.WeilSheaf.Stalk
import WeilConjectures.DeligneLaumon.FrobeniusPowerStalkTransport
import WeilConjectures.WeilSheaf.StalkCharpoly

/-! # Stalk comparison for two embedded power-return summands

Source: `sk-i-dl-general-real`, geometric Frobenius orbit argument.
(blueprint: lem-zl-geometric-power-orbit-stalk).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Endofunctor
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.WeilSheaf
open ProEtale

private theorem restrict_commuting_returns
    {D : Type*} [Category D] {F G : D ⥤ D} (c : F ⋙ G ≅ G ⋙ F)
    {W : D} (a : G.obj W ≅ W) (b : F.obj W ≅ W)
    (hab : c.hom.app W ≫ F.map a.hom ≫ b.hom = G.map b.hom ≫ a.hom)
    (P Q : IsoAlgebra G) (iP : P.carrier ⟶ W) (iQ : Q.carrier ⟶ W) [Mono iQ]
    (hP : G.map iP ≫ a.hom = P.str.hom ≫ iP)
    (hQ : G.map iQ ≫ a.hom = Q.str.hom ≫ iQ)
    (e : F.obj P.carrier ≅ Q.carrier)
    (he : e.hom ≫ iQ = F.map iP ≫ b.hom) :
    G.map e.hom ≫ Q.str.hom = c.hom.app P.carrier ≫ F.map P.str.hom ≫ e.hom := by
  apply (cancel_mono iQ).mp
  calc
    (G.map e.hom ≫ Q.str.hom) ≫ iQ = G.map (e.hom ≫ iQ) ≫ a.hom := by
      rw [Category.assoc, ← hQ, ← Category.assoc, ← Functor.map_comp]
    _ = G.map (F.map iP) ≫ G.map b.hom ≫ a.hom := by
      rw [he, Functor.map_comp, Category.assoc]
    _ = G.map (F.map iP) ≫ c.hom.app W ≫ F.map a.hom ≫ b.hom := by
      rw [← hab]
    _ = c.hom.app P.carrier ≫ F.map (G.map iP) ≫ F.map a.hom ≫ b.hom := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun f ↦ f ≫ F.map a.hom ≫ b.hom) (c.hom.naturality iP)
    _ = c.hom.app P.carrier ≫ F.map (P.str.hom ≫ iP) ≫ b.hom := by
      rw [← Functor.map_comp_assoc, hP]
    _ = (c.hom.app P.carrier ≫ F.map P.str.hom ≫ e.hom) ≫ iQ := by
      rw [Functor.map_comp]
      simp only [Category.assoc, he]

private theorem fixed_conjugate_power
    {D : Type*} [Category D] {Y Z R : D} (θ : Y ≅ Z)
    (a : Aut Y) (b : Aut Z) (r j : ℕ)
    (hθ : θ.hom ≫ b.hom = (a ^ r).hom ≫ θ.hom)
    (s : R ⟶ Z) (m : ℕ) (σ : R ⟶ R)
    (hs : s ≫ (b ^ m).hom = σ ≫ s) :
    (s ≫ θ.inv ≫ (a ^ j).hom ≫ θ.hom) ≫ (b ^ m).hom =
      σ ≫ (s ≫ θ.inv ≫ (a ^ j).hom ≫ θ.hom) := by
  let β := θ.inv ≫ (a ^ j).hom ≫ θ.hom
  have hθinv : b.hom ≫ θ.inv = θ.inv ≫ (a ^ r).hom := by
    have h := congrArg (fun f ↦ θ.inv ≫ f ≫ θ.inv) hθ
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using h
  have hcomm : (a ^ j).hom ≫ (a ^ r).hom = (a ^ r).hom ≫ (a ^ j).hom := by
    rw [Aut.pow_hom_comp_pow_hom, Aut.pow_hom_comp_pow_hom, Nat.add_comm]
  have hβ : β ≫ b.hom = b.hom ≫ β := by
    dsimp only [β]
    calc
      (θ.inv ≫ (a ^ j).hom ≫ θ.hom) ≫ b.hom =
          θ.inv ≫ (a ^ j).hom ≫ (a ^ r).hom ≫ θ.hom := by
        simp only [Category.assoc, hθ]
      _ = θ.inv ≫ (a ^ r).hom ≫ (a ^ j).hom ≫ θ.hom := by
        simpa only [Category.assoc] using
          congrArg (fun f ↦ θ.inv ≫ f ≫ θ.hom) hcomm
      _ = b.hom ≫ (θ.inv ≫ (a ^ j).hom ≫ θ.hom) := by
        rw [← Category.assoc b.hom, hθinv]
        simp only [Category.assoc]
  have hβm : ∀ n : ℕ, β ≫ (b ^ n).hom = (b ^ n).hom ≫ β := by
    intro n
    induction n with
    | zero =>
      change β ≫ 𝟙 Z = 𝟙 Z ≫ β
      simp
    | succ n ih =>
      simp only [pow_succ, Aut.Aut_mul_def, Iso.trans_hom, Category.assoc]
      rw [← Category.assoc β b.hom, hβ, Category.assoc, ih]
  have h : (s ≫ β) ≫ (b ^ m).hom = σ ≫ (s ≫ β) := by
    rw [Category.assoc, hβm, ← Category.assoc s, hs, Category.assoc]
  simpa only [β, Category.assoc] using h

/-- Two power-return subobjects related by the original Weil return have the
same local Frobenius module at deck-related points of a constant extension.

Source: blueprint `sec-deligne-laumon-general/sk-i-dl-general-real/_section.md`,
first step, and `thm-zl-real-mixed-by-curves.proof.md`, local power comparison.
(blueprint: lem-zl-geometric-power-orbit-stalk).

Proof: The j-th power of the finite-field Frobenius induces a deck automorphism
of the cartesian constant extension C over X. Send t by this automorphism (with
the inverse convention if required by the pullback convention), obtaining t'.
An automorphism preserves finite points and gives an isomorphism of residue
fields. Thus c(t')=c(t) and their residue cardinalities coincide. On geometric
fibers this deck transformation is the original j-th Frobenius, after changing
the geometric point by the corresponding automorphism of the algebraic closure.
Transport e along the canonical geometric-fiber isomorphism. The equation with
the two monic inclusions says that this transport is the restriction of V's
j-th Weil return. The r-th and j-th iterates of one Weil return commute, including
the canonical pullback-composition identifications. Cancel the inclusion to see
that this transport intertwines the induced r-th returns on P and Q. Iterating
to the common residue degree gives an intertwiner of the local Frobenius maps.
The stalk transport is an isomorphism, hence the required Frobenius-module
equivalence. This is a comparison of two supplied subobjects; it uses neither
simplicity nor a decomposition nor any eigenvalue choice. -/
theorem exists_stalk_equiv_of_power_orbit
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    {k₁ : Type u} [Field k₁] [Finite k₁] [Algebra k₀ k₁]
    [Algebra.IsAlgebraic k₀ k₁] [Fact (ringChar k₁ ≠ l)]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₁))] {c : C ⟶ X}
    (hc : IsPullback c (C ↘ Spec (CommRingCat.of k₁)) (X ↘ Spec (CommRingCat.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))))
    (r : ℕ) (hrpos : 0 < r) (hr : Nat.card k₁ = Nat.card k₀ ^ r)
    (V : WeilSheaf k₀ l X)
    (P Q : IsoAlgebra (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r))
    (iP : P ⟶ (ProEtaleWeilSheaf.powFunctor k₀ l X r).obj V.obj)
    (iQ : Q ⟶ (ProEtaleWeilSheaf.powFunctor k₀ l X r).obj V.obj)
    [Mono iP] [Mono iQ] (j : ℕ)
    (e : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).obj P.carrier ≅ Q.carrier)
    (he : e.hom ≫ iQ.hom.f =
      (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).map iP.hom.f ≫
        (V.obj.frobeniusPowIso j).hom)
    (A B : WeilSheaf k₁ l C)
    (hA : A.obj = (IsoAlgebra.mapOfNatIso (ProEtaleWeilSheaf.transportCommIso
      (Scheme.Hom.geometricFiberBaseChangeIso hc) r
      (Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius
        hc r hr))).obj P)
    (hB : B.obj = (IsoAlgebra.mapOfNatIso (ProEtaleWeilSheaf.transportCommIso
      (Scheme.Hom.geometricFiberBaseChangeIso hc) r
      (Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius
        hc r hr))).obj Q)
    (t : C.finitePoints) :
    ∃ t' : C.finitePoints, c t'.1 = c t.1 ∧
      (C ↘ Spec (CommRingCat.of k₁)).residueCard t'.1 =
        (C ↘ Spec (CommRingCat.of k₁)).residueCard t.1 ∧
      Nonempty ((B.stalk t).Equiv (A.stalk t')) := by
  have _hrpos := hrpos
  have : Mono iQ.hom.f := (IsoAlgebra.forget _).map_mono iQ
  have hret := restrict_commuting_returns
    (ProEtaleWeilSheaf.frobeniusPowerCommIso j r) (V.obj.frobeniusPowIso r)
    (V.obj.frobeniusPowIso j) (ProEtaleWeilSheaf.frobeniusPowIso_comm V.obj j r)
    P Q iP.hom.f iQ.hom.f iP.hom.h iQ.hom.h e he
  obtain ⟨t', hct, hcard, hpoint⟩ :=
    Scheme.Hom.exists_frobenius_power_deck_point hc j t
  have hdegree : (C ↘ Spec (.of k₁)).degreeOver t'.1 =
      (C ↘ Spec (.of k₁)).degreeOver t.1 :=
    Nat.pow_right_injective (show 2 ≤ Nat.card k₁ from Finite.one_lt_card) hcard
  have hs := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (C ↘ Spec (.of k₁)) t
  rw [← hdegree] at hs
  have hs' := fixed_conjugate_power (Scheme.Hom.geometricFiberBaseChangeIso hc)
    (X ↘ Spec (.of k₀)).geometricGaloisFrobenius
    (C ↘ Spec (.of k₁)).geometricGaloisFrobenius r j
    (Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius hc r hr)
    _ _ _ hs
  obtain ⟨eBA⟩ := nonempty_stalk_equiv_of_equivariant_power_translate
    hc r hr P Q j e hret A B hA hB
    ((C ↘ Spec (.of k₁)).geometricFiberPointOfFinitePoint t)
    ((C ↘ Spec (.of k₁)).degreeOver t'.1) hs hs'
  obtain ⟨eAA⟩ := A.nonempty_equiv_stalkAt _ _
    (hpoint.trans (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base
      (C ↘ Spec (.of k₁)) t').symm)
    (by rw [hpoint]; exact t'.2) _ hs'
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
      (C ↘ Spec (.of k₁)) t')
  refine ⟨t', hct, hcard, ?_⟩
  simpa only [stalk, hdegree] using (Nonempty.intro (eBA.trans eAA))

end AlgebraicGeometry.WeilSheaf
