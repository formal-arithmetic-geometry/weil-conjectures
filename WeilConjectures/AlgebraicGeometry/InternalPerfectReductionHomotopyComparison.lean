/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectReductionHomEquiv
public import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryStepCounitChain
public import WeilConjectures.AlgebraicGeometry.InternalPerfectReductionCounitCoherence
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Actual derived reductions and ordinary homotopy endomorphisms -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option profiler true in
set_option maxHeartbeats 1000000 in
-- The balancing squares unfold the derived counits of successor extension.
/-- The canonical levelwise derived-to-homotopy comparisons commute with successor
scalar extension. The levelwise bijections themselves are already constructed and proved.
No scalar Hom cohomology or locally constant functions enter this assertion.

Source: Stacks Tags 06YY and 064B; blueprint Compatible isomorphisms.
(blueprint: lem-pe-internal-perfect-reduction-homotopy-comparison).

Proof: use the derived counit comparison fixed in internalPerfectReductionOrdinaryIso.
The ordinary and derived balancing isomorphisms are mates of the same restriction
compositor, including the equality of the composite quotient map with the direct
quotient. Write gamma_n for the canonical model isomorphism, alpha_n for derived
balancing, a_n for ordinary balancing, and epsilon_psi for the counit of successor
extension. After the specified quotient factorizations, the square is
alpha_n followed by gamma_n = L(psi)(gamma_(n+1)) followed by epsilon_psi followed
by Qh(a_n). The ordinary quotient complex is K-flat, so epsilon_psi is invertible.
The formulas for the derived adjunction unit on the homotopy quotient
identify the two mate squares after applying the restriction adjunction's hom
bijection. Its injectivity proves the balancing square on these K-flat models.
Naturality of the derived counit then identifies extension of a representative
chain map with ordinary extension of that chain map. Conjugating by the balancing
isomorphisms gives equality after localization. The K-projective localization
bijection is injective, so this proves the displayed equality in the homotopy
category. Every homotopy class has a chain-map representative. The same identities
apply for zero complexes and empty schemes, without a nonzero-basis assumption. -/
theorem internalPerfectReduction_homotopyComparison
    (X : Scheme.{u}) (W : X.ProEt) (_hAffine : IsAffine W.left)
    (_hweak : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) :
    ∀ (n : ℕ) (x : (internalReductionHomTower l E W.left
      (internalPerfectScalarModel l E W.left P)
      (internalPerfectScalarModel l E W.left P)).obj (op (n + 1))),
      internalPerfectReductionHomEquiv l E X W _hweak P a b _ha _hb _hfree n
        ((internalReductionHomTower l E W.left
          (internalPerfectScalarModel l E W.left P)
          (internalPerfectScalarModel l E W.left P)).map (homOfLE (Nat.le_succ n)).op x) =
      internalPerfectOrdinaryHomStep l E W.left P n
        (internalPerfectReductionHomEquiv l E X W _hweak P a b _ha _hb _hfree (n + 1) x) := by
  intro n x
  let F := Mod.extendScalars (AdicCompletion.transition l E W.left n)
  let T := internalPerfectScalarModel l E W.left P
  let α := AdicCompletion.reductionComp l E W.left n
  let γ := internalPerfectReductionOrdinaryIso l E W.left P a b _ha _hb _hfree
  let ε := F.leftDerivedFunctorCounit.app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (internalPerfectOrdinaryReduction l E W.left P (n + 1)))
  let H := HomotopyCategory.quotient
    (Mod (Sheaf (Scheme.ProEt.topology W.left) Ab.{u + 1})
      (AdicCompletion.finiteRing l E W.left n)) (.up ℤ)
  let a₀ := internalPerfectOrdinaryReductionStep l E W.left P n
  let δ := ε ≫ DerivedCategory.Qh.map (H.map a₀.hom)
  have hγ (k : ℕ) : (γ k).hom =
      (Mod.extendScalars (AdicCompletion.quotient l E W.left k)).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (internalPerfectIntegralComplex l E W.left P)) := by
    change (AdicCompletion.derivedReduction l E W.left k).map (𝟙 _) ≫ _ = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have hs : α.hom.app T ≫ (γ n).hom =
      F.leftDerivedFunctor.map (γ (n + 1)).hom ≫ δ := by
    simpa only [F, T, α, γ, ε, H, a₀, δ] using
      internalPerfectReduction_counit_coherence l E W.left P a b _ha _hb _hfree n
  let f := internalPerfectReductionHomEquiv l E X W _hweak P a b _ha _hb _hfree (n + 1) x
  let H₁ := HomotopyCategory.quotient
    (Mod (Sheaf (Scheme.ProEt.topology W.left) Ab.{u + 1})
      (AdicCompletion.finiteRing l E W.left (n + 1))) (.up ℤ)
  obtain ⟨g, hg⟩ := H₁.map_surjective f
  have hf : f = H₁.map g := hg.symm
  have hx : x ≫ (γ (n + 1)).hom = (γ (n + 1)).hom ≫ DerivedCategory.Qh.map f := by
    rw [internalPerfectReductionHomEquiv_localize]
    simp only [γ, Iso.hom_inv_id_assoc]
  have hn : F.leftDerivedFunctor.map (DerivedCategory.Qh.map f) ≫ δ =
      δ ≫ DerivedCategory.Qh.map (internalPerfectOrdinaryHomStep l E W.left P n f) := by
    rw [hf]
    rw [internalPerfectOrdinaryHomStep_map]
    simpa only [δ, ε, F, H, H₁, a₀, Category.assoc,
      Functor.mapHomotopyCategory_map, Functor.map_comp] using
      internalPerfectOrdinaryStepCounit_chain l E W.left P n g
  let := internalPerfectOrdinaryReduction_kprojective l E W.left
    (Scheme.ProEt.isWeaklyContractible_self_of_object X W _hweak) P b _hb _hfree n
  apply (CochainComplex.IsKProjective.Qh_map_bijective
    (internalPerfectOrdinaryReduction l E W.left P n) _).1
  rw [internalPerfectReductionHomEquiv_localize]
  simp only [internalReductionHomTower, CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ]
  change (γ n).inv ≫ (α.inv.app T ≫ F.leftDerivedFunctor.map x ≫ α.hom.app T) ≫
    (γ n).hom = DerivedCategory.Qh.map (internalPerfectOrdinaryHomStep l E W.left P n f)
  apply (cancel_epi (α.hom.app T ≫ (γ n).hom)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_app_assoc]
  rw [hs, reassoc_of% hs]
  rw [← F.leftDerivedFunctor.map_comp_assoc, hx, F.leftDerivedFunctor.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun z ↦ F.leftDerivedFunctor.map (γ (n + 1)).hom ≫ z) hn

end AlgebraicGeometry.ProEtale
