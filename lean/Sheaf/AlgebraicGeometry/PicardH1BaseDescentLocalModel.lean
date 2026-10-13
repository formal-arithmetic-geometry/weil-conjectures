/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

import Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel
import Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison

/-! # Local scalar models and degree-one comparison for Picard descent

Source: Stacks Project, Tag 0BF2, the finite-free complexes and the representing chain maps.
(blueprint: lem-sc-picard-h1-base-descent-local-model)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 800000 in
-- Comparing the derived direct-image expressions and localized module instances is expensive.
/-- Construct the local finite-free model and its degree-one comparison square, without
assuming injectivity on H¹ and without realizing degree-zero cycles as sections.
Source: Stacks Project, Tag 0BF2, through the displayed chain maps, using Tags 0B91,
0BCD and 08CR. (blueprint: lem-sc-picard-h1-base-descent-local-model)

Proof: Apply picard_h1_common_minimal_model to choose a common affine U, target
trivializations, and a bounded finite-free source complex with its term-rank
isomorphisms, section bases, derived comparison, and vanishing residue differential.
Each term-rank isomorphism exhibits the term as a finite-free retract, proving strict
perfectness. For a negative degree the Betti number is zero, so the term is isomorphic
to the free module on the empty type; its identity is zero by freeHomEquiv.
Apply picard_h1_fixed_model_comparison to this fixed source complex and the supplied
target trivializations. It constructs q, b, alpha, beta and the cohomology square, and
asserts that b kills the image of the outgoing source differential. Define d to be
the coordinates of the differential on e0 inverse(1). Linearity of e0 inverse, the
module differential and e1 gives the formula for every scalar a. The residue equation
is the one supplied by the minimal-model theorem, and b(d)=0 is the annihilation
identity evaluated at 1. Assemble these witnesses. Empty free terms and the empty
target family are covered by the two intermediate statements without case exclusions. -/
theorem picard_h1_base_descent_local_model
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hOi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLi : ∀ i, ∃ (N : W.Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        (Modules.tensorPullback (pullback.snd (fi i) k)).obj N))
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N)) :
    ∃ (U : W.Opens) (hwU : w ∈ U), IsAffineOpen U ∧
      ∃ (m q : ℕ) (d : Fin m → Γ(W, U))
        (b : (Fin m → Γ(W, U)) →ₗ[Γ(W, U)] (Fin q → Γ(W, U)))
        (K : CochainComplex
          (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ),
        IsStrictlyPerfect W U K ∧ (∀ i : ℤ, i < 0 → IsZero (K.X i)) ∧
        ∃ (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
          (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U))),
          Nonempty ((SheafOfModules.overFunctor.{v}
            (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
              ((schemeDerivedDirectImage (pullback.snd f k)).obj
                ((DerivedCategory.singleFunctor
                  (SheafOfModules.{v}
                    (moduleRings (pullback f k).toRingedSpace)) 0).obj
                      ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
            DerivedCategory.Q.obj K) ∧
          (∀ a : Γ(W, U), e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a)) = a • d) ∧
          (∀ i, W.evaluation U w hwU (d i) = 0) ∧ b d = 0 ∧
          let p := RingHom.ker (W.evaluation U w hwU).hom
          letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
            ∃ (α : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+
                Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
              (β : (p.ResidueField ⊗[Γ(W, U)] (Fin q → Γ(W, U))) →+
                (∀ i, Sheaf.H
                  (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)),
              ∀ z, β ((b.baseChange p.ResidueField) z) = fun i ↦
                structureSheafCohomologyPullback
                  (((Over.pullback (S.fromSpecResidueField s)).map
                    (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                      (ui i) (hui i))).left) 1 (α z) := by
  obtain ⟨U, hwU, hU, htrivial, m, K, hbounded, hbetti, hrank, e0, e1, hE, hdw⟩ :=
    picard_h1_common_minimal_model f Xi fi ui hui hO hOi L W k w s hw hLi hLs
  have hK : IsStrictlyPerfect W U K := by
    refine ⟨hbounded, fun j ↦ ?_⟩
    obtain ⟨e⟩ := hrank j
    exact ⟨_, e.hom, e.inv, e.hom_inv_id⟩
  have hnegative : ∀ j : ℤ, j < 0 → IsZero (K.X j) := by
    intro j hj
    obtain ⟨e⟩ := hrank j
    rw [hbetti j hj] at e
    have hfree : IsZero (SheafOfModules.free
        (R := (moduleRings W.toRingedSpace).over U)
        (ULift.{v} (Fin 0))) := by
      rw [IsZero.iff_id_eq_zero]
      apply (SheafOfModules.freeHomEquiv _).injective
      ext i
      exact Fin.elim0 i.down
    exact hfree.of_iso e
  obtain ⟨q, b, hb, hcomparison⟩ :=
    picard_h1_fixed_model_comparison f Xi fi ui hui hO hOi L W k w s hw hLs
      U hwU hU htrivial m K hK hnegative hrank e0 e1 hE
  let d := e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm 1))
  refine ⟨U, hwU, hU, m, q, d, b, K, hK, hnegative, e0, e1, hE, ?_, hdw,
    hb 1, hcomparison⟩
  intro a
  have ha : e0.symm a = a • e0.symm 1 := by
    rw [← e0.symm.map_smul]
    simp
  rw [ha]
  rw [map_smul, e1.map_smul]

end AlgebraicGeometry.Scheme
