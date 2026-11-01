/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassDiagonal
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.PowerSystemAcyclicResolution
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralUnitReduction
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystem

/-! # Derived reduction of the supported integral source -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Reduction of the supported integral source is its ordinary quotient, with
comparison normalized by the ordinary scalar-insertion unit.

Source: latest blueprint classes proof, clause (3), torsion-free supported source.
(blueprint: lem-sp-tower-class-supported-reduction-comparison).

Proof: the supported integer sheaf has injective multiplication by every positive
prime power, since constant integers do and direct image preserves monomorphisms.
The same holds termwise for its degree-zero constant tower. Regular complexes
form a resolving class for quotient reduction: the published acyclic resolution
supplies replacements and reduction preserves quasi-isomorphisms between regular
complexes by the cokernel short exact sequence of variable prime powers.
The universal derived counit is therefore invertible on this single complex.
Compose it with the standard single-complex comparison. Its transpose is the
ordinary scalar-insertion unit, by the representative transpose equation. -/
theorem supportedReduction_comparison (l : ℕ) [Fact l.Prime] (S : Scheme.{u})
    (r : Reduction (diagonalSurface S) (Rrings l (diagonalSurface S))) :
    let X := (constant (diagonalSurface S)).obj (diagonalIntegralSource S)
    ∃ a : r.derived.obj ((DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).obj X) ≅
        (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
          (Rrings l (diagonalSurface S))) 0).obj (r.ordinary.obj X),
      r.model.sourceNormalization a (r.model.adjunction.unit.app X) := by
  let T := diagonalSurface S
  let X := (constant T).obj (diagonalIntegralSource S)
  let regular : Set (CochainComplex (Ab T) ℤ) := fun P ↦
    ∀ (i : ℤ) (n : ℕ), Mono (l ^ (n + 1) • 𝟙 ((P.X i).obj (op n)))
  have hres (K : CochainComplex (Ab T) ℤ) :
      ∃ (P : CochainComplex (Ab T) ℤ) (q : P ⟶ K), regular P ∧ QuasiIso q := by
    obtain ⟨P, q, hq, hP, _⟩ := powerSystem_acyclic_resolution l T r K
    exact ⟨P, q, hP, hq⟩
  have hx : regular ((CochainComplex.singleFunctor (Ab T) 0).obj X) := by
    intro i n
    change Mono (l ^ (n + 1) • 𝟙
      ((((CochainComplex.singleFunctor (Ab T) 0).obj X).X i).obj (op n)))
    let hm : Mono (l ^ (n + 1) • 𝟙 X) := by
      let : ∀ k : ℕᵒᵖ, Mono ((l ^ (n + 1) • 𝟙 X).app k) :=
        fun _ ↦ source_mono l S n
      exact NatTrans.mono_of_mono_app _
    let hsingle : Mono (l ^ (n + 1) • 𝟙
        (((CochainComplex.singleFunctor (Ab T) 0).obj X).X i)) := by
      change Mono (l ^ (n + 1) • 𝟙
        (((HomologicalComplex.single (Ab T) (.up ℤ) 0).obj X).X i))
      exact single_scalar_mono (l ^ (n + 1)) X hm i
    let ev := (evaluation ℕᵒᵖ (DiagonalAb T)).obj (op n)
    have hmap := ev.map_mono (l ^ (n + 1) • 𝟙
      (((CochainComplex.singleFunctor (Ab T) 0).obj X).X i))
    simp only [Functor.map_nsmul, CategoryTheory.Functor.map_id] at hmap
    change Mono (l ^ (n + 1) • 𝟙
      ((((CochainComplex.singleFunctor (Ab T) 0).obj X).X i).obj (op n))) at hmap
    exact hmap
  have he : IsIso (r.model.epsilon.app
      ((CochainComplex.singleFunctor (Ab T) 0).obj X)) :=
    counit_computes_of_resolving r.model regular hres
      (fun f hP hQ hf ↦ reduction_preserves_regular_quasiIso l T r f hP hQ hf) _ hx
  obtain ⟨a, ha⟩ := normalize_single r.model (Iso.refl (r.ordinary.obj X)) he
  refine ⟨a, ?_⟩
  have hid : (r.model.adjunction.homEquiv X (r.ordinary.obj X))
      (Iso.refl (r.ordinary.obj X)).hom = r.model.adjunction.unit.app X := by
    rw [Iso.refl_hom, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  rw [hid] at ha
  exact ha

end AlgebraicGeometry.ProEtale.SpTowerClasses
