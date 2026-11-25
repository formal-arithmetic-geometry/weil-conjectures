/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTower
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.Localization.Defs
import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberLocalization
import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberColimit

/-!
# Categorical presentation of the closed-fibre system

The closed fibres `S_i / m_i S_i`, `T_i / m_i T_i` and `N_i / m_i N_i` of a Noetherian local model
tower form a local Noetherian diagram whose colimit is the closed fibre of the limit.

## Implementation details

The transitions are obtained by quotienting the localization `fibreTransition` and the module
base change `moduleTransition` by `m_j`. The cocones are colimits: a quotient representative
mapping to zero is a finite sum of multiples of elements of `m_R`, which descends to a common
stage by locality and the eventual-equality fields of the tower.

## References

* [Stacks, Tag 00R7] (the paragraph beginning with the colimit of the maximal ideals)
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

/-- The closed-fibre quotients form a local Noetherian diagram with localization
transitions and module base-change transitions, and its colimit is the closed fibre.
There is no flatness assumption or flat-stage conclusion. -/
theorem NoetherianLocalModelTower.exists_fiber_diagram
    {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing S'] [IsLocalRing R] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
    [IsScalarTower S S' M]
    (X : NoetherianLocalModelTower R S S' M) :
    letI := X.preorder
    letI := X.commR
    letI := X.commS
    letI := X.localR
    letI := X.algRS
    letI := X.addN
    letI := X.moduleS
    ∃ (A B : X.ι ⥤ CommRingCat.{max u v w})
      (D : X.ι ⥤ AddCommGrpCat.{max u v w t})
      (act : ∀ i, Module (B.obj i) (D.obj i)),
    letI := act
    ∃ (φ : ∀ i, A.obj i →+* B.obj i)
      (ψ : (colimit A : CommRingCat.{max u v w}) →+*
        (colimit B : CommRingCat.{max u v w}))
      (limitAct : Module (colimit B : CommRingCat.{max u v w})
        (colimit D : AddCommGrpCat.{max u v w t})),
    letI := limitAct
    (∀ i, IsLocalRing (A.obj i)) ∧
    (∀ i, IsLocalRing (B.obj i)) ∧
    (∀ i, IsNoetherianRing (A.obj i)) ∧
    (∀ i, IsNoetherianRing (B.obj i)) ∧
    (∀ i, Module.Finite (B.obj i) (D.obj i)) ∧
    (∀ i, IsLocalHom (φ i)) ∧
    (∀ (i j : X.ι) (f : i ⟶ j), IsLocalHom (A.map f).hom) ∧
    (∀ (i j : X.ι) (f : i ⟶ j), IsLocalHom (B.map f).hom) ∧
    (∀ (i j : X.ι) (f : i ⟶ j),
      (B.map f).hom.comp (φ i) = (φ j).comp (A.map f).hom) ∧
    (∀ (i j : X.ι) (f : i ⟶ j) (b : B.obj i) (x : D.obj i),
      (D.map f).hom (b • x) = (B.map f).hom b • (D.map f).hom x) ∧
    (∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i)) ∧
    (∀ (i : X.ι) (b : B.obj i) (x : D.obj i),
      (colimit.ι D i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι D i).hom x) ∧
    (∀ (i j : X.ι) (f : i ⟶ j),
      letI := (φ i).toAlgebra
      letI := (A.map f).hom.toAlgebra
      ∃ (q : B.obj i ⊗[A.obj i] A.obj j →+* B.obj j)
        (U : Submonoid (B.obj i ⊗[A.obj i] A.obj j)),
        (∀ (b : B.obj i) (a : A.obj j),
          q (b ⊗ₜ[A.obj i] a) = (B.map f).hom b * φ j a) ∧
        (letI := q.toAlgebra; IsLocalization U (B.obj j))) ∧
    (∀ (i j : X.ι) (f : i ⟶ j),
      letI := (B.map f).hom.toAlgebra
      ∃ e : (B.obj j ⊗[B.obj i] D.obj i) ≃ₗ[B.obj j] D.obj j,
        ∀ (b : B.obj j) (x : D.obj i),
          e (b ⊗ₜ[B.obj i] x) = b • (D.map f).hom x) ∧
    (∀ i, ∃
      (eA : A.obj i ≃+*
        (X.S₀ i ⧸ Ideal.map (algebraMap (X.R₀ i) (X.S₀ i))
          (IsLocalRing.maximalIdeal (X.R₀ i))))
      (eD : D.obj i ≃+
        ((X.S₀ i ⧸ Ideal.map (algebraMap (X.R₀ i) (X.S₀ i))
          (IsLocalRing.maximalIdeal (X.R₀ i))) ⊗[X.S₀ i] X.N₀ i)),
      letI := Module.compHom (D.obj i) (φ i)
      ∀ a x, eD (a • x) = eA a • eD x) ∧
    (∃
      (eA : (colimit A : CommRingCat.{max u v w}) ≃+*
        (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)))
      (eD : (colimit D : AddCommGrpCat.{max u v w t}) ≃+
        ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M)),
      letI := Module.compHom (colimit D : AddCommGrpCat.{max u v w t}) ψ
      ∀ a x, eD (a • x) = eA a • eD x) := by
  let := X.preorder
  let := X.commR
  let := X.commS
  let := X.localR
  let := X.algRS
  let := X.addN
  let := X.moduleS
  let := X.fiberAct
  have hloc := X.fiber_localization
  obtain ⟨limitAct, ⟨hsem, hlim⟩, _⟩ := X.fiber_colimit
  refine ⟨X.fiberA, X.fiberB, X.fiberD, X.fiberAct,
    X.fiberφ, X.fiberψ, limitAct, X.fiberA_local, X.fiberB_local,
    X.fiberA_noetherian, X.fiberB_noetherian, X.fiberD_finite,
    X.fiberφ_local, X.fiberA_map_local, X.fiberB_map_local,
    X.fiber_square, X.fiberD_map_smul, X.fiberψ_comp_ι,
    hsem, hloc, X.fiber_module_baseChange, ?_, hlim⟩
  intro i
  exact ⟨RingEquiv.refl _, X.fiberDEquiv i, X.fiberDEquiv_smul i⟩

end Module
