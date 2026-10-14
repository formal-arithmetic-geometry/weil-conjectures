/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Small-universe module descent over an essentially finite type base system
Source: Stacks Project, Algebra, Tags 00QV, 00QX and 00R1.
(blueprint: lem-weil-pbc-limit-module-small-over-system)
-/

@[expose] public section

universe u v p

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingHom

/-- Single-ring descent with the module diagram in the universe of the limit module.
The extra essential finite type hypothesis permits shrinking the finite stage modules.

Source: Stacks Project, Algebra, Tags 00QV, 00QX and 00R1, with the universe transport
in the proof of `lem-weil-pbc-limit-tower-over-local-system`.
(blueprint: lem-weil-pbc-limit-module-small-over-system)

Proof: Lift N to ULift in universe max u v, carrying its additive group and T-module
structure along ULift.down. Compose the given cokernel equivalence with the inverse
linear equivalence of this lift. Apply
`exists_limit_module_essentially_finite_presentation_over_system` to the lifted module.
Keep its tail, stage rings, ring maps, localness, colimit and ring tensor comparisons.
Each stage ring is essentially of finite type over Z: compose the supplied base
essential finite type map with the descended structure map. An essentially finite
type algebra over a countable ring is countable: its finite set of essential generators
spans a countable polynomial quotient, and its localization consists of fractions
represented by pairs in that countable quotient. Each descended stage module is a
quotient of a finite power of this countable ring by its descended matrix range,
so it is countable and hence small in universe v.
Choose Shrink in universe v for each of these concrete stage modules, transporting
its additive group and module structure through equivShrink. Define each transition
by conjugating the original transition with the two equivalences. Define the cocone
components by the same conjugation at the source and ULift.down at the target.
The inverse equivalences show the identity and composition laws and naturality.
Transport the cokernel and tensor equivalences by these module equivalences;
semilinearity gives the induced tensor equivalences, and checking pure tensors
proves the displayed formulas. For the colimit universal property, lift a test cocone
in universe v to universe max u v, use the original IsColimit, and conjugate its
descending map back; the component equalities and uniqueness follow by the inverse
bijections. These operations preserve all returned clauses, including the component
identifications for the auxiliary maps. Empty Fin s or Fin t are included: their
finite powers and quotients are still countable, and no nonzero-rank assumption is used.
-/
theorem exists_limit_module_small_over_system
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ i : I, IsLocalRing (F.obj i)] [IsLocalRing c.pt]
    (hF : ∀ (i j : I) (h : i ≤ j), IsLocalHom (F.map (homOfLE h)).hom)
    (hFfinite : ∀ i, Algebra.EssFiniteType ℤ (F.obj i))
    (hcLocal : ∀ i : I, IsLocalHom (c.ι.app i).hom)
    (T : CommRingCat.{u}) [IsLocalRing T] (τ : c.pt →+* T) [IsLocalHom τ]
    (P : Type p) [CommRing P] [Algebra c.pt P] [Algebra.FinitePresentation c.pt P]
    (W : Submonoid P) (f : P →+* T)
    (hf : f.comp (algebraMap c.pt P) = τ)
    (hT : letI := f.toAlgebra; IsLocalization W T)
    (N : AddCommGrpCat.{v}) [Module T N]
    (s t : ℕ) (H : (Fin s → T) →ₗ[T] (Fin t → T))
    (hN : Nonempty (((Fin t → T) ⧸ LinearMap.range H) ≃ₗ[T] N)) :
    ∃ i₀ : I,
      ∃ (B : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u}) (β : B ⟶ (Functor.const _).obj T),
        Nonempty (IsColimit (Cocone.mk T β)) ∧
        ∃ (κ : ∀ i : {i : I // i₀ ≤ i}, B.obj i →+* T),
          (∀ i, ∀ x : B.obj i, κ i x = (β.app i).hom x) ∧
          (∀ i, IsLocalRing (B.obj i)) ∧ (∀ i, IsLocalHom (κ i)) ∧
          (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
            IsLocalHom (B.map (homOfLE h)).hom) ∧
          ∃ (τ₀ : ∀ i : {i : I // i₀ ≤ i}, F.obj i.1 →+* B.obj i),
            (∀ i, IsLocalHom (τ₀ i)) ∧ (∀ i, (τ₀ i).EssFiniteType) ∧
            (∀ i, (κ i).comp (τ₀ i) = τ.comp (c.ι.app i.1).hom) ∧
            (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
              (B.map (homOfLE h)).hom.comp (τ₀ i) =
                (τ₀ j).comp (F.map (homOfLE h)).hom) ∧
            ∃ (D : {i : I // i₀ ≤ i} ⥤ AddCommGrpCat.{v})
              (δ : D ⟶ (Functor.const _).obj N),
              Nonempty (IsColimit (Cocone.mk N δ)) ∧
              ∃ (ν : ∀ i : {i : I // i₀ ≤ i}, D.obj i →+ N)
                (_ : ∀ i : {i : I // i₀ ≤ i}, Module (B.obj i) (D.obj i)),
                (∀ i, ∀ x : D.obj i, ν i x = (δ.app i).hom x) ∧
                (∀ i, ∀ (y : B.obj i) (x : D.obj i), ν i (y • x) = κ i y • ν i x) ∧
                (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j)
                  (y : B.obj i) (x : D.obj i),
                  (D.map (homOfLE h)).hom (y • x) =
                    (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
                (∀ i, Module.Finite (B.obj i) (D.obj i)) ∧
                (∀ i, ∃ H₀ : (Fin s → B.obj i) →ₗ[B.obj i] (Fin t → B.obj i),
                  Nonempty (((Fin t → B.obj i) ⧸ LinearMap.range H₀) ≃ₗ[B.obj i] D.obj i)) ∧
                (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
                  letI := (τ₀ i).toAlgebra
                  letI := (F.map (homOfLE h)).hom.toAlgebra
                  (∃ φ : B.obj i ⊗[F.obj i.1] F.obj j.1 →+* B.obj j,
                    (∀ (x : B.obj i) (y : F.obj j.1),
                      φ (x ⊗ₜ[F.obj i.1] y) =
                        (B.map (homOfLE h)).hom x * τ₀ j y) ∧
                    (letI := φ.toAlgebra
                     ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] F.obj j.1),
                       IsLocalization U (B.obj j))) ∧
                  (letI := (B.map (homOfLE h)).hom.toAlgebra
                   ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
                     ∀ (y : B.obj j) (x : D.obj i),
                       e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x)) ∧
                (∀ i : {i : I // i₀ ≤ i},
                  letI := (τ₀ i).toAlgebra
                  letI : Algebra (F.obj i.1) c.pt := (c.ι.app i.1).hom.toAlgebra
                  (∃ φ : B.obj i ⊗[F.obj i.1] c.pt →+* T,
                    (∀ (x : B.obj i) (y : c.pt),
                      φ (x ⊗ₜ[F.obj i.1] y) = κ i x * τ y) ∧
                    (letI := φ.toAlgebra
                     ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] c.pt), IsLocalization U T)) ∧
                  (letI := (κ i).toAlgebra
                   ∃ e : T ⊗[B.obj i] D.obj i ≃ₗ[T] N,
                     ∀ (y : T) (x : D.obj i), e (y ⊗ₜ[B.obj i] x) = y • ν i x)) := by
  sorry

end RingHom
