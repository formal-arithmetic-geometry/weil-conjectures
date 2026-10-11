/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
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

/-! # Limit presentation of an essentially finitely presented local tower
Source: literature/stacks-project/algebra.tex, proof of Lemma Tag 00R7
(blueprint: lem-weil-pbc-limit-tower-essentially-finite-presentation).
-/

@[expose] public section

universe u v p q

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace WeilConjectures

/-- Limit presentation of a tower `R → S → S'` of local rings, `S` and `S'` essentially of
finite presentation over `R`, with a finitely presented `S'`-module `M`. The colimits are
colimit cocones over the directed set `Λ` (in `CommRingCat` and `AddCommGrpCat`);
scalar-extension maps are specified on pure tensors, and the module tensors put the new
scalar ring first (tensor symmetry matches the source).

Source: Stacks Project, Algebra, proof of Tag 00R7, with the constructions of Tags 00QU,
00QV and 00QX
(blueprint: lem-weil-pbc-limit-tower-essentially-finite-presentation).

Proof:
1. (Base system.) Write `R` as a directed colimit of local rings `R_λ` essentially of
   finite type over `ℤ` with local transition maps and local maps `π_λ : R_λ → R`
   [lem-weil-pbc-local-ring-colimit-essentially-finite-type-over-z].
2. (Middle ring.) Apply [lem-weil-pbc-limit-module-essentially-finite-presentation-over-system]
   to this system, `T = S`, `τ = α` and the zero module: on a tail `Λ₁` get local `S_λ`,
   local `ρ_λ`, `s_{μλ}`, `κ_λ` with `S = colim S_λ`, `S_λ` essentially of finite type over
   `R_λ`, and the base changes `S_λ ⊗ R_μ → S_μ`, `S_λ ⊗ R → S` localizations.
3. `S'` is essentially of finite presentation over `S` via `β`
   [lem-weil-pbc-essentially-finite-presentation-over-intermediate].
4. (Top ring and module.) Apply the same node to `(S_λ)_{Λ₁}`, `T = S'`, `τ = β` and `M`:
   on a tail `Λ₂` get `S'_λ`, `σ_λ`, `s'_{μλ}`, `κ'_λ`, modules `M_λ` with semilinear maps,
   `S' = colim S'_λ`, `M = colim M_λ`, the `M_λ` cokernels of `t × s` matrices, and the
   localization and module base-change clauses.
5. (Restriction.) `Λ₂` is cofinal in `Λ` and in `Λ₁`, so `R` and `S` remain the colimits
   over `Λ₂` [lem-weil-pbc-colimit-initial-full-subcategory].
6. (Conclusion.) Index everything by `Λ₂`; clauses (1)–(5) are steps 2, 4 and 5.
-/
theorem limit_tower_essentially_finite_presentation
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    (α : R →+* S) (β : S →+* S') [IsLocalHom α] [IsLocalHom β]
    -- `S` is essentially of finite presentation over `R` via `α`
    (B : Type p) [CommRing B] [Algebra R B] [Algebra.FinitePresentation R B]
    (W : Submonoid B) (f : B →+* S) (hf : f.comp (algebraMap R B) = α)
    (hS : letI := f.toAlgebra; IsLocalization W S)
    -- `S'` is essentially of finite presentation over `R` via `β ∘ α`
    (B' : Type q) [CommRing B'] [Algebra R B'] [Algebra.FinitePresentation R B']
    (W' : Submonoid B') (f' : B' →+* S') (hf' : f'.comp (algebraMap R B') = β.comp α)
    (hS' : letI := f'.toAlgebra; IsLocalization W' S')
    -- `M` is a finitely presented `S'`-module
    (M : Type v) [AddCommGroup M] [Module S' M]
    (s t : ℕ) (H : (Fin s → S') →ₗ[S'] (Fin t → S'))
    (hM : Nonempty (((Fin t → S') ⧸ LinearMap.range H) ≃ₗ[S'] M)) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (A Bs C : Λ ⥤ CommRingCat.{u}) (ρ : A ⟶ Bs) (σ : Bs ⟶ C)
      (π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R))
      (κ : Bs ⟶ (Functor.const Λ).obj (CommRingCat.of S))
      (κ' : C ⟶ (Functor.const Λ).obj (CommRingCat.of S'))
      (D : Λ ⥤ AddCommGrpCat.{v})
      (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
      (_ : ∀ i : Λ, Module (C.obj i) (D.obj i)),
      -- local rings and local homomorphisms
      (∀ i, IsLocalRing (A.obj i)) ∧ (∀ i, IsLocalRing (Bs.obj i)) ∧
      (∀ i, IsLocalRing (C.obj i)) ∧
      (∀ i, IsLocalHom (ρ.app i).hom) ∧ (∀ i, IsLocalHom (σ.app i).hom) ∧
      (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (A.map (homOfLE h)).hom) ∧
      (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (Bs.map (homOfLE h)).hom) ∧
      (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (C.map (homOfLE h)).hom) ∧
      (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i))) ∧
      (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i))) ∧
      (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ'.app i))) ∧
      -- the maps to `R, S, S'` commute with `α, β`
      (∀ i, ρ.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom α) ∧
      (∀ i, σ.app i ≫ κ'.app i = κ.app i ≫ CommRingCat.ofHom β) ∧
      -- semilinearity of the module maps
      (∀ (i j : Λ) (h : i ≤ j) (y : C.obj i) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (C.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ i (y : C.obj i) (x : D.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ'.app i)) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) ∧
      -- (1) the colimits
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R) π)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S') κ')) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)) ∧
      -- (2) essential finite type
      (∀ i, (algebraMap ℤ (A.obj i)).EssFiniteType) ∧
      (∀ i, (ρ.app i).hom.EssFiniteType) ∧
      (∀ i, (σ.app i).hom.EssFiniteType) ∧
      -- (3) finite generation, indeed cokernels of `t × s` matrices
      (∀ i, Module.Finite (C.obj i) (D.obj i)) ∧
      (∀ i, ∃ H₀ : (Fin s → C.obj i) →ₗ[C.obj i] (Fin t → C.obj i),
        Nonempty (((Fin t → C.obj i) ⧸ LinearMap.range H₀) ≃ₗ[C.obj i] D.obj i)) ∧
      -- (4) transition base changes
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (ρ.app i).hom.toAlgebra
        letI := (A.map (homOfLE h)).hom.toAlgebra
        ∃ φ : Bs.obj i ⊗[A.obj i] A.obj j →+* Bs.obj j,
          (∀ (x : Bs.obj i) (y : A.obj j),
            φ (x ⊗ₜ[A.obj i] y) = (Bs.map (homOfLE h)).hom x * (ρ.app j).hom y) ∧
          (letI := φ.toAlgebra
           ∃ U : Submonoid (Bs.obj i ⊗[A.obj i] A.obj j), IsLocalization U (Bs.obj j))) ∧
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (σ.app i).hom.toAlgebra
        letI := (Bs.map (homOfLE h)).hom.toAlgebra
        ∃ φ : C.obj i ⊗[Bs.obj i] Bs.obj j →+* C.obj j,
          (∀ (x : C.obj i) (y : Bs.obj j),
            φ (x ⊗ₜ[Bs.obj i] y) = (C.map (homOfLE h)).hom x * (σ.app j).hom y) ∧
          (letI := φ.toAlgebra
           ∃ U : Submonoid (C.obj i ⊗[Bs.obj i] Bs.obj j), IsLocalization U (C.obj j))) ∧
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (C.map (homOfLE h)).hom.toAlgebra
        ∃ e : C.obj j ⊗[C.obj i] D.obj i ≃ₗ[C.obj j] D.obj j,
          ∀ (y : C.obj j) (x : D.obj i),
            e (y ⊗ₜ[C.obj i] x) = y • (D.map (homOfLE h)).hom x) ∧
      -- (5) base changes to the limit
      (∀ i,
        letI := (ρ.app i).hom.toAlgebra
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)).toAlgebra
        ∃ φ : Bs.obj i ⊗[A.obj i] R →+* S,
          (∀ (x : Bs.obj i) (y : R),
            φ (x ⊗ₜ[A.obj i] y) =
              (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) x * α y) ∧
          (letI := φ.toAlgebra
           ∃ U : Submonoid (Bs.obj i ⊗[A.obj i] R), IsLocalization U S)) ∧
      (∀ i,
        letI := (σ.app i).hom.toAlgebra
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)).toAlgebra
        ∃ φ : C.obj i ⊗[Bs.obj i] S →+* S',
          (∀ (x : C.obj i) (y : S),
            φ (x ⊗ₜ[Bs.obj i] y) =
              (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ'.app i)) x * β y) ∧
          (letI := φ.toAlgebra
           ∃ U : Submonoid (C.obj i ⊗[Bs.obj i] S), IsLocalization U S')) ∧
      (∀ i,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ'.app i)).toAlgebra
        ∃ e : S' ⊗[C.obj i] D.obj i ≃ₗ[S'] M,
          ∀ (y : S') (x : D.obj i),
            e (y ⊗ₜ[C.obj i] x) =
              y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) := by
  sorry

end WeilConjectures
