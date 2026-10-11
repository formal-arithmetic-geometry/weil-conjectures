/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Sheaf.Algebra.Homology.MixedTotalTensor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.Linear
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Balanced K-flat models and the action of the second coefficient ring

Source: Stacks Project, More on Algebra, Section 06Y5 and Lemma 06Y6
(blueprint: lem-pc-balanced-derived-tensor-model).

The bifunctor `T` is characterized by the left-derived universal property in the `R`-complex
variable. Its value on `(M, R'[0])` is `M ⊗ᴸ_R R'` in `D(A)`. The unique model isomorphism is
specified by a compatibility equation with the resolution maps, rather than just by existence
of an unspecified isomorphism. Comparing any two models through this common value gives the
canonical comparison and its cocycle identity. The bifunctor and the naturality equation for
`α` express functoriality in `M`, including morphisms in `D(A)`.
-/

universe uB wA wR

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace DerivedCategory

variable (R A R' : Type uB) [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  [HasDerivedCategory.{wA} (ModuleCat.{uB} A)]
  [HasDerivedCategory.{wR} (ModuleCat.{uB} R)]

set_option quotPrecheck false in
local notation "S" => CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)
set_option quotPrecheck false in
local notation "E" => (S).obj (ModuleCat.of R R')
set_option quotPrecheck false in
local notation "B" => ModuleCat.mixedTotalTensor (algebraMap R A)

/-- (blueprint: lem-pc-balanced-derived-tensor-model) Balanced K-flat models of the tensor
of an `A`-module complex with the `R`-algebra `R'`, with canonical comparisons, functoriality,
and the commuting coefficient actions on cohomology. Source: Stacks Project, Lemma 06Y6.

Proof (the DAG's four steps):
1. The given quasi-isomorphisms are K-flat resolutions over `A` and `R`, respectively
   (`def-pc-kflat-complex`, `lem-pc-kflat-resolution`, ordinary-module specialization).
2. `lem-pc-derived-tensor-second-factor-functor` computes the derived tensor using the
   K-flat `R`-complex `F`. Tensoring `P → M` with `F` is a quasi-isomorphism; the signed
   symmetry interchanges the two tensor factors (`def-pc-tensor-complex-sheaves`). Thus the
   total tensor is the required model in `D(A)`. K-flatness over `A` is not confused with
   K-flatness over `R`.
3. Apply that functor to multiplication by `b : R'`. Composition, identity and addition
   give the ring homomorphism `ρ`. Naturality with multiplication by `a : A` gives commuting
   endomorphisms. The induced actions on each cohomology module agree on `R`, and the
   tensor-product universal property gives the displayed `A ⊗_R R'` action.
4. The universal property and the K-flat computation give canonical comparison maps;
   both models compare to the same derived object, so comparisons satisfy the cocycle
   identity. Naturality in both variables gives functoriality and compatibility of the
   actions (`lem-pc-derived-tensor-second-factor-functor`, clauses (2) and (3)). -/
theorem exists_balancedDerivedTensorModel :
    ∃ T : DerivedCategory (ModuleCat.{uB} A) ⥤
        DerivedCategory (ModuleCat.{uB} R) ⥤ DerivedCategory (ModuleCat.{uB} A),
      ∃ α : ∀ M : CochainComplex (ModuleCat.{uB} A) ℤ,
          Q ⋙ T.obj (Q.obj M) ⟶ (B).obj M ⋙ Q,
        (∀ M, (T.obj (Q.obj M)).IsLeftDerivedFunctor (α M)
          (HomologicalComplex.quasiIso (ModuleCat.{uB} R) (.up ℤ))) ∧
        (∀ M F, (HomologicalComplex.quasiIso (ModuleCat.{uB} R) (.up ℤ)).kFlat F →
          IsIso ((α M).app F)) ∧
        (∀ (M N : CochainComplex (ModuleCat.{uB} A) ℤ) (g : M ⟶ N)
            (F : CochainComplex (ModuleCat.{uB} R) ℤ),
          (T.map (Q.map g)).app (Q.obj F) ≫ (α N).app F =
            (α M).app F ≫ Q.map (((B).map g).app F)) ∧
        (∀ (M P : CochainComplex (ModuleCat.{uB} A) ℤ) (q : P ⟶ M),
          QuasiIso q → (HomologicalComplex.quasiIso (ModuleCat.{uB} A) (.up ℤ)).kFlat P →
          ∀ (F : CochainComplex (ModuleCat.{uB} R) ℤ) (f : F ⟶ E),
            QuasiIso f → (HomologicalComplex.quasiIso (ModuleCat.{uB} R) (.up ℤ)).kFlat F →
            ∃! e : Q.obj (((B).obj P).obj F) ≅ (T.obj (Q.obj M)).obj (Q.obj E),
              (α P).app F ≫ e.hom =
                (T.map (Q.map q)).app (Q.obj F) ≫ (T.obj (Q.obj M)).map (Q.map f)) ∧
        (∀ M : CochainComplex (ModuleCat.{uB} A) ℤ,
          ∃ ρ : R' →+* End ((T.obj (Q.obj M)).obj (Q.obj E)),
            (∀ b : R', ρ b = (T.obj (Q.obj M)).map
              (Q.map ((S).map (ModuleCat.ofHom (LinearMap.mulLeft R b))))) ∧
            (∀ (a : A) (b : R'),
              Commute (ρ b) ((T.map (Q.map (a • 𝟙 M))).app (Q.obj E))) ∧
            ∀ i : ℤ,
              let H := homologyFunctor (ModuleCat.{uB} A) i
              ∃ m : Module (A ⊗[R] R') (H.obj ((T.obj (Q.obj M)).obj (Q.obj E))),
                ∀ (a : A) (b : R') (x : H.obj ((T.obj (Q.obj M)).obj (Q.obj E))),
                  letI := m
                  (a ⊗ₜ[R] b) • x = a • (H.map (ρ b)).hom x) :=
  sorry

end DerivedCategory
