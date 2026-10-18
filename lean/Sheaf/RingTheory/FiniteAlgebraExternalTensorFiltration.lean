/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Data.ZMod.Basic

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.LittleWedderburn
import Sheaf.Paper.FiniteFieldDerivedTensorSummand

/-!
# External tensor filtrations over a finite algebra

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
Lemma 7.4.7, pp. 307--308, with Lambda = F_ell
(blueprint: lem-per-finite-algebra-external-tensor-filtration).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Module

/-- A finite module over `A ⊗[ZMod ℓ] B` has a finite filtration whose layers are retracts
of external tensors of finite A-modules with simple left B-modules. The existential scalar
structures on N and L are required to extend their A- and B-actions. The tensor action is
specified on all pure tensors, hence uniquely fixed by the displayed formula. The retraction
maps are linear for this action. For t = 0 the endpoints say that M is zero and there are no
layers. The witness modules are allowed in the common universe of A, B and M.

Source: ILO, Travaux de Gabber, Expose XVII, Lemma 7.4.7, pp. 307--308
(blueprint: lem-per-finite-algebra-external-tensor-filtration).

Proof:
1. Choose generators b_i of B over F_ell and m_j of M over A tensor B. The vectors
   (1 tensor b_i)m_j generate M over A. Quotients remain finite, and submodules remain
   finite by lem-weil-pbc-noetherian-submodule-finite. If M is zero use t = 0; this
   also handles zero A or zero B.
2. B is a finite set, hence left Artinian. By lem-per-artinian-radical-semisimple-quotient,
   its two-sided radical J is nilpotent and S = B/J is semisimple. The submodules J^r M
   give a finite descending filtration. Every layer Q_r is killed by J, and therefore
   has commuting A- and S-actions.
3. Apply lem-per-semisimple-algebra-matrix-division and
   lem-per-finite-division-ring-commutative: S is a finite product of matrix algebras
   Mat_d(E) over finite fields. Its central factor idempotents split each Q_r into the
   corresponding components Q. All these components are finite over A.
4. In one component put N = e_11 Q. Matrix units give inverse maps N^d to Q and Q to
   N^d, namely (n_i) to sum_i e_i1 n_i and q to (e_1i q)_i. They are A-linear and
   intertwine the matrix action. The B-module L = E^d with column action is simple:
   from a nonzero coordinate, matrix units and inverse scalars produce every basis vector.
5. The algebraic clause of lem-pur-finite-field-derived-tensor-summand supplies
   e = sum_j x_j tensor y_j in E tensor E with sum_j x_j y_j = 1 and
   (z tensor 1)e = (1 tensor z)e. The maps beta(n tensor z) = zn and
   sigma(n) = sum_j x_j n tensor y_j are A-linear and E-linear for the second-factor
   E-action, and beta sigma = id. The centralizing identity proves E-linearity of sigma.
6. Apply sigma and beta in each of the d coordinates and use the canonical isomorphism
   (N tensor E)^d = N tensor E^d. These maps commute with every matrix, so conjugating
   by the matrix-unit isomorphisms gives the required A tensor B-linear retraction
   of Q from N tensor L. The other factors and J act by zero on both sides.
7. Filter each Q_r by successive partial sums of its finitely many components and pull
   these filtrations back to J^r M. Concatenating them in reverse radical-power order
   gives an increasing filtration from zero to M. Each successive quotient is one of
   the components just treated. Zero components may be omitted; an empty semisimple
   product forces M = 0. The tensor action throughout is (a tensor b)(n tensor l)
   = an tensor bl, precisely the action in the statement. -/
theorem exists_finiteAlgebra_externalTensor_filtration
    (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod ℓ) A] [IsNoetherianRing A]
    (B : Type v) [Ring B] [Algebra (ZMod ℓ) B] [Module.Finite (ZMod ℓ) B]
    (M : Type w) [AddCommGroup M] [Module (A ⊗[ZMod ℓ] B) M]
    [Module.Finite (A ⊗[ZMod ℓ] B) M] :
    ∃ (t : ℕ) (F : Fin (t + 1) → Submodule (A ⊗[ZMod ℓ] B) M),
      F 0 = ⊥ ∧ F (Fin.last t) = ⊤ ∧ Monotone F ∧
      ∀ i : Fin t,
        ∃ (N : ModuleCat.{max u v w} A) (L : ModuleCat.{max u v w} B)
          (_ : Module (ZMod ℓ) N) (_ : Module (ZMod ℓ) L)
          (_ : IsScalarTower (ZMod ℓ) A N) (_ : IsScalarTower (ZMod ℓ) B L),
          Module.Finite A N ∧ IsSimpleModule B L ∧
          ∃ _ : Module (A ⊗[ZMod ℓ] B) (N ⊗[ZMod ℓ] L),
            (∀ (a : A) (b : B) (n : N) (l : L),
              (a ⊗ₜ[ZMod ℓ] b) • (n ⊗ₜ[ZMod ℓ] l) =
                (a • n) ⊗ₜ[ZMod ℓ] (b • l)) ∧
            ∃ (s : (↥(F i.succ) ⧸ (F i.castSucc).comap (F i.succ).subtype) →ₗ[A ⊗[ZMod ℓ] B]
                (N ⊗[ZMod ℓ] L))
              (p : (N ⊗[ZMod ℓ] L) →ₗ[A ⊗[ZMod ℓ] B]
                (↥(F i.succ) ⧸ (F i.castSucc).comap (F i.succ).subtype)),
              p.comp s = LinearMap.id := by
  sorry

end Module
