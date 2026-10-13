/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
/-! # Affine lifting into ideal-power annihilator quotients

Source: Stacks Project, Properties, Lemmas 01PM and 01PQ.
(blueprint: lem-weil-pbc-ideal-power-quotient-affine-lifting-section).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A section over the ideal complement has a lift on a single affine open.

Source: Stacks Project, Properties, Lemma 01PM (affine denominator construction)
and Lemma 01PQ (annihilator quotients).
(blueprint: lem-weil-pbc-ideal-power-quotient-affine-lifting-section).

Proof: Write V = Spec R, I|V = J~ with J finitely generated, and F|V = M~.
Finite generation of J^n identifies A_n|V with Ann_M(J^n)~: clearing a common
localization denominator for a finite set of generators proves this on principal
opens, and hann identifies the subsheaf. Thus Q_n|V = (M/Ann_M(J^n))~.
Choose J = (f_1,...,f_t). Its complement is the union of D(f_i). Represent s
there by x_i/f_i^k, with one positive k. Clear the finitely many overlap
relations with one exponent e, and replace x_i by f_i^e x_i and k by k+e,
so f_j^k x_i = f_i^k x_j in M. Put d = t*(k-1)+1 and
K = {x in M : f_i^k x = 0 for all i}. Every degree-d monomial contains f_i^k;
send it to the remaining monomial times x_i modulo K. For any relation,
multiplication of its image by f_j^k is the original relation times x_j,
hence zero. This proves independence of the chosen factor and of all relations,
giving a linear map J^d -> M/K. The same monomial bound gives
K <= Ann_M(J^d), so compose into M/Ann_M(J^d). On D(f_i), linearity gives
phi(f_i^d)/f_i^d = x_i/f_i^k; for t positive the bound d is at least k.
The affine tilde functor produces
the local sheaf morphism. The section one d maps to 1 under j_d, hence equals
the localized unit; naturality gives the displayed identity on every W.
For J=0 the complement is empty; use d=1 and the zero map. The empty affine
open is covered by this case. For J=R, degree zero and the section map work. -/
theorem ideal_power_quotient_affine_lifting_section
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (A : ℕ → X.Modules) (a : ∀ n : ℕ, A n ⟶ F)
    (hmono : ∀ n : ℕ, Mono (a n))
    (hqc : ∀ n : ℕ, (A n).IsQuasicoherent)
    (hann : ∀ (n : ℕ) (W : X.Opens) (s : Γ(F, W)),
      s ∈ Set.range ((a n).app W) ↔
        ∀ (W' : X.Opens) (h : W' ≤ W)
          (b : Γ((idealSheafPower ι n).1, W')),
          (F.smul (U := W') ((idealSheafPower ι n).2.val.app (op W') b)).hom
            (F.presheaf.map (homOfLE h).op s) = 0)
    (hquot : ∀ (n : ℕ) (W : X.Opens), W ≤ U →
      Function.Bijective ((cokernel.π (a n)).app W))
    (V : X.affineOpens) :
    ∀ s : Γ(F, U), ∃ (n : ℕ)
      (φ : ((idealSheafPower ι n).1).over V.1 ⟶ (cokernel (a n)).over V.1),
      ∀ (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V.1),
        (cokernel.π (a n)).app W (F.presheaf.map (homOfLE hWU).op s) =
          φ.val.app (op (Over.mk (homOfLE hWV)))
            (((idealSheafPower ι n).1).presheaf.map (homOfLE hWU).op (one n)) := by sorry

end AlgebraicGeometry.Scheme
