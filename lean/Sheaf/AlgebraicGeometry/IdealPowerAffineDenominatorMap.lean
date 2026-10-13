/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Affine denominator maps before annihilator quotient descent

Source: Stacks Project, Properties, Lemma 01PM, surjectivity calculation;
Lemma 01PQ, identification of affine annihilator modules.
(blueprint: lem-weil-pbc-ideal-power-affine-denominator-map).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The denominator construction gives an affine linear map modulo a submodule
of the specified annihilator, with the multiplication formula on affine sections.

Source: Stacks Project, Properties, Lemma 01PM, last four paragraphs; Lemma 01PQ,
first two paragraphs of the proof.
(blueprint: lem-weil-pbc-ideal-power-affine-denominator-map).

Proof: Put R = O_X(V), M = F(V), and identify the ideal with a finitely generated
ideal J of R. Its complement in V is U intersect V. Finite generation identifies
the sections of A_n on V with Ann_M(J^n): localization commutes with this
annihilator by clearing a denominator for each of finitely many generators.
The affine cokernel theorem identifies Q_n(V) with M/Ann_M(J^n).
The ideal powers are quasi-coherent by induction: the unit and I are
quasi-coherent, and tensor products and images preserve quasi-coherence.
Choose generators f_1,...,f_t. Express the section on D(f_i) as x_i/f_i^k,
with k positive. Equality on overlaps gives a common e killing all cross
relations after multiplication by (f_i f_j)^e. Replace x_i by f_i^e x_i and
k by k+e, so f_j^k x_i = f_i^k x_j. Put d=t(k-1)+1 and
K={x : f_i^k x=0 for every i}. Every degree-d monomial contains f_i^k.
Send it to the product with that factor removed, times x_i, modulo K.
Multiplication of the proposed image of any relation by each f_j^k is the
original relation times x_j, hence zero. The same calculation handles different
choices of index. This defines J^d -> M/K. The monomial bound shows
K <= Ann_M(J^d), hence hK. Its localization on D(f_i) is multiplication by
x_i/f_i^k. Thus the stated scalar identity holds first on these opens and
then on every W by sheaf separation. For J=0 use n=1, K=M, and the zero
map; U intersect V is empty. For J=R take n=0 and the section map. -/
theorem ideal_power_affine_denominator_map
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens)
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
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
    (V : X.affineOpens) (s : Γ(F, U)) :
    ∃ (n : ℕ) (K : Submodule Γ(X, V.1) Γ(F, V.1)),
      ((idealSheafPower ι n).1).IsQuasicoherent ∧
      K ≤ LinearMap.range ((a n).val.app (op V.1)).hom ∧
      ∃ f : Γ((idealSheafPower ι n).1, V.1) →ₗ[Γ(X, V.1)] (Γ(F, V.1) ⧸ K),
        ∀ (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V.1)
          (b : Γ((idealSheafPower ι n).1, V.1)) (x : Γ(F, V.1)),
          f b = K.mkQ x →
          (cokernel.π (a n)).app W (F.presheaf.map (homOfLE hWV).op x) =
            ((cokernel (a n)).smul (U := W) ((idealSheafPower ι n).2.val.app (op W)
              (((idealSheafPower ι n).1).presheaf.map (homOfLE hWV).op b))).hom
              ((cokernel.π (a n)).app W (F.presheaf.map (homOfLE hWU).op s)) := by sorry

end AlgebraicGeometry.Scheme
