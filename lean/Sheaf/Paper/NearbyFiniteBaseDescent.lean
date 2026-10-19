/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.Paper.OrgogozoInductionData
public import Sheaf.Paper.OrientedNearbyCycles
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.FiniteBaseCechComponents
import Sheaf.CategoryTheory.BoundedBelowCechConeComparison
import Sheaf.Paper.OrientedProductPointsConservative
import Sheaf.TraceFormula.FiniteBaseCechHypercohomology
import Sheaf.TraceFormula.FiniteCoverTubeComparison

/-!
# Finite surjective descent for nearby-cycle comparisons

Source: Orgogozo, *Modifications et cycles proches sur une base générale*, Lemma 2.6,
pp. 4--5 (blueprint: lem-trf-nearby-finite-base-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Orgogozo AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.Orgogozo

/-- Finite surjective descent of the universal truncated nearby-cycle comparison and of
full `Psi`-goodness.  The coefficient and bounded-constructible hypotheses are those of
`D^b_c(X_\mathrm{Et}, Λ)`, expressed through the transported oriented-site model.
Source: Orgogozo, Lemma 2.6, pp. 4--5 (blueprint: lem-trf-nearby-finite-base-descent).

Proof plan (the DAG proof, step by step, with its dependency references):
1. Fix `U → S`, `g : U' → U` and a geometric specialization `z'` of `V_{f_{U'}}`. Work with
constant-`Λ` module sheaves and the ordinary comparison `β_g` of
[def-trf-oriented-nearby-cycles]; [lem-trf-finite-cover-tube-comparison] identifies its stalk
with `u : RΓ(M, K_U) → RΓ(N, K_{U'})`. Choose `a` with `K ∈ D^{≥a}`; both tube complexes are
in `D^{≥a}`. By [lem-trf-oriented-product-points-conservative] it suffices to show
`H^i Cone(u) = 0` for `i ≤ r`.
2. Let `S₀ = U_{(f_U(x))}`, `U₀ = U'_{(f_{U'}(x'))}`, `P = T ×_S S₀`, `P_q = P^{×_{S₀}(q+1)}`,
`Q_q = U₀ ×_{S₀} P_q`. The tube lemma gives `A_q = RΓ(M ×_{S₀} P_q, K)` and
`B_q = RΓ(N ×_{U₀} Q_q, K)` with restriction maps and decomposition into local tubes of
`f_{P_q}`, `f_{Q_q}`. The covers are finite surjective by [lem-trf-finite-radicial-basechange]
and [lem-weil-pbc-surjective-base-change] ([def-pc-fibre-product]); they are Cech nerves.
3. [lem-trf-finite-base-cech-components] for `P_q → S₀` and `U₀ → S₀` makes `J_q → I_q`
bijective, compatibly with faces and degeneracies (projection-induced maps); the column map
`u_q : A_q → B_q` is the product of the ordinary comparison stalks for `Q_q → P_q`.
4. `P_q → T` (first projection) and `Q_q → P_q` are a preliminary and a further base change, so
`P_r(f_T, K_T)` kills each factor cone through degree `r`; finite products are componentwise, so
`H^j Cone(u_q) = 0` for `j ≤ r`.
5. `M ×_{S₀} P → M` is finite surjective; [lem-trf-finite-base-cech-hypercohomology] for it and
its pullback over `N` gives `RΓ(M, K) ≃ Tot(A_•)`, `RΓ(N, K) ≃ Tot(B_•)` and a commuting
augmentation square with top map `u`. [lem-trf-bounded-below-cech-cone-comparison] has
`E₁^{q,j} = H^j Cone(u_q)` (`q ≥ 0`, `j ≥ a - 1`); on a diagonal `n ≤ r` all terms vanish, and
finite convergence gives `H^n Cone(u) = 0` for `n ≤ r`.
6. As `U`, `g`, `z'` were arbitrary, exact stalks and conservativity give `P_r(f, K)`
([def-trf-orgogozo-induction-data]).
7. Ordinary comparisons compose: for `V' → V → T`, `β_{gh} = β_h ∘ v_h^* β_g` (counit
naturality and a triangle identity). If `(f_T, K_T)` is `Ψ`-good, every `β_h` is invertible, so
`P_r(f_T, K_T)` holds for all `r`; Steps 1--6 for all `r` make each comparison for `f` have an
acyclic cone, i.e. `(f, K)` is `Ψ`-good.
-/
theorem nearbyFiniteBaseDescent
    {X S T : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasInvertibleExponent Λ S]
    (K : EtaleDerived.{u, u + 1} X Λ)
    (hKb : IsBounded (etaleDatum.{u, u + 1} X)
      (Coeff.{u, u + 1} Λ) K)
    (hKc : ∀ q : ℤ,
      ∃ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ)),
        Scheme.IsConstructibleEtaleModuleSheaf F ∧
        Nonempty (
          (PresheafOfModules.forgetToPresheafModuleCat
            (op (⊤_ (EtaleSite.{u, u + 1} X))) terminalIsTerminal.op).obj
            ((PresheafOfModules.restrictScalars
              (Functor.whiskerRight
                (toSheafify (etaleTopology.{u, u + 1} X)
                  ((Functor.const (EtaleSite.{u, u + 1} X)ᵒᵖ).obj
                    (CommRingCat.of (Coeff.{u, u + 1} Λ))))
                (forget₂ CommRingCat RingCat))).obj
              ((DerivedCategory.homologyFunctor
                ((etaleDatum.{u, u + 1} X).modules
                  (Coeff.{u, u + 1} Λ)) q).obj K).val) ≅
          (AsSmall.down : EtaleSite.{u, u + 1} X ⥤ X.Etale).op ⋙ F.obj))
    (p : T ⟶ S) [IsFinite p] [Surjective p] (r : ℤ) :
    (UniversalTruncatedComparison (pullback.snd f p) Λ
        ⟨((etaleModules.{u, u + 1} (pullback.fst f p)).pull
            (Coeff.{u, u + 1} Λ)).obj K,
          ((etaleModules.{u, u + 1} (pullback.fst f p)).modulePull
            (Coeff.{u, u + 1} Λ)).bounded_mapDerivedCategory_obj hKb⟩ r →
      UniversalTruncatedComparison f Λ ⟨K, hKb⟩ r) ∧
    (IsPsiGood (pullback.snd f p) Λ
        (((etaleModules.{u, u + 1} (pullback.fst f p)).pull
          (Coeff.{u, u + 1} Λ)).obj K) →
      IsPsiGood f Λ K) := by
  sorry

end AlgebraicGeometry.Orgogozo
