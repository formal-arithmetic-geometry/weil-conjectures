/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralCoefficientPairingChange.GeneralEtalePairingChangeMaps

/-! # General finite coefficient change of an étale internal-adjunction pairing

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: lem-coef-general-etale-pairing-change).

The statement uses the canonical ordinary étale constructions of
`Sheaf.Paper.GeneralEtalePairingChangeMaps` (blueprint: def-coef-general-etale-pairing-maps):
the compact-support factorization, the ordinary direct-image comparison
`FiniteCoefficientOrdinary.directImageMaps.etale`, the evaluation comparison, and the
exceptional counit, over the fixed derived scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.GeneralCoefficientPairingChange

/-- Arbitrary finite coefficient change preserves the specified étale internal-adjunction
pairing.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: lem-coef-general-etale-pairing-change).

Proof. Put `T = R s_* Q`, `N' = s_B^! F_X M`, `Q' = H_B(F_S L, N')`, `w = H_B(1, b) u` and
`d = R s_{*,B}(w) c_{s,Q}`; write `μ` for the K-flat-normalized tensor comparison, `λ` for the
pullback/scalar comparison, `P_R` for the first pairing arrow and `h_A = ev_A (α_A ⊗ 1)`.
1. Use `c_g` on all derived objects as the counit-defined scalar mate and
   `q_s = R g_*(q_j) c_g` as a natural transformation; on the constructible inputs these are
   the comparisons of the statement.
2. Paste the direct scalar/projection square for `g` at `(V, j_! L)` with `R g_*` of the
   ordered open square for `j` at `(g^* V, L)`; scalar-mate naturality and the
   compactification pullback equation give
   `s_!(τ_V) q_s F_X(P_A(V, L)) μ_X = P_B(F_X V, F_S L)(1 ⊗ q_{s,L})`.
3. The defining transpose of `c_{s,Q}` and counit naturality give
   `α_{B,Q'} s_B^* d = w F_S α_A λ_T`.
4. The defining transpose of `u` and naturality of evaluation in `b` give
   `ev_B (w ⊗ 1) = b F_S ev_A μ_S(Q, L)`.
5. Substituting 3 and 4 and naturality of `μ_S` give `h_B (s_B^* d ⊗ 1) τ_T = b F_S h_A`.
6. The tensor--Hom transpose of the left side is `ε_B s_!(h_B) P_B(T', F_S L)(d ⊗ q_{s,L})`;
   naturality of `P_B`, Step 2 at `V = T` and Step 5 rewrite it as
   `ε_B s_!(b F_S h_A) q_s F_X P_A(T, L) μ_X`.
7. Naturality of `q_s` along `h_A` and the assumed counit equation `_hb` turn this into
   `F_X(ε_A s_!(h_A) P_A(T, L)) μ_X`, the scalar extension of the transpose of `I_A`.
8. By the defining transpose of `v` and naturality of `μ_X`, the right side has the same
   transpose; injectivity of the tensor--Hom hom equivalence gives the equality. No
   invertibility of `v` is used.
-/
theorem generalEtalePairingChange
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (_hell : IsUnit (ell : k))
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (_hA : ∃ r : ℕ, (ell ^ r : A) = 0)
    (_hB : ∃ r : ℕ, (ell ^ r : B) = 0)
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    {S Z : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (M : DerivedCategoryModule A X) (L : DerivedCategoryModule A S)
    (_hM : DerivedCategory.isBoundedConstructible A X M)
    (_hMtor : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b M)
    (_hL : DerivedCategory.isBoundedConstructible A S L)
    (_hLtor : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A S a b L)
    (_hN : DerivedCategory.isBoundedConstructible A S
      ((exceptional A g j).obj M))
    (_hNtor : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A S a b
      ((exceptional A g j).obj M))
    (_hQ : DerivedCategory.isBoundedConstructible A S
      (((derivedHom (ModuleCat A) S).obj (op L)).obj ((exceptional A g j).obj M)))
    (_hQtor : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A S a b
      (((derivedHom (ModuleCat A) S).obj (op L)).obj ((exceptional A g j).obj M)))
    (b : (scalarExtension φ S).obj ((exceptional A g j).obj M) ≅
      (exceptional B g j).obj ((scalarExtension φ X).obj M))
    (_hb : CounitCompatible φ g j M b) :
    PairingChangeEquation φ g j L M b := by
  sorry

end AlgebraicGeometry.Etale.GeneralCoefficientPairingChange
