/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.TorusProjectiveWeightData
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts

/-! # The extremal weight affine attraction chart

Source: Milne, Algebraic Groups (2017), Theorem 12.12, pp.234--235,
Lemma 13.51 and Propositions 13.52--13.53(a), pp.274--276,
and the coordinate paragraph in the proof of Theorem 17.65, p.374.
(blueprint: lem-sfb-torus-extreme-weight-affine-chart).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

open TorusProjectiveWeight

/-- The minimum-weight line determines the affine open consisting of precisely the
rational points whose torus orbit closure contains that line. The projective space
uses the arbitrary basis b of E; it parametrizes lines. Finite, reduced and nonempty
F over the algebraically closed field is exactly a nonempty finite disjoint union
of reduced k-points. The fixed-functor hypothesis tests every algebra extension.

Source: Milne, Algebraic Groups (2017), Lemma 13.51 and Propositions 13.52--13.53(a),
pp.274--276, and proof of Theorem 17.65, p.374.
(blueprint: lem-sfb-torus-extreme-weight-affine-chart).

Proof:
1. The weight decomposition (lem-sfb-split-torus-representation-weight-decomposition)
   and the Laurent monomial description of characters give a separating cocharacter
   by lem-sfb-projective-torus-fixed-weight-schemes. For any such cocharacter the
   projective fixed schemes agree. Smoothness gives regularity and local Noetherianity
   by lem-weil-pbc-smooth-scheme-over-field-regular. Connectedness then gives integrality
   by lem-sc-regular-connected-integral, hence irreducibility of X.
2. On the nonzero least-weight-projection locus W, project the tautological line to
   the least-weight space. In a weight basis, multiply coordinate ratios by
   t^(m_c-m_min). The exponents are nonnegative. The standard charts of
   lem-weil-pbc-projective-space-standard-charts give the polynomial morphism.
   Its restriction to t invertible is the action and lies in X. The ideal of X
   therefore vanishes in B[t,t^-1], hence in B[t], whose localization map is injective
   even with zero divisors. Thus the limit map factors through X and through F,
   since every line in a single character space is fixed after all extensions.
3. Spanning makes W nonempty. Its irreducibility makes its image in finite discrete F
   one point x0. Every projected rational line lies in i(x0). Project the spanning
   equality to the least-weight space to conclude that this space is this single
   line and has dimension one. The closed immersion gives uniqueness of x0.
4. For nonzero e0 in that line, the direct sum gives the unique dual form f0 with
   f0(e0)=1 and zero on the other summands. In an adapted basis this is the least
   homogeneous coordinate. Its nonvanishing chart is affine by the standard-chart
   lemma; intersecting with the closed subscheme X remains affine by
   def-weil-closed-immersion. This is exactly the inverse image of dualOpen b f0.
5. For y in the chart normalize its least component to e0. The polynomial curve
   [e0 + sum t^(m_c-m_min) v_c] limits to x0 and equals ell(t)y for t invertible.
   The infinite algebraically closed field makes k^times dense in A^1, hence x0
   belongs to the closure of the torus orbit of y. Outside the chart, the orbit
   stays in the closed complementary weight hyperplane, which excludes x0.
   Thus the rational-point sets agree. With rank zero the same argument has one
   weight and allows the trivial cocharacter, including X=Spec k and dim E=1. -/
theorem torus_extreme_weight_affine_chart
    (k : Type u) [Field k] [IsAlgClosed k]
    (E : Type v) [AddCommGroup E] [Module k E] [FiniteDimensional k E] [Nontrivial E]
    (I : Type u) [Fintype I] [DecidableEq I] (b : Module.Basis I k E)
    (T : Grp (Over (Spec (.of k)))) (r : ℕ)
    (_hT : Nonempty (T ≅ MultiplicativeType.splitTorus k r))
    (ρ : T.X ⟶ GeneralLinearGroup I k) [IsMonHom ρ]
    [pact : ModObj T.X (Over.mk (ProjectiveSpace I (Spec (.of k)) ↘ Spec (.of k)))]
    (_hinduced : IsInduced T ρ)
    (X : Over (Spec (.of k))) [Smooth X.hom] [ConnectedSpace X.left]
    [IsProjective X.hom] [xact : ModObj T.X X]
    (i : X ⟶ Over.mk (ProjectiveSpace I (Spec (.of k)) ↘ Spec (.of k)))
    [IsClosedImmersion i.left]
    (_hequiv : xact.smul ≫ i = (T.X ◁ i) ≫ pact.smul)
    (_hspan : Submodule.span k {e : E | ∃ y : StandardGroupSchemes.affine k k ⟶ X,
      Represents (CommAlgCat.of k k) (y ≫ i) (fun j ↦ b.repr e j)} = ⊤)
    (F : Over (Spec (.of k))) [IsFinite F.hom] [IsReduced F.left] [Nonempty F.left]
    (j : F ⟶ X) [IsClosedImmersion j.left]
    (_hfixed : ∀ (A : CommAlgCat.{u} k) (x : StandardGroupSchemes.affine k A ⟶ X),
      (∃ z : StandardGroupSchemes.affine k A ⟶ F, z ≫ j = x) ↔
        ∀ (B : CommAlgCat.{u} k) (f : A ⟶ B)
          (t : StandardGroupSchemes.affine k B ⟶ T.X),
          t • (StandardGroupSchemes.map k f.hom ≫ x) = StandardGroupSchemes.map k f.hom ≫ x)
    (Ω : Type w) [Finite Ω] [DecidableEq Ω] (χ : Ω → RankOneRoots.Character T)
    (_hχ : Function.Injective χ) (W : Ω → Submodule k E)
    (_hnonzero : ∀ c : Ω, W c ≠ ⊥) (_hdirect : DirectSum.IsInternal W)
    (_hweights : ∀ (c : Ω) (e : E), e ∈ W c ↔ IsWeightVector b T ρ (χ c) e) :
    (∃ (ell : RankOneRoots.Cocharacter T) (m : Ω → ℤ), Separates T χ ell m) ∧
    ∀ (ell : RankOneRoots.Cocharacter T) (m : Ω → ℤ), Separates T χ ell m →
      ∃ c₀ : Ω, (∀ c : Ω, c ≠ c₀ → m c₀ < m c) ∧ Module.finrank k (W c₀) = 1 ∧
        (∃! x₀ : StandardGroupSchemes.affine k k ⟶ F,
          ∀ e₀ : E, e₀ ∈ W c₀ → e₀ ≠ 0 →
            Represents (CommAlgCat.of k k) (x₀ ≫ j ≫ i) (fun a ↦ b.repr e₀ a)) ∧
        ∀ x₀ : StandardGroupSchemes.affine k k ⟶ F,
          (∀ e₀ : E, e₀ ∈ W c₀ → e₀ ≠ 0 →
            Represents (CommAlgCat.of k k) (x₀ ≫ j ≫ i) (fun a ↦ b.repr e₀ a)) →
          ∀ e₀ : E, e₀ ∈ W c₀ → e₀ ≠ 0 →
            ∃ f₀ : Module.Dual k E, f₀ e₀ = 1 ∧
              (∀ c : Ω, c ≠ c₀ → ∀ e ∈ W c, f₀ e = 0) ∧
              ∀ f : Module.Dual k E, f e₀ = 1 →
                (∀ c : Ω, c ≠ c₀ → ∀ e ∈ W c, f e = 0) →
                IsAffineOpen (i.left ⁻¹ᵁ dualOpen b f) ∧
                {y : StandardGroupSchemes.affine k k ⟶ X |
                  y.left (IsLocalRing.closedPoint k) ∈ i.left ⁻¹ᵁ dualOpen b f} =
                {y : StandardGroupSchemes.affine k k ⟶ X |
                  (x₀ ≫ j).left (IsLocalRing.closedPoint k) ∈
                    closure (Set.range fun t : StandardGroupSchemes.affine k k ⟶ T.X ↦
                      (t • y).left (IsLocalRing.closedPoint k))} := by
  sorry

end AlgebraicGeometry
