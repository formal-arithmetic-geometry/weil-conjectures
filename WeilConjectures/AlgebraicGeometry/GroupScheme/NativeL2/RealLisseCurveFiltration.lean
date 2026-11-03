/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Curve construction and trace descent of a pure filtration

Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraphs 1--5,
including finite constant-extension trace descent. (blueprint: lem-zl-real-lisse-curve-filtration)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeL2

/-- On a positive-dimensional smooth geometrically connected affine model, curve tests
and finite constant-extension trace descent produce a finite pure filtration of the
original real lisse Weil module.

Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraphs 1--5.
(blueprint: lem-zl-real-lisse-curve-filtration)

Proof:
1. Apply the geometric-constituent filtration after one finite constant extension
 g : X'_0 -> X_0. Work over its enlarged constant field, with the corresponding
power of Frobenius. Pullback preserves reality because positive powers preserve
conjugation-stable spectra. The nonzero lisse quotients are geometrically irreducible.
2. Fix one closed point x_* on the smooth connected model. Each nonzero lisse
quotient has positive constant rank, so its fibre at this same point is nonzero.
For any closed point x, test through geometric points over x_* and x on a smooth
geometrically connected affine curve. Each quotient remains irreducible there.
Exact restriction makes it a constituent of the restricted real whole module, so
the real curve purity theorem applies. Reality of individual quotients is not assumed.
3. At the point over x_* the eigenvalues and residue cardinality are alpha^e and
q_{x_*}^e for the same positive degree e. Curve purity therefore fixes the weight
2 log_{q_{x_*}} |iota(alpha)|, independently of the curve. The same calculation at
x proves purity on the whole enlarged-field model. Retain the actual Weil filtration.
4. Push this filtration forward along the finite constant extension g. Finite
pushforward is exact and preserves the pure quotient weights. Etale-locally g is a
disjoint union of d = deg(g) copies; sum the projections to define Tr : g_*g^*M -> M.
Permutation invariance glues the sums and makes Tr Frobenius-equivariant. For the
diagonal adjunction unit eta, eta followed by Tr is d times the identity. Since d
is invertible in Q_l, Tr/d is a Weil-equivariant retraction. Mixed direct-summand
stability gives a filtration of M itself. Unpack that finite mixed filtration and
forget its common upper bound to obtain the stated pure quotients. The nonzero
hypothesis concerns only this lisse input; repeated filtration terms are allowed. -/
theorem real_lisse_curve_filtration
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hℓ : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [IsAffine X₀.left] [Smooth X₀.hom] [GeometricallyConnected X₀.hom]
    (hpos : 0 < topologicalKrullDim X₀.left)
    (M : WeilModule D l X₀)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (hlisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (hnonzero : ¬ IsZero M)
    (iota : PadicAlgCl l →+* ℂ)
    (hreal : NativeCondensedWeil.Real D l X₀ M iota) :
    ∃ (n : ℕ) (G : Fin (n + 1) → WeilModule D l X₀)
      (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ),
      (∀ i, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber X₀).left (G i).carrier) ∧
      IsZero (G 0) ∧ Nonempty (G (Fin.last n) ≅ M) ∧
      (∀ i, Mono (φ i)) ∧
      ∀ i : Fin n, ∃ v : ℝ, Pure D l X₀ (cokernel (φ i)) iota v := by
  sorry

end WeilConjectures.NativeL2
