/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedWeilPointFlags.CondensedPointWeilFlagsStatement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Frontier gluing of real constructible Weil filtrations

Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraphs 6--9,
including the final finite trace descent.
(blueprint: lem-zl-real-mixed-frontier-filtration)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeL2

/-- Positive-dimensional lisse mixedness and point mixedness give a finite pure
filtration of an arbitrary real constructible module on its original model. The two
local assertions are independent inputs. The conclusion includes descent of the
common finite constant extension by its trace divided by its degree.

Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraphs 6--9.
(blueprint: lem-zl-real-mixed-frontier-filtration)

Proof:
1. Pass to the reduction. Refine a constructible lisse partition by a finite reduced
closed frontier chain whose layers are finite disjoint unions of smooth connected
affine pieces. In each component choose a dense smooth affine open inside the lisse
locus avoiding the other components; the closed complement has smaller dimension.
Noetherian induction terminates. Descend the finitely many subschemes and inclusions
to one finite constant extension large enough to define each geometric component.
2. Restrict the pulled-back module to each piece, over this enlarged finite field.
It remains constructible, lisse and real. Apply the supplied lisse assertion on each
positive-dimensional piece. For a point piece, use its finite-field model and the
supplied point assertion. Choose actual finite mixed filtrations on these pieces.
3. Extend each component filtration by zero and concatenate over its disjoint layer.
For an open j and closed complement i use the Weil-equivariant exact sequence
0 -> j_! j^* M -> M -> i_* i^* M -> 0. Both support extension functors are exact and
preserve purity, since the other stalks are zero. Lift the closed filtration by
inverse image under the quotient and prepend the open filtration. Its successive
quotients are the specified pure quotients and its terms remain constructible.
4. Induct upward along the finite chain. All inclusions are defined over the common
finite field, so the construction is Weil-equivariant for its Frobenius. Descend
this common constant extension g exactly as in the lisse case: exact finite
pushforward preserves pure weights; local summation defines a Frobenius-equivariant
trace with Tr composed with the diagonal unit equal to deg(g) times the identity.
Divide by deg(g) in Q_l and use mixed direct-summand stability. Unpack the resulting
finite mixed filtration on the original model and forget its upper bound. The empty
scheme and zero module have length-zero filtrations. -/
theorem real_mixed_frontier_filtration
    (l : ℕ) [Fact l.Prime] (iota : PadicAlgCl l →+* ℂ)
    (hlisse : ∀ (E : FiniteFieldDatum.{u}) (hℓ : l ≠ E.p)
      (Y₀ : Over (Spec (.of E.k₀))) [LocallyOfFiniteType Y₀.hom]
      [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
      [IsAffine Y₀.left] [Smooth Y₀.hom] [GeometricallyConnected Y₀.hom],
      0 < topologicalKrullDim Y₀.left → ∀ N : WeilModule E l Y₀,
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (E.geometricFiber Y₀).left N.carrier →
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) N.carrier →
      NativeCondensedWeil.Real E l Y₀ N iota → ∃ w : ℝ, Mixed E l Y₀ N iota w)
    (hpoint : ∀ (E : FiniteFieldDatum.{u}) (hℓ : l ≠ E.p)
      (N : WeilModule E l (CondensedWeilPointFlags.pointModel E)),
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (CondensedWeilPointFlags.pointSpace E) N.carrier →
      ∃ w : ℝ, Mixed E l (CondensedWeilPointFlags.pointModel E) N iota w)
    (D : FiniteFieldDatum.{u}) (hℓ : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (M : WeilModule D l X₀)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
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
