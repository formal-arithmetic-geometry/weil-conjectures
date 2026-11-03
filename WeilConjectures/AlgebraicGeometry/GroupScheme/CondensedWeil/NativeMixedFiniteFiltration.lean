/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights

/-! # Mixed weights on finite filtrations with subquotient graded pieces

Source: latest blueprint, lem-zl-sheaves-to-complexes.proof.md,
subquotient and extension bounds in the native condensed Weil heart.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeil

/-- A finite constructible Weil filtration whose graded pieces are constructible
subquotients of mixed objects of upper bound w has the same upper bound.
Source: latest blueprint, lem-zl-sheaves-to-complexes.proof.md, last paragraph;
lem-a1-subquotient-extension-bounds and lem-a1-extension-bounds, applied stalkwise
(blueprint: native-mixed-finite-filtration).

Proof: intersect each mixed filtration with the indicated subobject, then pass to its
images in the quotient. Exact geometric scalar sections identify the local Frobenius
operators with the restrictions and quotients of the original operator. At a closed
point the spaces are finite-dimensional, so eigenvalues of subobjects and quotients are
among those of the original pure piece. Thus each new piece retains its assigned pure
weight and upper bound. The coefficient heart is Serre, so all filtration terms remain
constructible. This proves mixedness of each graded piece. For a short exact extension,
concatenate the filtration of the subobject with inverse images of the filtration of
the quotient. The successive quotients are the old pure pieces with their old weights.
Start with the length-zero filtration of the zero object and induct along the given
finite filtration, using the mono-cokernel short exact sequences. Finally compose the
endpoint isomorphism with last; this witnesses Mixed for M.
The argument includes zero graded pieces and length zero. -/
theorem nativeMixed_finite_filtration
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact (Nat.Prime l)] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) (M : NativeL2.WeilModule D l X₀)
    (m : ℕ) (F : Fin (m + 1) → NativeL2.WeilModule D l X₀)
    (φ : ∀ i : Fin m, F i.castSucc ⟶ F i.succ)
    (hc : ∀ i, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left (F i).carrier)
    (hz : IsZero (F 0)) (last : F (Fin.last m) ≅ M) (hm : ∀ i, Mono (φ i))
    (hpieces : ∀ i : Fin m, ∃ E U : NativeL2.WeilModule D l X₀,
      ∃ (inc : U ⟶ E) (quo : U ⟶ cokernel (φ i)),
      Mono inc ∧ Epi quo ∧
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber X₀).left U.carrier ∧
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber X₀).left (cokernel (φ i)).carrier ∧
      NativeL2.Mixed D l X₀ E iota w) :
    NativeL2.Mixed D l X₀ M iota w := by
  sorry

end WeilConjectures.CondensedWeil
