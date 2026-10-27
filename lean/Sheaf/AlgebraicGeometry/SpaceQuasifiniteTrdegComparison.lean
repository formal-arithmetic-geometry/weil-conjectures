/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.ZetaSeries
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import WeilConjectures.AlgebraicGeometry.FiniteDimensionalResidueFieldOfIsolatedFiberPoint
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Transcendence degrees in quasi-finite algebraic-space charts

Source: Stacks Project, Morphisms of Spaces, Tag 06RX, `lemma-compare-tr-deg`,
specialized to `E → Y → Spec k`, and the chart interpretation following
`definition-dimension-fibre` (blueprint: lem-sfb-space-quasifinite-trdeg-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- The residue transcendence degree of a point in any representable étale scheme chart
of `E` equals that of its image in `Y`, and is independent of the chart and its point.
The point `g(e)` is evaluated as `(yoneda.preimage (c ≫ g)).left w`: Yoneda identifies
the composite with a scheme map, and `schemePointMap c w = e` identifies its image.
All maps are over `k`, since the presheaves and Yoneda are on `Over (Spec k)`.
Source: Stacks Project, Tag 06RX, `lemma-compare-tr-deg`, and the explanation following
`definition-dimension-fibre` (blueprint: lem-sfb-space-quasifinite-trdeg-comparison).

Proof:
1. Fix the chart `c` and point `w`, and put `f = (yoneda.preimage (c ≫ g)).left`.
   The chartwise assumption gives `f.IsLocallyQuasiFinite` (pqf-def-quasifinite).
   Apply lem-weil-pbc-lqf-locally-finite-type to obtain local finite type, and evaluate
   the same assumption at `w` to obtain quasi-finiteness there. No atlas surjectivity
   is needed.
2. By lem-weil-pbc-quasi-finite-at-point-isolated the point `f.asFiber w` is isolated.
   Apply lem-weil-pbc-isolated-fibre-point-residue-finite to obtain that
   `κ(f(w)) → κ(w)` is finite.
3. Functoriality of stalk and residue maps (def-weil-residue-field) gives the compatible
   tower `k → κ(f(w)) → κ(w)` because `f` is over `k` (def-pc-field-extension).
   In a finite-dimensional extension the powers of each element are linearly dependent,
   giving a nonzero annihilating polynomial. Hence the extension is algebraic.
   Both clauses of lem-kun-transcendence-degree-tower give the cardinal equality
   `trdeg_k κ(w) = trdeg_k κ(f(w)) + 0 = trdeg_k κ(f(w))`.
4. Two chart points above `e` have the same image under `g`, so applying the first
   equality to both proves chart independence. A chart with no point over `e` gives
   no case to check. No quasi-compactness or separation is used. -/
theorem trdeg_eq_of_chartwise_isLocallyQuasiFinite
    {k : Type u} [Field k] (Y : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType Y.hom] (E : AlgebraicSpace (Spec (CommRingCat.of k)))
    (g : E.obj.obj ⟶ yoneda.obj Y)
    (hg : ∀ (W : Over (Spec (CommRingCat.of k))) (c : yoneda.obj W ⟶ E.obj.obj),
      IsEtale c → (yoneda.preimage (c ≫ g)).left.IsLocallyQuasiFinite)
    (e : Point E.obj.obj) (W : Over (Spec (CommRingCat.of k)))
    (c : yoneda.obj W ⟶ E.obj.obj) (hc : IsEtale c)
    (w : W.left) (hw : schemePointMap c w = e) :
    @Algebra.trdeg k (W.left.residueField w) _ _
        (W.hom.residueFieldAlgebraMap w).toAlgebra =
      @Algebra.trdeg k (Y.left.residueField ((yoneda.preimage (c ≫ g)).left w)) _ _
        (Y.hom.residueFieldAlgebraMap ((yoneda.preimage (c ≫ g)).left w)).toAlgebra ∧
    ∀ (W' : Over (Spec (CommRingCat.of k))) (c' : yoneda.obj W' ⟶ E.obj.obj),
      IsEtale c' → ∀ w' : W'.left, schemePointMap c' w' = e →
        @Algebra.trdeg k (W.left.residueField w) _ _
            (W.hom.residueFieldAlgebraMap w).toAlgebra =
          @Algebra.trdeg k (W'.left.residueField w') _ _
            (W'.hom.residueFieldAlgebraMap w').toAlgebra := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
