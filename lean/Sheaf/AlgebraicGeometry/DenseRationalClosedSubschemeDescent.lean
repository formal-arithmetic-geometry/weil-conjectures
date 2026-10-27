/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.DensePoints
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Descent of a reduced closed subscheme with dense rational points

Source: Milne, Algebraic Groups (2017), Appendix A.24, A.28 and A.65, pp. 571–572,
580–581; the arbitrary-extension existence argument is the coefficient-basis argument
recorded in the DAG (blueprint: lem-sfb-dense-rational-closed-subscheme-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A reduced closed subscheme of `X_L` with dense base-changed `F`-rational points has
one reduced closed model in `X`. Closed subschemes are identified by their ideal sheaves:
`I.comap (pullback.fst ...) = i.ker` says that the model's base change is exactly `Z`,
including its scheme structure. The dense set is pulled back along the closed embedding
`i`, so density is in `Z` itself. Empty schemes and the empty set of points are allowed.

Source: Milne, Algebraic Groups (2017), Appendix A.24, A.28 and A.65, pp. 571–572,
580–581; arbitrary-extension existence by the DAG's coefficient-basis argument
(blueprint: lem-sfb-dense-rational-closed-subscheme-descent).

Proof:
1. Take the reduced induced closed subscheme of the closure of `S` in `X`, using
   lem-weil-pbc-reduced-induced-closed-subscheme. On an affine open `Spec A` its ideal is
   the intersection of the kernels of evaluations at the members of `S` in that open:
   vanishing on `S` implies vanishing on its closure, since nonvanishing is open
   (lem-weil-pbc-basic-open-function). Rational points give `F`-algebra evaluations.
2. By lem-weil-pbc-affine-chart-base-change-iso the base-changed chart is `Spec (L ⊗[F] A)`.
   Factorization makes its closed-subscheme ideal vanish at all the base-changed points.
   Conversely density makes any section vanishing on them nilpotent, and reducedness
   makes it zero (lem-weil-pbc-basic-open-function,
   lem-weil-pbc-zero-locus-eq-iff-radical-eq, lem-weil-pbc-affine-scheme-reduced-iff).
   Thus this ideal is the intersection of the base-changed evaluation kernels.
3. Apply lem-sfb-common-linear-kernel-field-extension and interchange tensor factors.
   The ideal is the `L`-linear span of `1 ⊗ I`, which is also its generated ideal:
   multiplication by pure tensors preserves this span since `I` is an ideal.
   The tensor operations are those of lem-weil-pbc-algebra-tensor-pushout-universal-property
   and def-weil-pbc-module-tensor-product.
4. By lem-pc-ideal-sheaf-comap-affine-extension these are exactly the ideals of the
   base-changed reduced closure. Equality on the affine cover gives equality of ideal
   sheaves (def-sbc-closed-immersion-ideal-sheaf), hence equality of closed subschemes by
   lem-weil-pbc-closed-immersions-equal-ideal-isomorphic.
5. For uniqueness, Spec L → Spec F is surjective (lem-pc-field-extension-surjective),
   and so is every base change (lem-weil-pbc-surjective-base-change). Two reduced models
   with the same base change therefore have the same support. Uniqueness in
   lem-weil-pbc-reduced-induced-closed-subscheme identifies them and their ideals.
   If `S` is empty, density makes `Z` empty and the reduced closure is empty;
   the corresponding empty intersections of ideals are the unit ideal. -/
theorem existsUnique_reduced_closedSubscheme_of_dense_rational_points
    (F L : Type u) [Field F] [Field L] [Algebra F L]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : Scheme.{u})
    (i : Z ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    [IsClosedImmersion i] [IsReduced Z] (S : Set (f.fieldPoints F))
    (hfactor : ∀ p ∈ S, ∃ q : Spec (CommRingCat.of L) ⟶ Z,
      q ≫ i = (f.baseChangeFieldPoint L p).1)
    (hdense : Dense (i ⁻¹' ((fun p : f.fieldPoints F ↦
      (f.baseChangeFieldPoint L p).1.base default) '' S))) :
    ∃! I : X.IdealSheafData, IsReduced I.subscheme ∧
      I.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F L)))) = i.ker := by
  sorry

end AlgebraicGeometry
