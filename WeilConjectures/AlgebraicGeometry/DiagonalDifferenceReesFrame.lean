/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalDifferenceFrameData
import WeilConjectures.AlgebraicGeometry.DiagonalDifferenceNormalFrameConstruction
import WeilConjectures.AlgebraicGeometry.DiagonalDifferenceCentredChartConstruction
import WeilConjectures.AlgebraicGeometry.DiagonalDifferenceFrameChange
import WeilConjectures.AlgebraicGeometry.DiagonalDifferenceChartRestriction

/-! # Coordinate differences and the homogeneous normal frame
Source: current blueprint chart proof, Steps 1--3; Stacks Tags 0630--0635 and 08S2
(blueprint: lem-pur-diagonal-difference-rees-frame).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.DiagonalDifferenceReesFrame

/-- Coordinate differences give a centred Cartesian zero square, the positively normalized
conormal and homogeneous normal frame, and the etale Rees map with its specified endpoints.
No injectivity of the chart, no nonempty-source hypothesis and no positive-rank hypothesis
are imposed.
Source: current blueprint chart proof, Steps 1--3; Stacks 0634, 0635, 08S2
(blueprint: lem-pur-diagonal-difference-rees-frame).

Proof:
1. Base change the etale chart using the first projection. Translate the second coordinates
by minus the first coordinates. This constructs the difference map and proves it etale
(lem-weil-pbc-etale-scheme-base-change, lem-weil-pbc-etale-composition-cancellation).
2. Its zero fibre is affine and etale separated over U. The diagonal section is clopen
(lem-weil-pbc-etale-section-clopen-immersion). Remove its complementary closed component
from W. The resulting zero square is Cartesian as schemes, even for a noninjective chart.
3. In the polynomial zero-section ideal, monomials of degree m form the basis of J^m/J^(m+1).
Use lem-pur-conormal-algebra-flat-base-change and lem-pur-conormal-graded-algebra to obtain
the graded polynomial algebra in the classes of the differences on the whole diagonal.
4. The symmetric-algebra universal property and its quasi-coherent affine comparison
identify the actual canonical symmetricComparison with this graded polynomial isomorphism
(lem-weil-pbc-symmetric-algebra-universal-property,
lem-weil-pbc-quasi-coherent-symmetric-algebra-affine).
5. The normalized diagonal derivation is a -> [p2*a-p1*a]
(lem-sc-diagonal-conormal-derivation-exists). Its affine comparison is bijective
(lem-sc-diagonal-conormal-affine-comparison). Invert this sheaf map; the sign is positive,
and the ordered differences correspond to the pullbacks of dt_i.
6. Take relative spectra (lem-weil-pbc-affine-morphism-relative-spec). The augmentation
kills degree one, so zero sections agree. ReesConeNormalized sends [a]_1 to a/t mod t.
Existence is lem-pur-rees-cone-normalized-existence; comparison independence follows
from lem-pur-conormal-cone-hom-ext, since degree one generates the cone algebra.
7. On every ambient affine chart the deformation map is t -> t, v_i -> f_i/t.
The Cartesian zero square gives I=(f_i); the affine etale criterion and
lem-pur-dnc-etale-rees-chart prove etaleness. At one evaluation gives the difference map;
at zero lem-pur-rees-associated-graded-chart and its degree-one formula give N.normal.
8. Localization sends (a/r^n)/t to r^(-n)(a/t), so the same formulas agree on smaller
centred neighbourhoods and open restrictions. Common principal refinements are supplied
by lem-sc-affine-inter-principal-both. Changing chart changes degree one by the differential
frame matrix, and therefore changes normal coordinates by exactly that matrix. For d=0
the centred open is U, the conormal is zero and Sym(0)=O_U; all maps are identity data.
The empty scheme satisfies the same formulas without additional assumptions. -/
theorem diagonal_difference_rees_frame (k : Type u) [Field k]
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (aU : U ⟶ Spec (.of k)) (aV : V ⟶ Spec (.of k))
    [LocallyOfFiniteType aU] [LocallyOfFiniteType aV]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [SmoothOfRelativeDimension d h]
    (hk : h ≫ aV = aU)
    (c : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale c]
    (hc : c ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    ∃ N : NormalFrame d h (fun i ↦ c.appTop (AffineSpace.coord V i)),
      Nonempty (CentredChart d h (fun i ↦ c.appTop (AffineSpace.coord V i)) N) ∧
      (∀ (C C' : CentredChart d h (fun i ↦ c.appTop (AffineSpace.coord V i)) N)
        (T : (pullback h h).Opens) (ht : T ≤ C.O) (ht' : T ≤ C'.O),
        ((pullback.diagonal h).ker.deformationSpace).homOfLE
            ((pullback.diagonal h).ker.deformationSpaceProj.preimage_mono ht) ≫
              C.deformation =
          ((pullback.diagonal h).ker.deformationSpace).homOfLE
            ((pullback.diagonal h).ker.deformationSpaceProj.preimage_mono ht') ≫
              C'.deformation) ∧
      (∀ (c' : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale c']
        (_hc' : c' ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h)
        (N' : NormalFrame d h (fun i ↦ c'.appTop (AffineSpace.coord V i))),
        ∃ M H : Matrix (Fin d) (Fin d) Γ(U, ⊤),
          M * H = 1 ∧ H * M = 1 ∧
          (∀ j : Fin d,
            h.relativeDifferentialsDerivation.d (X := op ⊤)
                (c'.appTop (AffineSpace.coord V (ULift.up j))) =
              ∑ i : Fin d, M j i • h.relativeDifferentialsDerivation.d (X := op ⊤)
                (c.appTop (AffineSpace.coord V (ULift.up i)))) ∧
          (∀ j : Fin d,
            N'.normal.hom.appTop (AffineSpace.coord U (ULift.up j)) =
              ∑ i : Fin d,
                (PurityNormalBundle.projection (pullback.diagonal h)).appTop (M j i) *
                  N.normal.hom.appTop (AffineSpace.coord U (ULift.up i)))) := by
  obtain ⟨N⟩ := normal_frame_exists k aU aV d h hk c hc
  obtain ⟨C⟩ := centred_chart_exists k aU aV d h hk c hc N
  refine ⟨N, ⟨C⟩, ?_, ?_⟩
  · exact fun C C' T ht ht' => CentredChart.restrict_eq C C' T ht ht'
  · intro c' _ hc' N'
    exact frame_change N N'

end AlgebraicGeometry.DiagonalDifferenceReesFrame
