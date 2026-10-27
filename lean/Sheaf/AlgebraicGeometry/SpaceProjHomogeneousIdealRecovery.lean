/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.SpaceRelativeProjQuotientClosedImmersion
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.TraceFormula.ProjCommonDegreeTwistInvertible
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import WeilConjectures.AlgebraicGeometry.Modules.QcqsSections
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Recovery of closed subspaces of relative Proj by homogeneous ideals

Source: Stacks Project, spaces-divisors.tex, Tag 085L, lemma-closed-subscheme-proj,
using divisors.tex, Tag 0801 (blueprint: lem-sfb-space-proj-homogeneous-ideal-recovery).

The ideal is represented by the degreewise kernels of a homogeneous quotient map.
The quotient is a degreewise epimorphism of the existing graded algebra sheaves.
The final isomorphism commutes with the canonical quotient-induced closed immersion,
so it identifies closed subspaces with their full scheme structure.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every closed subspace of a quasi-compact relative Proj is cut out by a degreewise
quasi-coherent homogeneous ideal. Here I_n is `kernel (φ.degree n)`, included by
`kernel.ι`; the sectionwise product clause says A_m I_n is contained in I_(m+n).
Since every `φ.degree n` is epi, B is the quotient A/I in module sheaves, with
multiplication and unit descending along the homogeneous algebra homomorphism φ.
The systems C, R and Q are the existing normalized coefficient, Proj and quotient
realizations; their existence is supplied by the recorded dependency theorems.

Source: Stacks Project, spaces-divisors.tex, Tag 085L, lemma-closed-subscheme-proj;
divisors.tex, Tag 0801 (blueprint: lem-sfb-space-proj-homogeneous-ideal-recovery).

Proof:
1. On an affine etale chart, the scheme-test comparison identifies the projection with
   ordinary Proj. Absolute separatedness of Proj (lem-trf-proj-separated) and base change
   of closed immersions (lem-weil-pbc-closed-immersion-base-change) make this projection
   separated. Its sources are quasi-compact by hypothesis. Apply
   lem-trf-space-qc-separated-etale-local to conclude that p is quasi-compact separated.
2. The ideal/closed-subspace correspondence
   lem-sfb-space-ideal-closed-subspace-correspondence makes H = i_* O_Z the quotient of
   O_P by a quasi-coherent ideal. Its quasi-coherence follows from
   lem-sfb-space-qcoh-kernels-colimits. Use the twisting algebra E_n and maps psi_n of
   lem-sfb-space-relative-proj-graded-twists. Tensor with H and take adjuncts to obtain
   alpha_n : A_n to p_*(E_n tensor H), using def-trf-space-etale-module-functors.
   Products satisfy alpha_(m+n)(ab) = alpha_m(a) alpha_n(b). The pushforwards are
   quasi-coherent by lem-trf-space-qc-separated-quasi-coherent-pushforward. Their
   kernels I_n are quasi-coherent by lem-sfb-space-qcoh-kernels-colimits and stable
   under A multiplication by this product equation. The chart calculus
   lem-sfb-space-qcoh-affine-chart-calculus constructs the degreewise quotient B = A/I
   with its homogeneous operations and quotient epimorphism phi.
3. Restrict to an affine etale chart U of X. The chart diagrams defining direct image
   restrict to the diagrams over P times_X U, including evaluation maps and i_* O_Z.
   The twisting comparisons and
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence identify these with ordinary
   scheme twists. The affine chart calculus computes I(U) as the kernel of the map
   from C = direct sum A_n(U) to the sections of all nonnegative twists tensored with H.
   This uses only restriction to etale slices, not arbitrary nonflat base change.
4. If Proj C is nonempty, choose a finite positive-degree standard-open cover using
   quasi-compactness and def-pc-proj. Raise its generators f_j to powers of a common
   positive degree D. By lem-trf-proj-common-degree-twist-invertible, the twists O(kD)
   are invertible, with frame f_j^k on D_+(f_j). Let J_j be the kernel defining Z on
   this affine chart, in C_(f_j). Empty scheme tests require no comparison.
5. By lem-sfb-space-relative-proj-quotient-closed-immersion the quotient Proj maps
   canonically into Proj C. Its ideal on D_+(f_j) consists of fractions g/f_j^e with
   g in I_(eD): the localization zero criterion allows multiplication of a numerator
   by a further power of f_j (def-nagata-homogeneous-localization-degree-zero).
   Such fractions vanish in H by the definition of I and trivialization by f_j^e.
   Thus its chart ideal J'_j is contained in J_j, including nilpotent equations.
6. Conversely let g/f_0^e belong to J_0. On chart j, put a_j = f_0/f_j and let t_j
   be the image of g/f_j^e in H. It vanishes on D(a_j). Apply
   pqf-lem-qcoh-compact-section-power-torsion to obtain a_j^N_j t_j = 0. A single
   exponent N dominates the finitely many N_j. Then f_0^N g has zero coefficient
   on every chart in the frame f_j^(e+N), so vanishes globally in the twist tensored
   with H. Thus f_0^N g belongs to I_((e+N)D), and g/f_0^e belongs to J'_0.
   Repeat for every chart to get equality of the full ideals.
7. The scheme-test closed subschemes are therefore equal. An affine etale atlas pulls
   back to cover P by lem-trf-space-fibre-products-etale-covers. The ideal/closed-subspace
   correspondence identifies the two ideals on this cover; membership in a subsheaf
   is local, so they are equal globally. The resulting isomorphism commutes with the
   canonical quotient immersion Q.map. For Z empty one may take I = A; for Z = P,
   the canonical kernel may have irrelevant torsion, but the same chart argument works.
   No quasi-compactness or quasi-separatedness of X, finite presentation of i, finite
   generation, reducedness, nonzero ring or nonemptiness assumption is used. -/
theorem space_proj_homogeneousIdeal_recovery {S : Scheme.{u}}
    (C : SpaceProjCoefficients S) (R : SpaceProjSystem C)
    (Q : SpaceProjQuotientSystem C R) {X : AlgebraicSpace S} (A : SpaceProjInput X)
    (hqc : ∀ (W : Over S) (g : schemeSpace W ⟶ X), IsAffine W.left →
      CompactSpace (spaceProjScheme W (C.scheme A W g).affine).left)
    (Z : AlgebraicSpace S) (i : Z ⟶ (R.realization A).space)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom) :
    ∃ (B : SpaceProjInput X) (φ : EtaleGradedModuleAlgebra.Hom A.algebra B.algebra)
      (hφ : ∀ n : ℕ, Epi (φ.degree n)),
      (∀ n : ℕ, (kernel (φ.degree n)).IsQuasicoherent) ∧
      (∀ (m n : ℕ) (V : X.EtaleSite) (a : (A.piece m).val.obj (op V))
        (t : (kernel (φ.degree n)).val.obj (op V)),
        ∃ c : (kernel (φ.degree (m + n))).val.obj (op V),
          (kernel.ι (φ.degree (m + n))).val.app (op V) c =
            A.algebra.mul m n V a ((kernel.ι (φ.degree n)).val.app (op V) t)) ∧
      ∃ e : (R.realization B).space ≅ Z, e.hom ≫ i = Q.map φ hφ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
