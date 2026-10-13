/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardChartsPullback
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardChartsNonvanishing
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardChartsAffine

/-!
# Standard charts and coordinate sections of projective space

Source: Stacks Project, Tags 01NG, 01MV, 01MS, 01ND, 01JR and 01I4
(blueprint: lem-weil-pbc-projective-space-standard-charts).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The standard opens cover projective space; coordinate sections freely generate the
pulled-back twisting module on each chart, satisfy the coordinate-ratio relation, and have
that chart as their nonvanishing locus. Over every affine base open the chart is affine,
with coordinate ring the polynomial ring in the other coordinates.
Source: Stacks Project, Tags 01NG, 01MV, 01MS, 01ND, 01JR and 01I4
(blueprint: lem-weil-pbc-projective-space-standard-charts).

Proof:
0. Identify the glued twisting module with the graded twisting module, preserving all T_k
   (lem-weil-pbc-projective-space-twist-glued-identification).
1. The coordinates generate the irrelevant ideal; their Proj opens cover. Pull back this
   cover along rho (prop-nagata-proj-standard-open).
2. Identify successive tensor pullbacks with pullback along rho composed with g, preserving
   pulled sections (lem-weil-pbc-invertible-pullback-tensor).
3. The value of a pulled section is its residue-field scalar extension; this is nonzero
   exactly when the original value is nonzero. Thus the nonvanishing locus is the chart
   preimage (lem-weil-pbc-projective-space-twisting-sheaf-charts).
4. Apply lem-weil-pbc-nonvanishing-section-trivializes: multiplication by T_i is bijective
   on sections over every smaller open.
5. Apply the O-linear adjunction unit to T_j = (T_j/T_i) T_i on the integral chart, then
   transport by the identifications in steps 0 and 2.
6. The intersection with the preimage of an affine base open is its fibre product with
   the integral chart (lem-weil-pbc-open-fibre-product).
7. This fibre product is Spec of the tensor product of the two coordinate rings
   (lem-weil-pbc-fibre-product-affine-spectra); polynomial scalar extension identifies it
   with R[U_j : j != i] (lem-weil-pbc-polynomial-scalar-extension).
8. Taking global sections gives an R-linear ring equivalence sending U_j to u_{j/i}.
   Its coefficient map is the restriction of q-sharp, so it is the specified R-algebra map.
-/
theorem projectiveSpace_standardCharts (n : Type u) (S : Scheme.{u})
    [Finite n] [Nonempty n] :
    (⨆ i : n, standardOpen n S i) = ⊤ ∧
    (∀ (Y : Scheme.{u}) (g : Y ⟶ ℙ(n; S)) (i j : n),
      ((Scheme.Modules.tensorPullback g).obj (twist n S 1)).IsInvertible ∧
      (∀ (V : Y.Opens), V ≤ g ⁻¹ᵁ standardOpen n S i →
        ∀ t : Γ((Scheme.Modules.tensorPullback g).obj (twist n S 1), V),
          ∃! a : Γ(Y, V), t = a •
            ((Scheme.Modules.tensorPullback g).obj (twist n S 1)).presheaf.map
              (homOfLE (le_top : V ≤ ⊤)).op 
                (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
                  (twist n S 1)).val.app (op ⊤) (twistOneSection n S i))) ∧
      ((Scheme.Modules.tensorPullback g).obj (twist n S 1)).presheaf.map
          (homOfLE (le_top : g ⁻¹ᵁ standardOpen n S i ≤ ⊤)).op 
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
              (twist n S 1)).val.app (op ⊤) (twistOneSection n S j)) =
        g.app (standardOpen n S i)
          ((toProjInt n S).app
            (Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i))
            (Proj.awayToSection _ _ (MvPolynomial.awayXRatio (ULift.{u} ℤ) i j))) •
          ((Scheme.Modules.tensorPullback g).obj (twist n S 1)).presheaf.map
            (homOfLE (le_top : g ⁻¹ᵁ standardOpen n S i ≤ ⊤)).op 
                (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
                  (twist n S 1)).val.app (op ⊤) (twistOneSection n S i))) ∧
    (∀ i : n, Scheme.Modules.nonvanishingLocus (twist n S 1) (twistOneSection n S i) =
          (standardOpen n S i : Set ℙ(n; S))) ∧
    ∀ (V : S.Opens) (R : CommRingCat.{u}) (eV : V.toScheme ≅ Spec R) (i : n),
      IsAffineOpen (standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V) ∧
      ∃ (h : (standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V).toScheme ⟶ V.toScheme)
        (E : MvPolynomial {j : n // j ≠ i} R ≃+*
          Γ(ℙ(n; S), standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V)),
        h ≫ V.ι = (standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V).ι ≫ (ℙ(n; S) ↘ S) ∧
        (∀ r : R, E (MvPolynomial.C r) =
          (standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V).topIso.hom
            ((h ≫ eV.hom).appTop ((Scheme.ΓSpecIso R).inv r))) ∧
        ∀ j : {j : n // j ≠ i}, E (MvPolynomial.X j) =
          (ℙ(n; S)).presheaf.map (homOfLE
            (inf_le_left : standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V ≤ standardOpen n S i)).op
          ((toProjInt n S).app
            (Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i))
            (Proj.awayToSection _ _ (MvPolynomial.awayXRatio (ULift.{u} ℤ) i j.1))) := by
  exact ⟨iSup_standardOpen n S, projectiveSpace_standardCharts_part1 n S,
    projectiveSpace_standardCharts_part2 n S, projectiveSpace_standardCharts_part3 n S⟩

end
end AlgebraicGeometry.ProjectiveSpace
