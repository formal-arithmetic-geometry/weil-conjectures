/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.AlgebraicGeometry.RelativeSectionAlgebraCanonicalMap
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange

/-! # Descent of the normalized relative section algebra

Source: Stacks Project, Morphisms, Tag 01VJ, (3) implies (5), section-algebra paragraph.
(blueprint: lem-trf-section-algebra-open-cover-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The section algebras given on an affine base cover determine a global section
algebra, together with coefficientwise pullback maps normalized on every section.
The section formula is the expanded `canonicalSectionOpenPull` formula; expanding it
here keeps the definitions in the gluing module and avoids a cyclic import.

Source: Stacks, Morphisms, Tag 01VJ, (3) implies (5), section-algebra paragraph;
Constructions, Tag 01O9(3).
(blueprint: lem-trf-section-algebra-open-cover-descent).

Proof: For each affine V in S take the externally graded ring whose degree n component
is Gamma(h inverse V, N tensor n). Multiplication is tensor multiplication of sections,
and the unit is the section 1 of the degree-zero structure module. Additivity, the
associativity, symmetry and unit identities of tensor powers give the graded ring
laws. Restriction of sections gives the ring restriction maps and their identities.
Each homogeneous sheaf h_*(N tensor n) restricts on U_i to the corresponding sheaf
for the restricted morphism: the normalized pullback unit is 1 tensor s, followed by
the tensor-power comparison. This gives the displayed section formula, including
n = 0. The given local section identifications identify these sheaves with the local
quasi-coherent homogeneous pieces. Quasi-coherence is local on the base, so all global
pieces are quasi-coherent. On affine inclusions their restriction maps consequently
exhibit scalar extension; thus the externally graded section rings form the existing
GradedAlgebraData. The identity maps on homogeneous sections give sectionEquiv and
its scalar, unit, multiplication and restriction laws. On an affine W of U_i mapping
into V, the same restriction formula defines a graded ring map into A_local i by
its inverse section identifications. It respects multiplication and the unit and is
coefficientwise base change by quasi-coherence. Restriction on either side commutes
with it because all maps are restrictions of the same sections. This is PullbackData
with exactly the required normalization. Empty schemes and empty covers cause no
exception: all section modules on the empty scheme are zero. -/
theorem exists_section_algebra_open_cover_descent {Z S : Scheme.{u}} (h : Z ⟶ S)
    [QuasiCompact h] [IsSeparated h] (N : Z.Modules) [N.IsInvertible]
    {I : Type v} (U : I → S.Opens) (hU : ∀ i : I, IsAffineOpen (U i))
    (hcover : iSup U = ⊤)
    (A_local : ∀ i : I, RelativeSectionAlgebra (h ∣_ U i)
      ((tensorPullback (h ⁻¹ᵁ U i).ι).obj N)) :
    ∃ A : RelativeSectionAlgebra h N, ∀ i : I,
      ∃ D : Scheme.GradedAlgebraData.PullbackData (U i).ι A.data (A_local i).data,
        ∀ (V : S.affineOpens) (W : (U i).toScheme.affineOpens)
          (hle : W.1 ≤ (U i).ι ⁻¹ᵁ V.1) (n : ℕ) (a : A.data.grading V n),
        (A_local i).sectionEquiv W n
            ⟨D.map hle a, (D.map hle).map_mem a.property⟩ =
          (((tensorPullback (h ⁻¹ᵁ U i).ι).obj N).tensorPow n).val.map
            (homOfLE (by
              intro x hx
              change h ((h ⁻¹ᵁ U i).ι x) ∈ V.1
              rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι]
              exact hle hx)).op
            ((boundaryPullbackPowIso (h ⁻¹ᵁ U i).ι N n).hom.app _
              (tensorPullbackSection (h ⁻¹ᵁ U i).ι (N.tensorPow n) (h ⁻¹ᵁ V.1)
                (A.sectionEquiv V n a))) := by sorry

end AlgebraicGeometry.Scheme.Modules
