/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData

/-! # Epimorphy of the normalized symmetric Proj quotient

Source: Stacks Project, Constructions, Tags 01NR and 01OB.
(blueprint: lem-trf-symmetric-proj-normalized-quotient-epi).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomogeneousLocalization
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

/-- The adjoint of a section-normalized map to the degree-one twist is epic.
Source: Stacks, Tags 01OB and 01O4 (lemma-apply-relative).
(blueprint: lem-trf-symmetric-proj-normalized-quotient-epi).

Proof: the standard opens D_+(iota(m)) cover each affine symmetric Proj. Indeed, if a
homogeneous prime contained all iota(m), it would contain the positive-degree ideal,
contradicting the definition of Proj. On D_+(iota(m)), multiplication by iota(m)
trivializes the degree-one twist, with inverse division by iota(m). The assumed
normalization says that the adjoint quotient takes the actual pulled-back section
1 tensor m to this frame. Thus the quotient is surjective there: a target section
is uniquely a scalar times the frame and is lifted by that scalar times 1 tensor m.
Transport across the chart isomorphism and the tensor-pullback composition comparison.
These standard opens over all affine base opens cover the global relative Proj, so
local surjectivity proves the quotient is epic. The argument also covers zero and
nilpotent sections: their standard opens are empty. -/
theorem epi_of_symmetric_twist_sections
    {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    (L : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules)
    (chart : ∀ U : S.affineOpens,
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)).obj L ≅
          Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) 1)
    (σ : E ⟶ (Scheme.Modules.pushforward
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj L)
    (hσ :
    ∀ (U : S.affineOpens) (m : E.val.obj (op U.1))
      (hm : SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m ∈
        (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1),
    (chart U).hom.app
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
        (Scheme.Modules.tensorPullbackSection
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U) L
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
          (σ.app U.1 m)) =
      Scheme.Modules.Hom.app (Proj.unitToTwist
        (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) hm)
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
        (1 : Γ(Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U),
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)))) :
    Epi (((Scheme.Modules.tensorPullbackSectionAdjunction
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).homEquiv E L).symm σ) := by
  sorry

end AlgebraicGeometry.SymmetricProjTautologicalCharts
