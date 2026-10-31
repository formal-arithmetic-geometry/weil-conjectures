/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleSymmetricAlgebraIso
import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricGradedAlgebraIso
import WeilConjectures.AlgebraicGeometry.RelativeProj.GradedPullbackDataTransport
import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraPullbackData
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundlePullbackSectionNormalization

/-! # Coefficientwise base change for arbitrary normalized symmetric-algebra realizations

Source: Stacks Project, Constructions, Tags 01OB and 01O3.
(blueprint: lem-pur-projective-bundle-coefficient-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- The canonical symmetric-algebra base-change map transports to arbitrary normalized
realizations, with exactly their prescribed section-generator formula.
Source: Stacks Project, Tags 01OB and 01O3.
Proof: use the canonical coefficientwise pullback, conjugate by the realization section
isomorphisms and by the symmetric algebra of the module isomorphism. Transport preserves
coefficientwise base change and restrictions. Evaluation on degree-one generators is the
canonical pure-tensor formula, which agrees with the projective-bundle adjunction unit.
(blueprint: lem-pur-projective-bundle-coefficient-comparison). -/
theorem exists_projectiveBundleCoefficientComparison
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    [F.IsQuasicoherent] [F'.IsQuasicoherent]
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (A : B.SymmetricGradedAlgebraData F) (A' : B'.SymmetricGradedAlgebraData F') :
    ∃ b : Scheme.GradedAlgebraData.PullbackData g A.data A'.data,
      ∀ (U : B.affineOpens) (U' : B'.affineOpens) (h : U'.1 ≤ g ⁻¹ᵁ U.1)
        (x : F.val.obj (op U.1)),
      b.map h (A.sectionEquiv U (SymmetricAlgebra.ι _ _ x)) =
        A'.sectionEquiv U' (SymmetricAlgebra.ι _ _ (e.inv.app U'.1
          (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE h).op
            (projectiveBundlePullbackSection g x)))) := by
  let : ((Scheme.Modules.tensorPullback g).obj F).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent B'.ringCatSheaf).prop_of_iso e inferInstance
  obtain ⟨b, hb⟩ := SymmetricAlgebraSheaf.exists_normalized_pullbackData g F
  let a := (projectiveBundleSymmetricAlgebraIso A).symm
  let a' := SymmetricAlgebraSheaf.gradedAlgebraIso e.symm ≪≫
    projectiveBundleSymmetricAlgebraIso A'
  refine ⟨b.transport a a', ?_⟩
  intro U U' h x
  change A'.sectionEquiv U'
    ((SymmetricAlgebraSheaf.gradedAlgebraIso e.symm).hom.app U'
      (b.map h ((A.sectionEquiv U).symm (A.sectionEquiv U (SymmetricAlgebra.ι _ _ x))))) = _
  rw [AlgEquiv.symm_apply_apply, hb]
  refine (congrArg (A'.sectionEquiv U')
    (SymmetricAlgebraSheaf.gradedAlgebraIso_hom_app_ι e.symm U' _)).trans ?_
  exact congrArg (fun t ↦ A'.sectionEquiv U' (SymmetricAlgebra.ι _ _ (e.inv.app U'.1
    (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE h).op t))))
    (projectiveBundlePullbackSection_eq_tensorPullbackSection g x).symm

end AlgebraicGeometry
