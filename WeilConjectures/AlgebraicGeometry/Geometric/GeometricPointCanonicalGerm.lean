/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalGerm
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk

/-!
# The canonical germ at the identity geometric point

Source: Stacks Project, Tags 04JQ, 04JN and 03Q1 (3).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- The canonical global germ on the spectrum of an algebraically closed field is invertible.
Source: Stacks Project, Tags 04JQ, 04JN and 03Q1 (3). -/
theorem isIso_globalGerm_identity (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    IsIso (globalGerm (𝟙 (Spec (.of Ω)))) := by
  let : IsSepClosed (IsLocalRing.ResidueField Ω) :=
    IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing Ω
  let : IsStrictlyHenselianLocalRing Ω :=
    (isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed Ω).2
      ⟨inferInstance, inferInstance⟩
  have h := Scheme.strictlyHenselianSections_geometricStalk_isIso.{u, u}
    (R := Ω) (hR := inferInstance) (s := 𝟙 (Spec (.of Ω)))
    (by exact Subsingleton.elim _ _)
  apply @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun F ↦ ?_)
  unfold globalGerm
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    GrothendieckTopology.Point.toPresheafFiberNatTrans_app]
  change IsIso ((Sheaf.ΓNatIsoSheafSections _ _
    (MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) _)).hom.app F ≫
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (Scheme.Etale.mk (𝟙 _))
        (Over.homMk (𝟙 _) (Category.comp_id _)) F.obj)
  have hi : IsIso ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
      (Scheme.Etale.mk (𝟙 _))
      (Over.homMk (𝟙 _) (Category.comp_id _)) F.obj) := h.1 F
  infer_instance

end AlgebraicGeometry.Etale
