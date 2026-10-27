/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension

/-!
# Étale prelog restriction and the strict-local ring comparison

Source: ILO VI 1.1--1.2, 1.6; VIII 3.3.8; Stacks, Tags 00Y0 and 03EH
(blueprint: def-trf-log-etale-restriction-stalk-comparison).

The slice restriction keeps the same monoid sections and structural maps on every
test scheme. The ring comparison is the canonical isomorphism between the geometric
structure-ring stalk and the small affine pointed-neighbourhood colimit.

These definitions are moved from the log-locality and completed-chart theorem modules;
those modules publicly import this one. Their names, signatures and bodies are unchanged.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Restriction of a prelog structure to an étale object. This is `Sheaf.over`,
transported through the canonical equivalence with the small étale site of its source;
its structural map is the original one on the identical test scheme.
Source: ILO VI 1.1, VIII 3.3.8; Stacks, Tags 00Y0 and 03EH
(blueprint: def-trf-log-etale-restriction-stalk-comparison). -/
noncomputable def EtalePrelogStructure.etaleRestrict {T : Scheme.{u}}
    (M : EtalePrelogStructure T) (U : T.Etale) : EtalePrelogStructure U.left where
  monoidSheaf := ((Scheme.Etale.overEquiv U).sheafCongr
    (T.smallEtaleTopology.over U) U.left.smallEtaleTopology CommMonCat.{u}).functor.obj
      (M.monoidSheaf.over U)
  alpha := Functor.whiskerLeft ((Scheme.Etale.etaleToOver U ⋙ Over.forget U).op) M.alpha

/-- Canonical identification of the étale structure-ring stalk with the recorded
strict henselization. Source: ILO VI 1.2, 1.6; the affine pointed-neighbourhood
colimit description (blueprint: def-trf-log-etale-restriction-stalk-comparison).
It is induced by restriction to the initial affine neighbourhood subcategory. -/
noncomputable def strictLocalRingStrictHenselizationIso
    (X : Scheme.{u}) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) : strictLocalRing X t ≅ Scheme.strictHenselizationRing t := by
  let F := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods t)).inverse ⋙
    Scheme.strictHenselizationAffineInclusion t ⋙ Scheme.AffinePointedEtaleNeighborhood.ι t
  letI : F.Initial := (Scheme.strictHenselization_properties t).1
  exact IsColimit.coconePointUniqueUpToIso
    ((Scheme.pointSmallEtale t).isColimitPresheafFiberCocone X.etaleStructurePresheaf)
    (colimit.isColimit
      ((CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op ⋙
        X.etaleStructurePresheaf)) ≪≫
    (Functor.Final.colimitIso F.op
      ((CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op ⋙
        X.etaleStructurePresheaf)).symm ≪≫
    HasColimit.isoOfNatIso
      (F := F.op ⋙ (CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op ⋙
        X.etaleStructurePresheaf)
      (G := Scheme.strictHenselizationAffineDiagram t)
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
        intro i j f
        rfl))

end AlgebraicGeometry
