/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Paper.CechCupResolutionComparisonData
public import Mathlib.Topology.Sheaves.Flasque
import Sheaf.Paper.CechFlasqueComparisonCore
import Sheaf.Paper.CechFlasqueComparisonClasses

/-! # Canonical Cech comparison for a flasque computing resolution

Source: Stacks Project, Tags 01EQ and 0FKV.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- A termwise flasque computing resolution admits the canonical Cech comparison.
Source: Stacks Project, Tags 01EQ and 0FKV, resolution-comparison argument.
(blueprint: lem-sc-cech-flasque-resolution-comparison)

Proof: define alpha by restrictions of sections and beta by the augmentation.
Restriction naturality and the augmentation cochain identity give chain maps.
The augmented Cech complex of each flasque term is exact in positive degree,
and sheaf gluing identifies degree-zero cohomology with global sections.
First-quadrant column comparison therefore makes alpha a quasi-isomorphism.
Compose the inverse computing comparison to the injective resolution and its
cohomology identification with H(alpha) to obtain iso and alpha_class.
The map to the injective resolution induces a map of Cech total complexes.
Its alpha and beta squares commute. Its homology map is invertible by the
alpha square and the computing comparison. Apply IsModuleCechComparison to
that injective resolution and cancel this homology map to obtain beta_class.
Empty covers of the empty scheme and degree zero use the same identities. -/
theorem cupCechFlasqueResolutionComparison {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) (hU : iSup U = ⊤) {F : X.Modules}
    (D : CupAcyclicResolution F)
    (hD : ∀ n : ℕ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (D.K.X n))) :
    Nonempty (CupCechResolutionComparison U D) := by
  obtain ⟨alpha, beta, halpha, hbeta, hq⟩ :=
    cechFlasqueComparisonCore U hU D hD
  let : QuasiIso alpha := hq
  obtain ⟨iso, halpha_class, hbeta_class⟩ :=
    cechFlasqueComparisonClasses U D alpha beta halpha hbeta
  exact ⟨{
    alpha := alpha
    beta := beta
    alpha_f := halpha
    beta_f := hbeta
    alpha_quasiIso := inferInstance
    iso := iso
    alpha_class := halpha_class
    beta_class := hbeta_class }⟩

end
end AlgebraicGeometry.Scheme.Modules
