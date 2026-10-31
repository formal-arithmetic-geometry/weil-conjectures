/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionBasicData
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionComparisonData

/-! # Normalized system presentations

Source: Zheng, Constructions 4.1 and 5.14--5.15, Lemma 5.16; Stacks Tag 0GL6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The proper/open system presentation exists on the actual vertical sequence sites.
Source: Zheng Constructions 4.1, 5.14--5.15; Stacks 03D7, 03S2, 07A4, 0GL6
(blueprint: lem-pur-etale-system-projection-existence).

Proof: Use base change on each small etale site and the identity on coefficient indices.
The constant-sheaf universal property gives the structural ring map, characterized on
constant generators. Take its module inverse-image/direct-image adjunction. The
coefficient rings are identified under inverse image, so inverse image is exact.
For an open immersion, localization of the site supplies exact extension by zero
left adjoint to inverse image. Module sheaves on the sequence site have K-injective
resolutions. Use these functors for the support presentation at every coefficient
sequence. Evaluation is exact; the ordinary direct-image evaluation comparison is
identity on sections. Its inverse-image mate is invertible, and its exact localization
has invertible derived mate. The same construction for scalar restriction gives its
sectionwise identity comparison, and the normalized scalar-extension adjunction gives
its invertible scalar mate. The open comparisons are the open-adjunction mates of
those inverse-image comparisons and are exact. Paste the proper and open comparisons.
All equations required by Theory are the defining mate equations or exact localization
identities, including the fixed scalar model's unit normalization. -/
theorem etaleSystemProjectionTheory_nonempty
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (l : ℕ) :
    Nonempty (Theory c l) := by
  obtain ⟨b⟩ := etaleSystemProjectionBasicData_nonempty c l
  obtain ⟨d⟩ := etaleSystemProjectionComparisonData_nonempty b
  exact ⟨{
    support := b.support
    evaluationX := b.evaluationX
    evaluationZ := b.evaluationZ
    evaluationY := b.evaluationY
    supportEvaluation := d.supportEvaluation
    scalarX := b.scalarX
    scalarY := b.scalarY
    scalarEvaluationX := d.scalarEvaluationX
    scalarEvaluationY := d.scalarEvaluationY
    restriction := d.restriction
  }⟩

end AlgebraicGeometry.Etale.SystemProjection
