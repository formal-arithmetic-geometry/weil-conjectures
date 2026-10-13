/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import Sheaf.AlgebraicGeometry.EtaleOpenCechInjectiveAugmentation
import Sheaf.Algebra.Homology.FirstQuadrantAugmentation

/-! # Global restriction augmentation quasi-isomorphism
Source: Stacks Project, Tag 01EQ, Lemma 20.11.2. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The global restriction augmentation is a quasi-isomorphism of complexes.
Source: Stacks Project, Tag 01EQ, Lemma 20.11.2, augmentation alpha.
(blueprint: lem-pbc-etale-additive-cech-alpha-quasiiso)

Proof: Global restrictions commute with the resolution differential and with the
alternating Cech cofaces. The latter cancel in horizontal degree zero, so the
components alpha form a chain map. The canonical open inclusion preserves
coverings and finite limits, and its value at top is terminal. Each injective
resolution term therefore has a quasi-isomorphic augmented open-cover Cech row,
by etaleOpenCechInjectiveAugmentation_quasiIso. Apply the first-quadrant column
augmentation criterion, with Cech degree first, to these rows. Its component
formula is precisely additiveCechAlpha, so the resulting map is a quasi-isomorphism.
Degree zero uses sheaf gluing; empty covers force the scheme and its sections to
be empty and zero respectively, and repeated or empty intersections cause no change. -/
theorem etaleAdditiveCech_alpha_quasiIso
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hcover : iSup U = ⊤) (I : InjectiveResolution X.etaleAdditiveSheaf) :
    ∃ a : additiveCechGlobal I ⟶ additiveCechTotal U I,
      (∀ n : ℕ, a.f n = additiveCechAlpha U I n) ∧ QuasiIso a := by sorry

end AlgebraicGeometry.Scheme.Modules
