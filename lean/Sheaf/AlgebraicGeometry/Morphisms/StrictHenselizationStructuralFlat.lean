/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.ProEtale.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Flatness of the canonical affine strict henselization map
Source: Stacks Project, Tags 04HX and 07QM; Tag 0EYG, first reduction paragraph.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
/ -- The ring map inducing the canonical strict henselization structural map is flat.
Source: Stacks Project, Tags 04HX and 07QM; Tag 0EYG, first reduction paragraph.
(blueprint: lem-sbc-affine-strict-henselization-structural-flat)

Proof: For an affine base Spec R, the pointed affine etale neighbourhood coordinate
rings are etale R-algebras. The canonical structural map restricts to their
structure maps, by its defining common-composite identity. Thus the canonical
colimit ring is the filtered colimit of flat R-modules (etale algebras are flat).
Filtered colimits of flat modules are flat. Spec is faithful on ring maps,
so the displayed structural-map equality identifies b with this canonical
colimit algebra map. This works at any geometric point, whether or not it lies
on a specified divisor; no regularity or Noetherian hypothesis is needed. - /
theorem strictHenselization_structural_ringHom_flat
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    RingHom.Flat b.hom := by
  sorry
-/

end AlgebraicGeometry.Scheme
