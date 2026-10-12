/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Sheaf.AlgebraicGeometry.FpqcMorphismsDescend
import Sheaf.AlgebraicGeometry.FpqcOpenSubschemeDescent
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing effective descent on invariant open subschemes

Source: Stacks Project, Descent, Lemma 35.35.13, Tag 0AP4.
(blueprint: lem-pd-effective-invariant-open-cover).
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

/-- Effective compatible data on an open covering glue to an effective datum.
Source: Stacks Project, Descent, Lemma 35.35.13, Tag 0AP4.
(blueprint: lem-pd-effective-invariant-open-cover).

Proof: First select one covering open for each point of V if the index universe is
larger than that of V. Choose effective models W_i over Y for the selected data E_i.
Their pullbacks identify
with U_i, compatibly with D by hcompat. The preimages of U_i intersect U_j in each
U_i are invariant under E_i: transport compatibility and the restriction to U_j
show invariance in both directions, the latter using inverse transport. Descend
these opens along the fpqc map U_i -> W_i using descent of compatible opens (03N0).
The identity on U_i intersect U_j then descends by fpqc full faithfulness (02W0)
to an isomorphism of the resulting opens of W_i and W_j. Faithfulness proves the
identity and triple-overlap cocycle laws. Scheme gluing gives W over Y. The local
pullback identifications glue to an isomorphism V = W times_Y X, since hcover says
the U_i cover V. Its projection witnesses IsEffective; transport compatibility is
checked on the inverse-image covering of each test scheme. For an empty cover,
hcover forces V empty; the empty scheme over Y and its empty pullback give the
same construction. No affineness of the U_i or finiteness of p is required. -/
theorem isEffective_of_effective_open_cover
    {X Y : Scheme.{u}} {p : X ⟶ Y}
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y)
    {V : Over X} (D : Over.DescentDatum p V)
    {I : Type v} (U : I → V.left.Opens)
    (hcover : ∀ x : V.left, ∃ i, x ∈ U i)
    (E : ∀ i, Over.DescentDatum p (Over.mk ((U i).ι ≫ V.hom)))
    (hcompat : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ (U i).ι =
        (D.transport f₁ f₂ h (Over.homMk (a.left ≫ (U i).ι)
          (by simpa only [Over.mk_hom, Category.assoc] using Over.w a))).left)
    (heffective : ∀ i, (E i).IsEffective) : D.IsEffective := by sorry

end CategoryTheory.Over.DescentDatum
