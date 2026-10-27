/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.AlgebraicGeometry.NormalTowerCoverGluingData

/-! # Effective descent of finite etale chart covers

Source: Stacks Tags 01JB and 01JC (blueprint: lem-sfb-normal-tower-overlap-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

open NormalTowerCoverGluing

/-- A specified overlap system of finite etale chart covers is effective, including
its specified identification on U. Normality and generic points play no role here:
the overlap isomorphisms and their coherence are input data.

Source: Stacks Tags 01JB and 01JC, gluing schemes and morphisms; finiteness and
etaleness are Zariski local on the target.
(blueprint: lem-sfb-normal-tower-overlap-descent)

Proof: Pull each chart cover back along q and glue these schemes along the
isomorphisms d.α. Their overlap domains are the inverse images of the actual
pairwise chart intersections. Since the isomorphisms are over those intersections,
they preserve the triple domains; d.identity and d.cocycle give a scheme gluing
datum. The glued chart maps are open immersions and cover the glued scheme.
Glue the structural maps to A.left, which agree on overlaps because d.α lies
over the base. The inverse image of the j-th base chart equals the image of the
j-th glued cover chart: any point in another chart above that base chart is in
the overlap and is identified with its d.α image in the j-th chart. Thus these
charts give the stated isomorphisms e and induce exactly d.α. Finiteness and
etaleness are local on the target, so the structural map is finite etale.
The local identifications composed with e glue over U by
d.overlap_identification; their inverses glue as well. The two composites are
identities on the chart cover and hence globally. This constructs θ and proves
identification. The empty covering is allowed: hcover forces A.left to be empty,
and both its global cover and its pullback to U are empty. -/
theorem normalTower_overlap_descent {V : Scheme.{u}} (A : Over V) (U : V.Opens)
    (P : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ U.toScheme)
    {s : ℕ} (B : Fin s → Over V) (W : Fin s → V.Opens)
    (q : ∀ j : Fin s, A ⟶ B j)
    (Y : ∀ j : Fin s,
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ (chart (B j) (W j)))
    (θlocal : ∀ j : Fin s,
      (MorphismProperty.Over.pullback _ ⊤
        (chartInclusion (B j) (inf_le_left : W j ⊓ U ≤ W j))).obj (Y j) ≅
      (MorphismProperty.Over.pullback _ ⊤
        (chartToOpen (B j) (inf_le_right : W j ⊓ U ≤ U))).obj P)
    (hcover : (⨆ j : Fin s, W j) = ⊤)
    (d : Overlaps A U P B W q Y θlocal) :
    Nonempty (Realization A U P B W q Y θlocal d) := by sorry

end AlgebraicGeometry.Scheme
