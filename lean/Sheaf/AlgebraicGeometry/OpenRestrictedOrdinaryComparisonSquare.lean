/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.OpenRestrictedTensorComplexIso
public import Sheaf.AlgebraicGeometry.AffineSpectrumOrdinaryComparisonSquare

/-! # Open restriction of the comparison before the pullback counit

Source: Stacks Project, Tags 0DJ8 and 0098.
(blueprint: lem-pc-open-restricted-ordinary-comparison-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- Open restriction transports the comparison into ordinary tensor pullback.
There is no K-flatness assumption or inverse derived pullback counit in this square.

Proof: write j = U.ι, p = pullback.fst g' j and q = pullback.snd g' j.
The stalk maps of j at qz and p at z are ring isomorphisms. The pullback
condition identifies j(qz) with g'(pz). The equalities stalkMap_comp and
stalkMap_congr_hom identify the base stalk ring, the base-changed stalk ring,
and their algebra maps for the original and restricted squares. The natural
restriction-stalk map sends a restricted section germ to the same original
section germ and is semilinear for the inverse open stalk map. Apply it in
all degrees to the literal restricted complex. Transport the universal
left-derived base scalar extension through the exact ring equivalences.
Uniqueness with its universal counit identifies the two derived tensor
objects. Naturality of the A-action makes the cohomology identification
linear over the identified tensor algebras. Extend to the final stalk rings
and forget scalars to construct l and its inverse. The comparison_eq and
localized_eq equations of the two models identify their comparison maps
with the transported universal counit and its scalar-extension transpose.
Their naturality gives the square for localizedComparison. The same-germ
formula for tensorStalkIso identifies the ordinary tensor-pullback factors
with the adjunction-defined openTensorRestrictionComplexIso. Exact-stalk
homology and exact-restriction homology identify the target transport with
openDerivedStalkIso followed by openRestrictedTensorDerivedIso. Composing
these identities gives the stated equation. This uses no invertibility of
the horizontal comparison, no K-flatness or base flatness, and no bounds.
For an empty open no z exists; top opens, zero complexes and zero rings
satisfy the same functorial identities.
Source: Stacks Project, Tag 0DJ8, locality of equation-bc; Tag 0098, stalks
of pullback; Tag 0D5U, exact restriction; Tag 06Y6, derived tensor functoriality.
(blueprint: lem-pc-open-restricted-ordinary-comparison-square). -/
theorem exists_open_restricted_ordinary_comparison_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (U : X.Opens)
    (sqU : IsPullback (pullback.snd g' U.ι) (pullback.fst g' U.ι ≫ f') (U.ι ≫ f) g)
    (z : (pullback g' U.ι : Scheme.{u})) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let Q := ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
    let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (pullback.fst g' U.ι z)))
      AddCommGrpCat.{u}
    let FU := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z))
      AddCommGrpCat.{u}
    let HU := comparisonStalkCohomology (pullback g' U.ι) z i ⋙ FU
    let a := F.map (comparisonIntoTensorPullback f f' g g' sq
      (pullback.fst g' U.ι z) P i)
    let b := FU.map (comparisonIntoTensorPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g (pullback.snd g' U.ι) sqU z Q i)
    ∃ l : (Arrow.mk a).left ≅ (Arrow.mk b).left,
      a ≫ (openDerivedStalkIso (pullback.fst g' U.ι) z i).hom.app
          (DerivedCategory.Q.obj Pg) =
        l.hom ≫ b ≫ HU.map (openRestrictedTensorDerivedIso g' U P).inv := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
