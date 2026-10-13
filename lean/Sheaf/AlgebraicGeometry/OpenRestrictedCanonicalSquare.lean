/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
public import Sheaf.AlgebraicGeometry.OpenRestrictedComparisonComposition
public import Sheaf.AlgebraicGeometry.OpenDerivedStalkIso

/-! # Comparison square on literal restrictions

Source: Stacks Project, Tags 0DJ8 and 0DJ9 (locality of the stalk comparison).
(blueprint: lem-pc-open-restricted-canonical-square).
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange
/-- Compatibility of the two comparison arrows on a literal restriction, using
only the constructed derived-stalk isomorphism and representing isomorphism.
Source: Stacks Project, Tag 0DJ8, locality of equation-bc; Tag 0DJ9,
source-open induction paragraph; Tag 0D5U, exact open restriction.
(blueprint: lem-pc-open-restricted-canonical-square).

Proof: put j = U.ι, p = pullback.fst g′ j and q = pullback.snd g′ j.
Both j and p are open immersions, so their stalk ring maps are isomorphisms.
The pullback condition and stalkMap_comp identify the source and base stalk
ring maps for the two squares. The scalar-compatible restriction-stalk
extension isomorphism identifies the stalk complexes of P and its literal
restriction Q. Transport the universal base-derived tensor functors over
these ring isomorphisms, then apply cohomology and extension to the final
stalk ring. This constructs l, including its inverse, independently of
any invertibility of the comparison arrow. The model equations comparison_eq
and localized_eq express both comparison arrows as universal derived
counits followed by scalar-extension adjunction transposes. Their naturality
under these ring and stalk identifications, and tensorStalkIso, proves their
commutative square. Exact-restriction homology and restriction-stalk naturality
identify its right side with the constructed openDerivedStalkIso. The
universal-counit equation defining the derived composition comparisons
identifies the bottom transport with openRestrictedCompositionMap. The
localization factor of exact restriction is precisely
openRestrictionRepresentativeIso. Thus the equality is the displayed one.
K-flatness of P computes the original derived pullback; exact open restriction
preserves K-flatness. The supplied hcQ computes the restricted derived pullback.
This calculation has no arbitrary represented object or representing isomorphism.
Empty opens have no z. Top opens, zero complexes and zero rings use the same
functorial identifications; there is no nonzero or nonempty assumption. -/
theorem exists_open_restricted_canonical_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (U : X.Opens)
    (sqU : IsPullback (pullback.snd g' U.ι) (pullback.fst g' U.ι ≫ f') (U.ι ≫ f) g)
    (z : (pullback g' U.ι : Scheme.{u})) (i : ℤ) :
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (pullback.fst g' U.ι z)))
      AddCommGrpCat.{u}
    let FU := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z))
      AddCommGrpCat.{u}
    let HU := comparisonStalkCohomology (pullback g' U.ι) z i ⋙ FU
    ∀ (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (hP : P.IsKFlat)
        (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
      ,
      let Q : CochainComplex
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ :=
        ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
      ∀ (hcQ : IsIso ((counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q))),
      let eQ := openRestrictionRepresentativeIso U.ι P
      let η := openDerivedStalkIso (pullback.fst g' U.ι) z i
      let a := F.map (comparisonIntoPullback f f' g g' sq
        (pullback.fst g' U.ι z) P hcP i)
      let b := FU.map (comparisonIntoPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
        g (pullback.snd g' U.ι) sqU z Q hcQ i)
      let β := openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P)
      ∃ l : (Arrow.mk a).left ≅ (Arrow.mk b).left,
        a ≫ η.hom.app ((derivedPullback g').obj (DerivedCategory.Q.obj P)) =
          l.hom ≫ b ≫ HU.map ((derivedPullback (pullback.snd g' U.ι)).map eQ.hom ≫ β) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
