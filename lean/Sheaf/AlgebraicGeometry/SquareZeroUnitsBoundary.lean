module

public import WeilConjectures.AlgebraicGeometry.Thickening
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.ZariskiUnitsRestriction
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # The normalized units boundary of a square-zero thickening

Source: Stacks Project, More on Morphisms, Tag 0C6R, proof
(blueprint: def-sfb-square-zero-units-boundary).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] CategoryTheory.Abelian.Ext
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme

/-- The canonical kernel sequence of restriction on units.
Source: Stacks Project, Tag 0C6R, proof
(blueprint: def-sfb-square-zero-units-boundary). -/
@[reducible]
noncomputable def squareZeroUnitsSequence {Z X : Scheme.{u}} (j : Z ⟶ X) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk (kernel.ι (unitsSheafToPushforward j))
    (unitsSheafToPushforward j) (kernel.condition _)

/-- Restriction of units across a first order thickening is locally surjective.
Source: Stacks Project, Tag 0C6R, proof
(blueprint: def-sfb-square-zero-units-boundary).

Proof: the first map is the categorical kernel inclusion, hence is mono and exact
at the middle term. A closed immersion gives local lifts u,v of a unit and its inverse.
Their product is 1+a in the ideal; square zero gives (1+a)(1-a)=1. Thus u has inverse
v(1-a). This proves sheaf epimorphy, without asserting surjectivity on global sections,
and completes short exactness, including on the empty scheme. -/
theorem squareZeroUnitsSequence_shortExact {Z X : Scheme.{u}} (j : Z ⟶ X)
    (hj : IsFirstOrderThickening j) : (squareZeroUnitsSequence j).ShortExact := by
  sorry

/-- The unique identification of the additive ideal with the kernel of units restriction,
normalized by a ↦ 1+a on every open.
Source: Stacks Project, Tag 0C6R, proof
(blueprint: def-sfb-square-zero-units-boundary).

Proof: the inclusion of the ideal identifies its sections with sections killed by j♯,
by def-sbc-closed-immersion-ideal-sheaf and the ideal-to-module construction. Send a to
1+a, whose inverse is 1-a. Since products of ideal sections vanish, this respects addition
and restriction. Conversely a unit restricting to 1 has u-1 in this ideal. These maps are
mutually inverse sectionwise and commute with restrictions, hence give a sheaf isomorphism.
The normalization and injectivity of the kernel inclusion force its hom component and
therefore the entire isomorphism uniquely. -/
theorem existsUnique_squareZeroIdealUnitsIso {Z X : Scheme.{u}} (j : Z ⟶ X)
    (hj : IsFirstOrderThickening j) :
    ∃! e : (SheafOfModules.toSheaf X.ringCatSheaf).obj j.ker.toModules ≅
        (squareZeroUnitsSequence j).X₁,
      ∀ (U : X.Opens) (a : Γ(j.ker.toModules, U)),
        (unitsSheaf.toUnits ((kernel.ι (unitsSheafToPushforward j)).hom.app (op U)
          (e.hom.hom.app (op U) a)) : Γ(X, U)) =
          (1 : Γ(X, U)) + @id Γ(X, U) (j.ker.toModulesι.app U a) := by
  sorry

/-- The uniquely section-normalized identification a ↦ 1+a. Only the proof of this
uniquely determined isomorphism is postponed; its normalization fixes all its data.
Source: Stacks Project, Tag 0C6R, proof
(blueprint: def-sfb-square-zero-units-boundary). -/
noncomputable def squareZeroIdealUnitsIso {Z X : Scheme.{u}} (j : Z ⟶ X)
    (hj : IsFirstOrderThickening j) :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj j.ker.toModules ≅
      (squareZeroUnitsSequence j).X₁ :=
  Classical.choose (existsUnique_squareZeroIdealUnitsIso j hj)

/-- The cohomological units boundary, Stacks 0C6R.
(blueprint: def-sfb-square-zero-units-boundary). -/
noncomputable def squareZeroUnitsBoundary {Z X : Scheme.{u}} (j : Z ⟶ X)
    (hj : IsFirstOrderThickening j) :
    Sheaf.H ((squareZeroUnitsSequence j).X₃) 1 →+
      Sheaf.H ((squareZeroUnitsSequence j).X₁) 2 :=
  Sheaf.H.δSucc (squareZeroUnitsSequence_shortExact j hj) 1

/-- The inverse normalized ideal identification on cohomology, Stacks 0C6R.
(blueprint: def-sfb-square-zero-units-boundary). -/
noncomputable def squareZeroUnitsIdealCohomology {Z X : Scheme.{u}} (j : Z ⟶ X)
    (hj : IsFirstOrderThickening j) :
    Sheaf.H ((squareZeroUnitsSequence j).X₁) 2 →+
      Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj j.ker.toModules) 2 :=
  Sheaf.H.map (squareZeroIdealUnitsIso j hj).inv 2

end AlgebraicGeometry.Scheme
