module

public import Sheaf.CategoryTheory.RingedSiteDgOpenRestriction
public import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.LeftDerivedExactWhenDefined
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass

/-! # Derived scalar adjunction on ringed sites

Source: Stacks Project, sdga.tex, Tags 0FT4, 0FT5, 0FTF, 0FTR
(blueprint: lem-sfb-ringed-dg-scalar-adjunction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u

open CategoryTheory TopologicalSpace

namespace CategoryTheory.RingedSiteDg

/-- The standard triangulations and exact derived extension/restriction adjunction exist.
Its Hom equivalence is `ScalarModel.adjunction.homEquiv`; the inverse is extension
followed by the action counit (`ScalarModel.inverseTranspose`, `ScalarModel.counit`).
Restriction is the actual `Mod.comap`, preserving the entire underlying complex,
its cohomology and cone. Applying this to `oppositeMap φ` gives the left-module assertion.

Source: Stacks 0FT4, 0FT5, 0FTF, 0FTR, identity geometric morphism
(blueprint: lem-sfb-ringed-dg-scalar-adjunction).

Proof plan:
1. Use lem-sfb-sheaf-dg-homotopy-system to construct signed shifts and cones and their
homotopy triangulation; restriction preserves their underlying complexes literally.
2. Use lem-weil-pbc-localization-universal-property and lem-pur-localization-triangles-05r6
at quasi-isomorphisms to put the induced standard triangulation on the fixed localization.
3. Construct the balanced sheaf tensor and its chain-level restriction adjunction; its
unit inserts 1 and its counit is the action. Total tensor preserves shifts and cones.
4. By lem-sfb-sheaf-dg-good-resolutions, resolve by good modules, and show extension sends
quasi-isomorphisms between good modules to quasi-isomorphisms using their acyclic cones.
5. Apply lem-pur-resolving-class-essential-constancy, the pointwise Kan bridge
lem-pur-left-derived-defined-pointwise-kan-bridge, and lem-pur-total-left-derived-localization
to obtain the total left derived functor with comparison to ordinary extension.
6. Apply lem-pur-left-derived-exact-when-defined to obtain its shift and exactness data.
7. Derive the chain-level adjunction by lem-sc-derived-adjunction-from-underived;
restriction is already exact. The derived counit is the comparison followed by action.
8. The inverse Hom transpose is extension of the given arrow followed by this counit.
9. The signed opposite converts left modules to right modules, preserving all this data. -/
theorem ringed_dg_scalar_adjunction
    {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Sheaf J CommRingCat.{u}) (A B : Algebra.{c, v, u} O) (φ : A ⟶ B) :
    Nonempty (ScalarSystem.{c, v, u} φ) := by
  sorry

/-- Scalar extension/restriction and both adjunction maps commute with open restriction.
The target is the slice open site, canonically the open site of the subspace U.

Source: Stacks sdga, good resolutions restricted to opens; 0FTF, 0FTR
(blueprint: lem-sfb-ringed-dg-scalar-adjunction).

Proof plan: restrict the actual complexes, algebra multiplication and module action
sectionwise. Good resolutions remain good after open restriction by
lem-sfb-sheaf-dg-good-resolutions. The tensor comparison on good resolutions is the
ordinary balanced-tensor comparison. Extend it using lem-sc-nattrans-from-resolving-class
and the localization universal property; it is invertible on resolutions, hence everywhere.
Restriction of the ordinary unit inserts the same 1, and restriction of the ordinary
counit is the same action. Their derived comparisons agree on resolutions and therefore
everywhere. The displayed equations express the compatibility of both adjunction maps. -/
theorem ringed_dg_scalar_adjunction_open
    (X : TopCat.{c}) [EssentiallySmall.{u} (Opens X)]
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (A B : Algebra.{c, c, u} O) (φ : A ⟶ B)
    [DerivedStructure.{c, c, u} A] [DerivedStructure.{c, c, u} B]
    (s : ScalarModel.{c, c, u} φ) (U : Opens X) :
    Nonempty (OpenScalarSystem.{c, c, u} (O := O) φ s U) := by
  sorry

end CategoryTheory.RingedSiteDg
