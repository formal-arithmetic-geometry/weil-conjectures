module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.EtaleAtlasPresentation
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.LocallyFinitePresentationAffineLimitCriterion
import Sheaf.AlgebraicGeometry.FppfSheafificationAffineContinuity
import Sheaf.AlgebraicGeometry.SpaceChangeBase

/-! # Relative affine limit criterion for algebraic spaces

Source: Stacks Project, Limits of Spaces, Tags 04AK and 06BC; the chart convention
is Morphisms of Spaces, Tag 03XP (blueprint: lem-sfb-space-relative-affine-limit-criterion).

The comparison map is constructed from restriction to the cone point and composition
with the given morphism. Its codomain is the fibre product in sets.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical relative comparison map for an inverse system of schemes over `S`.
Its first component restricts a stage point to the cone point. Its second component
composes with `f` at the stage, then takes its colimit class. The compatibility of
these two components is naturality of `f`, checked on the colimit coprojections.
No limit or affineness hypothesis is needed to construct this map.

Source: Stacks Project, Limits of Spaces, Tag 06BC, the displayed cartesian square
(blueprint: lem-sfb-space-relative-affine-limit-criterion). -/
def relativeAffineLimitComparison {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Over S) (c : Cone D) :
    colimit (D.rightOp ⋙ X.obj.obj) ⟶
      Limits.pullback (f.hom.hom.app (op c.pt))
        (colimit.desc (D.rightOp ⋙ Y.obj.obj)
          (Y.obj.obj.mapCocone (coconeRightOpOfCone c))) :=
  Limits.pullback.lift
    (colimit.desc (D.rightOp ⋙ X.obj.obj)
      (X.obj.obj.mapCocone (coconeRightOpOfCone c)))
    (colimMap (Functor.whiskerLeft D.rightOp f.hom.hom)) (by
      apply colimit.hom_ext
      intro i
      simp only [colimit.ι_desc_assoc, ι_colimMap_assoc, colimit.ι_desc]
      exact f.hom.hom.naturality (c.π.app (op i)).op)

/-- A morphism of algebraic spaces is locally of finite presentation exactly when its
relative comparison map is bijective on every nonempty directed affine inverse system.
`MapIsLocallyOfFinitePresentation` is the existing étale chart predicate. By
`local_properties_chart_test`, it is equivalent to requiring local finite presentation
of every scheme map `W → V` for surjective étale charts `V → Y` and `W → X ×_Y V`.
No quasi-compactness or quasi-separatedness of either space is imposed.

Source: Stacks Project, Limits of Spaces, Tags 04AK and 06BC; Morphisms of Spaces,
Tag 03XP (blueprint: lem-sfb-space-relative-affine-limit-criterion).

Proof:
1. For a map of functors, the relative cartesian-square condition is equivalent to
continuity of every fibre functor over every scheme B. Represent a base colimit class
at a stage, restrict to its cofinal tail, and use eventual equality of representatives
to obtain both existence and uniqueness. Conversely apply the relative condition to
the compatible base point and increase the stage to make its base equality hold
[lem-weil-pbc-filtered-colimit-sets-elementwise, lem-weil-pbc-limit-affine-transition].
2. The chart condition is preserved by base change to a scheme B: base change target
and source atlases, use the scheme base-change property, and apply the chart test
[def-trf-algebraic-space, lem-trf-space-fibre-products-etale-covers,
lem-trf-space-representable-etale-scheme-tests, lem-weil-pbc-qcqs-morphism-permanence,
lem-sfb-space-local-properties-chart-test].
3. For a locally finitely presented space Z over B, choose a presentation U/R. Both
U and R are locally finitely presented over B, by the chart test, étaleness of R → U,
and composition. Their point functors commute with directed affine limits by the
scheme criterion [def-trf-algebraic-space, lem-a1-etale-atlas-presentation,
lem-sfb-space-local-properties-chart-test, def-weil-etale-morphism,
lem-sbc-locally-finite-presentation-composition, lem-sfb-scheme-affine-limit-lfp-criterion].
4. The quotient presheaf U/R commutes with these limits: descend representatives using
U and descend relations using R; eventual equality makes their projections agree at a
common stage. Its fppf sheafification Z has the same continuity
[lem-a1-etale-atlas-presentation, lem-weil-pbc-filtered-colimit-sets-elementwise,
lem-sfb-fppf-sheafification-affine-continuity].
5. Apply steps 2–4 to X ×_Y B viewed over B. The change-of-base equivalence identifies
its points with the fibre functor of f over the given B-point of Y. Step 1 gives the
required bijection [lem-sfb-space-change-base-to-integers,
lem-trf-space-fibre-products-etale-covers].
6. The fibrewise criterion is stable under base change, since the fibres are unchanged.
It is stable under composition, by pasting the two cartesian comparison squares.
7. Conversely take arbitrary surjective étale charts V → Y and U → X ×_Y V.
Base change gives the relative criterion for X ×_Y V → V. Every scheme base change
of U → X ×_Y V is étale, hence locally finitely presented, so the scheme criterion
and step 1 give its relative criterion. Step 6 gives the relative criterion for U → V
[lem-trf-space-fibre-products-etale-covers,
lem-trf-space-representable-etale-scheme-tests, def-weil-etale-morphism,
lem-sfb-scheme-affine-limit-lfp-criterion].
8. Use the identity V-point to identify its fibre functor with Mor_V(-, U).
The reverse scheme criterion proves U → V locally finitely presented. Since the
charts were arbitrary, this is the chart condition for f. All systems remain in the
fixed universe and no compactness or separation is used
[lem-sfb-scheme-affine-limit-lfp-criterion]. -/
theorem locallyOfFinitePresentation_iff_relative_affine_limit_bijective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    MapIsLocallyOfFinitePresentation f ↔
      ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
        (D : Iᵒᵖ ⥤ Over S),
        (∀ i : Iᵒᵖ, IsAffine (D.obj i).left) →
        ∀ c : Cone D, IsLimit c → Function.Bijective (relativeAffineLimitComparison f D c) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
