/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFlatLfpSource
import Sheaf.AlgebraicGeometry.SpaceOpenChartTests
import Sheaf.AlgebraicGeometry.FppfAffineRefinement
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct
import Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover
import Mathlib.AlgebraicGeometry.Limits

/-! # Smooth locality and fpqc descent of local finite type for algebraic spaces

Source: Stacks Project, Spaces Descent, Tags 06F8, 06FC(3) and 041S
(blueprint: lem-sfb-space-lft-smooth-fpqc-locality).

Both smoothness and local finite type use the existing compatible étale chart test.
Coverings in the second statement are tested on schemes, using arbitrary surjective
étale scheme atlases of the pulled-back members. This includes nonrepresentable maps
and arbitrary algebraic-space targets; it does not require the members to be schemes.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The three conditions of smooth locality on source-and-target for local finite type.
Source: Stacks, Spaces Descent, Tags 06F8 and 06FC(3)
(blueprint: lem-sfb-space-lft-smooth-fpqc-locality).

Proof (node steps 1--3): first establish scheme fppf source locality. For an fppf
family Tᵢ → T, form its scheme coproduct Q. Open-source locality of flatness and local
finite presentation makes Q → T flat and locally finitely presented, and joint
surjectivity makes it surjective. Local finite type of every composite Tᵢ → Z gives
local finite type of Q → Z by open-source locality. Apply
lem-a1-lft-flat-lfp-source-descent, using lem-weil-pbc-scheme-coproduct-family and
lem-sfb-stack-chartwise-smooth-etale-calculus. Next use
lem-sfb-scheme-etale-source-target-properties,
lem-sfb-space-etale-presentation-property-criterion and
lem-sfb-space-fppf-source-locality-transfer to transfer source locality to spaces.
Every space map is representable by spaces by lem-trf-space-fibre-products-etale-covers.
Smooth maps are locally finitely presented, hence locally of finite type; composition
and base-change calculus give the first two clauses. For the pointwise criterion,
identity squares give the forward direction. Conversely bₓhₓ = raₓ is locally of
finite type for every x. The smooth maps aₓ cover X since uₓ maps to x, hence form an
fppf family; the transferred source locality gives local finite type of r. When X is
empty the same argument uses the empty covering and has no nonemptiness assumption. -/
theorem locallyOfFiniteType_smooth_local_source_target {S : Scheme.{u}} :
    (∀ (X Y Z : AlgebraicSpace S) (a : X ⟶ Y) (f : Y ⟶ Z),
      MapIsLocally (@Smooth) a → MapIsLocally (@LocallyOfFiniteType) f →
        MapIsLocally (@LocallyOfFiniteType) (a ≫ f)) ∧
    (∀ (X Y V : AlgebraicSpace S) (f : X ⟶ Y) (b : V ⟶ Y),
      MapIsLocally (@LocallyOfFiniteType) f → MapIsLocally (@Smooth) b →
        MapIsLocally (@LocallyOfFiniteType) (enlargedFibreProductFst b f)) ∧
    (∀ (X Y : AlgebraicSpace S) (r : X ⟶ Y),
      MapIsLocally (@LocallyOfFiniteType) r ↔
        ∀ x : Point X.obj.obj,
          ∃ (U V : AlgebraicSpace S) (a : U ⟶ X) (b : V ⟶ Y)
            (h : U ⟶ V) (p : Point U.obj.obj),
            MapIsLocally (@Smooth) a ∧ MapIsLocally (@Smooth) b ∧
              mapPoint a.hom.hom p = x ∧ a ≫ r = h ≫ b ∧
                MapIsLocally (@LocallyOfFiniteType) h) := by
  sorry

/-- Local finite type descends and ascends along fpqc and fppf families of spaces.
The covering hypothesis spells out the node's scheme-pullback convention: for every
scheme T → Y, any surjective étale scheme atlases Uᵢ → Yᵢ ×_Y T give a covering
family Uᵢ → T in the indicated scheme precoverage. The maps Uᵢ → T are the canonical
second projections, recovered by Yoneda, with no arbitrary comparison maps.
Source: Stacks, Spaces Descent, Tag 041S; Topologies on Spaces, Tag 0DFQ
(blueprint: lem-sfb-space-lft-smooth-fpqc-locality).

Proof (node steps 4--7): verify the affine criterion
lem-sfb-space-fpqc-property-affine-criterion for local finite type. Finite disjoint
unions preserve it: lem-trf-algebraic-space-coproduct and
lem-trf-fppf-sheaf-coproduct-partition give open-and-closed component inclusions;
lem-a1-space-open-chart-tests makes them étale. Composition and open-source locality
from lem-sfb-stack-chartwise-smooth-etale-calculus give the claim, including the empty
union. Affine detection follows by covering a target atlas V by affine opens Vⱼ and
pulling back a source atlas U. The chart test
lem-sfb-space-local-properties-chart-test gives local finite type on Uⱼ → Vⱼ;
composition with Vⱼ → V and open-source locality descend it to U → V and then X → Y.
For flat surjective affine Z' → Z, choose an étale scheme atlas U → X. Its pullback
U' → Z' is locally of finite type by the chart test and
lem-trf-space-chartwise-etale-permanence. The singleton Z' → Z is fpqc: finitely many
standard opens cover any affine open of Z, and their inverse images are affine and
cover it by surjectivity. Apply lem-weil-pbc-fpqc-descend-locally-finite-type to U → Z
and the chart test again. The affine criterion now gives descent. The stated covering
condition gives its finite flat affine refinements by applying the scheme fpqc
condition to each affine test T. For fppf covers the same refinements follow from
lem-pc-fppf-affine-refinement, so they too are fpqc. Ascending follows from arbitrary
base-change stability on charts. Empty affine tests allow the empty refinement. -/
theorem locallyOfFiniteType_iff_of_schemeTestCover {S : Scheme.{u}}
    (J : Precoverage Scheme.{u})
    (hJ : J = Scheme.fpqcPrecoverage ∨ J = Scheme.fppfPrecoverage)
    {I : Type w} {X Y : AlgebraicSpace S} (r : X ⟶ Y)
    (Yᵢ : I → AlgebraicSpace S) (g : ∀ i : I, Yᵢ i ⟶ Y)
    (hcover : ∀ (T : Over S) (t : yoneda.obj T ⟶ Y.obj.obj)
      (U : I → Over S)
      (a : ∀ i : I, yoneda.obj (U i) ⟶ Limits.pullback (g i).hom.hom t),
      (∀ i : I, IsEtale (a i) ∧ IsSurjective (a i)) →
        Presieve.ofArrows (fun i : I ↦ (U i).left)
          (fun i : I ↦
            (yoneda.preimage (a i ≫ Limits.pullback.snd (g i).hom.hom t)).left) ∈
          J T.left) :
    MapIsLocally (@LocallyOfFiniteType) r ↔
      ∀ i : I, MapIsLocally (@LocallyOfFiniteType) (enlargedFibreProductFst (g i) r) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
