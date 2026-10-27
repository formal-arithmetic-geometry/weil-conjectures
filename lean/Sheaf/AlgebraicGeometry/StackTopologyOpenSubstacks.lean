module

public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
import WeilConjectures.FieldTheory.CommonExtensionFields
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Topology and open substacks of Deligne--Mumford stacks

Source: Stacks Project, stacks-properties.tex, Tags 04XF, 04XG, 04XH, 04XL and 06FJ
(blueprint: lem-sfb-stack-topology-open-substacks).

The point quotient, full open substacks, atlases and 2-fibre products are the existing
moduli interfaces. Opens are expressed as closed complements using the existing
`ModuliPointIsClosed` predicate; its atlas criterion below proves atlas independence.
No additional topology or scheme-point map is constructed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- The actual point image of the full inclusion of an open substack.
Source: Stacks 06FJ (blueprint: lem-sfb-stack-topology-open-substacks). -/
def OpenModuliSubstack.pointImage {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} (U : OpenModuliSubstack F) :
    Set (ModuliPoints F) :=
  Set.range (moduliPointMap (fullModuliInclusion F U.property))

/-- The existing arrow-generated quotient is exactly the common-extension quotient:
a common field object maps to both representatives, encoding their isomorphic pullbacks.
Source: Stacks 04XF and 04XG (blueprint: lem-sfb-stack-topology-open-substacks).

Proof, step 1: arrows give equality in the quotient. Conversely, the relation of having
such a common field object is reflexive and symmetric. For transitivity, amalgamate
the two fields over the middle field by lem-weil-common-extension-fields, lift the
objects using def-sfb-stable-pointed-moduli-groupoids, and compose the fibre isomorphisms.
It is therefore an equivalence relation containing the generating arrows, and every
quotient equality supplies the asserted common-extension representative. -/
theorem moduliPoints_eq_iff_common_field {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (hF : IsDeligneMumfordModuliStack F)
    (x y : ModuliFieldObject F) :
    Quot.mk (ModuliFieldRelation F) x = Quot.mk (ModuliFieldRelation F) y ↔
      ∃ z : ModuliFieldObject F, Nonempty (z.val ⟶ x.val) ∧ Nonempty (z.val ⟶ y.val) := by
  sorry

/-- Every étale surjective scheme atlas detects the same open subsets.
Source: Stacks 04XL (blueprint: lem-sfb-stack-topology-open-substacks).

Proof, steps 2--6: field maps to schemes are points with residue-field embeddings
(lem-weil-pbc-morphism-from-spec-field); their equivalence is tested over a common
extension (lem-weil-common-extension-fields). A field object lifts through an atlas
by taking a residue field in an étale scheme chart of its base change, using
lem-a1-space-affine-etale-cover and lem-sfb-stack-chartwise-smooth-etale-calculus.
Thus the atlas map on points is surjective. Two atlases have a common étale scheme
refinement: cover their 2-fibre product by an étale scheme. Both projections are open
continuous surjections by lem-weil-pbc-etale-morphism-open-map and the chart calculus.
Their inverse images of a subset coincide, so the two atlas tests agree. Inverse image
preserves unions and finite intersections. Taking complements in the existing
closed-set predicate gives exactly the displayed open-set criterion. Identity atlases
recover the scheme topology. -/
theorem moduliPointIsClosed_compl_iff {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (hF : IsDeligneMumfordModuliStack F)
    (T : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (ha : IsEtaleModuliAtlas a) (W : Set (ModuliPoints F)) :
    ModuliPointIsClosed F Wᶜ ↔ IsOpen (moduliChartPreimage a W) := by
  sorry

/-- For a scheme the point quotient and its topology are the usual point space.
Source: Stacks 04XG, 04XL and Spaces 03BV
(blueprint: lem-sfb-stack-topology-open-substacks).

Proof, steps 2 and 6: use lem-weil-pbc-morphism-from-spec-field to identify a field
map with its image point and residue-field embedding. Representatives with the same
point agree over a common extension by lem-weil-common-extension-fields, and every
point has its residue-field representative. This proves bijectivity and characterizes
the equivalence by the existing chart preimage for the identity chart. Apply the atlas
criterion to the identity atlas to identify exactly the usual open subsets. -/
theorem moduliSchemePoint_topology {S : Scheme.{u}} (T : Over S) :
    ∃ e : T.left ≃ ModuliPoints (discreteModuli (yoneda.obj T)),
      (∀ W : Set (ModuliPoints (discreteModuli (yoneda.obj T))),
        moduliChartPreimage (BasedFunctor.id (discreteModuli (yoneda.obj T))) W =
          e ⁻¹' W) ∧
      ∀ W : Set (ModuliPoints (discreteModuli (yoneda.obj T))),
        ModuliPointIsClosed (discreteModuli (yoneda.obj T)) Wᶜ ↔ IsOpen (e ⁻¹' W) := by
  sorry

/-- The point image gives an inclusion-preserving bijection between open substacks
and open subsets of the field-point topology.
Source: Stacks 06FJ (blueprint: lem-sfb-stack-topology-open-substacks).

Proof, steps 7--9: for an atlas A, surjectivity on points identifies subsets of the
stack with saturated subsets of A. The 2-fibre-product point calculation identifies
saturation with equality of the two inverse images on A ×_F A. For open subsets this
is equality of open subspaces by lem-a1-space-etale-open-image. Apply
lem-sfb-invariant-open-substack-descent to the smooth surjective atlas (étale implies
smooth by lem-sfb-stack-chartwise-smooth-etale-calculus). It gives the inclusion-
preserving bijection with invariant opens. Strict fullness makes the point map of
an open substack injective. The 2-fibre-product point calculation identifies its
atlas pullback with the inverse image of its point image, so the resulting bijection
is the actual assignment in this statement. -/
theorem moduliOpenSubstack_pointImage_bijection {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (hF : IsDeligneMumfordModuliStack F) :
    ∃ e : OpenModuliSubstack F ≃
        {W : Set (ModuliPoints F) // ModuliPointIsClosed F Wᶜ},
      (∀ U : OpenModuliSubstack F, (e U).val = U.pointImage) ∧
      ∀ U V : OpenModuliSubstack F,
        U.IsContainedIn V → (e U).val ⊆ (e V).val := by
  sorry

/-- Pulling back an open substack gives the inverse image on point sets. The full
subcategory has exactly the pulled-back object predicate, and its comparison with
the actual 2-fibre product commutes with the projection to the source stack.
Source: Stacks 04XH, 04YM and 06FJ
(blueprint: lem-sfb-stack-topology-open-substacks).

Proof, step 10: every scheme test of the pullback is the corresponding scheme test
of the original open, by associativity of 2-fibre products. Its strictly full essential
image consists exactly of objects mapped into U. The inclusion and its defining
isomorphisms give an equivalence with the actual 2-fibre product over the source.
Projection gives one containment of point sets. Conversely, an image point in |U|
has a representative in U and a common-extension isomorphism; their triple defines
a point of the 2-fibre product. Strict fullness gives injectivity as in step 9.
Thus the classification assigns precisely the inverse image displayed here. -/
theorem moduliOpenSubstack_pointImage_pullback {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (hF : IsDeligneMumfordModuliStack F) (hG : IsDeligneMumfordModuliStack G)
    (f : BasedFunctor G F) (U : OpenModuliSubstack F) :
    ∃ V : OpenModuliSubstack G,
      (∀ y : G.obj, V.property y ↔ U.property (f.obj y)) ∧
      (∃ e : BasedFunctor V.category
          (moduliTwoFiberProduct f (fullModuliInclusion F U.property)),
        e.toFunctor.IsEquivalence ∧
          Nonempty (ModuliTwoIso
            (e.comp (moduliTwoFiberFst f (fullModuliInclusion F U.property)))
            (fullModuliInclusion G V.property))) ∧
      V.pointImage = moduliPointMap f ⁻¹' U.pointImage := by
  sorry

end CategoryTheory
