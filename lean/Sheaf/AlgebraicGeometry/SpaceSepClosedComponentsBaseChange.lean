/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Sites.Subcanonical
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Connected components of algebraic spaces over a separably closed field

Source: Stacks Project, Spaces over Fields, Tag 0A12;
Morphisms of Spaces, Tag 06DN; Properties of Spaces, Tags 03BZ and 03IE
(blueprint: lem-sfb-space-sepclosed-components-base-change).

The helpers construct the canonical structural map and the actual sheaf scalar extension.
The component correspondence is inverse image on maximal nonempty connected subsets.
Open component subspaces descend as literal subfunctors, with pullback given by preimage.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical structural morphism to the base, represented by its identity scheme.
It is the unique map to the Yoneda image of the terminal object of `Over S`.
Source: Stacks, Spaces over Fields, Tag 0A12, structural maps to the base
(blueprint: lem-sfb-space-sepclosed-components-base-change). -/
def structuralMapToBase {S : Scheme.{u}} (Z : AlgebraicSpace S) :
    Z ⟶ schemeSpace (Over.mk (𝟙 S)) :=
  ObjectProperty.homMk
    ((Over.mkIdTerminal.isTerminalObj (Scheme.fppfTopology.over S).yoneda).from Z.obj)

/-- The spectrum of the extension field, as an algebraic space over the ground field.
Source: Stacks, Spaces over Fields, Tag 0A12, `Spec L` over `Spec k`
(blueprint: lem-sfb-space-sepclosed-components-base-change). -/
def extensionFieldSpace (k L : Type u) [Field k] [Field L] [Algebra k L] :
    AlgebraicSpace (Spec (CommRingCat.of k)) :=
  schemeSpace (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))))

/-- The canonical map from the extension-field spectrum to the base spectrum.
Source: Stacks, Spaces over Fields, Tag 0A12
(blueprint: lem-sfb-space-sepclosed-components-base-change). -/
def extensionFieldBaseMap (k L : Type u) [Field k] [Field L] [Algebra k L] :
    extensionFieldSpace k L ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
  structuralMapToBase (extensionFieldSpace k L)

/-- Scalar extension is the sheaf fibre product over the represented base spectrum.
Its algebraic-space property is the recorded fibre-product theorem, not chosen data.
Source: Stacks, Spaces over Fields, Tag 0A12, `Z_L = Z ×_k Spec L`
(blueprint: lem-sfb-space-sepclosed-components-base-change). -/
abbrev fieldScalarExtension (k L : Type u) [Field k] [Field L] [Algebra k L]
    (Z : AlgebraicSpace (Spec (CommRingCat.of k))) :
    AlgebraicSpace (Spec (CommRingCat.of k)) :=
  enlargedFibreProduct (structuralMapToBase Z) (extensionFieldBaseMap k L)

/-- The canonical first projection of the scalar-extension sheaf fibre product.
Source: Stacks, Spaces over Fields, Tag 0A12, the projection `p : Z_L → Z`
(blueprint: lem-sfb-space-sepclosed-components-base-change). -/
abbrev fieldScalarExtensionProjection (k L : Type u) [Field k] [Field L] [Algebra k L]
    (Z : AlgebraicSpace (Spec (CommRingCat.of k))) : fieldScalarExtension k L Z ⟶ Z :=
  enlargedFibreProductFst (structuralMapToBase Z) (extensionFieldBaseMap k L)

/-- Arbitrary scalar extension over a separably closed field is an open continuous
surjection and induces the inverse-image bijection of connected components. Clopenness
of components is reflected, and every clopen component open subspace descends uniquely.
Finally connectedness is equivalent to connectedness after every field extension.
Source: Stacks, Spaces over Fields, Tag 0A12; Morphisms of Spaces, Tag 06DN;
Properties of Spaces, Tags 03BZ and 03IE
(blueprint: lem-sfb-space-sepclosed-components-base-change).

Proof:
1. Apply lem-sfb-space-over-field-universally-open to `Spec L` and `Z`; the projection
   is open. Continuity is lem-a1-space-point-open-calculus. No finite presentation is used.
2. The field spectrum `Spec L` is nonempty and connected. By
   lem-weil-separably-closed-geometrically-connected it is geometrically connected over k.
3. Represent a point of Z by Spec K. The point-image formula of
   lem-a1-space-point-open-calculus identifies the projection fibre with the image of
   Spec L ×_k Spec K. The sheaf universal property of
   lem-trf-space-fibre-products-etale-covers identifies this fibre product. Step 2 makes
   it nonempty and connected; its continuous image is nonempty and connected as well.
   Thus every projection fibre is connected, and the projection is surjective.
4. An open continuous surjection is a quotient map. Apply
   lem-sfb-quotient-connected-component-preimage to identify the inverse image of the
   component of p(x) with the component of x. Surjectivity now proves both surjectivity
   and injectivity of inverse image on component subsets. Empty point spaces cause no issue.
5. Continuity preserves clopenness under inverse image. Conversely the images of a clopen
   inverse image and its complement are open and equal the subset and its complement,
   by openness and surjectivity. Hence clopenness is reflected for each component.
6. Use lem-a1-space-etale-open-image to give the unique corresponding open component its
   open-subspace structure. The point-image identity of
   lem-a1-space-open-factor-scheme-tests identifies its pullback with the given clopen
   component upstairs; injectivity on subsets and the open-subspace correspondence prove
   uniqueness as subfunctors.
7. Apply the component bijection to every extension to deduce geometric connectedness
   from connectedness. Conversely use the identity field extension. Connected means
   nonempty throughout, so the empty space satisfies neither side of the equivalence. -/
theorem sepClosed_components_baseChange (k L : Type u) [Field k] [IsSepClosed k]
    [Field L] [Algebra k L] (Z : AlgebraicSpace (Spec (CommRingCat.of k))) :
    Continuous (mapPoint (fieldScalarExtensionProjection k L Z).hom.hom) ∧
    Function.Surjective (mapPoint (fieldScalarExtensionProjection k L Z).hom.hom) ∧
    IsOpenMap (mapPoint (fieldScalarExtensionProjection k L Z).hom.hom) ∧
    Set.BijOn
      (fun D : Set (Point Z.obj.obj) ↦
        mapPoint (fieldScalarExtensionProjection k L Z).hom.hom ⁻¹' D)
      (Set.range (connectedComponent (α := Point Z.obj.obj)))
      (Set.range (connectedComponent (α := Point (fieldScalarExtension k L Z).obj.obj))) ∧
    (∀ D ∈ Set.range (connectedComponent (α := Point Z.obj.obj)),
      IsClopen D ↔
        IsClopen (mapPoint (fieldScalarExtensionProjection k L Z).hom.hom ⁻¹' D)) ∧
    (∀ C : OpenSubspace (fieldScalarExtension k L Z),
      pointImage C.val.ι ∈
        Set.range (connectedComponent (α := Point (fieldScalarExtension k L Z).obj.obj)) →
      IsClopen (pointImage C.val.ι) →
      ∃! D : OpenSubspace Z,
        pointImage D.val.ι ∈ Set.range (connectedComponent (α := Point Z.obj.obj)) ∧
        IsClopen (pointImage D.val.ι) ∧
        D.val.preimage (fieldScalarExtensionProjection k L Z).hom.hom = C.val) ∧
    (ConnectedSpace (Point Z.obj.obj) ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        ConnectedSpace (Point (fieldScalarExtension k K Z).obj.obj)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
