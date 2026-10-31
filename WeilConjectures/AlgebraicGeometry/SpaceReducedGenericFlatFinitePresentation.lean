/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ReducedAlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.StackQcqsMorphism
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.EtaleSchemeMapOpenImage
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Generic flatness and local finite presentation over a reduced algebraic space

Source: Stacks Project, Morphisms of Spaces, Tag 06QS,
proposition-generic-flatness-reduced, applied to the structure sheaf
(blueprint: lem-sfb-space-reduced-generic-flat-finite-presentation).

The open subspace is the existing open subfunctor. The projection to it is the canonical
presheaf pullback projection, which computes the underlying sheaf fibre product. Both
properties are tested on every compatible pair of etale scheme charts of this projection.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite type morphism to a reduced algebraic space is flat and locally of finite
presentation over a dense open subspace. Neither space is required to be quasi-separated,
and the target is not required to be Noetherian, irreducible, quasi-compact or nonempty.

Source: Stacks Project, Morphisms of Spaces, Tag 06QS,
proposition-generic-flatness-reduced, the morphism conclusion for the structure sheaf
(blueprint: lem-sfb-space-reduced-generic-flat-finite-presentation).

Proof:
1. By lem-a1-space-affine-etale-cover choose affine etale charts V_i covering Y.
   Each V_i is reduced. Quasi-compactness of f makes X_i = X ×_Y V_i quasi-compact.
   Refine a scheme atlas of X_i to an affine surjective etale atlas U_i using
   lem-trf-space-qc-finite-affine-atlas-refinement. This needs no separatedness.
2. The map U_i → V_i is locally of finite type by
   lem-sfb-scheme-etale-source-target-properties and
   lem-sfb-space-etale-presentation-property-criterion. Apply
   lem-sfb-reduced-affine-generic-flat-finite-presentation to get a dense open D_i
   over which E_i = U_i ×_{V_i} D_i is flat and locally of finite presentation.
3. The images of D_i in Y are open by lem-a1-etale-scheme-map-open-image.
   Their union is an open subspace D by lem-a1-space-etale-open-image.
   The E_i form a jointly surjective etale covering of X ×_Y D, using
   lem-trf-space-representable-etale-scheme-tests and
   lem-trf-space-fibre-products-etale-covers for the base changes and compositions.
4. For any presentation A → B of X ×_Y D → D, form B_i = B ×_D D_i and
   C_i = A ×_{X ×_Y D} E_i. These are schemes. The etale squares from C_i → B_i
   to E_i → D_i transfer both properties by
   lem-sfb-scheme-etale-source-target-properties. Every point of A lifts to some C_i;
   the pointwise source-and-target locality criterion gives both properties on A → B.
   Thus every compatible etale chart diagram of the projection has both properties.
5. Every nonempty open O of Y has nonempty inverse image in some V_i. Density of D_i
   gives a point of O in the image of D_i, hence in D. Therefore D is dense.
   For empty Y take D = Y. Empty source charts and empty atlases are permitted, so
   the same argument covers empty X, without an irreducible-component decomposition. -/
theorem exists_dense_open_flat_locallyOfFinitePresentation_of_reduced
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hred : IsReduced Y) (hft : MapIsFiniteType f) :
    ∃ D : OpenSubspace Y, Dense (pointImage D.val.ι) ∧
      ∀ (U V : Over S)
        (a : yoneda.obj U ⟶ Limits.pullback f.hom.hom D.val.ι)
        (b : yoneda.obj V ⟶ D.val.toFunctor) (h : U ⟶ V),
        IsEtale a → IsEtale b →
          a ≫ Limits.pullback.snd f.hom.hom D.val.ι = yoneda.map h ≫ b →
            Flat h.left ∧ LocallyOfFinitePresentation h.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
