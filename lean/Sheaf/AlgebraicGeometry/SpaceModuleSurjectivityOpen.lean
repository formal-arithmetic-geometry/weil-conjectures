/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SpaceInvariantOpenQuotient
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import Sheaf.AlgebraicGeometry.SpaceGeometricPointsConservative
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests

/-! # Universal openness of module surjectivity with proper target support

Source: Stacks Project, spaces-flat.tex, Tag 09TP, lemma-F-surj-open,
with situation-iso (blueprint: lem-sfb-space-module-surjectivity-open).

The canonical inclusion of the open subfunctor represents the surjectivity condition.
For every scheme map to the base it gives a unique factor exactly when the tensor
pullback is surjective. This specifies the natural identifications by composition
with the inclusion, rather than by choosing arbitrary bijections of sets.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Surjectivity after any scheme base change is represented by an open subspace.
`Epi` means surjectivity of module sheaves, not surjectivity on every set of sections.
The proper-support hypothesis is the specified closed proper carrier, with its finite
type quasi-coherent module and direct-image identification. Neither finite type of F
nor flatness of G is required. The unique-factor criterion specifies the natural
bijection: send a map to the open subspace to its composite with the inclusion.
Precomposition with any scheme map commutes with this operation; uniqueness makes
its inverse natural as well.

Source: Stacks Project, Tag 09TP, lemma-F-surj-open, with situation-iso
(blueprint: lem-sfb-space-module-surjectivity-open).

Proof:
1. Let C be the cokernel of u. It is quasi-coherent by
   lem-sfb-space-qcoh-kernels-colimits and finite type as a quotient of G. Tensor
   pullback is left adjoint to moduleDirectImage, so
   lem-weil-pbc-left-adjoint-preserves-colimits identifies the cokernel of every u_T
   with C_T. Thus u_T is surjective exactly when C_T is zero, without left exactness.
2. By lem-sfb-space-finite-type-support-pullback, D = Supp(C) is closed. It is contained
   in Supp(G), hence in the image of its closed proper carrier i : Z → X. Outside
   this image all chart sections defining i_*N are zero. The inverse image of D in Z
   is closed by continuity (lem-a1-space-point-open-calculus). Universal closedness of
   f i, from def-sfb-space-morphism-properties, shows E = f(D) is closed in B.
3. Apply lem-a1-space-invariant-open-quotient to the invariant open complement of E
   on an etale atlas of B, obtaining the open subspace V with point image B minus E.
4. For any b : T → B, support pullback gives Supp(C_T) = p⁻¹(D).
   The geometric-point conservativity of lem-sfb-space-geometric-points-conservative
   detects C_T = 0 by emptiness of this support. Realize D by the reduced closed
   subspace of lem-sfb-space-reduced-closed-support. Fibre-product associativity and
   the arbitrary Cartesian point-image formula of lem-a1-space-point-open-calculus
   give f_T(Supp(C_T)) = b⁻¹(E). Thus C_T = 0 exactly when the image of b avoids E.
   This argument applies to nonflat base change too.
5. By lem-a1-space-open-factor-scheme-tests, image containment in V is equivalent to
   unique factorization through its inclusion. This proves the displayed criterion.
   Composing factors with scheme maps proves naturality; tensor pullback composition
   identifies the pulled arrows. Empty bases, empty fibres, and the zero target are
   covered by the same empty-support argument. -/
theorem module_surjectivity_open {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (hf : MapIsLocallyOfFinitePresentation f)
    (F G : X.QCoh) (u : F.obj ⟶ G.obj) (hG : G.obj.IsFiniteType)
    (hproper : ∃ (Z : AlgebraicSpace S) (i : Z ⟶ X),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
      MapIsProper (i ≫ f) ∧ ∃ N : Z.Modules,
        N.IsQuasicoherent ∧ N.IsFiniteType ∧
          Nonempty ((moduleDirectImage i).obj N ≅ G.obj)) :
    ∃ V : OpenSubspace B, ∀ (T : Over S) (b : yoneda.obj T ⟶ B.obj.obj),
      Epi ((moduleTensorPullback (properQuotFst f (CostructuredArrow.mk b))).map u) ↔
        ∃! v : yoneda.obj T ⟶ V.val.toFunctor, v ≫ V.val.ι = b := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
