/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.DimZeroFiniteOverField
import Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage
import Sheaf.AlgebraicGeometry.FiniteFlatAffineRelationQuotient
import Sheaf.AlgebraicGeometry.RepresentableEtaleFppfLocalLifting
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.SeparatedAffineCoverCriterion
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits

/-! # Artinian components of a zero-dimensional algebraic space over a field

Source: Stacks Project, Spaces over Fields, Tag 06LZ, case (2), and Varieties,
Tag 06LH, locally algebraic case (blueprint: lem-sfb-zero-dimensional-field-space-components).

The dimension bound is expanded using all representable étale scheme charts and, at each
chart point, the infimum of the topological Krull dimensions of its open neighbourhoods.
The representing scheme and its component inclusions retain their structures over the
given field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite type, zero-dimensional algebraic space over a field is a separated
scheme; its quasi-compact opens are affine, and it is the coproduct of its singleton
components, each the spectrum of a nonzero local Artinian finite-dimensional algebra.
Source: Stacks Project, Tag 06LZ, case (2), and Tag 06LH, locally algebraic case
(blueprint: lem-sfb-zero-dimensional-field-space-components).

Proof:
1. Choose affine étale charts. Their structure maps are locally of finite type and their
   dimensions are at most zero. Quasi-compactness makes them finite type; apply
   lem-pc-algebraic-dim-zero-affine-finite and lem-weil-pbc-finite-type-dim-zero-artinian.
   Factor each chart through its open image by lem-a1-etale-scheme-map-open-image.
2. For a chart U over its open image Y, form R = U ×_Y U. Both projections are étale;
   their composites are charts of X by lem-weil-pbc-etale-composition-cancellation.
   Hence R has dimension at most zero and is locally of finite type over K.
3. The relation map R → U ×_K U is a monomorphism. By def-weil-radicial-morphism its
   point map is injective. The affine fibre product has coordinate ring A ⊗_K A by
   lem-weil-pbc-fibre-product-affine-spectra. This ring is finite-dimensional, Artinian
   by lem-weil-pbc-finite-dim-algebra-artinian, and has finite spectrum by
   lem-sfb-artinian-spectrum-finite. Consequently R has finitely many points.
4. Thus R is quasi-compact and finite type, so lem-pc-algebraic-dim-zero-affine-finite
   makes it affine and finite over K. A K-spanning list also spans its coordinate ring
   over A for either projection. Thus the projections are finite, flat and locally
   finitely presented, hence finite locally free (def-pc-finite-locally-free).
5. Apply lem-a1-finite-flat-affine-relation-quotient to obtain an affine quotient M.
   The local lifts of lem-a1-representable-etale-fppf-local-lifting identify Y with
   the fppf sheafification of U/R; Yoneda (lem-pc-yoneda) identifies it with h_M.
6. These affine open images cover X. The largest schematic open of
   lem-sfb-space-largest-schematic-open therefore has full point image and equals X
   by lem-a1-space-point-open-calculus. This gives the representing K-scheme.
7. A quasi-compact open is again locally finite type, and its dimension is at most
   zero by lem-weil-pbc-open-subspace-dimension-monotone. Apply
   lem-pc-algebraic-dim-zero-affine-finite to make it affine. Each affine chart is
   discrete by lem-weil-pbc-finite-type-dim-zero-artinian, so X is discrete.
8. The singleton open at x is quasi-compact, hence Spec A_x finite over K. Its ring
   is nonzero, finite-dimensional and Artinian (lem-weil-pbc-finite-dim-algebra-artinian).
   Its unique prime ideal is its unique maximal ideal, so A_x is local.
9. The singleton inclusions exhibit X as their coproduct by
   lem-weil-pbc-scheme-coproduct-family and lem-weil-pbc-scheme-morphism-gluing.
   Their ranges are precisely the one-point connected components. The index set may
   be empty or infinite.
10. Apply lem-weil-pbc-separated-affine-cover-criterion to the singleton cover over
    Spec Z. Distinct members have empty overlap, whose section ring is zero. A member's
    self-overlap has the surjective multiplication map A_x ⊗_Z A_x → A_x, since
    a is the image of a ⊗ 1. This proves absolute separatedness. -/
theorem zeroDimensional_fieldSpace_components {K : Type u} [Field K]
    (X : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hft : ∀ (U : Over (Spec (CommRingCat.of K)))
      (p : yoneda.obj U ⟶ X.obj.obj), IsEtale p → LocallyOfFiniteType U.hom)
    (hdim : ∀ (U : Over (Spec (CommRingCat.of K)))
      (p : yoneda.obj U ⟶ X.obj.obj), IsEtale p →
        ∀ v : U.left, (⨅ (W : U.left.Opens) (_ : v ∈ W), topologicalKrullDim W) ≤ 0) :
    ∃ Y : Over (Spec (CommRingCat.of K)),
      Nonempty (yoneda.obj Y ≅ X.obj.obj) ∧
      IsClosedImmersion (prod.lift (𝟙 Y.left) (𝟙 Y.left)) ∧
      (∀ V : Y.left.Opens, IsCompact (V : Set Y.left) → IsAffine V.toScheme) ∧
      ∃ (I : Type u) (A : I → CommAlgCat.{u} K)
        (ι : ∀ i : I, Spec (CommRingCat.of (A i)) ⟶ Y.left),
        Nonempty (IsColimit (Cofan.mk Y.left ι)) ∧
        (∀ i : I,
          Nontrivial (A i) ∧ IsLocalRing (A i) ∧ IsArtinianRing (A i) ∧
          FiniteDimensional K (A i) ∧
          ι i ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K (A i))) ∧
          IsOpenImmersion (ι i) ∧ IsClosed (Set.range (ι i)) ∧
          Subsingleton (Spec (CommRingCat.of (A i)))) ∧
        ∀ x : Y.left, ∃! i : I, Set.range (ι i) = connectedComponent x := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
