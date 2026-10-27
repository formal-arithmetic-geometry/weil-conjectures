/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteEtaleSource
import Sheaf.AlgebraicGeometry.SpaceInvariantOpenQuotient
import Sheaf.AlgebraicGeometry.SpaceLqfAtlasRefinement
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.QuasiFiniteLocusOpen
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The quasi-finite locus of an algebraic space over a scheme

Source: Stacks Project, Morphisms of Spaces, Tag 04NW
(blueprint: lem-sfb-space-quasifinite-locus-open).

The target scheme is an object of `Over S`, where `S` is an ambient base. This permits
all scheme base changes while keeping the presheaves on one fixed site. The pointwise
predicate is also defined on presheaves, so it applies directly to the sheaf fibre product.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A map to a scheme is quasi-finite at a point when every lift of that point in every
representable étale scheme chart is quasi-finite for the composite scheme morphism.
The scheme predicate includes the finite-type requirement of Stacks Tag 01TD.
Source: Stacks Project, Morphisms of Spaces, Tag 04NW, with the scheme-chart criterion
from Tag 0ABM (blueprint: lem-sfb-space-quasifinite-locus-open). -/
def MapToSchemeQuasiFiniteAt {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T : Over S} (h : F ⟶ yoneda.obj T) (x : Point F) : Prop :=
  ∀ (U : Over S) (a : yoneda.obj U ⟶ F), IsEtale a →
    ∀ z : U.left, schemePointMap a z = x →
      Scheme.Hom.IsQuasiFiniteAtPoint (yoneda.preimage (a ≫ h)).left z

/-- For a locally finite type map from an algebraic space to a scheme, the quasi-finite
locus is open, is the point image of an open subspace, and commutes with every scheme
base change. Open-subspace inclusions are representable by open immersions on all scheme
tests, by `OpenSubspace`.
Source: Stacks Project, Morphisms of Spaces, Tag 04NW
(blueprint: lem-sfb-space-quasifinite-locus-open).

Proof:
1. Choose a representable surjective étale atlas p : U → E (def-trf-algebraic-space).
   Its composite to T is locally of finite type by hft. By
   lem-sc-quasi-finite-points-open its scheme quasi-finite locus V is open and locally
   quasi-finite over T. Its point image O in E is open by lem-a1-space-point-open-calculus.
2. For any representable étale chart A → E, form W = V ×_E A using
   lem-trf-space-fibre-products-etale-covers. Both projections are étale and the image
   in A is A_O, by lem-a1-space-point-open-calculus. Restricting the second projection
   to A_O is surjective étale (lem-a1-etale-open-restriction). Apply both directions of
   lem-a1-scheme-lqf-etale-source-locality to see A_O is locally quasi-finite over T.
   Its affine witnesses are affine opens in A, so pqf-def-quasifinite proves O ⊆ Q_h.
   Conversely every atlas lift of a point of Q_h belongs to V. Atlas surjectivity gives
   Q_h ⊆ O and also p⁻¹(Q_h) = V.
3. Apply lem-a1-space-invariant-open-quotient to this open subset. It gives an open
   subspace J with point image Q_h, whose inclusion is representable by open immersions.
4. For arbitrary b : T' → T, lem-a1-space-lqf-atlas-refinement supplies the pulled-back
   surjective étale atlas U' → E'. Its composite to T' is locally of finite type by
   lem-weil-pbc-lft-base-change. Repeat steps 1 and 2 to identify the inverse image of
   Q_h' in U' with the scheme quasi-finite locus V'. By
   lem-sfb-scheme-quasifinite-at-base-change, V' is the inverse image of V in U'.
   Surjectivity on points of U' → E' gives the asserted equality of subsets of |E'|.
   The inclusion criterion of lem-a1-space-point-open-calculus also identifies the
   corresponding open subspaces after base change. No separation or compactness is used. -/
theorem isOpen_mapToSchemeQuasiFiniteAt {S : Scheme.{u}} (T : Over S)
    (E : AlgebraicSpace S) (h : E.obj.obj ⟶ yoneda.obj T)
    (hft : MapToSchemeIsLocally (@LocallyOfFiniteType) E T h) :
    IsOpen {x : Point E.obj.obj | MapToSchemeQuasiFiniteAt h x} ∧
      (∃ J : OpenSubspace E,
        pointImage J.val.ι = {x : Point E.obj.obj | MapToSchemeQuasiFiniteAt h x}) ∧
      ∀ (T' : Over S) (b : T' ⟶ T),
        mapPoint (Limits.pullback.fst h (yoneda.map b)) ⁻¹'
            {x : Point E.obj.obj | MapToSchemeQuasiFiniteAt h x} =
          {x : Point (Limits.pullback h (yoneda.map b)) |
            MapToSchemeQuasiFiniteAt (Limits.pullback.snd h (yoneda.map b)) x} := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
