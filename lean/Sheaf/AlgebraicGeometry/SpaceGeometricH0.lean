/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.SpaceProperFieldGlobalFunctions

/-! # Universal functions for reduced connected geometric fibres of algebraic spaces

Source: Stacks Project, Spaces Perfect, Tag 0E0S,
lemma-proper-flat-geom-red-connected (blueprint: lem-sfb-space-geometric-h0).

The geometric fibre is the sheaf fibre product with an algebraically closed field point.
Reducedness is tested on all representable étale scheme charts. Connectedness uses the
atlas topology on field-valued point classes and includes nonemptiness.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical structure map is an isomorphism, universally, for a proper flat finitely
presented algebraic-space morphism with reduced nonempty connected geometric fibres.
The base-change projection below is the second projection of the actual sheaf pullback,
using the existing `enlargedFibreProduct` construction.

Source: Stacks Project, Spaces Perfect, Tag 0E0S,
lemma-proper-flat-geom-red-connected (blueprint: lem-sfb-space-geometric-h0).

Proof:
1. For every field-valued point u : Spec k → Y, form the algebraic-space fibre X_u
   using lem-trf-space-fibre-products-etale-covers. It is proper, flat and finitely
   presented by lem-sfb-space-flat-proper-fp-locality.
2. For every algebraically closed extension Omega/k, associativity of sheaf pullbacks
   identifies (X_u)_Omega with X ×_Y Spec Omega. The geometric hypothesis says this
   fibre is reduced, nonempty and connected. Apply
   lem-sfb-space-proper-field-global-functions to conclude that the canonical map
   k → Gamma(X_u, O) is an isomorphism.
3. Apply lem-sfb-space-proper-flat-h0-criterion to all the field-valued points at once.
   Its remaining hypotheses are precisely properness, flatness and finite presentation
   of f. It gives both the original canonical structure-map isomorphism and the same
   canonical isomorphism after every algebraic-space base change T → Y. -/
theorem isIso_moduleStructureMap_of_geometricFibres_reduced_connected
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hp : MapIsProper f) (hf : MapIsFlat f)
    (hfp : MapIsLocallyOfFinitePresentation f ∧ MapIsQuasiCompact f.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (b : Spec (CommRingCat.of Ω) ⟶ S)
      (y : yoneda.obj (Over.mk b) ⟶ Y.obj.obj),
      (∀ T : CostructuredArrow yoneda (Limits.pullback f.hom.hom y),
        IsEtale T.hom → AlgebraicGeometry.IsReduced T.left.left) ∧
      ConnectedSpace (Point (Limits.pullback f.hom.hom y))) :
    IsIso (moduleStructureMap f) ∧
      ∀ (T : AlgebraicSpace S) (g : T ⟶ Y),
        IsIso (moduleStructureMap
          (ObjectProperty.homMk (Limits.pullback.snd f.hom g.hom) :
            enlargedFibreProduct f g ⟶ T)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
