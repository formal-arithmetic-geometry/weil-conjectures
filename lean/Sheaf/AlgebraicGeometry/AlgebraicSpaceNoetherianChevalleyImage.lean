/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceConstructibleAffineEtaleTest
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Constructible images over Noetherian algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tags 0ECX and 06G4;
Decent Spaces, Tag 0ECZ (blueprint: lem-sfb-noetherian-space-chevalley-image).

The Noetherian target hypotheses are compactness, absolute quasi-separatedness, and
local Noetherianity of every representable étale scheme chart. Morphism properties
and the map on point classes use the existing algebraic-space interfaces.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated finite-type morphism to a Noetherian algebraic space sends constructible
subsets to constructible subsets; in particular its full point image is constructible.
Source: Stacks Project, Morphisms of Spaces, Tags 0ECX (theorem-chevalley) and 06G4;
Decent Spaces, Tag 0ECZ (blueprint: lem-sfb-noetherian-space-chevalley-image).

Proof:
1. For an affine étale chart `V → Z`, form `W = Y ×_Z V` using
lem-trf-space-fibre-products-etale-covers. Quasi-compactness of `f` makes its point space
compact, and `W → Y` is representable étale by the scheme-test definition.
2. Refine a scheme atlas of `W` by disjoint affine opens. Open immersions and composites
are étale by lem-weil-pbc-etale-composition-cancellation. By
lem-a1-space-finite-affine-subatlas, finitely many affine charts `Uᵢ → W` cover it.
The maps `Uᵢ → V` are locally of finite type by the compatible-chart hypothesis on `f`.
3. The scheme `V` is locally Noetherian, so each `Uᵢ` and its étale charts are locally
Noetherian by pqf-lem-locnoeth-lft. Affine compactness
(lem-weil-pbc-affine-scheme-qcqs) and lem-sfb-noetherian-space-topology give Noetherian
atlas point spaces. Identify these with the ordinary scheme spaces by residue-field
factorization (lem-weil-pbc-morphism-from-spec-field) and the identity-chart topology
criterion (def-a1-algebraic-space-point-classes, def-a1-space-point-topology).
The maps to `Y` are continuous by lem-a1-space-point-open-calculus. Pulling back a finite
union of locally closed sets therefore gives a constructible subset of each `Uᵢ`, by
def-weil-constructible-subset and Noetherianity.
4. By pqf-lem-lft-fp-locnoeth, each `Uᵢ → V` is locally finitely presented. Maps between
affine schemes are quasi-compact: inverse images of principal opens are affine, and a
compact open has a finite principal-open cover. Since `V` is affine and qcqs, apply
lem-weil-pbc-chevalley-constructible-image to the pulled-back constructible subsets.
5. Point lifting for fibre products and the jointly surjective charts
(lem-a1-space-point-open-calculus) identify the preimage of the desired image in `V`
with the finite union of these scheme images, which is constructible.
6. By lem-sfb-space-constructible-affine-etale-test and the compact, quasi-separated
target hypotheses, the original image is constructible. The whole source is
constructible (def-weil-constructible-subset); applying the first assertion to it gives
the full-image assertion. Empty spaces, empty finite chart families, and empty subsets
are covered by the same argument. -/
theorem isConstructible_image_of_noetherian {S : Scheme.{u}} (Y Z : AlgebraicSpace S)
    (f : Y ⟶ Z) (hqc : CompactSpace (Point Z.obj.obj))
    (hqs : IsAbsolutelyQuasiSeparated Z)
    (hnoeth : ∀ (U : Over S) (a : yoneda.obj U ⟶ Z.obj.obj),
      IsEtale a → IsLocallyNoetherian U.left)
    (hsep : MapIsSeparated f) (hft : MapIsFiniteType f) :
    (∀ A : Set (Point Y.obj.obj), Topology.IsConstructible A →
      Topology.IsConstructible (mapPoint f.hom.hom '' A)) ∧
    Topology.IsConstructible (Set.range (mapPoint f.hom.hom)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
