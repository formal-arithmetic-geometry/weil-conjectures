/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.AlgebraicGeometry.EtaleFieldGeometricAction
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.FieldTheory.EtaleFieldGaloisClassification

/-!
# Local realization of equivariant geometric-point maps

Source: Stacks Project, Tag 03QR.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- An equivariant geometric-point map is realized on a neighbourhood of each source point.
Source: Stacks Project, Tag 03QR, finite-spectrum classification in the equivalence proof
(blueprint: lem-exc-etale-field-point-map-local).

Proof: Take the singleton open U at the given point. By the étale fibre decomposition
it is Spec L for a finite separable K-extension L. Its geometric points identify with
K-embeddings L → Ksep and form a nonempty transitive Galois set. Equivariance makes
their images lie in one orbit, hence in the singleton open Spec L' of the target.
The finite Galois classification gives a K-algebra homomorphism L' → L whose map on
embeddings is exactly the restriction of the given equivariant map. Apply Spec,
transport through the singleton-open isomorphisms, and compose with the target open
immersion. This gives f, its equality over Spec K, and the displayed identity for
every geometric point of U. There is no source point to consider for an empty source;
if the target is empty, existence of the given map excludes any nonempty source. -/
theorem etaleFieldPointMap_local
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (X Y : Scheme.Etale (Spec (CommRingCat.of K)))
    (φ : etaleFieldGeometricAction K Ksep X ⟶ etaleFieldGeometricAction K Ksep Y)
    (x : X.left) :
    ∃ U : X.left.Opens, x ∈ U ∧ ∃ f : U.toScheme ⟶ Y.left,
      f ≫ Y.hom = U.ι ≫ X.hom ∧
        ∀ (p : Spec (CommRingCat.of Ksep) ⟶ U.toScheme)
          (hp : p ≫ (U.ι ≫ X.hom) = (etaleFieldBasePoint K Ksep).hom),
          p ≫ f = (φ.hom (Over.homMk (p ≫ U.ι) (by simpa using hp))).left := by sorry

end AlgebraicGeometry
