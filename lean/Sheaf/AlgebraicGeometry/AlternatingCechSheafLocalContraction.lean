/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSheafConstruction
public import Sheaf.AlgebraicGeometry.TensorPullback

/-! # Local contraction of the increasing-tuple sheaf augmentation

Source: Stacks Project, Tag 01FM, alternating faces; local contraction paragraph of
lem-pc-s3-affine-alternating-cech-augmented-construction.
(blueprint: lem-pc-s3-alternating-cech-sheaf-local-contraction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The explicit sheaf augmentation is a quasi-isomorphism, also after tensor pullback.
Source: Stacks Project, Tag 01FM, signed ordered faces, and the local contraction
paragraph of lem-pc-s3-affine-alternating-cech-augmented-construction.
(blueprint: lem-pc-s3-alternating-cech-sheaf-local-contraction).

Proof: Restrict the augmented complex to U_i. Its term at a tuple t has sections of
G on V intersect U_i intersect the opens of t. Insert i into t in its unique ordered
position, with sign (-1) to that position, and set the operator to zero if i occurs
already. This is linear over O(V) and commutes with restrictions of V. In degree zero
the contracting map to G is the projection to the singleton i. In the differential
homotopy identity the face deleting the inserted i has coefficient one and returns
the original tuple. For each other face, deleting that face before inserting i and
after inserting i produces the same restriction composite with opposite coefficients.
If i occurs already, only its deletion contributes to the identity. Thus the augmented
complex is split contractible on U_i, including its degree-zero augmentation. Restrict
along p to p inverse U_i; tensor pullback commutes with restriction to these opens.
Apply the additive tensor pullback to the local homotopy identities. It preserves
finite sums, integer multiples, composition and identities, so the pulled-back
augmentation is again a local homotopy equivalence, without assuming flatness.
The U_i and their inverse images cover. Homology of module sheaf complexes is local,
so both augmentations are quasi-isomorphisms. Extension by zero from natural to integer
degrees preserves the homotopy identities and adds only zero terms. If r=0 the cover
condition makes X empty; Y is empty as it maps to X, and all these module sheaves are zero. -/
theorem alternatingCechSheafAugmentation_quasiIso
    {X Y : Scheme.{u}} (p : Y ⟶ X)
    [(Scheme.Modules.tensorPullback p).Additive]
    {r : ℕ} (U : Fin r → X.Opens) (hU : iSup U = ⊤) (G : X.Modules) :
    QuasiIso (alternatingCechSheafAugmentation U G) ∧
      QuasiIso (((Scheme.Modules.tensorPullback p).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (HomologicalComplex.extendMap
          (alternatingCechSheafAugmentation U G) ComplexShape.embeddingUpNat)) := by sorry

end AlgebraicGeometry
