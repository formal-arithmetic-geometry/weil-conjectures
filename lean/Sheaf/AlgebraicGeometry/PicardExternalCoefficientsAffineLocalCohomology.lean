/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

public import Sheaf.Topology.OpenModuleCohomology

/-! # Affine-local cohomology of external coefficients

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, acyclic base case.
(blueprint: lem-sc-picard-external-coefficients-affine-local-cohomology).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- Cohomology of external coefficients over an inverse-image affine open is the
tensor product of cohomology of F with sections of G. No acyclicity is required.
Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, paragraph
"Let V be an affine open".
(blueprint: lem-sc-picard-external-coefficients-affine-local-cohomology).

Proof: Choose a finite affine cover U_i of X. Affine diagonal makes its finite
nonempty intersections affine. The inverse image of V under the second projection
is X times V, covered by U_i times V, whose intersections are affine. Restricting
the external coefficient to this product agrees with the external coefficient of
F and G restricted to V, by the pullback adjunction units and tensor restriction.
The affine fibre-product, pullback-section and tensor-section formulas identify
its Cech complex with Cech(U,F) tensor_k G(V). On pure tensors these formulas commute
with restrictions, so they identify the differentials as well. Finite products
commute with tensor; over the field k tensor is exact, and therefore commutes with
cohomology. Affine Cech comparison identifies the result in degree q with
H^q(X,F) tensor_k G(V). Restriction of an injective resolution identifies
this cohomology with openModuleCohomology on the original product. The scalarObj
on the right is G restricted to V, evaluated at its top open; restriction of
scalars along V -> Y -> Spec k gives its k-vector-space structure. Empty X or V
and zero coefficients give zero complexes, so are included. -/
theorem picardExternalCupCoefficients_affine_local_cohomology
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [IsAffineHom (pullback.diagonal f)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (V : Y.Opens) (hV : IsAffineOpen V) (q : ℕ) :
    Nonempty
      (((RingedSpace.openModuleCohomology (Limits.pullback f g).toRingedSpace q
        ((pullback.snd f g) ⁻¹ᵁ V)).obj (externalCupCoefficients f g F G)) ≅
        AddCommGrpCat.of (scalarCohomology f F q ⊗[k]
          scalarObj (V.ι ≫ g) (G.restrict V.ι) (Opposite.op ⊤))) := by sorry

end AlgebraicGeometry.Scheme.Modules
