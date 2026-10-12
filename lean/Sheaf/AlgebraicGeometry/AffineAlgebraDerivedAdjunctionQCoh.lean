/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Quasi-coherence in the affine algebra derived adjunction

Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof
(blueprint: lem-sc-affine-algebra-derived-adjunction-qcoh).
-/

@[expose] public section

universe v wX wA

open CategoryTheory

namespace AlgebraicGeometry

/-- Every left adjoint to the canonical affine algebra derived direct image preserves
quasi-coherent cohomology.
Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof
(blueprint: lem-sc-affine-algebra-derived-adjunction-qcoh).

Proof: On affine opens write Y = Spec B and X = Spec A. At a point p above q,
the stalk map of g is A localized at q to A localized at p. The latter is a
localization of the former, so it is flat, and tensor pullback g^* is exact.
Applying this exact functor to kernels and images gives
H^i(Lg^*M) = g^*H^i(M) in every integer degree. No boundedness is used.
Tensor associativity identifies g^*G with the two tensor operations H(G) of
affine_module_correspondence: extend the inverse-image G to the pulled-back
algebra, then extend along its multiplication counit to O_X. The correspondence
says H(G) is quasi-coherent whenever G is. Thus each H^i(Lg^*M) is quasi-coherent.
These statements can be checked on the affine inverse images, which cover X.
The ringed-space derived adjunction supplies Lg^* as a left adjoint to Rg_*.
Uniqueness of left adjoints gives an adjunction-compatible natural isomorphism
from the given L to Lg^*. Apply cohomology and transport quasi-coherence through
this isomorphism to get the result for L. -/
theorem affine_algebra_derived_pullback_preserves_qcoh
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    (L : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) ⥤
      schemeDerivedCategory X)
    (adj : L ⊣ RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)) :
    (∀ M : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))),
      directImageAlgebraDerivedQCohProperty f M →
        schemeDerivedQCohProperty X (L.obj M)) := by sorry

end AlgebraicGeometry
