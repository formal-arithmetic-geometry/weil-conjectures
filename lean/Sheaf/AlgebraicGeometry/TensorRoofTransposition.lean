/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorAugmentation
public import Sheaf.Algebra.Homology.DerivedInternalHom
import Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction
import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
import Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel
import Sheaf.Algebra.Homology.HomComplexRestrictOpen
import Sheaf.Paper.DerivedInternalHomRestrictOpen

/-! # Transposing a supplied augmented complex after open restriction

Source: Stacks Project, Tags 08DJ, 08DL and 08EH.
(blueprint: lem-sc-tensor-roof-transposition).
-/

@[expose] public section

set_option autoImplicit false

universe uX wD

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 512 in
/-- Tensor-Hom transposition converts a supplied section representative into a map
from the total tensor model. The augmentation and its representative are inputs;
no affine hypothesis, quasi-coherence, or existence of a perfect roof is asserted.

Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DL; perfect.tex, Tag 08EH,
construction of the two maps and the restriction identity.
(blueprint: lem-sc-tensor-roof-transposition).

Proof:
1. The unit-tensor-Hom adjunction on U and the canonical restriction comparison
   for RHom identify Hom(R(Q(O_X[0])),R(RHom(A,E))) with Hom(R(A),R(E)).
   Use the tensor-unit comparison for restriction and the right unitor. This is
   the equivalence e, fixed by the canonical adjunction, rather than an arbitrary
   isomorphism between the objects supplied by restriction of RHom.
2. For a supplied K-flat J, transpose ξ:J→RHom(A,E) under the canonical derived
   tensor-Hom adjunction. The K-flat comparison identifies A tensor^L Q(J) with
   Q(Tot(P tensor J)), using eA on the first factor. Transport the transpose
   through this comparison to obtain γ.
3. Restriction is exact and preserves K-flat complexes and total tensors. The
   augmentation on the restricted total tensor identifies with id_R(A) tensor
   R(Q(u)), followed by the right unitor. Hence its image is invertible when
   R(Q(u)) is invertible; the chain right unitor and eA are also invertible.
4. The representative tensor-Hom adjunction commutes with restriction, since its
   evaluation maps on tensor summands are the same sheaf maps after restriction.
   Apply its naturality in J to R(Q(u))≫s=R(ξ). The unit adjunction and right-unitor
   identity give R(β)≫e(s)=R(γ), with β exactly the chain formula below.
   The zero complex and empty open satisfy the same identities. -/
theorem tensor_roof_transposition
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (A E : schemeDerivedCategory X)
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (eA : DerivedCategory.Q.obj P ≅ A) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let T := HomologicalComplex.tensorUnit
      (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    let H := (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf).obj (op A, E)
    ∃ e : (R.obj (DerivedCategory.Q.obj T) ⟶ R.obj H) ≃ (R.obj A ⟶ R.obj E),
      ∀ (J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
        (hJ : CochainComplex.IsKFlat (R := X.sheaf) J) (u : J ⟶ T),
        IsIso (R.map (DerivedCategory.Q.map u)) →
        ∀ (ξ : DerivedCategory.Q.obj J ⟶ H)
          (s : R.obj (DerivedCategory.Q.obj T) ⟶ R.obj H),
          R.map (DerivedCategory.Q.map u) ≫ s = R.map ξ →
          let B := DerivedCategory.Q.obj (CochainComplex.mapBifunctor P J (curriedTensor _))
          let β : B ⟶ A := DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _)
              (ComplexShape.up ℤ)) ≫
            DerivedCategory.Q.map (HomologicalComplex.rightUnitor P).hom ≫ eA.hom
          ∃ γ : B ⟶ E, IsIso (R.map β) ∧ R.map β ≫ e s = R.map γ := by sorry

end AlgebraicGeometry.Scheme
