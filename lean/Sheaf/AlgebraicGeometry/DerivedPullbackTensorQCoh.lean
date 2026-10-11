/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.Algebra.Homology.KFlat

/-! # Derived pullback and tensor preserve quasi-coherent cohomology

Source: Stacks Project, Derived Categories of Schemes, Lemmas 36.3.8 (Tag 08DW), part (1),
and 36.3.9 (Tag 08DX), part (1) (blueprint: lem-pc-derived-pullback-tensor-qcoh).
-/

@[expose] public section

universe uX wD

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The tensor product of sheaves of `𝒪_X`-modules, `SheafOfModules.monoidalCategory X.sheaf`
(def-pc-tensor-complex-sheaves), made a local instance for the total tensor complex below. -/
noncomputable local instance (X : Scheme.{uX}) :
    MonoidalCategory (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

set_option synthInstance.maxSize 256 in
/-- Derived pullback preserves quasi-coherent cohomology, and the derived tensor of two
objects with quasi-coherent cohomology has quasi-coherent cohomology.
There is no derived tensor bifunctor on `D(𝒪_X)`; as in
def-pc-derived-tensor-cohomology-vanishes, `K ⊗^L L` is stated through representatives:
`K ≅ Q(P)` with `P` K-flat (one exists by lem-pc-kflat-resolution) and `L ≅ Q(N)` for any
complex `N` (`Q` is essentially surjective), and then `K ⊗^L L ≅ Q(Tot(P ⊗_{𝒪_X} N))`.
Quantifying over all such `P` and `N` covers every pair `K, L`.
Source: Stacks Project, Tags 08DW(1) and 08DX(1)
(blueprint: lem-pc-derived-pullback-tensor-qcoh).

Proof (the two steps of the node):
1. Quasi-coherence of cohomology is local. Cover X by affine opens U mapping into affine
   opens V of Y. Restriction commutes with derived pullback by clause (1) of
   lem-pc-affine-derived-pullback-tensor-tilde. The equivalence
   lem-pc-affine-qcoh-derived-equivalence represents E restricted to V by an A-module
   complex M. Clause (2) of lem-pc-affine-derived-pullback-tensor-tilde identifies its
   pullback to U = Spec B with the tilde of M tensor^L_A B. This has quasi-coherent
   cohomology by the affine equivalence over B, and the opens U cover X.
2. Cover X by affine opens U = Spec A. Restriction commutes with derived tensor by
   clause (1) of lem-pc-affine-derived-pullback-tensor-tilde. Represent the restrictions
   of K and L by module complexes M and N using lem-pc-affine-qcoh-derived-equivalence.
   Clause (3) of lem-pc-affine-derived-pullback-tensor-tilde identifies their tensor
   with the tilde of M tensor^L_A N. The affine equivalence gives quasi-coherent
   cohomology on U, hence on X. -/
theorem derivedPullback_tensor_preserve_QCoh {X Y : Scheme.{uX}} (f : X ⟶ Y)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings Y.toRingedSpace))] :
    (∀ E : schemeDerivedCategory Y, schemeDerivedQCohProperty Y E →
      schemeDerivedQCohProperty X ((derivedPullback f).obj E)) ∧
    (∀ P N : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsKFlat (R := X.sheaf) P →
      schemeDerivedQCohProperty X (DerivedCategory.Q.obj P) →
      schemeDerivedQCohProperty X (DerivedCategory.Q.obj N) →
        schemeDerivedQCohProperty X
          (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N (curriedTensor _)))) := by
  sorry

end AlgebraicGeometry
