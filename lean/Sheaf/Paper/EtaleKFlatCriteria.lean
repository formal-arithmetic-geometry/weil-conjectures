/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.KFlatTensorConeTwoOutOfThree
import Sheaf.Algebra.Homology.FilteredColimitsTensor

/-!
# K-flat criteria on the small étale site

Source: Stacks Project, Cohomology on Sites, Tags 06YQ, 07A3 and 06YR;
Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`
(blueprint: lem-kun-kflat-criteria).

The module category is that of modules over the sheafified constant commutative ring.
The existing ringed-site `IsAcyclicTensorKFlat` uses the direct-sum total tensor with Koszul signs;
signed symmetry identifies its acyclic test with the convention of def-kun-derived-tensor.
No derived category or derived-category distinguished triangle is used in the criteria.
The category `T.Etale` is small in the chosen coefficient universe `u + 1`, so passing
through its small model changes neither its sheaves nor these assertions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

/-- The three K-flat criteria and their cone and filtered-flat corollaries on the small
étale site. Source: Stacks Project, Tags 06YQ, 07A3 and 06YR
(blueprint: lem-kun-kflat-criteria).

Proof:
1. Apply lem-pc-bounded-above-flat-kflat-site to the constant ring sheaf on the
small étale site. Its only mathematical hypotheses are an upper degree bound and
exactness of tensor with every term; no lower bound is required.
2. For a cone triangle, tensor with an arbitrary acyclic complex. The two K-flat
terms give acyclic tensors, and lem-pc-kflat-tensor-cone-two-out-of-three gives the
third. The signed symmetry x tensor y maps to (-1)^(pq) y tensor x, reconciling the
left and right acyclic-test conventions. This also proves the explicit cone clause.
3. A distinguished homotopy-category triangle is isomorphic to a cone triangle by
lem-pur-homotopy-category-triangulated. K-flatness is invariant under homotopy
isomorphism: on A^p tensor K^q a homotopy h acts as (-1)^p (1 tensor h).
In dH + Hd the terms involving d_A cancel, leaving 1 tensor (dh + hd).
Thus tensor preserves homotopy equivalences and their induced cohomology
isomorphisms. Transfer the cone criterion along the three object isomorphisms;
all three choices of the pair of K-flat terms are included.
4. For any small filtered diagram, lem-pc-module-filtered-colimits-tensor commutes
the direct-sum total tensor with its degreewise sheaf colimit and makes that
colimit exact. For acyclic tensors C_i, the exact sequences from cycles in degree
n to C_i^n to cycles in degree n+1 remain exact after colimit. Hence image and
kernel of each colimit differential agree, and the colimit tensor is acyclic.
This proves K-flatness of the colimit. Apply the first criterion to every term
to obtain the last corollary; the upper bound may depend on the diagram object.

The three complexes in the triangle clause are arbitrary representatives of its
objects, identified by homotopy-category isomorphisms. No choices of representatives
or extra hypotheses on its arrows are imposed. -/
theorem etale_kflat_criteria (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    (∀ P : CochainComplex
      (SheafOfModules.{u + 1}
        ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)))) ℤ,
      (∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (P.X n)) →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := T.smallEtaleTopology) (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) (P.X n)) →
      CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) P) ∧
    (∀ (Δ : Triangle (HomotopyCategory (SheafOfModules.{u + 1}
        ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)))) (ComplexShape.up ℤ)))
      (K₁ K₂ K₃ : CochainComplex (SheafOfModules.{u + 1}
        ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)))) ℤ),
      Δ ∈ distTriang (HomotopyCategory (SheafOfModules.{u + 1}
        ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)))) (ComplexShape.up ℤ)) →
      Nonempty (Δ.obj₁ ≅ (HomotopyCategory.quotient (SheafOfModules.{u + 1}
        ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)))) (ComplexShape.up ℤ)).obj K₁) →
      Nonempty (Δ.obj₂ ≅ (HomotopyCategory.quotient (SheafOfModules.{u + 1}
        ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)))) (ComplexShape.up ℤ)).obj K₂) →
      Nonempty (Δ.obj₃ ≅ (HomotopyCategory.quotient (SheafOfModules.{u + 1}
        ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)))) (ComplexShape.up ℤ)).obj K₃) →
      (CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) K₁ ∧ CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) K₂ →
        CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) K₃) ∧
      (CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) K₁ ∧ CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) K₃ →
        CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) K₂) ∧
      (CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) K₂ ∧ CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) K₃ →
        CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) K₁)) ∧
    (∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u + 1}
        ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)))) ℤ) (f : K₁ ⟶ K₂),
      CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) K₁ → CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) K₂ →
      CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) (CochainComplex.mappingCone f)) ∧
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (F : I ⥤ CochainComplex (SheafOfModules.{u + 1}
        ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)))) ℤ),
      (∀ i : I, CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) (F.obj i)) →
      CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) (colimit F)) ∧
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (F : I ⥤ CochainComplex (SheafOfModules.{u + 1}
        ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)))) ℤ),
      (∀ i : I, (∃ b : ℤ, ∀ n : ℤ, b < n → IsZero ((F.obj i).X n)) ∧
        ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := T.smallEtaleTopology) (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) ((F.obj i).X n)) →
      CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) (colimit F)) := by
  sorry

end AlgebraicGeometry.Scheme
