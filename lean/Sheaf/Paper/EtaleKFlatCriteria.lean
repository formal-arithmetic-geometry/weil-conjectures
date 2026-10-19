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
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

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

private lemma acyclic_colimit
    {D I : Type*} [Category* D] [Abelian D] [Category* I]
    [HasColimitsOfShape I D] [HasExactColimitsOfShape I D]
    (F : I ⥤ CochainComplex D ℤ) (hF : ∀ j, (F.obj j).Acyclic) :
    (colimit F).Acyclic := by
  intro i
  let S : ShortComplex (I ⥤ D) :=
    (ShortComplex.functorEquivalence I D).inverse.obj
      (F ⋙ HomologicalComplex.shortComplexFunctor D (.up ℤ) i)
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
    intro j
    exact IsZero.of_iso ((hF j i).isZero_homology)
      (S.mapHomologyIso ((CategoryTheory.evaluation I D).obj j)).symm
  exact colim.exact_mapShortComplex hS
    (isColimitOfPreserves (HomologicalComplex.eval D (.up ℤ) ((ComplexShape.up ℤ).prev i))
      (colimit.isColimit F))
    (isColimitOfPreserves (HomologicalComplex.eval D (.up ℤ) i)
      (colimit.isColimit F))
    (isColimitOfPreserves (HomologicalComplex.eval D (.up ℤ) ((ComplexShape.up ℤ).next i))
      (colimit.isColimit F))
    ((colimit F).d _ i) ((colimit F).d i _)
    (fun j ↦ (colimit.ι F j).comm _ _) (fun j ↦ (colimit.ι F j).comm _ _)

set_option synthInstance.maxSize 512 in
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
  let R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
    (CommRingCat.of Λ)
  let M := SheafOfModules.{u + 1}
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  have hbounded (P : CochainComplex M ℤ)
      (hb : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (P.X n))
      (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := T.smallEtaleTopology) (R := R) (P.X n)) :
      CochainComplex.IsAcyclicTensorKFlat (R := R) P := by
    obtain ⟨b, hb⟩ := hb
    have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).mpr hb
    exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
      R P b hf
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  have (N : M) : PreservesColimitsOfSize.{u + 1, u + 1}
      (MonoidalCategory.tensorLeft N) :=
    SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R N
  have (N : M) : PreservesColimitsOfSize.{0, 0}
      (MonoidalCategory.tensorLeft N) :=
    preservesColimitsOfSize_shrink (MonoidalCategory.tensorLeft N)
  have htriangle : ∀ (Δ : Triangle (HomotopyCategory M (.up ℤ)))
      (K₁ K₂ K₃ : CochainComplex M ℤ),
      Δ ∈ distTriang (HomotopyCategory M (.up ℤ)) →
      Nonempty (Δ.obj₁ ≅ (HomotopyCategory.quotient M (.up ℤ)).obj K₁) →
      Nonempty (Δ.obj₂ ≅ (HomotopyCategory.quotient M (.up ℤ)).obj K₂) →
      Nonempty (Δ.obj₃ ≅ (HomotopyCategory.quotient M (.up ℤ)).obj K₃) →
      (K₁.IsAcyclicTensorKFlat ∧ K₂.IsAcyclicTensorKFlat → K₃.IsAcyclicTensorKFlat) ∧
      (K₁.IsAcyclicTensorKFlat ∧ K₃.IsAcyclicTensorKFlat → K₂.IsAcyclicTensorKFlat) ∧
      (K₂.IsAcyclicTensorKFlat ∧ K₃.IsAcyclicTensorKFlat → K₁.IsAcyclicTensorKFlat) := by
    intro Δ K₁ K₂ K₃ hΔ ⟨e₁⟩ ⟨e₂⟩ ⟨e₃⟩
    have htest (A : CochainComplex M ℤ) :
        ((A.mapBifunctor K₁ (MonoidalCategory.curriedTensor M)).Acyclic ∧
          (A.mapBifunctor K₂ (MonoidalCategory.curriedTensor M)).Acyclic →
          (A.mapBifunctor K₃ (MonoidalCategory.curriedTensor M)).Acyclic) ∧
        ((A.mapBifunctor K₁ (MonoidalCategory.curriedTensor M)).Acyclic ∧
          (A.mapBifunctor K₃ (MonoidalCategory.curriedTensor M)).Acyclic →
          (A.mapBifunctor K₂ (MonoidalCategory.curriedTensor M)).Acyclic) ∧
        ((A.mapBifunctor K₂ (MonoidalCategory.curriedTensor M)).Acyclic ∧
          (A.mapBifunctor K₃ (MonoidalCategory.curriedTensor M)).Acyclic →
          (A.mapBifunctor K₁ (MonoidalCategory.curriedTensor M)).Acyclic) := by
      let G := ((MonoidalCategory.curriedTensor M).bifunctorMapHomotopyCategory
        (.up ℤ) (.up ℤ) (.up ℤ)).obj ((HomotopyCategory.quotient M (.up ℤ)).obj A)
      let P := HomotopyCategory.subcategoryAcyclic M
      have hd := G.map_distinguished Δ hΔ
      have h₁ : P (G.obj Δ.obj₁) ↔
          (A.mapBifunctor K₁ (MonoidalCategory.curriedTensor M)).Acyclic := by
        exact (P.prop_iff_of_iso (G.mapIso e₁)).trans
          (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)
      have h₂ : P (G.obj Δ.obj₂) ↔
          (A.mapBifunctor K₂ (MonoidalCategory.curriedTensor M)).Acyclic := by
        exact (P.prop_iff_of_iso (G.mapIso e₂)).trans
          (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)
      have h₃ : P (G.obj Δ.obj₃) ↔
          (A.mapBifunctor K₃ (MonoidalCategory.curriedTensor M)).Acyclic := by
        exact (P.prop_iff_of_iso (G.mapIso e₃)).trans
          (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)
      exact ⟨fun h ↦ h₃.mp (P.ext_of_isTriangulatedClosed₃ _ hd (h₁.mpr h.1) (h₂.mpr h.2)),
        fun h ↦ h₂.mp (P.ext_of_isTriangulatedClosed₂ _ hd (h₁.mpr h.1) (h₃.mpr h.2)),
        fun h ↦ h₁.mp (P.ext_of_isTriangulatedClosed₁ _ hd (h₂.mpr h.1) (h₃.mpr h.2))⟩
    exact ⟨fun h A hA ↦ (htest A).1 ⟨h.1 A hA, h.2 A hA⟩,
      fun h A hA ↦ (htest A).2.1 ⟨h.1 A hA, h.2 A hA⟩,
      fun h A hA ↦ (htest A).2.2 ⟨h.1 A hA, h.2 A hA⟩⟩
  have hfiltered (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (F : I ⥤ CochainComplex M ℤ) (hF : ∀ i, (F.obj i).IsAcyclicTensorKFlat) :
      (colimit F).IsAcyclicTensorKFlat := by
    have : HasExactColimitsOfShape I M :=
      HasExactColimitsOfShape.domain_of_functor I (SheafOfModules.toSheaf _)
    intro A hA
    let G := ((MonoidalCategory.curriedTensor M).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)).obj A
    have hcol : (colimit (F ⋙ G)).Acyclic :=
      acyclic_colimit (F ⋙ G) (fun i ↦ hF i A hA)
    intro i
    exact (hcol i).of_iso (preservesColimitIso G F).symm
  refine ⟨hbounded, htriangle, ?_, hfiltered, ?_⟩
  · intro K₁ K₂ f h₁ h₂
    exact (htriangle _ K₁ K₂ (CochainComplex.mappingCone f)
      (HomotopyCategory.mappingCone_triangleh_distinguished f)
      ⟨Iso.refl _⟩ ⟨Iso.refl _⟩ ⟨Iso.refl _⟩).1 ⟨h₁, h₂⟩
  · intro I _ _ F hF
    exact hfiltered I F (fun i ↦ hbounded _ (hF i).1 (hF i).2)

end AlgebraicGeometry.Scheme
