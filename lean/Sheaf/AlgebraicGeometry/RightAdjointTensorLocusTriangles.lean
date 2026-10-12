/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonNatural
import Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonDiagrams

/-! # The pinned right-adjoint tensor locus is closed under shifts and third triangle objects.

Source: Stacks Project, Tag 0A9U.
(blueprint: lem-sc-right-adjoint-tensor-locus-triangles).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- The pinned right-adjoint tensor locus is closed under shifts and third triangle objects.
Source: Stacks Project, Duality for Schemes, Section 48.8, equation (48.8.0.1),
and Tag 0A9U, first two sentences of proof.
(blueprint: lem-sc-right-adjoint-tensor-locus-triangles).

Proof. Construct the natural comparison by the pinned projection formula and the
two adjunctions as in lem-sc-right-adjoint-tensor-comparison-natural. K-flat derived
pullback and tensorRight are exact and have their canonical shift comparisons.
Derived direct image is exact. Its right adjoint on the quasi-coherent derived
subcategory is exact: transport the shift isomorphism by the adjunction, and test
the resulting triangle by all representable Hom functors. The comparison respects
these shift structures by the monoidal coherence and the two counit identities.
Thus its component on a shift is conjugate to the shift of its component. Transport
along the given ambient isomorphism to obtain the shift clause. For a distinguished
ambient triangle, its quasi-coherent vertices give a triangle in the full subcategory.
Apply both exact functors and the comparison to get a morphism of distinguished
triangles. Transport the first two components along the specified isomorphisms;
they are invertible by membership in the locus. The two-out-of-three lemma for
triangle morphisms makes the third component invertible. Transport to C along the
third isomorphism. Uniqueness of the pinned pf converts these invertibility results
to the displayed existential locus. Zero triangles and shift zero are included. -/
theorem rightAdjointTensorLocus_triangles
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory Z),
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c) :
    let P : ObjectProperty (schemeDerivedQCohCategory Y) := fun K ↦
      ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
          pf.inv = (a.homEquiv _ _)
            ((Functor.Monoidal.μIso (derivedPullback f) K.obj
              ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
              (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
          IsIso ((adj.homEquiv
            ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
              hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
            (ObjectProperty.homMk (pf.hom ≫
              K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))
    (∀ (A : schemeDerivedQCohCategory Y) (n : ℤ), P A →
      ∀ (B : schemeDerivedQCohCategory Y), Nonempty (B.obj ≅ A.obj⟦n⟧) → P B) ∧
    (∀ (A B : schemeDerivedQCohCategory Y), P A → P B →
      ∀ (T : Pretriangulated.Triangle (schemeDerivedCategory Y)),
        T ∈ Pretriangulated.distinguishedTriangles →
        Nonempty (T.obj₁ ≅ A.obj) → Nonempty (T.obj₂ ≅ B.obj) →
        ∀ (C : schemeDerivedQCohCategory Y), Nonempty (T.obj₃ ≅ C.obj) → P C) := by
  dsimp only
  obtain ⟨τ, hτ⟩ := rightAdjointTensorComparison_natural f hRf hO hTensor a c adj
  obtain ⟨hshift, htriangle⟩ :=
    rightAdjointTensorComparison_diagrams f hRf hO hTensor a c adj τ hτ
  have hP (K : schemeDerivedQCohCategory Y) :
      (∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
          pf.inv = (a.homEquiv _ _)
            ((Functor.Monoidal.μIso (derivedPullback f) K.obj
              ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
              (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
          IsIso ((adj.homEquiv
            ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
              hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
            (ObjectProperty.homMk (pf.hom ≫
              K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))) ↔
        IsIso (τ.app K).hom := by
    obtain ⟨pf, hpf, heq⟩ := hτ K
    constructor
    · rintro ⟨pf', hpf', hiso⟩
      have hp : pf' = pf := Iso.ext_inv (hpf'.trans hpf.symm)
      subst pf'
      rw [heq]
      exact (ObjectProperty.isIso_hom_iff _).2 hiso
    · intro hiso
      refine ⟨pf, hpf, ?_⟩
      apply (ObjectProperty.isIso_hom_iff _).1
      rwa [← heq]
  constructor
  · intro A n hA B e
    have : IsIso (τ.app A).hom := (hP A).1 hA
    obtain ⟨eF, ec, heq⟩ := hshift A n B e
    apply (hP B).2
    have : IsIso ((τ.app B).hom ≫ ec.hom) := by
      rw [heq]
      infer_instance
    exact IsIso.of_isIso_comp_right (τ.app B).hom ec.hom
  · intro A B hA hB T hT eA eB C eC
    have : IsIso (τ.app A).hom := (hP A).1 hA
    have : IsIso (τ.app B).hom := (hP B).1 hB
    obtain ⟨T₁, T₂, m, hT₁, hT₂, eF₁, ec₁, eF₂, ec₂, eF₃, ec₃, hm₁, hm₂, hm₃⟩ :=
      htriangle A B C T hT eA eB eC
    have hmiso₁ : IsIso m.hom₁ := by rw [hm₁]; infer_instance
    have hmiso₂ : IsIso m.hom₂ := by rw [hm₂]; infer_instance
    have hmiso₃ : IsIso m.hom₃ :=
      Pretriangulated.isIso₃_of_isIso₁₂ m hT₁ hT₂ hmiso₁ hmiso₂
    apply (hP C).2
    have : IsIso (eF₃.hom ≫ (τ.app C).hom ≫ ec₃.inv) := by
      rw [← hm₃]
      exact hmiso₃
    have : IsIso ((τ.app C).hom ≫ ec₃.inv) :=
      IsIso.of_isIso_comp_left eF₃.hom _
    exact IsIso.of_isIso_comp_right (τ.app C).hom ec₃.inv


end AlgebraicGeometry
