/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.CategoryTheory.FiniteAdmissibleBrownFromCD
import WeilConjectures.CategoryTheory.CompactObjectsFiniteAdmissible
import Mathlib.CategoryTheory.ObjectProperty.Small

/-! # Compactness for finite coefficients

Source: blueprint latest, `sec-six-functors-basics/sk-prop-ctf-finite-compact`,
statement and proof (blueprint: sk-prop-ctf-finite-compact); Stacks Project Tags 0F11,
0D6J, 09SM and 09SN.

The coefficient ring is represented by the finite condensed ring
`Profinite.continuousMapRingObj A`.  The bounded constructible finite-Tor category is
`ConstantModelConstructibleFiniteTor`, and its localizing closure is
`localizingClosureProEtale`.  The skeleton is the canonical categorical skeleton of the
full subcategory, and `IsTriangulatedGeneratingFamily` renders the vanishing-of-Homs
criterion for all integer shifts.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- For a finite admissible coefficient ring, bounded constructible finite-Tor complexes
are exactly the compact objects of their pro-etale localizing closure, and a small skeleton
of them is a set of compact generators.

Proof: finite or algebraically closed fields have finite ℓ-cohomological dimension.
The finite admissible Brown helper transports the ordinary finite-coefficient compactness
calculation to the condensed model and supplies thickness, smallness and generation.
The compact-object characterization uses the generator telescope and finite thick
factorization. Finally, take the skeleton of a small categorical model of the constructible
finite-Tor subcategory. Its equivalence and the Brown bundle give the required skeleton
of compact generators, while the compact-object characterization gives the final equality.
(blueprint: sk-prop-ctf-finite-compact). -/
theorem compactness_finite_admissible
    (ℓ : ℕ) {p : ℕ} [Fact ℓ.Prime]
    {k : Type u} [Field k] [CharP k p]
    (hK : Finite k ∨ IsAlgClosed k) (hℓ : p ≠ ℓ)
    {X : Scheme.{u}} (aX : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (hA : ∃ r : ℕ, ∀ a : A, (ℓ ^ r) • a = 0) :
    let Λ := Profinite.continuousMapRingObj.{u} A
    let S := constantModelBoundedConstructible Λ X ⊓
      fun K ↦ DerivedCategory.finiteTorAmplitude _ K
    let L := localizingClosureProEtale Λ X
    ∃ hTri : L.IsTriangulated,
      letI := hTri
      ∃ hSums : HasCoproducts.{u + 1} L.FullSubcategory,
        letI := hSums
        (∀ C : S.FullSubcategory,
            ∃ hC : L C.obj,
              @CategoryTheory.IsCompactObject _ _ _ hSums
                (ObjectProperty.FullSubcategory.mk C.obj hC)) ∧
          ObjectProperty.EssentiallySmall.{u + 1} S ∧
          (∃ (G : Type (u + 1)) (hCat : Category.{u + 1} G),
             letI := hCat
             ∃ (e : G ≌ S.FullSubcategory),
               (∀ g g' : G, Nonempty (g ≅ g') → g = g') ∧
               ∃ hL : ∀ g : G, L (e.functor.obj g).obj,
                 (∀ g : G,
                    @CategoryTheory.IsCompactObject _ _ _ hSums
                      (ObjectProperty.FullSubcategory.mk (e.functor.obj g).obj (hL g))) ∧
                 (let E : G → L.FullSubcategory := fun g ↦
                     (ObjectProperty.FullSubcategory.mk (e.functor.obj g).obj (hL g) :
                       L.FullSubcategory)
                  letI : HasCoproducts.{u + 1} L.FullSubcategory := hSums
                  IsTriangulatedGeneratingFamily E)) ∧
          (∀ K : L.FullSubcategory,
            @CategoryTheory.IsCompactObject _ _ _ hSums K ↔ S K.obj) := by
  dsimp
  let Λ := Profinite.continuousMapRingObj.{u} A
  let S := constantModelBoundedConstructible Λ X ⊓
    fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  let L := localizingClosureProEtale Λ X
  have hcd : BaseFieldFiniteCD ℓ k := by
    rcases hK with hfin | halg
    · exact BaseFieldFiniteCD.of_finite ℓ k
    · exact BaseFieldFiniteCD.of_isAlgClosed ℓ k
  have hB : CategoryTheory.BrownHypothesesFor Λ X :=
    brownHypotheses_finite_admissible_of_cd ℓ hℓ hcd aX A hA
  obtain ⟨hTri, hSums, hcompactEq⟩ :=
    CategoryTheory.compact_objects_eq_finite_admissible Λ X hB
  let _ := hTri
  let _ := hSums
  obtain ⟨hsmall, _, hSIso, hSTri, hSClosedIso, hSRetr,
      hEss, _, hgen⟩ := hB
  have hSL : S ≤ L := by
    intro K hK' P hP hSP
    exact hSP K hK'
  let : ObjectProperty.EssentiallySmall.{u + 1} S := hEss
  obtain ⟨Q, hQ, hQS, hSQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le S
  let _ : LocallySmall.{u + 1} S.FullSubcategory :=
    locallySmall_of_faithful (ObjectProperty.ιOfLE hSL)
  let _ : LocallySmall.{u + 1} Q.FullSubcategory :=
    locallySmall_of_faithful (ObjectProperty.ιOfLE hQS)
  let _ : (ObjectProperty.ιOfLE hQS).IsEquivalence :=
    (ObjectProperty.isEquivalence_ιOfLE_iff hQS).mpr hSQ
  let _ : EssentiallySmall.{u + 1} S.FullSubcategory :=
    (essentiallySmall_congr (ObjectProperty.ιOfLE hQS).asEquivalence).mp
      (essentiallySmall_of_small_of_locallySmall _)
  let M := SmallModel.{u + 1} S.FullSubcategory
  let G := Skeleton M
  let e := (skeletonEquivalence M).trans (equivSmallModel.{u + 1} S.FullSubcategory).symm
  have hL (g : G) : L (e.functor.obj g).obj :=
    hSL _ (e.functor.obj g).property
  obtain ⟨_, hgen⟩ := hgen
  have hgen' := hgen G e hL
  have hcompact (g : G) : IsCompactObject
      (ObjectProperty.FullSubcategory.mk (e.functor.obj g).obj (hL g) : L.FullSubcategory) :=
    hgen'.1 g
  have hGgen : IsTriangulatedGeneratingFamily
      (fun g : G ↦ (ObjectProperty.FullSubcategory.mk (e.functor.obj g).obj (hL g) :
        L.FullSubcategory)) := hgen'.2
  refine ⟨hTri, hSums, ?_, hEss, ⟨G, inferInstance, e, ?_, hL, hcompact, hGgen⟩, ?_⟩
  · intro C
    have hC : L C.obj := hSL _ C.property
    exact ⟨hC, (hcompactEq ⟨C.obj, hC⟩).mpr C.property⟩
  · intro g g' h
    exact skeleton_skeletal _ ⟨h.some⟩
  · intro K
    exact hcompactEq K

end AlgebraicGeometry.ProEtale
