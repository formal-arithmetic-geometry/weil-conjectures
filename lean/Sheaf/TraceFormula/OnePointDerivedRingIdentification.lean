/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Sheaf.ProperBaseChange.SingletonSiteModuleComparison
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-!
# Derived identification for the punctual ringed site

Source: Stacks Project, `sites-modules.tex`, Tag 03CW, and `derived.tex`,
Tags 05RN and 05RU (blueprint: lem-trf-one-point-derived-ring-identification).

The punctual-site module comparison supplies the canonical evaluation equivalence,
its one-object inverse, tensor comparison, localization comparison, and the
normalized universal scalar-extension pairs.  The statement below records the
remaining termwise total-tensor and cohomology comparisons explicitly.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory

namespace CategoryTheory

/-- The clauses of terminal-site evaluation and derived scalar extension.
Source: Stacks Project, sites-modules.tex Tag 03CW and derived.tex Tags 05RN, 05RU
(blueprint: lem-trf-one-point-derived-ring-identification).
The tensor, localization and universal-pair predicates are the existing punctual-site
comparison interfaces, with explicit total-tensor and cohomology clauses. -/
structure OnePointDerivedRingIdentification (A : Type u) [CommRing A] : Prop where
  /-- Exact evaluation and the specified one-object inverse. -/
  equivalence : ∃ e : singletonModuleCategory A ≌ ModuleCat.{u} A,
    e.functor = singletonEvaluation A ∧
      e.inverse = singletonConstantModuleSheaf (R := A) ∧
      (∀ T : ShortComplex (singletonModuleCategory A), T.ShortExact →
        (T.map e.functor).ShortExact)
  /-- The tensor comparison and its action on morphisms. -/
  tensor : singletonTensorComparison A
  /-- Termwise evaluation identifies direct-sum total tensor complexes. -/
  totalTensor : ∃ e : singletonModuleCategory A ≌ ModuleCat.{u} A,
    e.functor = singletonEvaluation A ∧
    (∀ (F G : CochainComplex (singletonModuleCategory A) ℤ),
      Nonempty
        (((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor F G (MonoidalCategory.curriedTensor _))) ≅
          CochainComplex.mapBifunctor
            ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
            ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj G)
            (MonoidalCategory.curriedTensor _)))
  /-- Evaluation commutes with every cohomology object. -/
  cohomology : ∃ e : singletonModuleCategory A ≌ ModuleCat.{u} A,
    e.functor = singletonEvaluation A ∧
    (∀ (F : CochainComplex (singletonModuleCategory A) ℤ) (n : ℤ),
      Nonempty (e.functor.obj (F.homology n) ≅
        ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj F).homology n))
  /-- Termwise evaluation preserves and reflects quasi-isomorphisms. -/
  quasiIso : ∀ {K L : CochainComplex (singletonModuleCategory A) ℤ} (f : K ⟶ L),
    QuasiIso f ↔
      QuasiIso (((singletonEvaluation A).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)
  /-- Evaluation preserves and reflects K-flatness. -/
  kFlat : ∀ (K : CochainComplex (singletonModuleCategory A) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients
        (J := singletonTopology) (R := singletonRingSheaf A) K ↔
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)).kFlat
        (((singletonEvaluation A).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)
  /-- The equivalence on homotopy categories is induced termwise by evaluation. -/
  homotopy : ∃ e : HomotopyCategory (singletonModuleCategory A) (ComplexShape.up ℤ) ≌
      HomotopyCategory (ModuleCat.{u} A) (ComplexShape.up ℤ),
    e.functor = (singletonEvaluation A).mapHomotopyCategory (ComplexShape.up ℤ)
  /-- Homotopy and derived localization are transported by evaluation. -/
  localization : ∃ (hA : HasDerivedCategory.{u + 1} (singletonModuleCategory A))
      (hM : HasDerivedCategory.{u + 1} (ModuleCat.{u} A)),
    singletonDerivedLocalizationCompatible A hA hM
  /-- Sheaf and ordinary extension of scalars, with their derived universal pairs. -/
  scalarExtension : ∀ (B : Type u) [CommRing B] (f : A →+* B),
    ∃ (E : singletonModuleCategory A ⥤ singletonModuleCategory B)
      (h : ∀ M, E.obj M = singletonSheafExtensionObj f M)
      (_ : ∀ {M N} (g : M ⟶ N), E.map g =
        eqToHom (h M) ≫ singletonSheafExtensionMap f g ≫ eqToHom (h N).symm)
      (_ : E.Additive)
      (s : E ⋙ singletonEvaluation B ≅
        singletonEvaluation A ⋙ ModuleCat.extendScalars f)
      (r : singletonSheafRestriction f ⋙ singletonEvaluation A ≅
        singletonEvaluation B ⋙ ModuleCat.restrictScalars f)
      (a : E ⊣ singletonSheafRestriction f),
      singletonScalarUnitCompatible f E h s r a ∧
      singletonOrdinaryUnitFormula f ∧
      ∃ (_ : HasDerivedCategory.{u + 1} (singletonModuleCategory A))
        (_ : HasDerivedCategory.{u + 1} (singletonModuleCategory B))
        (_ : HasDerivedCategory.{u + 1} (ModuleCat.{u} A))
        (_ : HasDerivedCategory.{u + 1} (ModuleCat.{u} B)),
        singletonDerivedScalarComparison f E s r a

/--
Terminal-site evaluation identifies ordinary modules and derived scalar extension.

Source: Stacks Project, `sites-modules.tex`, Tag 03CW, specialized to the
one-object category with its trivial topology; complexes and localization are
from `derived.tex`, Tags 05RN and 05RU.
(blueprint: lem-trf-one-point-derived-ring-identification)

The equivalence field gives exact evaluation and its inverse one-object sheaf.
The tensor field gives the sheaf tensor comparison, including morphisms.  The
total-tensor and cohomology fields state the degreewise comparisons for all
integer-indexed complexes, while the quasi-isomorphism and K-flat fields state
the corresponding homological invariance.  The localization field records the
induced homotopy and derived equivalences.  Finally, the scalar field records
termwise sheaf extension as ordinary extension of scalars together with the
universal K-flat derived pair, its counit, and the resolution computation.
All quantification is over unbounded complexes; no flatness hypothesis occurs.

Proof of the statement, following the node's twelve steps:
1. On the one-object identity category every presheaf is a sheaf for
   `singletonTopology`; evaluation and `singletonConstantModuleSheaf` are inverse by
   their sole component, giving the exact equivalence in `equivalence`.
2. Kernels, cokernels, images, exact sequences, and arbitrary direct sums are
   sectionwise at the sole object, so evaluation preserves exactness and sums.
3. The sectionwise tensor is already a sheaf; its sheafification unit sends a pure
   tensor to the ordinary pure tensor, and `singletonTensorComparison` records this
   map and its naturality in both morphisms.
4. For a ring map `f`, the sectionwise change of rings has value the ordinary tensor
   and the scalar action and morphism formulas are those of `singletonSheafExtensionObj`
   and `singletonSheafExtensionMap`; the ordinary unit is `singletonOrdinaryUnitFormula`.
5. Applying the equivalence in every degree gives the displayed total-tensor
   comparison.  It respects both differential terms, including the sign in the
   second factor, and works for unbounded complexes.
6. Evaluation commutes with kernels, images, and quotients, hence with each
   `F.homology n`; this is the `cohomology` field and gives the `quasiIso` field.
7. The induced homotopy equivalence and its shift and cone maps descend through the
   localization universal property, giving `localization` with the stated comparison
   to both localization functors.
8. The total-tensor comparison carries acyclic complexes to acyclic complexes in both
   directions, so the two K-flat tests coincide, exactly as recorded in `kFlat`.
9. For `f`, apply the K-flat resolution and derived-change-of-rings clauses to the
   sheaf extension.  The evaluation comparison identifies its K-flat resolutions and
   quasi-isomorphism invariance with the ordinary ones.
10. The universal left-derived lemma supplies a functor and counit, invertible on
    K-flat representatives; transporting them through the equivalences gives the
    universal pairs in `singletonDerivedScalarComparison`.
11. Conjugating the transported counit by the localization comparisons gives the
    ordinary derived scalar-extension counit and the resolution computation
    isomorphisms, with no flatness or boundedness restriction.
12. All maps are natural in complexes and ring maps; zero rings, zero complexes,
    identity maps, and arbitrary unbounded complexes are included by the same
    formulas.
-/
theorem one_point_derived_ring_identification (A : Type u) [CommRing A] :
    OnePointDerivedRingIdentification A := by
  sorry

end CategoryTheory

