/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # Normalization of the strict coefficient unit tower

Source: tower-geometric gamma proof (1) and (3), the coefficient unit's actual reductions.
(blueprint: lem-sp-coefficient-unit-tower-normalized).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.ProEtale.SpFiniteOrientation

-- Unfold the diagram to compare its levels with B, but keep the shared leaves closed.
attribute [local irreducible] spCoefficientRings
  CategoryTheory.constantSheaf Padic Padic.coefficientExtensionIntegers
-- Use the canonical ring instance throughout the section calculations.
attribute [local instance 20000] CommRing.toRing

section UnitEvaluation
universe c v r
variable {C : Type c} [Category.{v} C] {D : Type*} [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{r})

end UnitEvaluation

section RingMap
universe c v r
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})

end RingMap

private theorem isIso_app_of_iso
    {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (τ : F ⟶ G) {K L : C} (e : K ≅ L)
    [IsIso (τ.app K)] : IsIso (τ.app L) := by
  exact IsIso.of_isIso_fac_left (τ.naturality e.hom)

section ScalarUnit
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {R S : Sheaf J CommRingCat.{r}}
private abbrev scalarRing (A : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A
private abbrev scalarRestrict (φ : R ⟶ S) := SheafOfModules.restrictScalars
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)

end ScalarUnit

-- Keep the section calculation over a variable ring diagram: specializing its proof
-- to constant quotient sheaves would make conversion unfold their sheafifications.
section UnitCoordinates
universe c v r
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (L : SheafOfModules.StrictRingSystem.{c, v, r} B)
    (N : SemilinearSections.Systems.{c, v, r} J (fun i ↦ B.obj (op i))
      (fun i ↦ B.map (homOfLE (Nat.le_succ i)).op))
    (ε : N ⟶ SheafOfModules.unit (SemilinearSections.ring (coefficientSequenceTopology J)
      (SemilinearSections.systemRing J (fun i ↦ B.obj (op i))
        (fun i ↦ B.map (homOfLE (Nat.le_succ i)).op))))
    (d : ∀ i (U : Cᵒᵖ), (L.level i).val.obj U → N.val.obj (op (i, U.unop)))
    (e : ∀ i, L.level i ⟶ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj (B.obj (op i))))
    (hs : ∀ i (U : Cᵒᵖ), HEq ((L.level i).val.obj U) (N.val.obj (op (i, U.unop))))
    (ht : ∀ {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ),
      HEq ((L.transition h).val.app U)
        (N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op))

variable (hd : ∀ i (U : Cᵒᵖ) (x : (L.level i).val.obj U), HEq (d i U x) x)

variable (he : ∀ i (U : Cᵒᵖ) (x : (L.level i).val.obj U),
      ((SheafOfModules.Hom.val (e i)).app U).hom x = ε.val.app (op (i, U.unop)) (d i U x))

end UnitCoordinates

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (q : SpTowerCalculus.Coordinates l E b)
    (T : Scheme.{u})

end AlgebraicGeometry.ProEtale.SpFiniteOrientation
