/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Sheaf.CategoryTheory.DerivedModuleFreeGeneration
import Sheaf.AlgebraicGeometry.ProperGeometricPointDerivedCoproducts
import Sheaf.AlgebraicGeometry.ProjectionFormulaTriangleClosure
import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Proper projection formula over a geometric point

Source: Stacks Project, Tags 0F0G and 0F12.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

open Scheme
variable (Λ : Type (u + 1)) [CommRing Λ]
variable (k : Type u) [Field k] [IsAlgClosed k]
private lemma constantCounit (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((constantSheafAdj (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ) terminalIsTerminal).counit.app F) := by
  let J := (Spec (.of k)).smallEtaleTopology
  let U := CategoryTheory.forget (ModuleCat.{u + 1} Λ)
  let G := (sheafCompose J U).obj F
  have : IsIso ((constantSheafAdj J (Type (u + 1)) terminalIsTerminal).counit.app G) :=
    (Scheme.spec_algClosed_etale_sheaf_constant k G).1
  have : IsIso ((sheafCompose J U).map
      ((constantSheafAdj J (ModuleCat.{u + 1} Λ) terminalIsTerminal).counit.app F)) := by
    rw [← constantSheafAdj_counit_w J U F terminalIsTerminal]
    infer_instance
  exact isIso_of_reflects_iso _ (sheafCompose J U)

private lemma derivedConstantEssSurj
    (N : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ K : DerivedCategory (ModuleCat.{u + 1} Λ),
      Nonempty (D(constantSheaf (Spec (.of k)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj K ≅ N) := by
  let J := (Spec (.of k)).smallEtaleTopology
  let C := constantSheaf J (ModuleCat.{u + 1} Λ)
  let G := sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
    (CategoryTheory.evaluation _ _).obj (op (⊤_ (Spec (.of k)).Etale))
  let ep := (sheafSections J (ModuleCat.{u + 1} Λ)).mapIso
    (terminalIsTerminal.uniqueUpToIso (isTerminalEtalePoint (k := k))).op
  have : G.PreservesEpimorphisms := Functor.PreservesEpimorphisms.of_iso ep
  have : G.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels G
  have : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesHomology G
  have : IsIso (constantSheafAdj J (ModuleCat.{u + 1} Λ) terminalIsTerminal).counit := by
    let (F : Sheaf J (ModuleCat.{u + 1} Λ)) : IsIso
        ((constantSheafAdj J (ModuleCat.{u + 1} Λ) terminalIsTerminal).counit.app F) :=
      constantCounit Λ k F
    exact NatIso.isIso_of_isIso_app _
  let e : G ⋙ C ≅ 𝟭 _ := asIso (constantSheafAdj J (ModuleCat.{u + 1} Λ)
    terminalIsTerminal).counit
  exact ⟨D(G).obj N, ⟨((Functor.mapDerivedCategoryCompIso G C).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _).app N⟩⟩
private noncomputable def derivedConstantRingUnit :
    D(constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj
        (ModuleCat.of Λ (ULift.{0} Λ))) ≅
      𝟙_ (DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ))) := by
  let J := (Spec (.of k)).smallEtaleTopology
  let C := constantSheaf J (ModuleCat.{u + 1} Λ)
  let e : ModuleCat.of Λ (ULift.{0} Λ) ≅ ModuleCat.of Λ Λ :=
    (ULift.moduleEquiv : ULift.{0} Λ ≃ₗ[Λ] Λ).toModuleIso
  exact (Functor.mapDerivedCategorySingleFunctor C 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (C.mapIso e ≪≫
      (Functor.Monoidal.εIso (presheafToSheaf J (ModuleCat.{u + 1} Λ))).symm) ≪≫
    singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) (Spec (.of k))
private lemma derivedConstantPreservesCoproducts :
    ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      D(constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) := by
  let J := (Spec (.of k)).smallEtaleTopology
  let C := constantSheaf J (ModuleCat.{u + 1} Λ)
  let G := sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
    (CategoryTheory.evaluation _ _).obj (op (⊤_ (Spec (.of k)).Etale))
  let ep := (sheafSections J (ModuleCat.{u + 1} Λ)).mapIso
    (terminalIsTerminal.uniqueUpToIso (isTerminalEtalePoint (k := k))).op
  have : G.PreservesEpimorphisms := Functor.PreservesEpimorphisms.of_iso ep
  have : G.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels G
  have : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesHomology G
  let adj : C ⊣ G := constantSheafAdj J (ModuleCat.{u + 1} Λ) terminalIsTerminal
  have : D(C).IsLeftAdjoint := adj.mapDerivedCategoryAdjunction.isLeftAdjoint
  intro I
  exact inferInstance

omit [IsAlgClosed k] in
private lemma shiftedUnitDualizable (n : ℤ) :
    IsDualizable ((𝟙_ (DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))))⟦n⟧) := by
  let U := 𝟙_ (DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)))
  have mk (a b : ℤ) (hab : a + b = 0) : U⟦a⟧ ⊗ U⟦b⟧ ≅ U :=
    DerivedCategory.shiftTensorShiftIso _ U U a b ≪≫
      (eqToIso (congrArg (fun n : ℤ => (U ⊗ U)⟦n⟧) hab)) ≪≫
      (shiftFunctorZero _ ℤ).app (U ⊗ U) ≪≫ λ_ U
  exact isDualizable_of_tensorIso (mk n (-n) (add_neg_cancel n))
    (mk (-n) n (neg_add_cancel n))

section CoproductFunctors
universe v
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

private lemma projectionSourcePreserves {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) ((derivedTensorRightDerivedLowerStar A p).obj M) :=
  inferInstanceAs (PreservesColimitsOfShape (Discrete I)
    (tensorLeft (R((p)_*[A]).obj M)))

private lemma projectionTargetPreserves {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) (I : Type (u + 1))
    [PreservesColimitsOfShape (Discrete I) (R((p)_*[A]))] :
    PreservesColimitsOfShape (Discrete I)
      ((rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar A p).obj M) := by
  have : (L((p)^*[A])).IsLeftAdjoint :=
    (derivedUpperStarLowerStarAdjunction A p).isLeftAdjoint
  exact inferInstanceAs (PreservesColimitsOfShape (Discrete I)
    ((L((p)^*[A]) ⋙ tensorLeft M) ⋙ R((p)_*[A])))
private lemma projectionAtDualizable [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) (hN : IsDualizable N) :
    IsIso (((rightDerivedLowerStarProjectionMap A p).app M).app N) := by
  let := leftDerivedUpperStarMonoidal A p
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory (Sheaf Y.smallEtaleTopology A)
  exact Adjunction.isIso_rightAdjointProjectionMap_app_app_of_isDualizable
    (derivedUpperStarLowerStarAdjunction A p) _ (fun _ _ => rfl) M hN

end CoproductFunctors

private lemma isoFromModuleGenerators (R : Type (u + 1)) [CommRing R]
    {B : Type*} [Category B]
    (F G : DerivedCategory (ModuleCat.{u + 1} R) ⥤ B)
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G]
    (α : F ⟶ G)
    (hgen : ∀ n : ℤ, IsIso (α.app (((DerivedCategory.singleFunctor
      (ModuleCat.{u + 1} R) 0).obj (ModuleCat.of R (ULift.{0} R)))⟦n⟧)))
    (htri : ∀ T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u + 1} R)),
      T ∈ Pretriangulated.distinguishedTriangles → IsIso (α.app T.obj₁) →
        IsIso (α.app T.obj₂) → IsIso (α.app T.obj₃))
    (K : DerivedCategory (ModuleCat.{u + 1} R)) : IsIso (α.app K) := by
  apply derivedModuleFreeGeneration.{u + 1, 0} R K (fun K => IsIso (α.app K)) hgen
  · intro I X S ι hc hx
    have : IsIso ((Discrete.functor X).whiskerLeft α) := by
      apply (NatTrans.isIso_iff_isIso_app _).2
      intro i
      exact hx i.as
    exact isIso_app_coconePt_of_preservesColimit (Discrete.functor X) α
      (Cofan.mk S ι) hc
  · exact htri
  · intro X Y h hY
    exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms B)
      (α.retractArrowApp h) hY

private lemma projectionAtConstantGenerator
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) p).app M).app
      (D(constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (((DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj
          (ModuleCat.of Λ (ULift.{0} Λ)))⟦n⟧))) := by
  let C := D(constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let K₀ := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj
    (ModuleCat.of Λ (ULift.{0} Λ))
  let E : C.obj (K₀⟦n⟧) ≅ (𝟙_ _)⟦n⟧ :=
    ((C.commShiftIso n).app K₀) ≪≫
    (shiftFunctor _ n).mapIso (derivedConstantRingUnit Λ k)
  have hdual := IsDualizable.of_iso E.symm (shiftedUnitDualizable Λ k n)
  exact projectionAtDualizable (ModuleCat.{u + 1} Λ) p M _ hdual

/-- The proper projection formula with base an algebraically closed field.
Source: Stacks Project, Tag 0F12, as used in the geometric-fibre proof of Tag 0F0G.
(blueprint: lem-etale-projection-formula-finite-geometric-point)

Proof in words: an etale module sheaf over Spec k is canonically constant, so its
unbounded derived category identifies with D(Λ). The proper k-scheme X is qcqs
and of finite torsion cohomological dimension. Consequently RΓ(X,-) commutes
with coproducts of arbitrary unbounded Λ-complexes. For fixed M, both functors
in the projection map are exact and preserve coproducts in L. The canonical
map is invertible on every shift of the free rank-one module, by the tensor
unit and the counit identity. Closure under triangles and coproducts, together
with generation of D(Λ) by these shifts, proves it for every L. The equivalence
at the point identifies this map with the displayed adjoint-of-counit map.
The zero ring, empty X and zero complexes are included. -/
theorem isIso_projection_over_geometricPoint
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : _root_.DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) p).app M).app N) := by
  let C := D(constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let α := (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) p).app M
  obtain ⟨K, ⟨e⟩⟩ := derivedConstantEssSurj Λ k N
  apply (NatTrans.isIso_app_iff_of_iso α e).mp
  have : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) C :=
    derivedConstantPreservesCoproducts Λ k
  have : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (R((p)_*[ModuleCat.{u + 1} Λ])) :=
    proper_geometricPoint_pushforward_preservesCoproducts Λ p
  have (I : Type (u + 1)) := projectionSourcePreserves (ModuleCat.{u + 1} Λ) p M I
  have (I : Type (u + 1)) := projectionTargetPreserves (ModuleCat.{u + 1} Λ) p M I
  apply isoFromModuleGenerators Λ _ _ (Functor.whiskerLeft C α) ?_ ?_ K
  · exact projectionAtConstantGenerator Λ p M
  · intro T ht h₁ h₂
    exact projection_triangle_isIso (ModuleCat.{u + 1} Λ) p M
      (C.mapTriangle.obj T) (C.map_distinguished T ht) h₁ h₂

end AlgebraicGeometry.Etale
