/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QlbarInternalHomCoefficientData

import WeilConjectures.AlgebraicGeometry.InternalSectionHomContinuityComparison
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexColimit
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexDiagram
import WeilConjectures.AlgebraicGeometry.CondensedDerivedTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.StrictFiniteFreeInternalHomColimit
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.AlgebraicGeometry.InternalScalarTensorComparison
public import WeilConjectures.Algebra.Homology.FlatInternalHomEvaluationRoof
public import WeilConjectures.CategoryTheory.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.DerivedInternalHomFilteredColimit
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexDiagram
public import WeilConjectures.AlgebraicGeometry.CondensedDerivedTensorComparisonSupplement
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.AlgebraicGeometry.FiniteSubextensionsDirected
import WeilConjectures.AlgebraicGeometry.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.CompletedCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.QlbarTailModuleColimit
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

/-! # Algebraic-closure coefficient comparison for internal Hom

Source: Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.14 and Remark 6.8.15;
the explicit-continuity specialization in the DAG
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).

## Main definitions and statements

* `evaluationComparison`: the actual scalar-extended evaluation transpose.
* `Continuous`: the explicit continuity hypothesis on strict filtered diagrams.
* `fields`, `coefficients`, `coefficientCocone`: the prescribed finite-field tail.
* `StrictColimitFormula`, `ColimitFormula`: the termwise colimit roof and its squares.
* `evaluationComparison_naturality`, `evaluationComparison_restriction`:
  naturality and scalar-adjunction normalization.
* `fieldDiagram`, `coefficientModules`, `coefficientRingColimit`:
  smallness, cofinality, finite freeness and the specified coefficient colimits.
* `coefficient_colimit_formula`: the three evaluation-normalized colimit arrows.
* `qlbar_internalHom_coefficient_comparison`: invertibility on the stated inputs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Sheaf.braidedCategory
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralReductionSiteEssentiallySmall
attribute [local irreducible]
  CategoryTheory.derivedInternalHomOfUniverses
  AlgebraicGeometry.ProEtale.CondensedRing.derivedTensor
  WeilConjectures.SfbHomFilteredColimit.comparison
  WeilConjectures.coefficientHomResolution
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.CondensedRing.derivedHom
  AlgebraicGeometry.ProEtale.CondensedRing.derivedTensorHomAdjunction
  AlgebraicGeometry.ProEtale.CondensedRing.internalScalarTensorIso
  CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Functor.Monoidal.toLaxMonoidal
  CategoryTheory.Functor.Monoidal.toOplaxMonoidal
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QlbarInternalHom

open ModuleObjectRingedComparison

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

attribute [local irreducible] evaluationComparison scalarHomIso
  coefficients coefficientCocone complexForward completedSubfieldCocone
  ColimitFormula Continuous

section ColimitProof

set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] WeilConjectures.SfbHomFilteredColimit.tensor
  WeilConjectures.SfbHomFilteredColimit.homFixed
  WeilConjectures.coefficientTotalTensor homComplexFunctor
  SheafOfModules.monoidalCategory SheafOfModules.scalarPairComplexComparison

private theorem coefficientCocone_isColimit (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Nonempty (IsColimit (coefficientCocone X ℓ E)) := by
  have : IsFiltered (AsSmall.{u + 1} (Under E)) := (fieldDiagram.{u, u} X ℓ E).1
  have : (fields.{u} ℓ E).Final := (fieldDiagram.{u, u} X ℓ E).2.1
  obtain ⟨hc⟩ := nonempty_isColimit_coefficientComplexCocone X ℓ
    ((HomologicalComplex.single (Internal (Profinite.continuousMapRingObj E) X)
      (.up ℤ) 0).obj (Mod.regular (padicSubfieldRingObj X ℓ E))) (fields ℓ E)
    (fun i ↦ leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom))
    (fun i ↦ leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom))
  have : PreservesColimitsOfShape (AsSmall.{u + 1} (Under E))
      (complexForward (Profinite.continuousMapRingObj E) X) := by
    unfold complexForward
    infer_instance
  unfold coefficientCocone coefficients
  exact PreservesColimit.preserves
    (F := complexForward (Profinite.continuousMapRingObj E) X ⋙
      HomologicalComplex.eval (Modules (Profinite.continuousMapRingObj E) X) (.up ℤ) 0) hc

@[no_expose] private abbrev FiniteFreeStage
    {A : Type*} [Category A] [HasFiniteProducts A] (U N : A) : Prop :=
  ∃ d : ℕ, Nonempty (N ≅ limit (Discrete.functor (fun _ : Fin d ↦ U)))

@[no_expose] private def finiteSumProductIso
    {A : Type*} [Category A] [Abelian A] (U : A) (d : ℕ) :
    (∐ (fun _ : Fin d ↦ U)) ≅ limit (Discrete.functor (fun _ : Fin d ↦ U)) := by
  have : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts (C := A)
  exact (biproductIso (fun _ : Fin d ↦ U)).symm

private theorem coefficient_finiteFree (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (i : AsSmall.{u + 1} (Under E)) :
    FiniteFreeStage
      (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (ring (Profinite.continuousMapRingObj E) X))) ((coefficients X ℓ E).obj i) := by
  unfold FiniteFreeStage
  obtain ⟨stage, _, _, _⟩ := coefficientModules X ℓ E
  obtain ⟨d, ⟨e⟩⟩ := (fieldDiagram.{u, u} X ℓ E).2.2 ((fields ℓ E).obj i)
    (leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom))
  let N := (Mod.comap (padicSubfieldRingObjMap X ℓ
    (leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom)))).obj
      (Mod.regular (padicSubfieldRingObj X ℓ ((fields ℓ E).obj i)))
  have h : Nonempty (N ≅ ∐ (fun _ : Fin d ↦
      Mod.regular (padicSubfieldRingObj X ℓ E))) :=
    ⟨e.symm ≪≫ biproduct.isoCoproduct _⟩
  obtain ⟨q⟩ := (finite_free_iff (Profinite.continuousMapRingObj E) X N d).1 h
  exact ⟨d, ⟨stage i ≪≫ q ≪≫ finiteSumProductIso _ d⟩⟩

private theorem quasiIso_natTrans_of_iso
    {A B : Type*} [Category A] [Category B] [Abelian B]
    {F G : A ⥤ CochainComplex B ℤ} (η : F ⟶ G) {a b : A} (e : a ≅ b)
    (h : QuasiIso (η.app a)) : QuasiIso (η.app b) := by
  have := h
  exact quasiIso_of_arrow_mk_iso _ _
    (Arrow.isoMk (F.mapIso e) (G.mapIso e) (η.naturality e.hom))

private theorem eighthClause {p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop}
    (h : p1 ∧ p2 ∧ p3 ∧ p4 ∧ p5 ∧ p6 ∧ p7 ∧ p8 ∧ p9 ∧ p10 ∧ p11) : p8 :=
  h.2.2.2.2.2.2.2.1

section GenericColimit

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

private theorem strict_formula_numerator
    (R : Sheaf J CommRingCat.{u + 1})
    {I : Type (u + 1)} [SmallCategory I]
    (T : I ⥤ WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u}
      J R) [HasColimit T] (c : Cocone T)
    (P L : CochainComplex (WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u}
      J R) ℤ)
    (h : StrictColimitFormula J R T c P L) :
    QuasiIso ((WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u}
      J R P L).app c.pt) := by
  unfold StrictColimitFormula at h
  exact eighthClause h

end GenericColimit

set_option backward.isDefEq.respectTransparency.types false in
/-- All three arrows of the strict colimit formula and the transition squares.
Representatives alone are K-flat and bounded: these impose no condition on K,L beyond
those in the main theorem. The numerator is the unique evaluation-normalized map.
Source: DAG displayed formula, Bhatt--Scholze 6.8.14--6.8.15
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof: the canonical coefficient-complex cocone is a colimit; section reconstruction
and degree-zero evaluation preserve it. Tensor preserves this colimit. Finite freeness
makes every stage numerator a quasi-isomorphism.
Exact filtered colimits preserve their quasi-isomorphisms. Apply continuity to the
common lower bound of F tensor L; the resolution units identify the I(L) models.
K-flatness gives the denominator quasi-isomorphisms.
Naturality of the normalized numerator and resolution unit gives both cocone squares.
The evaluation-roof identity of the general comparison identifies the resulting
numerator/inverse-denominator roof with the restriction characterized above. -/
theorem coefficient_colimit_formula
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K : DerivedCategory (Internal (Profinite.continuousMapRingObj E) X))
    (hK : Continuous X ℓ E K)
    (P L : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ (forward (Profinite.continuousMapRingObj E) X).obj K)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology X) (R := ring (Profinite.continuousMapRingObj E) X) P)
    (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology X) (R := ring (Profinite.continuousMapRingObj E) X) (P.X n))
    (hL : ∃ b : ℤ, ∀ n : ℤ, n < b → IsZero (L.X n)) :
    ColimitFormula X ℓ E P L := by
  set_option backward.isDefEq.respectTransparency.types true in
    unfold Continuous at hK
    unfold ColimitFormula StrictColimitFormula
    have _ := hflat
    have : IsFiltered (AsSmall.{u + 1} (Under E)) := (fieldDiagram.{u, u} X ℓ E).1
    exact strictColimitFormula_of_finiteFree (Scheme.ProEt.topology X)
      (ring (Profinite.continuousMapRingObj E) X)
      (coefficients X ℓ E) (coefficientCocone X ℓ E) (coefficientCocone_isColimit X ℓ E)
      (coefficient_finiteFree X ℓ E) P L hP (hK P ⟨eP⟩ _) hL

end ColimitProof


set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CondensedRing.internalScalarExtension
attribute [local irreducible] WeilConjectures.coefficientHomResolutionIso

private theorem finiteLimits_of_restriction_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ B) (f : C ≌ D)
    (F : A ⥤ C) (U : C ⥤ A) (hF : F ⊣ U) [PreservesFiniteLimits F]
    (G : B ⥤ D) (V : D ⥤ B) (hG : G ⊣ V)
    (r : U ⋙ e.functor ≅ f.functor ⋙ V) : PreservesFiniteLimits G := by
  let adj := e.symm.toAdjunction.comp (hF.comp f.toAdjunction)
  let i : (f.inverse ⋙ U) ⋙ e.functor ≅ V :=
    Functor.associator f.inverse U e.functor ≪≫
      Functor.isoWhiskerLeft f.inverse r ≪≫
      (Functor.associator f.inverse f.functor V).symm ≪≫
      Functor.isoWhiskerRight f.counitIso V ≪≫ Functor.leftUnitor V
  have : PreservesFiniteLimits (e.inverse ⋙ (F ⋙ f.functor)) := inferInstance
  exact preservesFiniteLimits_of_natIso ((adj.ofNatIsoRight i).leftAdjointUniq hG)

private theorem sectionScalar_exact
    [∀ A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{u + 1}
        (SheafOfModules.scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) A)]
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (s : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (sectionCoefficientMap (X := X) a))
    (r : Mod.comap (coefficientMap a X) ⋙ (equivalence R X).functor ≅
      (equivalence S X).functor ⋙
        SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (sectionCoefficientMap (X := X) a)) :
    PreservesFiniteLimits s.extension := by
  exact finiteLimits_of_restriction_transport (equivalence R X) (equivalence S X)
    (Mod.extendScalars (coefficientMap a X)) (Mod.comap (coefficientMap a X))
    (Mod.extendRestrictAdjunction (coefficientMap a X))
    s.extension (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionCoefficientMap (X := X) a))
    s.ordinaryAdjunction r

section FlatComparison

set_option hygiene false in
local notation "J₀" => Scheme.ProEt.topology X
variable [∀ A : Sheaf J₀ CommRingCat.{u + 1},
    HasDerivedCategory.{u + 1} (SheafOfModules.scalarModules.{u + 1, u, u + 1} J₀ A)]
  (M : ScalarHomModels.{u + 1, u, u, u + 1} J₀)
  (μ : ∀ {A B : Sheaf J₀ CommRingCat.{u + 1}} (a : A ⟶ B),
    ScalarHomTensorComparison.{u + 1, u, u, u + 1} M a)
  (α : ScalarInternalHomAdjunction.{u + 1, u, u, u + 1} M μ)
  (roof : SfbFlatHom.EvaluationRoof.{u + 1, u, u, u + 1} M μ α)
  {R S : Sheaf J₀ CommRingCat.{u + 1}} (a : R ⟶ S)
  (ha : PreservesFiniteLimits (M.scalar a).extension)

include α roof ha in
private theorem flat_comparison_isIso
    (P N : CochainComplex (SheafOfModules.scalarModules.{u + 1, u, u + 1} J₀ R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J₀) (R := R) P)
    (hp : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J₀) (R := R) (P.X n))
    (hn : QuasiIso (SfbFlatHom.numerator.{u + 1, u, u} a P N))
    (K L : DerivedCategory (SheafOfModules.scalarModules.{u + 1, u, u + 1} J₀ R))
    (eP : DerivedCategory.Q.obj P ≅ K) (eN : DerivedCategory.Q.obj N ≅ L) :
    IsIso (SfbFlatHom.comparison.{u + 1, u, u, u + 1} M μ a K L) := by
  let := hn
  let hd := roof.denominator_quasiIso a ha P N hP hp
  have hrep (B : CochainComplex (SheafOfModules.scalarModules.{u + 1, u, u + 1} J₀ R) ℤ) :
      IsIso (SfbFlatHom.representative.{u + 1, u, u, u + 1} M a (roof.tensorIso a) B) := by
    let := roof.exact_computes a ha B
    unfold SfbFlatHom.representative
    infer_instance
  have hsource : IsIso (SfbFlatHom.sourceMap.{u + 1, u, u, u + 1} M a (roof.tensorIso a) P N) := by
    unfold SfbFlatHom.sourceMap
    refine IsIso.comp_isIso' ?_ (hrep _)
    infer_instance
  have htarget : IsIso (SfbFlatHom.targetMap.{u + 1, u, u, u + 1} M a (roof.tensorIso a) P N) := by
    unfold SfbFlatHom.targetMap
    refine IsIso.comp_isIso' ?_ ?_
    · let := hrep N
      exact ((CategoryTheory.derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        J₀ R).mapIso ((Iso.refl (op (DerivedCategory.Q.obj P))).prod
          (asIso (SfbFlatHom.representative.{u + 1, u, u, u + 1}
            M a (roof.tensorIso a) N)))).isIso_hom
    · exact (WeilConjectures.coefficientHomResolutionIso.{u, u + 1, u, u + 1}
        J₀ R P ((SfbFlatHom.scalarTensor.{u + 1, u, u} a).obj N)).isIso_hom
  have he := roof.equation a ha P N hP hp
  have hbase : IsIso (SfbFlatHom.restrictedComparison.{u + 1, u, u, u + 1} M μ α a
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)) := by
    have hcomp : IsIso (SfbFlatHom.restrictedComparison.{u + 1, u, u, u + 1} M μ α a
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) ≫
      SfbFlatHom.targetMap.{u + 1, u, u, u + 1} M a (roof.tensorIso a) P N ≫
        DerivedCategory.Q.map (SfbFlatHom.denominator.{u + 1, u, u} a P N)) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (SfbFlatHom.targetMap.{u + 1, u, u, u + 1} M a (roof.tensorIso a) P N ≫
        DerivedCategory.Q.map (SfbFlatHom.denominator.{u + 1, u, u} a P N))
  have hnat := roof.naturality a (DerivedCategory.Q.obj P) K
    (DerivedCategory.Q.obj N) L eP.inv eN.hom
  have hnew : IsIso (SfbFlatHom.restrictedComparison.{u + 1, u, u, u + 1} M μ α a K L) := by
    have hcomp : IsIso
        ((SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1} a).map
          ((M.scalar a).derived.map
          ((CategoryTheory.derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
            J₀ R).map (Prod.mkHom eP.inv.op eN.hom))) ≫
          SfbFlatHom.restrictedComparison.{u + 1, u, u, u + 1} M μ α a K L) := by
      rw [hnat]
      refine IsIso.comp_isIso' hbase ?_
      exact ((CategoryTheory.derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        J₀ R).mapIso (eP.symm.op.prod
          ((SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1} a).mapIso
            ((M.scalar a).derived.mapIso eN)))).isIso_hom
    have hf : IsIso
        ((SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1} a).map
          ((M.scalar a).derived.map
            ((CategoryTheory.derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
              J₀ R).map (Prod.mkHom eP.inv.op eN.hom)))) :=
      ((SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1} a).mapIso
        ((M.scalar a).derived.mapIso
          ((CategoryTheory.derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
            J₀ R).mapIso (eP.symm.op.prod eN)))).isIso_hom
    exact IsIso.of_isIso_comp_left
      ((SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1} a).map
        ((M.scalar a).derived.map
          ((CategoryTheory.derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
            J₀ R).map (Prod.mkHom eP.inv.op eN.hom)))) _
  have hu : IsIso ((SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1} a).map
      (SfbFlatHom.comparison.{u + 1, u, u, u + 1} M μ a K L)) := by
    change IsIso (_ ≫ (α.iso a).hom.app
      (op K, (M.scalar a).derived.obj L)) at hnew
    have : IsIso ((α.iso a).hom.app (op K, (M.scalar a).derived.obj L)) :=
      ((α.iso a).app (op K, (M.scalar a).derived.obj L)).isIso_hom
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
      (((α.iso a).app (op K, (M.scalar a).derived.obj L)).isIso_hom) hnew
  exact ScalarInternalHomAdjunction.conservative.{u + 1, u, u, u + 1} α a _ hu

end FlatComparison

private theorem isIso_of_conjugacy
    {V : Type*} [Category V] {A B C D E F : V}
    (f : A ⟶ B) (i : B ≅ C) (j : C ≅ D) (k : A ≅ E) (l : E ≅ F)
    (g : F ⟶ D) (hg : IsIso g)
    (h : f ≫ i.hom ≫ j.hom = k.hom ≫ l.hom ≫ g) : IsIso f := by
  have := hg
  have hh : IsIso (f ≫ (i ≪≫ j).hom) := by
    change IsIso (f ≫ i.hom ≫ j.hom)
    rw [h]
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (i ≪≫ j).isIso_hom hh

private theorem evaluationComparison_isIso_of_numerators
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K L : DerivedCategory (Internal R X))
    (V : Modules R X) :
    letI : ∀ A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
        HasDerivedCategory.{u + 1}
          (SheafOfModules.scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) A) :=
      fun A ↦ HasDerivedCategory.ofIsGrothendieckAbelian
        (WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u}
          (Scheme.ProEt.topology X) A)
    ∀ (_hformula : ∀ (P N : CochainComplex (Modules R X) ℤ)
      (_eP : DerivedCategory.Q.obj P ≅ (forward R X).obj K)
      (_hP : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology X) (R := ring R X) P)
      (_hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite
        (J := Scheme.ProEt.topology X) (R := ring R X) (P.X n))
      (_hbound : ∃ m : ℤ, ∀ n : ℤ, n < m → IsZero (N.X n)),
      QuasiIso ((WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring R X) P N).app V))
    (_vertex : V ≅ (equivalence R X).functor.obj
      ((Mod.comap (coefficientMap a X)).obj (Mod.regular (condensedRingObj S X))))
    (_hL : ∃ m : ℤ, L.IsGE m), IsIso (evaluationComparison X a K L) := by
  intro hformula vertex hL
  classical
  let : ∀ A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{u + 1}
        (SheafOfModules.scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) A) :=
    fun A ↦ HasDerivedCategory.ofIsGrothendieckAbelian
      (WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u}
        (Scheme.ProEt.topology X) A)
  let b := sectionCoefficientMap (X := X) a
  refine Exists.elim (coefficient_comparison_roof X a) ?_
  intro M hM
  refine Exists.elim hM ?_
  intro μ hμ
  refine Exists.elim hμ ?_
  intro α hα
  refine Exists.elim hα ?_
  intro r hr
  refine And.elim ?_ hr
  intro _ hγ
  refine Exists.elim hγ ?_
  intro γ hγ
  rcases hγ with ⟨_, _, _, θR, θS, _, _, _, _, ⟨roof⟩, hcomparison⟩
  let G := DerivedCategory.Q.objPreimage ((forward R X).obj K)
  obtain ⟨P, q, hP, hp, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
  let := hq
  let eP : DerivedCategory.Q.obj P ≅ (forward R X).obj K :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso _
  have hflat (n : ℤ) : SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology X) (R := ring R X) (P.X n) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (ring R X) (P.X n)).symm (hp n)
  obtain ⟨m, hm⟩ := hL
  have : ((forward R X).obj L).IsGE m :=
    (cohomological_lower_bound_iff R X L m).1 hm
  obtain ⟨N, hN, ⟨eN⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE ((forward R X).obj L) m
  have hbound : ∃ m : ℤ, ∀ n : ℤ, n < m → IsZero (N.X n) :=
    ⟨m, fun n hn ↦ N.isZero_of_isStrictlyGE m n hn⟩
  have hvertex := hformula P N eP hP hflat hbound
  obtain ⟨q₀⟩ := (finite_free_iff S X (Mod.regular (condensedRingObj S X)) 1).1
    ⟨(coproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular (condensedRingObj S X))).symm⟩
  let e₀ := q₀ ≪≫ coproductUniqueIso (fun _ : Fin 1 ↦ SheafOfModules.unit
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring S X)))
  let v : V ≅
      (SheafOfModules.scalarRestriction b).obj (SheafOfModules.unit
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring S X))) :=
    vertex ≪≫ r.app (Mod.regular (condensedRingObj S X)) ≪≫
      (SheafOfModules.scalarRestriction b).mapIso e₀
  have hn : QuasiIso (SfbFlatHom.numerator.{u + 1, u, u} b P N) :=
    quasiIso_natTrans_of_iso
      (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring R X) P N) v hvertex
  have hc : IsIso (SfbFlatHom.comparison.{u + 1, u, u, u + 1} M μ b ((forward R X).obj K)
      ((forward R X).obj L)) :=
    flat_comparison_isIso X M μ α roof b (sectionScalar_exact X a (M.scalar b) r)
      P N hP hflat hn _ _ eP eN.symm
  have hmap : IsIso ((forward S X).map (evaluationComparison X a K L)) :=
    isIso_of_conjugacy _
      (θS.app (op ((CondensedRing.internalScalarExtension a X).obj K),
        (CondensedRing.internalScalarExtension a X).obj L))
      ((hom S X).mapIso ((γ.app K).symm.op.prod (γ.app L)))
      (γ.app (((CondensedRing.derivedHom R X).obj (op K)).obj L))
      ((M.scalar b).derived.mapIso (θR.app (op K, L)))
      (SfbFlatHom.comparison.{u + 1, u, u, u + 1} M μ b
        ((forward R X).obj K) ((forward R X).obj L)) hc (hcomparison K L)
  have : (equivalence S X).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (forward S X).IsEquivalence := by
    unfold forward
    exact Functor.isEquivalence_mapDerivedCategory _
  exact isIso_of_reflects_iso _ (forward S X)

/-- The canonical comparison is invertible for every continuous first input and every
cohomologically bounded-below second input, in the ordinary module-object categories.
Source: Bhatt--Scholze 6.8.14--6.8.15; explicit conditional argument of the DAG
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof:
1. fieldDiagram gives the small filtered cofinal tail and finite free stages.
2. The coefficient maps compose by lem-sfb-subfield-coefficient-map-comp.
   Restrict the ring cocone of sk-prop-sfb-qlbar-colimit-x to the cofinal tail.
   The canonical coefficient-complex colimit, transported to sections and evaluated
   in degree zero, gives its underlying module colimit with the prescribed legs.
3. Exact filtered colimits follow from the faithful exact module forgetful functor
   and exact filtered colimits of abelian sheaves (03DA, 03DB, 03CO).
4. lem-sfb-module-object-ringed-site-derived-comparison and
   lem-pe-internal-section-tensor-comparison transport tensor, Hom, evaluation,
   lower bounds and the continuity hypothesis to ringed-site module sheaves.
5. Choose a K-flat representative of K and a bounded-below representative of L.
   Apply lem-sfb-dc-hom-filtered-colimit to the finite-free coefficient diagram.
   Its scalarComparison_restriction and filteredColimit_comparison give the
   three-arrow colimit formula. Evaluation normalization identifies its map with
   evaluationComparison. Transport back. No bound on RHom(K,L) is used. -/
theorem qlbar_internalHom_coefficient_comparison
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K L : DerivedCategory (Internal (Profinite.continuousMapRingObj E) X))
    (hK : Continuous X ℓ E K) (hL : ∃ b : ℤ, L.IsGE b) :
    IsIso (evaluationComparison X (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) K L) := by
  classical
  let vertex := (coefficientModules X ℓ E).choose_spec.choose
  apply evaluationComparison_isIso_of_numerators X
    (R := Profinite.continuousMapRingObj E) (S := Profinite.padicAlgClRingObj ℓ)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) K L
    (coefficientCocone X ℓ E).pt
  · intro P N eP hP hflat hbound
    have h := coefficient_colimit_formula X ℓ E K hK P N eP hP hflat hbound
    unfold ColimitFormula at h
    exact strict_formula_numerator (Scheme.ProEt.topology X) _ (coefficients X ℓ E)
      (coefficientCocone X ℓ E) P N h
  · exact vertex
  · exact hL

end AlgebraicGeometry.ProEtale.QlbarInternalHom
