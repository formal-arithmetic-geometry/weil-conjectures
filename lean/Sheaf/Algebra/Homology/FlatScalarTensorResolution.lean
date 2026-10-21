/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Algebra.Homology.FlatScalarRealization
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.LeftDerived
import Sheaf.Algebra.Homology.FlatScalarRealizationExact
import Sheaf.Algebra.Homology.FlatScalarRealizationFlat
import Sheaf.Algebra.Homology.FlatScalarTensorComparison
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
/-! # Scalar projective resolutions compute the sheaf tensor -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open ZeroObject

namespace SheafOfModules

/-- A scalar projective resolution, tensored before realization, computes the
recorded sheaf derived tensor after flat realization.
Source: Stacks Project, Cohomology on Sites, Tags 06YQ, 06YP and 06YU;
Modules on Sites, Tags 093J, 03ER and 03EK
(blueprint: lem-sfb-flat-scalar-tensor-resolution).

Proof: exact scalar realization carries the projective resolution augmentation
and its cochain reindexing to a quasi-isomorphism. Scalar projective modules are
flat, and flatScalarRealization_flat makes every realized term flat. The complex
is nonpositive, so bounded-above flatness gives both the recorded and categorical
K-flatness. Resolve the degree-zero realization of Q, apply the proved total
tensor comparison, and use categorical K-flatness to remove that resolution.
The single-factor total tensor comparison leaves only the differential from the
resolved factor. Apply the natural ordinary scalar tensor comparison degreewise,
and commute the scalar tensor functor with cochain extension n maps to -n. These
chain isomorphisms give the exact displayed model. No finite-presentation, DVR,
point, or nonempty-site hypothesis is required. -/
theorem flat_scalar_tensor_resolution
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {A : Type (max u v)} [CommRing A] {R : Sheaf J CommRingCat.{max u v}}
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasDerivedCategory.{w, max u v, (max u v) + 1} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))]
    (α : realizationRing J A ⟶ R)
    (hflat : IsFlatOnSite (J := J) (R := realizationRing J A)
      ((restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map α)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))) :
    ∀ P Q : ModuleCat.{max u v} A,
      Nonempty ((siteDerivedTensorIndependentCoefficients J R).obj
          ((DerivedCategory.singleFunctor _ 0).obj ((flatScalarRealization J α).obj P),
            (DerivedCategory.singleFunctor _ 0).obj ((flatScalarRealization J α).obj Q)) ≅
        DerivedCategory.Q.obj
          (((flatScalarRealization J α).mapHomologicalComplex (.up ℤ)).obj
            ((((MonoidalCategory.tensorRight Q).mapHomologicalComplex (.down ℕ)).obj
              (projectiveResolution P).complex).extend (ComplexShape.embeddingUpIntLE 0)))) := by
  classical
  let F := flatScalarRealization J α
  let D := SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive R
  have (M : D) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
    have := tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (tensorLeft M)
  have (M : D) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : ∀ X Y Z : GradedObject ℤ D,
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := by infer_instance
  have : ∀ X Y Z : GradedObject ℤ D,
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := by infer_instance
  have : ∀ X Y Z W : GradedObject ℤ D,
      GradedObject.HasTensor₄ObjExt X Y Z W := by infer_instance
  have : AB5OfSize.{max u v, max u v} AddCommGrpCat.{max u v} := inferInstance
  have : AB5OfSize.{0, 0} AddCommGrpCat.{max u v} := AB5OfSize_shrink _
  have : HasExactColimitsOfShape ℤ D :=
    HasExactColimitsOfShape.domain_of_functor ℤ (toSheaf _)
  have := (flatScalarRealization_exact J α hflat).1
  have := (flatScalarRealization_exact J α hflat).2
  intro P Q
  let K : CochainComplex (ModuleCat.{max u v} A) ℤ :=
    (projectiveResolution P).complex.extend (ComplexShape.embeddingUpIntLE 0)
  let L : CochainComplex D ℤ := (F.mapHomologicalComplex (.up ℤ)).obj K
  have hLf (i : ℤ) : IsFlatOnSite (J := J) (R := R) (L.X i) := by
    apply flatScalarRealization_flat J α
    infer_instance
  have hb : L.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact F.map_isZero ((projectiveResolution P).complex.isZero_extend_X _ i
      (by intro n; change 0 - (n : ℤ) ≠ i; omega))
  have hL : L.IsKFlatIndependentCoefficients :=
    isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R L 0 hLf
  let f : K ⟶ (CochainComplex.singleFunctor (ModuleCat A) 0).obj P :=
    HomologicalComplex.extendMap (projectiveResolution P).π
        (ComplexShape.embeddingUpIntLE 0) ≫
      (HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntLE 0) P
        0 0 (by simp)).hom
  have : QuasiIso f := by dsimp [f]; infer_instance
  let g := (F.mapHomologicalComplex (.up ℤ)).map f ≫
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app P).hom
  have : QuasiIso g := by dsimp [g]; infer_instance
  let eP : DerivedCategory.Q.obj L ≅ (DerivedCategory.singleFunctor D 0).obj (F.obj P) :=
    asIso (DerivedCategory.Q.map g) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ D 0).app (F.obj P)).symm
  let S := (CochainComplex.singleFunctor D 0).obj (F.obj Q)
  let eQ : DerivedCategory.Q.obj S ≅ (DerivedCategory.singleFunctor D 0).obj (F.obj Q) :=
    ((DerivedCategory.singleFunctorIsoCompQ D 0).app (F.obj Q)).symm
  have hcat : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat L :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat L 0
      (fun i ↦ flat_to_cat R _ (hLf i))
  obtain ⟨U, a, hU, hUf, ha, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) S
  have hUf' (i : ℤ) : IsFlatOnSite (J := J) (R := R) (U.X i) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R _).symm (hUf i)
  have : QuasiIso a := ha
  let eU : DerivedCategory.Q.obj U ≅ (DerivedCategory.singleFunctor D 0).obj (F.obj Q) :=
    asIso (DerivedCategory.Q.map a) ≪≫ eQ
  obtain ⟨eTotal⟩ :=
    (KFlatTotalTensorModel.kFlat_total_tensor_model R L U hL hU hLf hUf').2.2.2
  have hmap : QuasiIso ((tensorLeft L).map a) := hcat.1 _ ha
  have : IsIso (DerivedCategory.Q.map ((tensorLeft L).map a)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso D _).2 hmap
  let T := siteDerivedTensorIndependentCoefficients J R
  let eDerived := (T.mapIso (eP.prod eU)).symm ≪≫ eTotal.symm ≪≫
    asIso (DerivedCategory.Q.map ((tensorLeft L).map a))
  obtain ⟨τ⟩ := flat_scalar_tensor_comparison J α Q
  let τ' : F ⋙ tensorRight (F.obj Q) ≅ tensorRight Q ⋙ F :=
    (Functor.isoWhiskerLeft F (siteSheafTensorRightIso R (F.obj Q))).symm ≪≫ τ
  let eTensor := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) (F.obj Q) L
  let eScalar := (Functor.mapHomologicalComplexCompIso τ' (.up ℤ)).app K
  let eExtend := F.mapHomologicalComplex (.up ℤ) |>.mapIso
    ((projectiveResolution P).complex.mapExtendIso
      (ComplexShape.embeddingUpIntLE 0) (tensorRight Q))
  exact ⟨eDerived ≪≫ DerivedCategory.Q.mapIso (eTensor ≪≫ eScalar ≪≫ eExtend)⟩

end SheafOfModules
