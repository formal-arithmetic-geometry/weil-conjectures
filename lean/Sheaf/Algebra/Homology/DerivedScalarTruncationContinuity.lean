/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.Algebra.Homology.RingedToposPullbackFilteredColimits
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplex
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-! # Derived scalar extension and upper truncations

Source: Stacks Project, Cohomology on Sites, Tag 077J, and Modules on Sites,
Tags 03DB and 03EP. This is the colimit step of the cohomological-bounds argument.
-/

@[expose] public section

set_option autoImplicit false

universe w r u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace SheafOfModules

private theorem lower_bound_colimit
    {A I : Type*} [Category* A] [Abelian A] [Category* I]
    [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
    (D : I ⥤ CochainComplex A ℤ) (c : Cocone D) (hc : IsColimit c)
    (a : ℤ) (hD : ∀ j, (D.obj j).IsGE a) : c.pt.IsGE a := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  let T : ShortComplex (I ⥤ A) :=
    (ShortComplex.functorEquivalence I A).inverse.obj
      (D ⋙ HomologicalComplex.shortComplexFunctor A (.up ℤ) i)
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
    intro j
    have := hD j
    exact IsZero.of_iso ((D.obj j).exactAt_of_isGE a i hi).isZero_homology
      (T.mapHomologyIso ((CategoryTheory.evaluation I A).obj j)).symm
  have hc₁ := isColimitOfPreserves
    (HomologicalComplex.eval A (.up ℤ) ((ComplexShape.up ℤ).prev i)) hc
  have hc₂ := isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) i) hc
  have hc₃ := isColimitOfPreserves
    (HomologicalComplex.eval A (.up ℤ) ((ComplexShape.up ℤ).next i)) hc
  exact colim.exact_mapShortComplex hT hc₁ hc₂ hc₃
    (c.pt.d _ i) (c.pt.d i _)
    (fun j ↦ (c.ι.app j).comm _ _) (fun j ↦ (c.ι.app j).comm _ _)

/-- A scalar-extension functor computed on K-flat complexes inherits a lower bound
from all finite upper truncations of a complex.
Source: Stacks Project, Cohomology on Sites, Tag 077J; Modules on Sites,
Tags 03DB and 03EP. Agent consequence, not a verbatim assertion of those tags.
(blueprint: lem-sbc-derived-scalar-truncation-continuity).

Proof: use the reduced functorial flat resolution to resolve every good upper
truncation of G compatibly. The integer-indexed degreewise colimit P of these
bounded-above flat resolutions maps quasi-isomorphically to G: exact filtered
colimits commute with cohomology, and in every degree the truncation cohomology
is eventually that of G. Each stage is K-flat, and filtered colimits of K-flat
complexes are K-flat because tensor commutes with them and exact colimits preserve
acyclicity. The supplied computation isomorphisms identify F(Q(P)) with E(P), and
likewise at each bounded stage. Scalar extension is left adjoint to restriction
of scalars, so termwise E commutes with this colimit. Each E(stage) has vanishing
cohomology below a by the hypothesis and the quasi-isomorphism to its truncation.
Exact filtered colimits therefore give the same vanishing for E(P). Transport
along Q(P) ≅ Q(G) gives the conclusion. The indexing integers are lifted to the
coefficient universe when necessary. Zero complexes, zero rings, and arbitrary
negative a are covered by the same argument; no upper bound on G is used. -/
theorem derivedScalar_lower_bound_of_truncations
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S))]
    (E : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S))
    (hobj : ∀ N, E.obj N = changeOfRings.{v, u, r} φ N)
    (hmap : ∀ {N N'} (f : N ⟶ N'), E.map f = eqToHom (hobj N) ≫
      changeOfRingsHom.{v, u, r} φ N f ≫ eqToHom (hobj N').symm)
    [E.Additive]
    (F : DerivedCategory
        (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⥤
      DerivedCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S)))
    (hcompute : ∀ P : CochainComplex
        (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) ℤ,
      P.IsKFlatIndependentCoefficients →
        Nonempty (F.obj (DerivedCategory.Q.obj P) ≅
          DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)))
    (G : CochainComplex
      (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) ℤ)
    (a : ℤ)
    (hfinite : ∀ b : ℤ, (F.obj (DerivedCategory.Q.obj (G.truncLE b))).IsGE a) :
    (F.obj (DerivedCategory.Q.obj G)).IsGE a := by
  let A := SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)
  let B := SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S)
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive R
  have (M : A) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) := by
    have := tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (MonoidalCategory.tensorLeft M)
  have (M : A) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : ∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂ := by
    infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ A,
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ A,
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A,
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance
  have : AB5OfSize.{0, 0} AddCommGrpCat.{r} :=
    AB5OfSize_of_univLE.{0, 0, r, r} AddCommGrpCat.{r}
  have : HasExactColimitsOfShape ℤ A :=
    HasExactColimitsOfShape.domain_of_functor ℤ (toSheaf _)
  have : HasExactColimitsOfShape ℤ B :=
    HasExactColimitsOfShape.domain_of_functor ℤ (toSheaf _)
  let := hasFunctorialFlatResolution_kfi R
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ A))).reduced
  let L := Λ.minusResolutionFunctor ⋙
    (ObjectProperty.flat.ι : _ ⥤ A).mapCochainComplexMinus ⋙ CochainComplex.Minus.ι A
  let D := G.filtrationLEMinus ⋙ L
  let P := Λ.resolutionFunctor.obj G
  have hp : QuasiIso (Λ.resolutionNatTrans.app G) := inferInstance
  have hk : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P :=
    Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le G
  have hP : P.IsKFlatIndependentCoefficients := by
    intro Z hZ
    let T := MonoidalCategory.tensorRight P
    have hz : QuasiIso (0 : (0 : CochainComplex A ℤ) ⟶ Z) := by
      rw [quasiIso_iff]
      intro i
      exact (quasiIsoAt_iff_exactAt _ i
        ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
    have hmap : QuasiIso (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) := hk.2 _ hz
    have htzero : (T.obj (0 : CochainComplex A ℤ)).Acyclic :=
      HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
    exact fun i ↦ (exactAt_iff_of_quasiIsoAt
      (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) i).1 (htzero i)
  obtain ⟨eP⟩ := hcompute P hP
  have : PreservesColimitsOfSize.{0, 0} E :=
    preservesColimits_specifiedChangeOfRings φ E hobj hmap
  let T := E.mapHomologicalComplex (.up ℤ)
  have hstage (b : ℤ) : CochainComplex.IsGE (T.obj (D.obj b)) a := by
    let K := G.filtrationLEMinus.obj b
    let P₀ := D.obj b
    have : K.obj.IsStrictlyLE b := by
      change (G.truncLE b).IsStrictlyLE b
      infer_instance
    have hbound : CochainComplex.IsStrictlyLE P₀ b := by
      have : (Λ.bicomplexFunctor.obj K.obj).HasTotal (.up ℤ) :=
        HomologicalComplex₂.hasTotal_of_isStrictlyLE _ b 0
      have : CochainComplex.IsStrictlyLE
          ((Λ.bicomplexFunctor.obj K.obj).total (.up ℤ)) b := inferInstance
      change CochainComplex.IsStrictlyLE
        (((ObjectProperty.flat.ι : _ ⥤ A).mapHomologicalComplex (.up ℤ)).obj
          ((Λ.bicomplexFunctor.obj K.obj).total (.up ℤ))) b
      exact (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff _
        (ObjectProperty.flat.ι : _ ⥤ A) b).2 inferInstance
    have hf (i : ℤ) : IsFlatOnSite (J := J) (R := R) (P₀.X i) := by
      exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P₀.X i)).symm
        (((Λ.bicomplexFunctor.obj K.obj).total (.up ℤ)).X i).property.2
    have hk₀ := isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R P₀ b hf
    obtain ⟨e₀⟩ := hcompute P₀ hk₀
    have : (F.obj (DerivedCategory.Q.obj K.obj)).IsGE a := hfinite b
    have : (F.obj (DerivedCategory.Q.obj P₀)).IsGE a :=
      DerivedCategory.TStructure.t.isGE_of_iso
        (F.mapIso (asIso (DerivedCategory.Q.map (Λ.totalπ K)))).symm a
    rw [← DerivedCategory.isGE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso e₀ a
  have hE : CochainComplex.IsGE (T.obj P) a := by
    apply lower_bound_colimit (D ⋙ T) (T.mapCocone (colimit.cocone D))
      (isColimitOfPreserves T (colimit.isColimit D)) a hstage
  have : (F.obj (DerivedCategory.Q.obj P)).IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso eP.symm a
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (F.mapIso (asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app G)))) a

end SheafOfModules
