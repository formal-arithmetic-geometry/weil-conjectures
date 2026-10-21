/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedInternalHomFilteredColimitData

import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-! # Filtered continuity for the strict internal-Hom roof -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u v r w a
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex MonoidalCategory
namespace WeilConjectures.SfbHomFilteredColimit

section Exactness
variable {A : Type a} [Category.{w} A] [Abelian A]
  [MonoidalCategory A] [MonoidalPreadditive A]

omit [Abelian A] [MonoidalPreadditive A] in
private theorem tensorLeft_unit_exact : PreservesFiniteLimits (tensorLeft (𝟙_ A)) := by
  exact preservesFiniteLimits_of_natIso (leftUnitorNatIso A).symm

private theorem tensorLeft_finiteFree_exact (d : ℕ) :
    PreservesFiniteLimits
      (tensorLeft (limit (Discrete.functor (fun _ : Fin d ↦ 𝟙_ A)))) := by
  let D := Discrete.functor (fun _ : Fin d ↦ 𝟙_ A)
  have : PreservesLimit D (curriedTensor A) :=
    preservesLimit_of_evaluation _ D (fun X ↦
      inferInstanceAs (PreservesLimit D (tensorRight X)))
  let e : tensorLeft (limit D) ≅ (D ⋙ curriedTensor A).flip ⋙ lim :=
    preservesLimitIso (curriedTensor A) D ≪≫ limitIsoFlipCompLim _
  have : PreservesFiniteLimits ((D ⋙ curriedTensor A).flip) :=
    preservesFiniteLimits_of_evaluation _ (fun j ↦ tensorLeft_unit_exact)
  exact preservesFiniteLimits_of_natIso e.symm

variable [HasColimitsOfSize.{w, w} A]
  [∀ X : A, PreservesColimitsOfSize.{w, w} (tensorRight X)]
  {I : Type w} [SmallCategory I] [HasExactColimitsOfShape I A]

omit [Abelian A] [MonoidalPreadditive A] in
private theorem tensorLeft_colimit_exact (T : I ⥤ A)
    (hT : ∀ i, PreservesFiniteLimits (tensorLeft (T.obj i))) :
    PreservesFiniteLimits (tensorLeft (colimit T)) := by
  have : ∀ i, PreservesFiniteLimits (tensorLeft (T.obj i)) := hT
  have : PreservesColimit T (curriedTensor A) :=
    preservesColimit_of_evaluation _ T (fun X ↦
      inferInstanceAs (PreservesColimit T (tensorRight X)))
  let e : tensorLeft (colimit T) ≅ (T ⋙ curriedTensor A).flip ⋙ colim :=
    preservesColimitIso (curriedTensor A) T ≪≫ colimitIsoFlipCompColim _
  have : PreservesFiniteLimits ((T ⋙ curriedTensor A).flip) :=
    preservesFiniteLimits_of_evaluation _ (fun j ↦ hT j)
  exact preservesFiniteLimits_of_natIso e.symm
end Exactness

section Transport
variable {A : Type a} [Category.{w} A] [Abelian A]
  [HasColimitsOfSize.{w, w} A]
  {I : Type w} [SmallCategory I] [HasExactColimitsOfShape I A]

private theorem post_quasiIso_transport
    (M N : I ⥤ CochainComplex A ℤ) (η : M ⟶ N)
    (H : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (hH : ∀ {K L : CochainComplex A ℤ} (f : K ⟶ L), QuasiIso f → QuasiIso (H.map f))
    (hη : ∀ i, QuasiIso (η.app i))
    (hM : QuasiIso (colimit.post M H)) : QuasiIso (colimit.post N H) := by
  have hηH : QuasiIso (colimMap (Functor.whiskerRight η H)) :=
    (HomologicalComplex.quasiIso A (.up ℤ)).colimMap _ (fun i ↦ hH _ (hη i))
  have hηc : QuasiIso (colimMap η) :=
    (HomologicalComplex.quasiIso A (.up ℤ)).colimMap η hη
  have hηcH : QuasiIso (H.map (colimMap η)) := hH _ hηc
  have heq : colimMap (Functor.whiskerRight η H) ≫ colimit.post N H =
      colimit.post M H ≫ H.map (colimMap η) := by
    exact (colimit.map_post η H).symm
  have hcomp : QuasiIso
      (colimMap (Functor.whiskerRight η H) ≫ colimit.post N H) := by
    rw [heq]
    infer_instance
  exact quasiIso_of_comp_left (colimMap (Functor.whiskerRight η H)) (colimit.post N H)
end Transport

section TensorMap
variable {A : Type a} [Category.{w} A] [Abelian A]
  [MonoidalCategory A] [MonoidalPreadditive A]

private theorem tensorSingle_map_quasiIso (T : A)
    [PreservesFiniteLimits (tensorLeft T)] [PreservesFiniteColimits (tensorLeft T)]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (mapBifunctorMap (𝟙 ((single A (.up ℤ) 0).obj T)) f
      (curriedTensor A) (.up ℤ)) := by
  have hmap : QuasiIso (((tensorLeft T).mapHomologicalComplex (.up ℤ)).map f) :=
    inferInstance
  have hcomp : QuasiIso
      (mapBifunctorMap (𝟙 ((single A (.up ℤ) 0).obj T)) f
        (curriedTensor A) (.up ℤ) ≫
          (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor A) T L).hom) := by
    rw [CochainComplex.mapBifunctorSingle₁Iso_hom_naturality]
    infer_instance
  exact quasiIso_of_comp_right _
    (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor A) T L).hom
end TensorMap

section Assemble
variable {A : Type a} [Category.{w} A] [Abelian A]
  [HasColimitsOfSize.{w, w} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [∀ X : A, PreservesColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : A, PreservesColimitsOfSize.{w, w} (tensorRight X)]
  {I : Type w} [SmallCategory I] [HasExactColimitsOfShape I A]

private theorem tensor_continuity
    (T : I ⥤ A)
    (hfree : ∀ i, ∃ d : ℕ,
      Nonempty (T.obj i ≅ limit (Discrete.functor (fun _ : Fin d ↦ 𝟙_ A))))
    (L L' : CochainComplex A ℤ) (e : L ⟶ L') (he : QuasiIso e)
    (H : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (hH : ∀ {K N : CochainComplex A ℤ} (f : K ⟶ N), QuasiIso f → QuasiIso (H.map f))
    (hcont : ∀ (M : I ⥤ CochainComplex A ℤ) (b : ℤ),
      (∀ i n, n < b → IsZero ((M.obj i).X n)) → QuasiIso (colimit.post M H))
    (b : ℤ) (hL : ∀ n, n < b → IsZero (L.X n)) :
    let Q := (curriedTensor A).map₂CochainComplex
    let U := single A (.up ℤ) 0
    QuasiIso (H.map ((Q.obj (U.obj (colimit T))).map e)) ∧
    QuasiIso (colimit.post T (U ⋙ Q.flip.obj L' ⋙ H)) ∧
    IsIso (colimit.post T (U ⋙ Q.flip.obj (H.obj L))) := by
  let Q := (curriedTensor A).map₂CochainComplex
  let U := single A (.up ℤ) 0
  let F (B : CochainComplex A ℤ) := U ⋙ Q.flip.obj B
  have hF (B : CochainComplex A ℤ) : PreservesColimitsOfShape I (F B) := by
    dsimp [F, U, Q]
    infer_instance
  have hstage (i : I) : PreservesFiniteLimits (tensorLeft (T.obj i)) := by
    obtain ⟨d, ⟨α⟩⟩ := hfree i
    have := tensorLeft_finiteFree_exact (A := A) d
    exact preservesFiniteLimits_of_natIso ((curriedTensor A).mapIso α).symm
  have hcolim : PreservesFiniteLimits (tensorLeft (colimit T)) :=
    tensorLeft_colimit_exact T hstage
  have hm : QuasiIso ((Q.obj (U.obj (colimit T))).map e) := by
    have : QuasiIso e := he
    exact tensorSingle_map_quasiIso (colimit T) e
  have hd : QuasiIso (H.map ((Q.obj (U.obj (colimit T))).map e)) := hH _ hm
  have hbound : ∀ i n, n < b → IsZero (((T ⋙ F L).obj i).X n) := by
    intro i n hn
    exact ((tensorLeft (T.obj i)).map_isZero (hL n hn)).of_iso
      (CochainComplex.mapBifunctorSingle₁XIso (curriedTensor A) (T.obj i) L n)
  have hp : QuasiIso (colimit.post (T ⋙ F L) H) := hcont _ b hbound
  let α : T ⋙ F L ⟶ T ⋙ F L' :=
    Functor.whiskerLeft T (Functor.whiskerLeft U (Q.flip.map e))
  have hα (i : I) : QuasiIso (α.app i) := by
    have := hstage i
    have : QuasiIso e := he
    exact tensorSingle_map_quasiIso (T.obj i) e
  have hq : QuasiIso (colimit.post (T ⋙ F L') H) :=
    post_quasiIso_transport _ _ α H hH hα hp
  have hc : QuasiIso (colimit.post T (F L' ⋙ H)) := by
    rw [← colimit.post_post]
    have := hF L'
    infer_instance
  have hs : IsIso (colimit.post T (F (H.obj L))) := by
    have := hF (H.obj L)
    infer_instance
  exact ⟨hd, hc, hs⟩
end Assemble

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]

private theorem hom_preserves (R : Sheaf J CommRingCat.{max u v r})
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ)
    {K L : CochainComplex (Modules.{u, v, r} J R) ℤ}
    (f : K ⟶ L) (hf : QuasiIso f) :
    QuasiIso ((homFixed.{u, v, r} J R P).map f) := by
  let :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, v, r}
      J R).1
  have : QuasiIso f := hf
  let B := SheafOfModules.{max u v r} ((sheafCompose J
    (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)
  let E := coefficientHomResolution.{r, u, v} J R
  let η := CochainComplex.toKInjectiveResolution.{max u v r} B
  have hη (X : CochainComplex B ℤ) : QuasiIso (η.app X) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max u v r} B X).2
  have hnat : η.app K ≫ E.map f = f ≫ η.app L := η.naturality f |>.symm
  have hcomp : QuasiIso (η.app K ≫ E.map f) := by
    rw [hnat]
    have := hη L
    exact quasiIso_comp f (η.app L)
  have hs : QuasiIso (E.map f) := by
    have := hη K
    exact quasiIso_of_comp_left (η.app K) (E.map f)
  have hKI : (E.obj K).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max u v r} B K
  have hLI : (E.obj L).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max u v r} B L
  have h := quasiIso_homComplex_mapOfUniverses.{u, v, r} (E.map f) (𝟙 P)
  rw [show (𝟙 P).op = 𝟙 (op P) from rfl,
    (homComplexFunctor.{u, v, max u v r, max u v r} (R := R)).map_id,
    NatTrans.id_app, Category.id_comp] at h
  exact h

/-- Continuity and exact coefficient tensor give the colimit-side roof denominator.
Source: Bhatt--Scholze, Lemma 6.8.12 and Remark 6.8.15, steps 2--3 and 8--9 of the
conditional ring-sheaf argument; Stacks Project, Tags 06YN, 08J9 and 079P.
(blueprint: lem-sfb-internal-hom-filtered-continuity).

Proof: sheaf tensor preserves colimits. At each finite-free stage it is a finite sum of
the identity, hence exact; exact filtered colimits show tensor by the colimit coefficient
is exact as well. This proves that tensoring the augmentation of L is a quasi-isomorphism,
and functorial derived Hom preserves it, giving the roof denominator. For the comparison
post map, use a good lower truncation of L with the supplied common lower bound. Exact
stage tensor preserves that bound, so the continuity hypothesis identifies the filtered
colimit of their derived Hom representatives with derived Hom of their colimit. The
augmentation L to its K-injective replacement induces quasi-isomorphisms both at the
stages and at the colimit. Exact filtered colimits preserve those quasi-isomorphisms;
the natural augmentation square and two-out-of-three therefore transport continuity
from L to its possibly unbounded K-injective replacement. Tensor preservation supplies
the last colimit isomorphism. The proof never assumes that the replacement itself has
a lower bound or that Hom(P,I(L)) is bounded. -/
theorem internalHom_filtered_continuity (R : Sheaf J CommRingCat.{max u v r})
    {I : Type (max u v r)} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I (Modules.{u, v, r} J R)]
    [HasExactColimitsOfShape I (Modules.{u, v, r} J R)]
    (T : I ⥤ Modules.{u, v, r} J R)
    (hfree : ∀ i : I, ∃ d : ℕ, Nonempty
      (T.obj i ≅ limit (Discrete.functor (fun _ : Fin d ↦
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)))))
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hcont : Continuous.{u, v, r} J R (I := I) P)
    (b : ℤ) (hL : ∀ n : ℤ, n < b → IsZero (L.X n)) :
    QuasiIso (roofDenominator.{u, v, r} J R P L (colimit T)) ∧
    QuasiIso (colimit.post T
      (tensorFixed.{u, v, r} J R ((coefficientHomResolution.{r, u, v} J R).obj L) ⋙
        homFixed.{u, v, r} J R P)) ∧
    IsIso (colimit.post T
      (tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L))) := by
  -- K-flatness is retained in the interface; this step uses derived Hom invariance.
  have _ := hP
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let M := Modules.{u, v, r} J R
  have (X : M) : PreservesColimitsOfSize.{max u v r, max u v r} (tensorLeft X) :=
    SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R X
  have (X : M) : PreservesColimitsOfSize.{max u v r, max u v r} (tensorRight X) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  let (X : M) : (tensorLeft X).Additive :=
    SheafOfModules.tensorLeft_additive_independent R X
  have (X : M) : (tensorRight X).Additive :=
    Functor.additive_of_iso (F := tensorLeft X) (BraidedCategory.tensorLeftIsoTensorRight X)
  let : MonoidalPreadditive M :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  have hη : QuasiIso ((resolutionUnit.{u, v, r} J R).app L) := by
    let :=
      (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, v, r}
        J R).1
    exact (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max u v r} M L).2
  let Q := (curriedTensor M).map₂CochainComplex
  let U := single M (.up ℤ) 0
  have hfixed (B : CochainComplex M ℤ) : tensorFixed.{u, v, r} J R B =
      U ⋙ Q.flip.obj B := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro X Y f
    change (Q.map (U.map f)).app B ≫ (Q.obj (U.obj Y)).map (𝟙 B) =
      (Q.map (U.map f)).app B
    rw [(Q.obj (U.obj Y)).map_id, Category.comp_id]
  obtain ⟨hd, hc, hs⟩ := tensor_continuity T hfree L
    ((coefficientHomResolution.{r, u, v} J R).obj L)
    ((resolutionUnit.{u, v, r} J R).app L) hη (homFixed.{u, v, r} J R P)
    (fun f hf ↦ hom_preserves.{u, v, r} J R P f hf) hcont b hL
  refine ⟨?_, ?_, ?_⟩
  · simpa [roofDenominator, tensor, coefficientTotalTensor] using hd
  · rw [hfixed]
    exact hc
  · rw [hfixed]
    exact hs

end WeilConjectures.SfbHomFilteredColimit
