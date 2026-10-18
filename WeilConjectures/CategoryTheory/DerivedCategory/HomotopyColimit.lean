/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.Abelian.SequentialColimit
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Homotopy colimits in the derived category

Let `C` be an abelian category in which colimits of shape `ℕ` are exact (for instance a
Grothendieck abelian category, such as the category of sheaves of modules on the small étale
site of a scheme), with K-injective resolutions.

* For a sequence `F₀ ⟶ F₁ ⟶ ⋯` of cochain complexes, the image in `D(C)` of its termwise colimit
  is a homotopy colimit of the images of the `Fₙ`
  (`DerivedCategory.isHomotopyColimit_mapCocone_Q`): the sequence
  `0 ⟶ ∐ Fₙ ──1 - t──▶ ∐ Fₙ ⟶ colim Fₙ ⟶ 0` is short exact
  (`CategoryTheory.Limits.shortExact_sequenceShift`), and the coproduct of complexes is a
  coproduct in `D(C)`.
* Every `E ∈ D(C)` is the homotopy colimit of its truncations `τ^{≤ N} E`
  (`DerivedCategory.isHomotopyColimit_truncLECocone`): if `E = Q(K)`, then `τ^{≤ N} E = Q(τ^{≤ N} K)`
  and `K` is the termwise colimit of the `τ^{≤ N} K`, the sequence of terms in each degree being
  eventually constant.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

section Colimit

variable [Abelian.HasKInjectiveResolutions C] [HasColimitsOfShape ℕ C]
  [HasExactColimitsOfShape ℕ C] [HasCoproductsOfShape ℕ C]

/-- Blueprint `lem-kun-complex-colimit-hocolim`: Sequential colimits represent homotopy colimits.

For a sequence `F₀ ⟶ F₁ ⟶ ⋯` of cochain complexes in an abelian category `C` with exact colimits
of shape `ℕ` (e.g. étale sheaves of modules), the image in `D(C)` of a colimit cocone of the
sequence is a homotopy colimit cocone: the termwise colimit is the homotopy colimit
`hocolim Q(Fₙ)`. Indeed `0 ⟶ ∐ Fₙ ──1 - t──▶ ∐ Fₙ ⟶ colim Fₙ ⟶ 0` is a short exact sequence of
complexes (`CategoryTheory.Limits.shortExact_sequenceShift`), whose distinguished triangle in
`D(C)` is the defining triangle of the homotopy colimit, the coproduct of complexes being a
coproduct in `D(C)` (`DerivedCategory.isColimitCofanMkQObj`). -/
theorem isHomotopyColimit_mapCocone_Q (F : ℕ ⥤ CochainComplex C ℤ) {c : Cocone F}
    (hc : IsColimit c) : IsHomotopyColimit (Q.mapCocone c) := by
  let P : Cofan fun n : ℕ ↦ F.obj n := Cofan.mk (∐ fun n ↦ F.obj n) (Sigma.ι _)
  let hP : IsColimit P := coproductIsCoproduct _
  have hS := shortExact_sequenceShift F hP hc
  let P' : Cofan fun n : ℕ ↦ (F ⋙ Q).obj n := Cofan.mk (Q.obj P.pt) fun n ↦ Q.map (P.inj n)
  let hP' : IsColimit P' := isColimitCofanMkQObj hP
  have ht : Q.map (sequenceShift hP) = sequenceShift hP' :=
    Cofan.IsColimit.hom_ext hP' _ _ fun n ↦ by
      change Q.map (P.inj n) ≫ _ = Q.map (P.inj n) ≫ _
      rw [← Q.map_comp, inj_sequenceShift, Q.map_comp]
      exact (inj_sequenceShift hP' n).symm
  refine ⟨P', hP', triangleOfSESδ hS, isomorphic_distinguished _
    (triangleOfSES_distinguished hS) _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_)⟩
  · simp [triangleOfSES, ht, Functor.map_sub]
  · refine Cofan.IsColimit.hom_ext hP' _ _ fun n ↦ ?_
    change Q.map (P.inj n) ≫ _ = Q.map (P.inj n) ≫ _
    simp only [triangleOfSES, Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₂,
      Iso.refl_hom, Category.comp_id, Category.id_comp, ← Q.map_comp, Cofan.IsColimit.fac]
    exact (Cofan.IsColimit.fac hP' _ n).symm
  · simp [triangleOfSES]

end Colimit

section Truncation

open TStructure

/-- The sequence `τ^{≤ 0} E ⟶ τ^{≤ 1} E ⟶ τ^{≤ 2} E ⟶ ⋯` of truncations of `E ∈ D(C)`. -/
noncomputable def truncLESequence (E : DerivedCategory C) : ℕ ⥤ DerivedCategory C :=
  Functor.ofSequence fun n : ℕ ↦
    (t.natTransTruncLEOfLE (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).app E

/-- The cocone `τ^{≤ N} E ⟶ E` over the sequence of truncations of `E`. -/
@[simps pt]
noncomputable def truncLECocone (E : DerivedCategory C) : Cocone (truncLESequence E) where
  pt := E
  ι := NatTrans.ofSequence (fun n ↦ (t.truncLEι (n : ℤ)).app E) (fun n ↦ by
    simp [truncLESequence])

@[simp]
lemma truncLECocone_ι_app (E : DerivedCategory C) (n : ℕ) :
    (truncLECocone E).ι.app n = (t.truncLEι (n : ℤ)).app E := rfl

/-- The truncations of a morphism, as a morphism of sequences of truncations. -/
noncomputable def truncLESequenceMap {E E' : DerivedCategory C} (f : E ⟶ E') :
    truncLESequence E ⟶ truncLESequence E' :=
  NatTrans.ofSequence (fun n ↦ (t.truncLE (n : ℤ)).map f) (fun n ↦ by
    simp [truncLESequence])

/-- The sequence `τ^{≤ 0} K ⟶ τ^{≤ 1} K ⟶ ⋯` of canonical truncations of a cochain complex. -/
noncomputable def complexTruncLESequence (K : CochainComplex C ℤ) : ℕ ⥤ CochainComplex C ℤ :=
  Functor.ofSequence fun n : ℕ ↦ K.truncLEMapOfLE (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)

/-- The cocone `τ^{≤ N} K ⟶ K` over the sequence of truncations of a cochain complex. -/
@[simps pt]
noncomputable def complexTruncLECocone (K : CochainComplex C ℤ) :
    Cocone (complexTruncLESequence K) where
  pt := K
  ι := NatTrans.ofSequence (fun n ↦ K.ιTruncLE (n : ℤ)) (fun n ↦ by
    simp [complexTruncLESequence])

/-- A cochain complex is the termwise colimit of its canonical truncations `τ^{≤ N} K`: in each
degree the sequence of terms is eventually constant. -/
noncomputable def isColimitComplexTruncLECocone (K : CochainComplex C ℤ) :
    IsColimit (complexTruncLECocone K) :=
  HomologicalComplex.isColimitOfEval _ _ fun i ↦
    isColimitOfIsEventuallyConstant _ (i + 1).toNat fun j f ↦
      K.isIso_ιTruncLE_f _ _ (by have := leOfHom f; omega)

lemma isIso_homologyFunctor_map_truncLEι_app (n q : ℤ) (hq : q ≤ n) (X : DerivedCategory C) :
    IsIso ((homologyFunctor C q).map ((t.truncLEι n).app X)) :=
  have : ((t.triangleLEGT n).obj X).obj₃.IsGE (n + 1) :=
    (inferInstance : t.IsGE ((t.truncGT n).obj X) (n + 1))
  isIso_homologyMap_mor₁ _ (t.triangleLEGT_distinguished n X) (q - 1) q
    (by lia) (isZero_of_isGE _ (n + 1) _ (by lia)) (isZero_of_isGE _ (n + 1) _ (by lia))

lemma isIso_liftTruncLE_Q_map_ιTruncLE (K : CochainComplex C ℤ) (n : ℤ) :
    IsIso (t.liftTruncLE (Q.map (K.ιTruncLE n)) n) := by
  rw [isIso_iff]
  intro q
  by_cases hq : q ≤ n
  · have h₁ : IsIso ((homologyFunctor C q).map (Q.map (K.ιTruncLE n))) := by
      have : QuasiIsoAt (K.ιTruncLE n) q := K.quasiIsoAt_ιTruncLE n q hq
      exact (NatIso.isIso_map_iff (homologyFunctorFactors C q) (K.ιTruncLE n)).2
        (by dsimp; infer_instance)
    have := isIso_homologyFunctor_map_truncLEι_app n q hq (Q.obj K)
    rw [← t.liftTruncLE_ι (Q.map (K.ιTruncLE n)) n, Functor.map_comp] at h₁
    exact IsIso.of_isIso_comp_right _
      ((homologyFunctor C q).map ((t.truncLEι n).app (Q.obj K)))
  · exact ⟨0, (isZero_of_isLE _ n q (by lia)).eq_of_src _ _,
      (isZero_of_isLE _ n q (by lia)).eq_of_src _ _⟩

/-- The truncation `Q(τ^{≤ n} K) ≅ τ^{≤ n} Q(K)` of a cochain complex. -/
noncomputable def QObjTruncLEIso (K : CochainComplex C ℤ) (n : ℤ) :
    Q.obj (K.truncLE n) ≅ (t.truncLE n).obj (Q.obj K) :=
  have := isIso_liftTruncLE_Q_map_ιTruncLE K n
  asIso (t.liftTruncLE (Q.map (K.ιTruncLE n)) n)

@[reassoc (attr := simp)]
lemma QObjTruncLEIso_hom_ι (K : CochainComplex C ℤ) (n : ℤ) :
    (QObjTruncLEIso K n).hom ≫ (t.truncLEι n).app (Q.obj K) = Q.map (K.ιTruncLE n) :=
  t.liftTruncLE_ι _ _

/-- The truncations of `Q(K)` are the images of the truncations of `K`, as sequences. -/
noncomputable def complexTruncLESequenceCompQIso (K : CochainComplex C ℤ) :
    complexTruncLESequence K ⋙ Q ≅ truncLESequence (Q.obj K) :=
  have : IsIso (NatTrans.ofSequence (F := complexTruncLESequence K ⋙ Q)
      (G := truncLESequence (Q.obj K)) (fun n ↦ (QObjTruncLEIso K n).hom) (fun n ↦ by
        have : t.IsLE (Q.obj (K.truncLE (n : ℤ))) ((n + 1 : ℕ) : ℤ) :=
          t.isLE_of_le _ (n : ℤ) _ (by omega)
        refine t.to_truncLE_obj_ext ?_
        simp [complexTruncLESequence, truncLESequence, ← Q.map_comp])) :=
    NatIso.isIso_of_isIso_app _
  asIso _

/-- Blueprint `lem-kun-hocolim-truncations`: Recovery from bounded-above truncations.

For every `E ∈ D(C)`, `C` an abelian category with exact colimits of shape `ℕ` (e.g. étale
sheaves of modules), the canonical morphism `hocolim_N τ^{≤ N} E ⟶ E` is an isomorphism: the
cocone `τ^{≤ N} E ⟶ E` is a homotopy colimit cocone. Writing `E = Q(K)`, the complex `K` is the
termwise colimit of its truncations `τ^{≤ N} K` (in each degree they are eventually constant),
so `Q(K)` is the homotopy colimit of the `Q(τ^{≤ N} K) = τ^{≤ N} E`
(`DerivedCategory.isHomotopyColimit_mapCocone_Q`, `lem-kun-complex-colimit-hocolim`). -/
theorem isHomotopyColimit_truncLECocone [Abelian.HasKInjectiveResolutions C]
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C] [HasCoproductsOfShape ℕ C]
    (E : DerivedCategory C) : IsHomotopyColimit (truncLECocone E) := by
  let K := Q.objPreimage E
  let e : Q.obj K ≅ E := Q.objObjPreimageIso E
  have h₁ : IsHomotopyColimit (truncLECocone (Q.obj K)) :=
    (isHomotopyColimit_mapCocone_Q _ (isColimitComplexTruncLECocone K)).of_iso
      (complexTruncLESequenceCompQIso K) _ (Iso.refl _) fun n ↦ by
        simp [complexTruncLESequenceCompQIso, complexTruncLECocone]
  have : IsIso (truncLESequenceMap e.hom) := by
    have (n : ℕ) : IsIso ((truncLESequenceMap e.hom).app n) := by
      dsimp [truncLESequenceMap]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact h₁.of_iso (asIso (truncLESequenceMap e.hom)) _ e fun n ↦ by
    simp [truncLESequenceMap]

end Truncation

end DerivedCategory
