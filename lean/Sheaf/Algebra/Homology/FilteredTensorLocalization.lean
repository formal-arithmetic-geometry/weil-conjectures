/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.Algebra.Homology.FilteredTensorLocalizationSetup
import Sheaf.Algebra.Homology.FiniteFilteredGradedComparison
import all Sheaf.Algebra.Homology.FilteredQuasiIsoTwoOutOfThree
import Sheaf.Algebra.Homology.FilteredTensorHomotopy
import Sheaf.Algebra.Homology.FilteredTensorComparisonDescent

/-!
# Convolution tensor on the finite filtered localization

Source: Stacks Project, More on Algebra, Tag 0H7Y (proposition-kunneth-filtered),
with the convolution construction preceding Tag 0H7W and Derived Categories Tags
05S2--05S3 (blueprint: lem-kun-filtered-tensor-localization).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.MonoidalCategory
open CochainComplex

namespace CochainComplex

variable {R : Type u} [CommRing R]

private theorem kunneth_filtered_congruence :
    Congruence (finiteFilteredModuleHomotopyRel R) where
  equivalence := {
    refl := by
      intro f
      refine ⟨Homotopy.refl _, ?_⟩
      intro i n m
      exact ⟨0, by simp [Homotopy.refl, Homotopy.ofEq]⟩
    symm := by
      rintro f g ⟨h, hh⟩
      refine ⟨h.symm, ?_⟩
      intro i n m
      obtain ⟨l, hl⟩ := hh i n m
      exact ⟨-l, by simpa using congrArg Neg.neg hl⟩
    trans := by
      rintro f g k ⟨h, hh⟩ ⟨h', hh'⟩
      refine ⟨h.trans h', ?_⟩
      intro i n m
      obtain ⟨l, hl⟩ := hh i n m
      obtain ⟨l', hl'⟩ := hh' i n m
      exact ⟨l + l', by simpa using congrArg₂ HAdd.hAdd hl hl'⟩ }
  comp_left := by
    rintro K L M f g g' ⟨h, hh⟩
    refine ⟨h.compLeft f.hom.hom, ?_⟩
    intro i n m
    obtain ⟨l, hl⟩ := hh i n m
    refine ⟨(FilteredObject.restrictionSteps f.hom i).f n ≫ l, ?_⟩
    rw [Category.assoc, hl, ← Category.assoc]
    have he := HomologicalComplex.congr_hom (restriction_arrow f.hom i) n
    simpa using congrArg (· ≫ h.hom n m) he
  comp_right := by
    rintro K L M f f' g ⟨h, hh⟩
    refine ⟨h.compRight g.hom.hom, ?_⟩
    intro i n m
    obtain ⟨l, hl⟩ := hh i n m
    refine ⟨l ≫ (FilteredObject.restrictionSteps g.hom i).f m, ?_⟩
    have he := HomologicalComplex.congr_hom (restriction_arrow g.hom i) m
    simp only [HomologicalComplex.comp_f] at he
    rw [Category.assoc, he, ← Category.assoc, hl]
    rfl

private abbrev kunnethHomObj (P : GoodFiniteFilteredModuleHomotopy R) :
    KunnethFilteredComplex R := ⟨P.obj.as.obj, P.property⟩

private noncomputable abbrev kunnethHomMap
    {P P' : GoodFiniteFilteredModuleHomotopy R} (f : P ⟶ P') :
    kunnethHomObj P ⟶ kunnethHomObj P' :=
  ObjectProperty.homMk
    (((CategoryTheory.Quotient.functor (finiteFilteredModuleHomotopyRel R)).preimage
      f.hom).hom)

private theorem kunnethHomMap_spec
    {P P' : GoodFiniteFilteredModuleHomotopy R} (f : P ⟶ P') :
    kunnethGoodRepresentativeMap (kunnethHomMap f) = f := by
  apply ObjectProperty.hom_ext
  change (CategoryTheory.Quotient.functor (finiteFilteredModuleHomotopyRel R)).map
    ((CategoryTheory.Quotient.functor (finiteFilteredModuleHomotopyRel R)).preimage
      f.hom) = f.hom
  exact (CategoryTheory.Quotient.functor (finiteFilteredModuleHomotopyRel R)).map_preimage _

@[simp] private theorem kunnethGoodMap_comp
    {P P' P'' : KunnethFilteredComplex R} (f : P ⟶ P') (g : P' ⟶ P'') :
    kunnethGoodRepresentativeMap (f ≫ g) =
      kunnethGoodRepresentativeMap f ≫ kunnethGoodRepresentativeMap g := by
  apply ObjectProperty.hom_ext
  change (finiteFilteredModuleHomotopyQuotient R).map
    (kunnethRepresentativeMap f ≫ kunnethRepresentativeMap g) = _
  exact (finiteFilteredModuleHomotopyQuotient R).map_comp _ _

private theorem kunnethGoodMap_surjective
    {P P' : GoodFiniteFilteredModuleHomotopy R} (f : P ⟶ P') :
    ∃ f' : kunnethHomObj P ⟶ kunnethHomObj P', kunnethGoodRepresentativeMap f' = f :=
  ⟨kunnethHomMap f, kunnethHomMap_spec f⟩

private theorem kunneth_tensor_homotopy_bifunctor
    (hconv : ∀ P Q : KunnethFilteredComplex R,
      HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj))
    (m : ∀ (P P' Q Q' : KunnethFilteredComplex R) (_f : P ⟶ P') (_g : Q ⟶ Q'),
      kunnethConvolutionObject P.obj Q.obj ⟶ kunnethConvolutionObject P'.obj Q'.obj)
    (hm : ∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q'),
      (m P P' Q Q' f g).hom = f.hom.hom ⊗ₘ g.hom.hom)
    (mid : ∀ P Q : KunnethFilteredComplex R, m P P Q Q (𝟙 P) (𝟙 Q) = 𝟙 _)
    (mcomp : ∀ (P P' P'' Q Q' Q'' : KunnethFilteredComplex R)
      (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q''),
      m P P'' Q Q'' (f ≫ f') (g ≫ g') =
        m P P' Q Q' f g ≫ m P' P'' Q' Q'' f' g')
    (mW : ∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q'),
      (∀ i : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom i)) →
      (∀ j : ℤ, QuasiIso (FilteredObject.gradedMapSteps g.hom j)) →
        ∀ a : ℤ, QuasiIso (FilteredObject.gradedMapSteps (m P P' Q Q' f g) a)) :
    ∃ (G : GoodFiniteFilteredModuleHomotopy R ⥤ GoodFiniteFilteredModuleHomotopy R ⥤
        GoodFiniteFilteredModuleHomotopy R),
      (∀ P Q, ((G.obj P).obj Q).obj.as.obj =
        kunnethConvolutionObject P.obj.as.obj Q.obj.as.obj) ∧
      (∃ hrep : ∀ P Q : KunnethFilteredComplex R,
        (G.obj (kunnethGoodRepresentative P)).obj (kunnethGoodRepresentative Q) =
          kunnethGoodRepresentative (kunnethConvolutionRepresentative hconv P Q),
      (∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q'),
        (G.map (kunnethGoodRepresentativeMap f)).app (kunnethGoodRepresentative Q) ≫
          (G.obj (kunnethGoodRepresentative P')).map (kunnethGoodRepresentativeMap g) =
        eqToHom (hrep P Q) ≫ kunnethGoodRepresentativeMap
          (kunnethConvolutionRepresentativeMap hconv (m P P' Q Q' f g)) ≫
            eqToHom (hrep P' Q').symm) ∧
      ∀ (P P' Q Q' : GoodFiniteFilteredModuleHomotopy R) (f : P ⟶ P') (g : Q ⟶ Q'),
        goodFiniteFilteredModuleQuasiIso R f → goodFiniteFilteredModuleQuasiIso R g →
        goodFiniteFilteredModuleQuasiIso R
          ((G.map f).app Q ≫ (G.obj P').map g)) := by
  classical
  let := kunneth_filtered_congruence (R := R)
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let conv (P Q : GoodFiniteFilteredModuleHomotopy R) :=
    kunnethGoodRepresentative (kunnethConvolutionRepresentative hconv
      (kunnethHomObj P) (kunnethHomObj Q))
  let t {P P' Q Q' : GoodFiniteFilteredModuleHomotopy R} (f : P ⟶ P') (g : Q ⟶ Q') :
      conv P Q ⟶ conv P' Q' :=
    kunnethGoodRepresentativeMap (kunnethConvolutionRepresentativeMap hconv
      (m _ _ _ _ (kunnethHomMap f) (kunnethHomMap g)))
  have ht {P P' Q Q' : GoodFiniteFilteredModuleHomotopy R}
      (f : kunnethHomObj P ⟶ kunnethHomObj P')
      (g : kunnethHomObj Q ⟶ kunnethHomObj Q') :
      t (kunnethGoodRepresentativeMap f) (kunnethGoodRepresentativeMap g) =
        kunnethGoodRepresentativeMap
          (kunnethConvolutionRepresentativeMap hconv (m _ _ _ _ f g)) := by
    apply ObjectProperty.hom_ext
    apply (CategoryTheory.Quotient.functor_map_eq_iff _ _ _).2
    apply kunnethConvolution_filtered_homotopy hconv m hm
    · apply (CategoryTheory.Quotient.functor_map_eq_iff _ _ _).1
      simpa only [kunnethGoodRepresentativeMap, ObjectProperty.homMk_hom,
        finiteFilteredModuleHomotopyQuotient, CategoryTheory.Quotient.functor] using
        congrArg (fun f ↦ f.hom) (kunnethHomMap_spec (kunnethGoodRepresentativeMap f))
    · apply (CategoryTheory.Quotient.functor_map_eq_iff _ _ _).1
      simpa only [kunnethGoodRepresentativeMap, ObjectProperty.homMk_hom,
        finiteFilteredModuleHomotopyQuotient, CategoryTheory.Quotient.functor] using
        congrArg (fun g ↦ g.hom) (kunnethHomMap_spec (kunnethGoodRepresentativeMap g))
  have tid (P Q : GoodFiniteFilteredModuleHomotopy R) : t (𝟙 P) (𝟙 Q) = 𝟙 _ := by
    change t (kunnethGoodRepresentativeMap (𝟙 (kunnethHomObj P)))
      (kunnethGoodRepresentativeMap (𝟙 (kunnethHomObj Q))) = _
    rw [ht, mid]
    change ObjectProperty.homMk ((finiteFilteredModuleHomotopyQuotient R).map (𝟙 _)) = _
    apply ObjectProperty.hom_ext
    change (finiteFilteredModuleHomotopyQuotient R).map (𝟙 _) = 𝟙 _
    exact (finiteFilteredModuleHomotopyQuotient R).map_id _
  have tcomp {P P' P'' Q Q' Q'' : GoodFiniteFilteredModuleHomotopy R}
      (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
      t (f ≫ f') (g ≫ g') = t f g ≫ t f' g' := by
    obtain ⟨f, rfl⟩ := kunnethGoodMap_surjective f
    obtain ⟨f', rfl⟩ := kunnethGoodMap_surjective f'
    obtain ⟨g, rfl⟩ := kunnethGoodMap_surjective g
    obtain ⟨g', rfl⟩ := kunnethGoodMap_surjective g'
    erw [← kunnethGoodMap_comp, ← kunnethGoodMap_comp, ht, ht, ht, mcomp]
    exact kunnethGoodMap_comp
      (kunnethConvolutionRepresentativeMap hconv (m _ _ _ _ f g))
      (kunnethConvolutionRepresentativeMap hconv (m _ _ _ _ f' g'))
  let G : GoodFiniteFilteredModuleHomotopy R ⥤ GoodFiniteFilteredModuleHomotopy R ⥤
      GoodFiniteFilteredModuleHomotopy R :=
    { obj := fun P ↦
        { obj := conv P
          map := fun g ↦ t (𝟙 P) g
          map_id := fun Q ↦ tid P Q
          map_comp := fun g g' ↦ by simpa using tcomp (𝟙 P) (𝟙 P) g g' }
      map := fun f ↦
        { app := fun Q ↦ t f (𝟙 Q)
          naturality := fun _ _ g ↦ by
            simpa using (tcomp (𝟙 _) f g (𝟙 _)).symm.trans
              (tcomp f (𝟙 _) (𝟙 _) g) }
      map_id := fun P ↦ NatTrans.ext (funext (fun Q ↦ tid P Q))
      map_comp := fun f f' ↦ NatTrans.ext (funext (fun Q ↦ by
        simpa using tcomp f f' (𝟙 Q) (𝟙 Q))) }
  have htG {P P' Q Q' : GoodFiniteFilteredModuleHomotopy R}
      (f : P ⟶ P') (g : Q ⟶ Q') :
      (G.map f).app Q ≫ (G.obj P').map g = t f g := by
    exact (tcomp f (𝟙 _) (𝟙 _) g).symm.trans (by simp)
  refine ⟨G, fun _ _ ↦ rfl, fun _ _ ↦ rfl, ?_, ?_⟩
  · intro P P' Q Q' f g
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
      kunnethHomObj, kunnethGoodRepresentative, kunnethFiniteRepresentative,
      finiteFilteredModuleHomotopyQuotient, CategoryTheory.Quotient.functor] using
      (htG _ _).trans (ht (P := kunnethGoodRepresentative P)
      (P' := kunnethGoodRepresentative P') (Q := kunnethGoodRepresentative Q)
      (Q' := kunnethGoodRepresentative Q') f g)
  · intro P P' Q Q' f g hf hg
    rw [htG]
    obtain ⟨f, rfl⟩ := kunnethGoodMap_surjective f
    obtain ⟨g, rfl⟩ := kunnethGoodMap_surjective g
    erw [ht]
    have hff : ∀ i : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom i) := by
      intro i
      apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).1
      have he := ((quasiIso_iff _).1 hf) i
      exact he
    have hgg : ∀ i : ℤ, QuasiIso (FilteredObject.gradedMapSteps g.hom i) := by
      intro i
      apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).1
      have he := ((quasiIso_iff _).1 hg) i
      exact he
    exact ⟨kunnethRepresentativeMap
      (kunnethConvolutionRepresentativeMap hconv (m _ _ _ _ f g)), rfl,
      mW _ _ _ _ f g hff hgg⟩

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

private theorem kunneth_graded_homotopy
    (i : ℤ) (K L : FiniteFilteredModuleComplex R) (f g : K ⟶ L)
    (h : finiteFilteredModuleHomotopyRel R f g) :
    (gradedFunctor R i ⋙ DerivedCategory.Q).map f =
      (gradedFunctor R i ⋙ DerivedCategory.Q).map g := by
  classical
  change DerivedCategory.Q.map (FilteredObject.gradedMapSteps f.hom i) =
    DerivedCategory.Q.map (FilteredObject.gradedMapSteps g.hom i)
  obtain ⟨h, hh⟩ := h
  let h' := restrictedHomotopy h hh i
  let jK := Subobject.ofLE (K.obj.filtration.step (i + 1))
    (K.obj.filtration.step i) (K.obj.filtration.antitone_step (by omega))
  let jL := Subobject.ofLE (L.obj.filtration.step (i + 1))
    (L.obj.filtration.step i) (L.obj.filtration.antitone_step (by omega))
  let πK := cokernel.π jK
  let πL := cokernel.π jL
  have hres (j n m : ℤ) : (restrictedHomotopy h hh j).hom n m ≫
      (L.obj.filtration.step j).arrow.f m =
      (K.obj.filtration.step j).arrow.f n ≫ h.hom n m :=
    Classical.choose_spec (hh j n m)
  have hcompat (n m : ℤ) : jK.f n ≫ h'.hom n m =
      (restrictedHomotopy h hh (i + 1)).hom n m ≫ jL.f m := by
    apply (cancel_mono ((L.obj.filtration.step i).arrow.f m)).1
    simp only [Category.assoc, h', hres]
    rw [← Category.assoc, ← HomologicalComplex.comp_f, Subobject.ofLE_arrow]
    dsimp only [jL]
    rw [← HomologicalComplex.comp_f, Subobject.ofLE_arrow, hres]
  have hz (n m : ℤ) : jK.f n ≫ h'.hom n m ≫ πL.f m = 0 := by
    rw [← Category.assoc, hcompat, Category.assoc]
    have hc := HomologicalComplex.congr_hom (cokernel.condition jL) m
    change jL.f m ≫ πL.f m = 0 at hc
    rw [hc, comp_zero]
  let lift (n m : ℤ) : (cokernel jK).X n ⟶ (cokernel jL).X m :=
    (PreservesCokernel.iso
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n) jK).hom ≫
      cokernel.desc (jK.f n) (h'.hom n m ≫ πL.f m) (hz n m)
  have hlift (n m : ℤ) : πK.f n ≫ lift n m = h'.hom n m ≫ πL.f m := by
    dsimp [lift, πK]
    have he := PreservesCokernel.π_iso_hom
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n) jK
    change (cokernel.π jK).f n ≫ _ = cokernel.π (jK.f n) at he
    rw [← Category.assoc, he, cokernel.π_desc]
  apply DerivedCategory.Q_map_eq_of_homotopy
  refine ⟨lift, ?_, ?_⟩
  · intro n m hnm
    apply (cancel_epi (πK.f n)).1
    rw [hlift, h'.zero n m hnm, zero_comp, comp_zero]
  · intro n
    apply (cancel_epi (πK.f n)).1
    have hf := HomologicalComplex.congr_hom (graded_projection f.hom i) n
    have hg := HomologicalComplex.congr_hom (graded_projection g.hom i) n
    simp only [HomologicalComplex.comp_f] at hf hg
    have hc := h'.comm n
    simp only [dNext, prevD, AddMonoidHom.mk'_apply] at hc ⊢
    simp only [Preadditive.comp_add, ← Category.assoc]
    erw [πK.comm, Category.assoc, hlift, hlift, Category.assoc, πL.comm]
    erw [hg]
    simpa only [Preadditive.add_comp, Category.assoc, πK, πL, gradedFunctor] using
      hf.trans (congrArg (· ≫ πL.f n) hc)

private noncomputable def kunnethForgetComplex :
    FiniteFilteredModuleComplex R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj K := K.obj.obj
  map f := f.hom.hom

private theorem kunneth_evaluation_descent
    (T : FiniteFilteredModuleComplex R ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
    (hT : ∀ (K L : FiniteFilteredModuleComplex R) (f g : K ⟶ L),
      finiteFilteredModuleHomotopyRel R f g →
        DerivedCategory.Q.map (T.map f) = DerivedCategory.Q.map (T.map g))
    (hW : ∀ (K L : FiniteFilteredModuleComplex R) (f : K ⟶ L),
      (∀ a : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom a)) →
        QuasiIso (T.map f)) :
    ∃ (H : (finiteFilteredModuleQuasiIso R).Localization ⥤
        DerivedCategory (ModuleCat.{u} R))
      (FH : FiniteFilteredModuleHomotopy R ⥤ DerivedCategory (ModuleCat.{u} R))
      (_hH : Localization.Lifting (finiteFilteredModuleQuasiIso R).Q
        (finiteFilteredModuleQuasiIso R) FH H)
      (hobj : ∀ K : FiniteFilteredModuleHomotopy R,
        FH.obj K = HomologicalComplexUpToQuasiIso.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj (T.obj K.as))),
      ∀ (K L : FiniteFilteredModuleHomotopy R) (f : K.as ⟶ L.as),
        FH.map ((finiteFilteredModuleHomotopyQuotient R).map f) =
          eqToHom (hobj ((finiteFilteredModuleHomotopyQuotient R).obj K.as)) ≫
            HomologicalComplexUpToQuasiIso.Qh.map
              ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map (T.map f)) ≫
            eqToHom (hobj ((finiteFilteredModuleHomotopyQuotient R).obj L.as)).symm := by
  let G := T ⋙ DerivedCategory.Q
  let FH := CategoryTheory.Quotient.lift (finiteFilteredModuleHomotopyRel R) G hT
  have hi : (finiteFilteredModuleQuasiIso R).IsInvertedBy FH := by
    rintro K L q ⟨f, rfl, hf⟩
    change IsIso (DerivedCategory.Q.map (T.map f))
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) _).2 (hW _ _ f hf)
  refine ⟨Localization.lift FH hi (finiteFilteredModuleQuasiIso R).Q, FH,
    inferInstance, fun _ ↦ rfl, ?_⟩
  intro K L f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The convolution tensor descends through filtered homotopy localizations, and its
underlying and associated-graded comparisons are natural in both localized variables.
Source: Stacks Project, More on Algebra, Tags 0H7W and 0H7Y, and Derived Categories
Tags 05S2--05S3 (blueprint: lem-kun-filtered-tensor-localization).

Proof sketch (the nine steps of the node):
1. On good representatives, `filteredTensor_graded_comparison` constructs the signed
   total tensor with convolution filtration, proves goodness, and fixes `m`, `e`, `c`,
   and `cgr` by their representative equations.
2. Tensoring filtered homotopies gives filtered homotopies; the mixed Koszul terms cancel,
   so the representative operation descends to the homotopy category.
3. The graded comparison shows that the operation inverts a graded quasi-isomorphism in
   either variable, hence it inverts the product class of denominators.
4. The product localization universal property supplies `B`; its `Lifting₂` witness
   records the canonical comparison with representatives.
5. The replacement theorem supplies `E` and its natural square with inclusion; transport
   across this equivalence gives `star`.
6. The family `τ` below is natural in both localized variables, so `star` is fixed by the
   transported representative bifunctor rather than objectwise choices.
7. Forgetting and grading invert denominators by finite filtration induction and by
   definition; their `Lifting` witnesses characterize `omega` and `gr`.
8. The fixed derived tensor comparison `c` descends to the natural underlying comparison
   `eta`, agreeing with tensoring representative maps.
9. The fixed `e` and `cgr` comparisons descend uniformly to finite diagonal biproducts;
   common finite support gives the final graded naturality square.
-/
theorem filteredTensor_localization :
    ∃ (E :
        (goodFiniteFilteredModuleQuasiIso R).Localization ≌
          (finiteFilteredModuleQuasiIso R).Localization),
      ∃ (eE :
        (goodFiniteFilteredModuleQuasiIso R).Q ⋙ E.functor ≅
          goodFiniteFilteredModuleInclusion R ⋙ (finiteFilteredModuleQuasiIso R).Q),
      ∃ (F :
        GoodFiniteFilteredModuleHomotopy R ⥤
          GoodFiniteFilteredModuleHomotopy R ⥤
            (goodFiniteFilteredModuleQuasiIso R).Localization),
        ∃ (B :
          (goodFiniteFilteredModuleQuasiIso R).Localization ⥤
            (goodFiniteFilteredModuleQuasiIso R).Localization ⥤
              (goodFiniteFilteredModuleQuasiIso R).Localization),
          ∃ hB : Localization.Lifting₂
            (goodFiniteFilteredModuleQuasiIso R).Q
            (goodFiniteFilteredModuleQuasiIso R).Q
            (goodFiniteFilteredModuleQuasiIso R)
            (goodFiniteFilteredModuleQuasiIso R) F B,
            ∃ (hconv : ∀ P Q : KunnethFilteredComplex R,
              HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj)),
            ∃ (conv : GoodFiniteFilteredModuleHomotopy R →
              GoodFiniteFilteredModuleHomotopy R → GoodFiniteFilteredModuleHomotopy R),
              (∀ P Q : GoodFiniteFilteredModuleHomotopy R,
                (F.obj P).obj Q = (goodFiniteFilteredModuleQuasiIso R).Q.obj (conv P Q)) ∧
              (∀ P Q : GoodFiniteFilteredModuleHomotopy R,
                (conv P Q).obj.as.obj = kunnethConvolutionObject P.obj.as.obj Q.obj.as.obj) ∧
              (∃ (hrep : ∀ P Q : KunnethFilteredComplex R,
                  (F.obj (kunnethGoodRepresentative P)).obj (kunnethGoodRepresentative Q) =
                    (goodFiniteFilteredModuleQuasiIso R).Q.obj
                      (kunnethGoodRepresentative (kunnethConvolutionRepresentative hconv P Q))),
              ∃ (m : ∀ (P P' Q Q' : KunnethFilteredComplex R)
                    (_f : P ⟶ P') (_g : Q ⟶ Q'),
                  kunnethConvolutionObject P.obj Q.obj ⟶
                    kunnethConvolutionObject P'.obj Q'.obj),
                (∀ (P P' Q Q' : KunnethFilteredComplex R)
                    (f : P ⟶ P') (g : Q ⟶ Q'),
                  (m P P' Q Q' f g).hom = f.hom.hom ⊗ₘ g.hom.hom) ∧
                (∀ P Q : KunnethFilteredComplex R,
                  m P P Q Q (𝟙 P) (𝟙 Q) = 𝟙 _) ∧
                (∀ (P P' P'' Q Q' Q'' : KunnethFilteredComplex R)
                    (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q''),
                  m P P'' Q Q'' (f ≫ f') (g ≫ g') =
                    m P P' Q Q' f g ≫ m P' P'' Q' Q'' f' g') ∧
              (∀ (P P' Q Q' : KunnethFilteredComplex R)
                  (f : P ⟶ P') (g : Q ⟶ Q'),
                (F.map (kunnethGoodRepresentativeMap f)).app
                      (kunnethGoodRepresentative Q) ≫
                    (F.obj (kunnethGoodRepresentative P')).map
                      (kunnethGoodRepresentativeMap g) =
                  eqToHom (hrep P Q) ≫
                    (goodFiniteFilteredModuleQuasiIso R).Q.map
                      (kunnethGoodRepresentativeMap
                        (kunnethConvolutionRepresentativeMap hconv
                          (m P P' Q Q' f g))) ≫
                    eqToHom (hrep P' Q').symm) ∧
              ∃ (star :
                (finiteFilteredModuleQuasiIso R).Localization ⥤
                  (finiteFilteredModuleQuasiIso R).Localization ⥤
                    (finiteFilteredModuleQuasiIso R).Localization),
                ∃ (τ : ∀ U V : (finiteFilteredModuleQuasiIso R).Localization,
                  (star.obj U).obj V ≅
                    E.functor.obj ((B.obj (E.inverse.obj U)).obj (E.inverse.obj V))),
                  (∀ (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
                      (f : U ⟶ U') (g : V ⟶ V'),
                    (τ U V).hom ≫
                        E.functor.map ((B.map (E.inverse.map f)).app (E.inverse.obj V) ≫
                          (B.obj (E.inverse.obj U')).map (E.inverse.map g)) =
                      (star.map f).app V ≫ (star.obj U').map g ≫ (τ U' V').hom) ∧
                  ∃ (omega :
                    (finiteFilteredModuleQuasiIso R).Localization ⥤
                      DerivedCategory (ModuleCat.{u} R)),
                    ∃ (Fω : FiniteFilteredModuleHomotopy R ⥤
                      DerivedCategory (ModuleCat.{u} R)),
                      ∃ hω : Localization.Lifting
                        (finiteFilteredModuleQuasiIso R).Q
                        (finiteFilteredModuleQuasiIso R)
                        Fω omega,
                        ∃ (hωobj : ∀ K : FiniteFilteredModuleHomotopy R,
                          Fω.obj K =
                            HomologicalComplexUpToQuasiIso.Qh.obj
                              ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                                K.as.obj.obj)),
                          (∀ (K L : FiniteFilteredModuleHomotopy R)
                              (f : K.as ⟶ L.as),
                            Fω.map ((finiteFilteredModuleHomotopyQuotient R).map f) =
                              eqToHom (hωobj ((finiteFilteredModuleHomotopyQuotient R).obj K.as)) ≫
                                HomologicalComplexUpToQuasiIso.Qh.map
                                  ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                                    f.hom.hom) ≫
                                eqToHom
                                  (hωobj ((finiteFilteredModuleHomotopyQuotient R).obj L.as)).symm
                                  ) ∧
                          ∃ (gr : ℤ →
                          (finiteFilteredModuleQuasiIso R).Localization ⥤
                            DerivedCategory (ModuleCat.{u} R)),
                          ∃ (Fgr : ∀ _a : ℤ, FiniteFilteredModuleHomotopy R ⥤
                            DerivedCategory (ModuleCat.{u} R)),
                            ∃ hgr : ∀ a : ℤ, Localization.Lifting
                              (finiteFilteredModuleQuasiIso R).Q
                              (finiteFilteredModuleQuasiIso R)
                              (Fgr a) (gr a),
                              ∃ (hgro : ∀ (a : ℤ) (K : FiniteFilteredModuleHomotopy R),
                                (Fgr a).obj K =
                                  HomologicalComplexUpToQuasiIso.Qh.obj
                                    ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                                      (K.as.obj.filtration.gradedPiece a))),
                                (∀ (a : ℤ) (K L : FiniteFilteredModuleHomotopy R)
                                    (f : K.as ⟶ L.as),
                                  (Fgr a).map ((finiteFilteredModuleHomotopyQuotient R).map f) =
                                    eqToHom
                                      (hgro a ((finiteFilteredModuleHomotopyQuotient R).obj K.as)) ≫
                                      HomologicalComplexUpToQuasiIso.Qh.map
                                        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                                          (FilteredObject.gradedMapSteps f.hom a)) ≫
                                      eqToHom
                                        (hgro a
                                          ((finiteFilteredModuleHomotopyQuotient R).obj L.as)).symm
                                      ) ∧
                                (∃ η : ∀ U V : (finiteFilteredModuleQuasiIso R).Localization,
                                omega.obj ((star.obj U).obj V) ≅
                                  (omega.obj U) ⊗ (omega.obj V),
                                (∀ (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
                                    (f : U ⟶ U') (g : V ⟶ V'),
                                  (η U V).hom ≫ (omega.map f ⊗ₘ omega.map g) =
                                    omega.map ((star.map f).app V ≫
                                      (star.obj U').map g) ≫ (η U' V').hom) ∧
                                ∃ (cη : ∀ P Q : KunnethFilteredComplex R,
                                  DerivedCategory.Q.obj P.obj.obj ⊗
                                      DerivedCategory.Q.obj Q.obj.obj ≅
                                    DerivedCategory.Q.obj (P.obj.obj ⊗ Q.obj.obj)),
                                  (∀ P Q : KunnethFilteredComplex R,
                                    (cη P Q).hom = Functor.LaxMonoidal.μ
                                      DerivedCategory.Q P.obj.obj Q.obj.obj) ∧
                                  (∀ P Q : KunnethFilteredComplex R,
                                    (η (kunnethLocalizedRepresentative E P)
                                      (kunnethLocalizedRepresentative E Q)).hom ≫
                                      ((kunnethRepresentativeLiftIso E eE omega Fω hω
                                        (fun K ↦ K.as.obj.obj) hωobj P).hom ⊗ₘ
                                      (kunnethRepresentativeLiftIso E eE omega Fω hω
                                        (fun K ↦ K.as.obj.obj) hωobj Q).hom) =
                                    omega.map
                                      (kunnethStarRepresentativeIso E F B hB hconv hrep
                                        star τ P Q).hom ≫
                                      (kunnethRepresentativeLiftIso E eE omega Fω hω
                                        (fun K ↦ K.as.obj.obj) hωobj
                                        (kunnethConvolutionRepresentative hconv P Q)).hom ≫
                                      (cη P Q).inv)) ∧
                              ∃ (e : ∀ (a : ℤ)
                                  (U V : (finiteFilteredModuleQuasiIso R).Localization)
                                  (s : Finset ℤ),
                                  (∀ i : ℤ, i ∉ s →
                                    IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V))) →
                                  ((gr a).obj ((star.obj U).obj V) ≅
                                    (⨁ fun i : ↥s =>
                                      ((gr i.1).obj U) ⊗ ((gr (a - i.1)).obj V)))),
                                (∀ (a : ℤ) (U V : (finiteFilteredModuleQuasiIso R).Localization),
                                  ∃ s : Finset ℤ,
                                    (∀ i : ℤ, i ∉ s →
                                      IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V)))) ∧
                                (∀ (a : ℤ)
                                    (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
                                    (f : U ⟶ U') (g : V ⟶ V') (s : Finset ℤ)
                                    (hs : ∀ i : ℤ, i ∉ s →
                                      IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V)))
                                    (hs' : ∀ i : ℤ, i ∉ s →
                                      IsZero (((gr i).obj U') ⊗ ((gr (a - i)).obj V'))),
                                  (e a U V s hs).hom ≫ biproduct.map (fun i : ↥s =>
                                    (gr i.1).map f ⊗ₘ (gr (a - i.1)).map g) =
                                    (gr a).map ((star.map f).app V ≫
                                      (star.obj U').map g) ≫ (e a U' V' s hs').hom)
                                ∧ (∀ (a : ℤ) (U V : (finiteFilteredModuleQuasiIso R).Localization)
                                    (s t : Finset ℤ) (hst : s ⊆ t)
                                    (hs : ∀ i : ℤ, i ∉ s →
                                      IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V)))
                                    (ht : ∀ i : ℤ, i ∉ t →
                                      IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V))),
                                  ∃ (ι :
                                      (⨁ fun i : ↥s =>
                                        ((gr i.1).obj U) ⊗ ((gr (a - i.1)).obj V)) ⟶
                                      (⨁ fun i : ↥t =>
                                        ((gr i.1).obj U) ⊗ ((gr (a - i.1)).obj V))),
                                    (∀ i : ↥s,
                                      biproduct.ι (fun j : ↥s =>
                                        ((gr j.1).obj U) ⊗ ((gr (a - j.1)).obj V)) i ≫ ι =
                                      biproduct.ι (fun j : ↥t =>
                                        ((gr j.1).obj U) ⊗ ((gr (a - j.1)).obj V))
                                        ⟨i.1, hst i.2⟩) ∧
                                    (e a U V s hs).hom ≫ ι =
                                      (e a U V t ht).hom)
                                ∧ (∀ (P Q : KunnethFilteredComplex R) (a : ℤ)
                                    (s : Finset ℤ)
                                    (hs : ∀ i : ℤ, i ∉ s →
                                      IsZero (((gr i).obj (kunnethLocalizedRepresentative E P)) ⊗
                                        ((gr (a - i)).obj (kunnethLocalizedRepresentative E Q)))),
                                  ∃ (cgr : ∀ i : ℤ,
                                    kunnethDerivedGraded P.obj Q.obj a i ≅
                                      DerivedCategory.Q.obj
                                        (kunnethTensorGraded P.obj Q.obj a i)),
                                  (∀ i : ℤ, (cgr i).hom =
                                    Functor.LaxMonoidal.μ DerivedCategory.Q
                                      (P.obj.filtration.gradedPiece i)
                                      (Q.obj.filtration.gradedPiece (a - i))) ∧
                                  (e a (kunnethLocalizedRepresentative E P)
                                      (kunnethLocalizedRepresentative E Q) s hs).hom ≫
                                    biproduct.desc (fun i : ↥s ↦
                                      ((kunnethRepresentativeLiftIso E eE (gr i.1) (Fgr i.1)
                                        (hgr i.1) (fun K ↦ K.as.obj.filtration.gradedPiece i.1)
                                        (hgro i.1) P).hom ⊗ₘ
                                      (kunnethRepresentativeLiftIso E eE (gr (a - i.1))
                                        (Fgr (a - i.1)) (hgr (a - i.1))
                                        (fun K ↦ K.as.obj.filtration.gradedPiece (a - i.1))
                                        (hgro (a - i.1)) Q).hom) ≫
                                      (cgr i.1).hom ≫ DerivedCategory.Q.map
                                        (Sigma.ι (kunnethTensorGraded P.obj Q.obj a) i.1)) =
                                    (gr a).map
                                      (kunnethStarRepresentativeIso E F B hB hconv hrep
                                        star τ P Q).hom ≫
                                    (kunnethRepresentativeLiftIso E eE (gr a) (Fgr a) (hgr a)
                                      (fun K ↦ K.as.obj.filtration.gradedPiece a) (hgro a)
                                      (kunnethConvolutionRepresentative hconv P Q)).hom ≫
                                    (DerivedCategory.Q.mapIso
                                      (kunnethRepresentativeGradedComparison P Q a)).inv))
              := by
  classical
  obtain ⟨_, ⟨E, ⟨eE⟩⟩, _⟩ := finiteFiltered_kFlat_replacement R
  obtain ⟨m, l, e, c, cgr, hconv, hl, he, hm, hen, mid, mcomp, hc, hcg, hcol, hdn, mW⟩ :=
    filteredTensor_graded_comparison (R := R)
  obtain ⟨G, hGobj, hGrep, hGmap, hGW⟩ :=
    kunneth_tensor_homotopy_bifunctor hconv m hm mid mcomp mW
  let Qg := (goodFiniteFilteredModuleQuasiIso R).Q
  let F := G ⋙ (whiskeringRight _ _ _).obj Qg
  have hrep (P Q : KunnethFilteredComplex R) :
      (F.obj (kunnethGoodRepresentative P)).obj (kunnethGoodRepresentative Q) =
        Qg.obj (kunnethGoodRepresentative (kunnethConvolutionRepresentative hconv P Q)) :=
    congrArg Qg.obj (hGrep P Q)
  have hFmap (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q') :
      (F.map (kunnethGoodRepresentativeMap f)).app (kunnethGoodRepresentative Q) ≫
        (F.obj (kunnethGoodRepresentative P')).map (kunnethGoodRepresentativeMap g) =
      eqToHom (hrep P Q) ≫ Qg.map (kunnethGoodRepresentativeMap
        (kunnethConvolutionRepresentativeMap hconv (m P P' Q Q' f g))) ≫
        eqToHom (hrep P' Q').symm := by
    simpa only [F, whiskeringRight, Functor.whiskerRight, Functor.comp_obj,
      Functor.comp_map, Functor.map_comp, eqToHom_map] using congrArg Qg.map
      (hGmap P P' Q Q' f g)
  let : (goodFiniteFilteredModuleQuasiIso R).ContainsIdentities :=
    { id_mem := fun P ↦ finiteFilteredModuleQuasiIso_id R P.obj }
  have hF : MorphismProperty.IsInvertedBy₂ (goodFiniteFilteredModuleQuasiIso R)
      (goodFiniteFilteredModuleQuasiIso R) F := by
    rintro ⟨P, Q⟩ ⟨P', Q'⟩ ⟨f, g⟩ ⟨hf, hg⟩
    change IsIso (Qg.map ((G.map f).app Q) ≫ Qg.map ((G.obj P').map g))
    rw [← Functor.map_comp]
    exact Localization.inverts Qg (goodFiniteFilteredModuleQuasiIso R) _
      (hGW P P' Q Q' f g hf hg)
  let B := Localization.lift₂ F hF Qg Qg
  let hB : Localization.Lifting₂ Qg Qg (goodFiniteFilteredModuleQuasiIso R)
      (goodFiniteFilteredModuleQuasiIso R) F B := inferInstance
  let star := E.inverse ⋙ B ⋙ (whiskeringLeft _ _ _).obj E.inverse ⋙
    (whiskeringRight _ _ _).obj E.functor
  let τ (U V : (finiteFilteredModuleQuasiIso R).Localization) :
      (star.obj U).obj V ≅ E.functor.obj
        ((B.obj (E.inverse.obj U)).obj (E.inverse.obj V)) := Iso.refl _
  have hτ (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
      (f : U ⟶ U') (g : V ⟶ V') :
      (τ U V).hom ≫ E.functor.map
        ((B.map (E.inverse.map f)).app (E.inverse.obj V) ≫
          (B.obj (E.inverse.obj U')).map (E.inverse.map g)) =
        (star.map f).app V ≫ (star.obj U').map g ≫ (τ U' V').hom := by
    simp [τ, star, Functor.map_comp]
  obtain ⟨omega, Fω, hω, hωobj, hωmap⟩ :=
    kunneth_evaluation_descent (kunnethForgetComplex (R := R))
      (fun K L f g h ↦ DerivedCategory.Q_map_eq_of_homotopy (ModuleCat R) h.choose)
      (fun K L f hf ↦ (finiteFilteredModule_graded_comparison f hf).1)
  have hgrades (a : ℤ) := kunneth_evaluation_descent (gradedFunctor R a)
    (kunneth_graded_homotopy a) (fun K L f hf ↦ hf a)
  choose gr Fgr hgr hgro hgrmap using hgrades
  refine ⟨E, eE, F, B, hB, hconv, (fun P Q ↦ (G.obj P).obj Q),
    (fun _ _ ↦ rfl), hGobj, hrep, m, hm, mid, mcomp, hFmap, star, τ, hτ,
    omega, Fω, hω, hωobj, hωmap, gr, Fgr, hgr, hgro, hgrmap, ?_⟩
  exact filteredTensor_localized_comparisons E eE F B hB hconv hrep m hm hFmap
    star τ hτ omega Fω hω hωobj hωmap gr Fgr hgr hgro hgrmap

end CochainComplex
