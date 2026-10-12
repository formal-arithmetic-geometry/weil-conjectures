/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives

/-!
# Coproducts in the derived category

Let `C` be an abelian category with K-injective resolutions. We show:

* the quotient functor `CochainComplex C ℤ ⥤ HomotopyCategory C (.up ℤ)` preserves coproducts
  (`HomotopyCategory.isColimitQuotientCofan`): homotopies glue along a coproduct of complexes;
* the derived category `D(C)` has the coproducts that `C` has, and the localization functors
  `DerivedCategory.Qh` and `DerivedCategory.Q` preserve them: morphisms into a K-injective
  complex are computed in the homotopy category;
* if coproducts of shape `J` in `C` are exact, the homology functors `Hⁿ : D(C) ⥤ C` preserve
  coproducts of shape `J` (`DerivedCategory.preservesColimitsOfShape_homologyFunctor`);
* an exact functor preserving coproducts induces a coproduct preserving functor on derived
  categories (`Functor.preservesColimitsOfShape_mapDerivedCategory`).

These are the formal inputs of Brown representability for derived categories of
Grothendieck abelian categories.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory

namespace Limits

/-- A cofan is a colimit cofan if morphisms out of its point correspond bijectively to families
of morphisms out of the summands. -/
noncomputable def Cofan.isColimitOfBijective {C : Type*} [Category* C] {J : Type*} {X : J → C}
    (c : Cofan X) (h : ∀ T : C, Function.Bijective fun (g : c.pt ⟶ T) (j : J) ↦ c.inj j ≫ g) :
    IsColimit c :=
  Cofan.IsColimit.mk c (fun t ↦ ((h t.pt).2 t.inj).choose)
    (fun t j ↦ congrFun ((h t.pt).2 t.inj).choose_spec j)
    (fun t m hm ↦ (h t.pt).1 ((funext hm).trans ((h t.pt).2 t.inj).choose_spec.symm))

lemma Cofan.bijective_of_isColimit {C : Type*} [Category* C] {J : Type*} {X : J → C}
    {c : Cofan X} (hc : IsColimit c) (T : C) :
    Function.Bijective fun (g : c.pt ⟶ T) (j : J) ↦ c.inj j ≫ g :=
  ⟨fun _ _ h ↦ Cofan.IsColimit.hom_ext hc _ _ fun j ↦ congrFun h j,
    fun f ↦ ⟨Cofan.IsColimit.desc hc f, funext fun j ↦ Cofan.IsColimit.fac hc f j⟩⟩

/-- Let `L : A ⥤ B` be essentially surjective and preserve coproducts of shape `J`, where `A` has
such coproducts. If `L ⋙ Φ` preserves coproducts of shape `J`, then so does `Φ`. -/
lemma preservesColimitsOfShape_discrete_of_essSurj {A B B' : Type*} [Category* A] [Category* B]
    [Category* B'] {J : Type*} [HasColimitsOfShape (Discrete J) A] (L : A ⥤ B) [L.EssSurj]
    [PreservesColimitsOfShape (Discrete J) L] (Φ : B ⥤ B')
    [PreservesColimitsOfShape (Discrete J) (L ⋙ Φ)] :
    PreservesColimitsOfShape (Discrete J) Φ := by
  refine ⟨fun {G} ↦ ?_⟩
  let X : J → A := fun j ↦ L.objPreimage (G.obj ⟨j⟩)
  let e : Discrete.functor X ⋙ L ≅ G :=
    Discrete.natIso fun j ↦ L.objObjPreimageIso (G.obj j)
  suffices PreservesColimit (Discrete.functor X ⋙ L) Φ from preservesColimit_of_iso_diagram Φ e
  exact preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves L (colimit.isColimit (Discrete.functor X)))
    (isColimitOfPreserves (L ⋙ Φ) (colimit.isColimit (Discrete.functor X)))

/-- Let `L : A ⥤ B` be essentially surjective and preserve coproducts of shape `J`, where `A` has
such coproducts. Then `B` has coproducts of shape `J`. -/
lemma hasColimitsOfShape_discrete_of_essSurj {A B : Type*} [Category* A] [Category* B]
    {J : Type*} [HasColimitsOfShape (Discrete J) A] (L : A ⥤ B) [L.EssSurj]
    [PreservesColimitsOfShape (Discrete J) L] : HasColimitsOfShape (Discrete J) B := by
  refine ⟨fun G ↦ ?_⟩
  let X : J → A := fun j ↦ L.objPreimage (G.obj ⟨j⟩)
  let e : Discrete.functor X ⋙ L ≅ G :=
    Discrete.natIso fun j ↦ L.objObjPreimageIso (G.obj j)
  exact hasColimit_of_iso e.symm

end Limits

namespace ShortComplex

variable {C : Type*} [Category* C] [Abelian C] {J : Type*} [Category* J]

/-- The natural transformation from the evaluation at `j` to the colimit functor. -/
@[simps]
noncomputable def evaluationToColim [HasColimitsOfShape J C] (j : J) :
    (evaluation J C).obj j ⟶ colim where
  app G := colimit.ι G j

variable [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

instance : (colim : (J ⥤ C) ⥤ C).PreservesHomology := {}

/-- If colimits of shape `J` are exact, the homology of a colimit of short complexes is the
colimit of the homologies. -/
noncomputable def isColimitHomologyMapCoconeColimitCocone (F : J ⥤ ShortComplex C) :
    IsColimit ((homologyFunctor C).mapCocone (colimitCocone F)) := by
  let S := (functorEquivalence J C).inverse.obj F
  let e : F ⋙ homologyFunctor C ≅ S.homology :=
    NatIso.ofComponents (fun j ↦ S.mapHomologyIso ((evaluation J C).obj j)) (fun {j j'} f ↦ by
      have := NatTrans.app_homology ((evaluation J C).map f) S
      dsimp at this ⊢
      rw [this, Iso.hom_inv_id_assoc]
      rfl)
  refine ((IsColimit.precomposeHomEquiv e _).symm (colimit.isColimit _)).ofIsoColimit
    (Cocones.ext (S.mapHomologyIso colim).symm fun j ↦ ?_)
  have := homologyMap_mapNatTrans (S := S) (evaluationToColim j)
  dsimp [e] at this ⊢
  rw [this]
  rfl

instance preservesColimitsOfShape_homologyFunctor :
    PreservesColimitsOfShape J (homologyFunctor C) :=
  ⟨fun {F} ↦ preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitHomologyMapCoconeColimitCocone F)⟩

end ShortComplex

end CategoryTheory

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {J : Type*} [Category* J]
  {ι : Type*} (c : ComplexShape ι)

instance preservesColimitsOfShape_shortComplexFunctor [HasColimitsOfShape J C] (i : ι) :
    PreservesColimitsOfShape J (shortComplexFunctor C c i) :=
  ⟨fun {_} ↦ ⟨fun {_} hs ↦ ⟨ShortComplex.isColimitOfIsColimitπ _
    (isColimitOfPreserves (eval C c (c.prev i)) hs) (isColimitOfPreserves (eval C c i) hs)
    (isColimitOfPreserves (eval C c (c.next i)) hs)⟩⟩⟩

/-- If colimits of shape `J` are exact, the homology functors of complexes preserve them. -/
instance preservesColimitsOfShape_homologyFunctor [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] (i : ι) :
    PreservesColimitsOfShape J (homologyFunctor C c i) :=
  preservesColimitsOfShape_of_natIso (homologyFunctorIso C c i).symm

end HomologicalComplex

namespace CategoryTheory.Limits

lemma Cofan.bijective_of_iso {C : Type*} [Category* C] {J : Type*} {X : J → C} (c : Cofan X)
    {T T' : C} (e : T ≅ T')
    (h : Function.Bijective fun (g : c.pt ⟶ T') (j : J) ↦ c.inj j ≫ g) :
    Function.Bijective fun (g : c.pt ⟶ T) (j : J) ↦ c.inj j ≫ g := by
  refine ⟨fun g₁ g₂ hg ↦ ?_, fun f ↦ ?_⟩
  · rw [← cancel_mono e.hom]
    exact h.1 (funext fun j ↦ by simpa using congrArg (· ≫ e.hom) (congrFun hg j))
  · obtain ⟨g, hg⟩ := h.2 fun j ↦ f j ≫ e.hom
    exact ⟨g ≫ e.inv, funext fun j ↦ by simp [reassoc_of% (congrFun hg j)]⟩

/-- A functor preserves coproducts of shape `J` if it sends the chosen coproduct cofans to
colimit cofans. -/
lemma preservesColimitsOfShape_discrete_of_isColimit_cofan {A B : Type*} [Category* A]
    [Category* B] {J : Type*} [HasColimitsOfShape (Discrete J) A] (Φ : A ⥤ B)
    (h : ∀ X : J → A, IsColimit (Cofan.mk (Φ.obj (∐ X)) fun j ↦ Φ.map (Sigma.ι X j))) :
    PreservesColimitsOfShape (Discrete J) Φ := by
  refine ⟨fun {G} ↦ ?_⟩
  let X : J → A := fun j ↦ G.obj ⟨j⟩
  suffices PreservesColimit (Discrete.functor X) Φ from
    preservesColimit_of_iso_diagram Φ (Discrete.natIso fun _ ↦ Iso.refl _ : _ ≅ G)
  exact preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct X)
    ((isColimitMapCoconeCofanMkEquiv Φ X _).symm (h X))

end CategoryTheory.Limits

namespace HomotopyCategory

variable {C : Type*} [Category* C] [Preadditive C] {J : Type*}
  [HasColimitsOfShape (Discrete J) C]
  {K : J → CochainComplex C ℤ} {P : CochainComplex C ℤ} {ι : ∀ j, K j ⟶ P}
  (hc : IsColimit (Cofan.mk P ι))

include hc in
/-- Homotopies glue along a coproduct of complexes. -/
noncomputable def homotopyOfIsColimitCofan {L : CochainComplex C ℤ} {φ ψ : P ⟶ L}
    (h : ∀ j, Homotopy (ι j ≫ φ) (ι j ≫ ψ)) : Homotopy φ ψ where
  hom p q := Cofan.IsColimit.desc
    (isColimitCofanMkObjOfIsColimit (HomologicalComplex.eval C _ p) _ _ hc)
    fun j ↦ (h j).hom p q
  zero p q hpq := Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (HomologicalComplex.eval C _ p) _ _ hc) _ _ fun j ↦ by
      simp [Cofan.IsColimit.fac, (h j).zero p q hpq]
  comm p := Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (HomologicalComplex.eval C _ p) _ _ hc) _ _ fun j ↦ by
      have hj := (h j).comm p
      have h₁ : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
      have h₂ : (ComplexShape.up ℤ).Rel (p - 1) p := by simp
      rw [dNext_eq _ h₁, prevD_eq _ h₂] at hj ⊢
      simp only [cofan_mk_inj, HomologicalComplex.eval_map, Preadditive.comp_add,
        HomologicalComplex.Hom.comm_assoc, HomologicalComplex.comp_f] at hj ⊢
      erw [Cofan.IsColimit.fac, Cofan.IsColimit.fac_assoc]
      exact hj

include hc in
/-- The quotient functor to the homotopy category preserves coproducts. -/
noncomputable def isColimitQuotientCofan :
    IsColimit (Cofan.mk ((quotient C (.up ℤ)).obj P) fun j ↦ (quotient C _).map (ι j)) :=
  Cofan.isColimitOfBijective _ fun T ↦ by
    obtain ⟨L, rfl⟩ := quotient_obj_surjective T
    refine ⟨fun f g hfg ↦ ?_, fun f ↦ ?_⟩
    · obtain ⟨φ, rfl⟩ := (quotient _ _).map_surjective f
      obtain ⟨ψ, rfl⟩ := (quotient _ _).map_surjective g
      refine eq_of_homotopy _ _ (homotopyOfIsColimitCofan hc fun j ↦ homotopyOfEq _ _ ?_)
      simpa only [cofan_mk_inj, Functor.map_comp] using congrFun hfg j
    · choose φ hφ using fun j ↦ (quotient C (.up ℤ)).map_surjective (f j)
      refine ⟨(quotient _ _).map (Cofan.IsColimit.desc hc φ), funext fun j ↦ ?_⟩
      simp only [cofan_mk_inj, ← Functor.map_comp, ← hφ]
      congr 1
      exact Cofan.IsColimit.fac hc φ j

omit [HasColimitsOfShape (Discrete J) C] in
lemma preservesColimitsOfShape_quotient [HasColimitsOfShape (Discrete J) C] :
    PreservesColimitsOfShape (Discrete J) (quotient C (.up ℤ)) :=
  preservesColimitsOfShape_discrete_of_isColimit_cofan _ fun X ↦
    isColimitQuotientCofan (coproductIsCoproduct X)

instance : PreservesColimitsOfShape (Discrete J) (quotient C (.up ℤ)) :=
  preservesColimitsOfShape_quotient

instance : HasColimitsOfShape (Discrete J) (HomotopyCategory C (.up ℤ)) :=
  hasColimitsOfShape_discrete_of_essSurj (quotient C (.up ℤ))

end HomotopyCategory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [HasKInjectiveResolutions C]

lemma exists_iso_Qh_obj_of_isKInjective (Y : DerivedCategory C) :
    ∃ (L : CochainComplex C ℤ) (_ : L.IsKInjective),
      Nonempty (Y ≅ Qh.obj ((HomotopyCategory.quotient _ _).obj L)) := by
  obtain ⟨L, hL, i, -, hi⟩ := HasKInjectiveResolutions.exists_isKInjective (Q.objPreimage Y)
  have : IsIso (Q.map i) := by rwa [isIso_Q_map_iff_quasiIso]
  exact ⟨L, hL, ⟨(Q.objObjPreimageIso Y).symm ≪≫ asIso (Q.map i) ≪≫
    ((quotientCompQhIso C).app L).symm⟩⟩

variable {J : Type*}

/-- The localization functor `Qh` from the homotopy category to the derived category preserves
coproducts. -/
noncomputable def isColimitQhCofan {X : J → HomotopyCategory C (.up ℤ)}
    {P : HomotopyCategory C (.up ℤ)} {ι : ∀ j, X j ⟶ P} (hc : IsColimit (Cofan.mk P ι)) :
    IsColimit (Cofan.mk (Qh.obj P) fun j ↦ Qh.map (ι j)) :=
  Cofan.isColimitOfBijective _ fun T ↦ by
    obtain ⟨L, _, ⟨e⟩⟩ := exists_iso_Qh_obj_of_isKInjective T
    refine Cofan.bijective_of_iso _ e ?_
    have hQh (Y : HomotopyCategory C (.up ℤ)) := CochainComplex.IsKInjective.Qh_map_bijective Y L
    rw [← Function.Bijective.of_comp_iff _ (hQh P)]
    have : ((fun (g : Qh.obj P ⟶ _) (j : J) ↦ (Cofan.mk (Qh.obj P) fun j ↦ Qh.map (ι j)).inj j ≫ g)
        ∘ fun g ↦ Qh.map g) =
        (fun (f : ∀ j, X j ⟶ _) (j : J) ↦ Qh.map (f j)) ∘
          fun (g : P ⟶ _) (j : J) ↦ (Cofan.mk P ι).inj j ≫ g := by
      ext g j
      simp
    rw [this]
    exact (Function.Bijective.piMap fun j ↦ hQh (X j)).comp (Cofan.bijective_of_isColimit hc _)

variable [HasColimitsOfShape (Discrete J) C]

instance : PreservesColimitsOfShape (Discrete J) (Qh (C := C)) :=
  preservesColimitsOfShape_discrete_of_isColimit_cofan _ fun X ↦
    isColimitQhCofan (coproductIsCoproduct X)

instance : HasColimitsOfShape (Discrete J) (DerivedCategory C) :=
  hasColimitsOfShape_discrete_of_essSurj (Qh (C := C))

instance : PreservesColimitsOfShape (Discrete J) (Q (C := C)) :=
  preservesColimitsOfShape_of_natIso (quotientCompQhIso C)

/-- If coproducts of shape `J` are exact in `C`, the homology functors `Hⁿ : D(C) ⥤ C` preserve
coproducts of shape `J`. -/
instance preservesColimitsOfShape_homologyFunctor [HasExactColimitsOfShape (Discrete J) C]
    (n : ℤ) : PreservesColimitsOfShape (Discrete J) (homologyFunctor C n) :=
  have := preservesColimitsOfShape_of_natIso (homologyFunctorFactors C n).symm
  preservesColimitsOfShape_discrete_of_essSurj (Q (C := C)) _

end DerivedCategory

namespace CategoryTheory.Functor

variable {C₁ C₂ : Type*} [Category* C₁] [Abelian C₁] [Category* C₂] [Abelian C₂]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasKInjectiveResolutions C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {J : Type*} [HasColimitsOfShape (Discrete J) C₁] [HasColimitsOfShape (Discrete J) C₂]
  [PreservesColimitsOfShape (Discrete J) F]

/-- The functor induced on derived categories by an exact functor preserving coproducts of
shape `J` preserves coproducts of shape `J`. -/
instance preservesColimitsOfShape_mapDerivedCategory [HasKInjectiveResolutions C₁] :
    PreservesColimitsOfShape (Discrete J) F.mapDerivedCategory :=
  have := preservesColimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  preservesColimitsOfShape_discrete_of_essSurj DerivedCategory.Q _

end CategoryTheory.Functor
