/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives

/-!
# Coproducts in derived categories

Let `C` be an abelian category with K-injective resolutions and with coproducts of shape `J`.
We show that the derived category `D(C)` has coproducts of shape `J` and that the
localization functor `Q : CochainComplex C ℤ ⥤ D(C)` preserves them: a coproduct of complexes
(computed degreewise) is also a coproduct in `D(C)`.

The proof goes through the homotopy category: the quotient functor to the homotopy category
preserves coproducts, because homotopies can be glued along a coproduct of complexes; and for a
K-injective complex `I`, morphisms `Q(K) ⟶ Q(I)` in `D(C)` are homotopy classes of morphisms
`K ⟶ I`. Since every object of `D(C)` is the image of a K-injective complex, this shows that
`Q` sends coproducts of complexes to coproducts.

As a consequence, a functor `G : D(C) ⥤ E` preserves coproducts of shape `J` as soon as
`Q ⋙ G` does; in particular, for an exact functor `F : C ⥤ D` preserving coproducts of shape
`J` (with `D` satisfying the same assumptions), the induced functor `F.mapDerivedCategory`
preserves coproducts of shape `J`.

## Main statements

- `HomotopyCategory.preservesColimitsOfShape_quotient`: the quotient functor to the homotopy
  category preserves coproducts.
- `DerivedCategory.preservesColimitsOfShape_Q`: `Q : CochainComplex C ℤ ⥤ D(C)` preserves
  coproducts of shape `J`.
- `DerivedCategory.hasColimitsOfShape_discrete`: `D(C)` has coproducts of shape `J`.
- `DerivedCategory.preservesColimitsOfShape_of_Q_comp`: a functor out of `D(C)` preserves
  coproducts of shape `J` if its composition with `Q` does.
- `CategoryTheory.Functor.preservesColimitsOfShape_mapDerivedCategory`: the functor induced on
  derived categories by an exact functor preserving coproducts preserves coproducts.
-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CategoryTheory.Limits.Cofan

variable {C : Type*} [Category* C] {J : Type*} {f : J → C}

/-- A cofan `c` is a colimit cofan if, for every object `Y`, a morphism `c.pt ⟶ Y` is uniquely
determined by its compositions with the injections, and every family of morphisms arises in
this way. -/
noncomputable def isColimitOfBijective (c : Cofan f)
    (h : ∀ Y : C, Function.Bijective (fun (φ : c.pt ⟶ Y) (j : J) ↦ c.inj j ≫ φ)) :
    IsColimit c :=
  Cofan.IsColimit.mk c (fun s ↦ (Equiv.ofBijective _ (h s.pt)).symm s.inj)
    (fun s j ↦ congrFun ((Equiv.ofBijective _ (h s.pt)).apply_symm_apply s.inj) j)
    (fun s m hm ↦ (Equiv.ofBijective _ (h s.pt)).injective (by
      rw [Equiv.apply_symm_apply]
      funext j
      exact hm j))

/-- For a colimit cofan `c`, morphisms out of `c.pt` are the same as families of morphisms out
of the components. -/
lemma bijective_of_isColimit {c : Cofan f} (hc : IsColimit c) (Y : C) :
    Function.Bijective (fun (φ : c.pt ⟶ Y) (j : J) ↦ c.inj j ≫ φ) :=
  ⟨fun _ _ h ↦ Cofan.IsColimit.hom_ext hc _ _ fun j ↦ congrFun h j,
    fun g ↦ ⟨Cofan.IsColimit.desc hc g, funext fun j ↦ Cofan.IsColimit.fac hc g j⟩⟩

/-- The bijectivity condition of `Cofan.isColimitOfBijective` is invariant under isomorphisms
of the test object. -/
lemma bijective_of_iso (c : Cofan f) {Y Y' : C} (e : Y ≅ Y')
    (h : Function.Bijective (fun (φ : c.pt ⟶ Y) (j : J) ↦ c.inj j ≫ φ)) :
    Function.Bijective (fun (φ : c.pt ⟶ Y') (j : J) ↦ c.inj j ≫ φ) := by
  have key : (fun (φ : c.pt ⟶ Y') (j : J) ↦ c.inj j ≫ φ) =
      (fun (ψ : ∀ j, f j ⟶ Y) (j : J) ↦ ψ j ≫ e.hom) ∘
        (fun (φ : c.pt ⟶ Y) (j : J) ↦ c.inj j ≫ φ) ∘ (fun φ ↦ φ ≫ e.inv) := by
    funext φ j
    simp
  rw [key]
  refine Function.Bijective.comp ?_ (h.comp ?_)
  · exact (Function.bijective_iff_has_inverse).2 ⟨fun ψ j ↦ ψ j ≫ e.inv,
      fun ψ ↦ by simp, fun ψ ↦ by simp⟩
  · exact (Function.bijective_iff_has_inverse).2 ⟨fun φ ↦ φ ≫ e.hom,
      fun φ ↦ by simp, fun φ ↦ by simp⟩

/-- A functor preserves coproducts of shape `J` if it sends colimit cofans to colimit cofans. -/
lemma _root_.CategoryTheory.Functor.preservesColimitsOfShape_discrete_of_isColimit_cofan
    {D : Type*} [Category* D] (F : C ⥤ D)
    (h : ∀ (K : J → C) (s : Cofan K), IsColimit s →
      Nonempty (IsColimit (Cofan.mk (F.obj s.pt) fun j ↦ F.map (s.inj j)))) :
    PreservesColimitsOfShape (Discrete J) F := by
  have (K : J → C) : PreservesColimit (Discrete.functor K) F :=
    ⟨fun {s} hs ↦ ⟨(isColimitMapCoconeCofanMkEquiv F K (Cofan.inj (f := K) s)).symm
      (h K s hs).some⟩⟩
  exact preservesColimitsOfShape_of_discrete F

end CategoryTheory.Limits.Cofan

namespace HomotopyCategory

variable {C : Type*} [Category* C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}

/-- Homotopies can be glued along a coproduct of complexes which is computed degreewise: if
`s` is a cofan of complexes such that each degree is a colimit cofan, and the compositions of
`f, g : s.pt ⟶ L` with all the injections are homotopic, then `f` and `g` are homotopic. -/
noncomputable def homotopyOfCofan {J : Type*} {K : J → HomologicalComplex C c} (s : Cofan K)
    (hs : ∀ i, IsColimit (Cofan.mk (s.pt.X i) fun j ↦ (s.inj j).f i))
    {L : HomologicalComplex C c} (f g : s.pt ⟶ L)
    (H : ∀ j, Homotopy (s.inj j ≫ f) (s.inj j ≫ g)) : Homotopy f g where
  hom i i' := Cofan.IsColimit.desc (hs i) fun j ↦ (H j).hom i i'
  zero i i' hii' := Cofan.IsColimit.hom_ext (hs i) _ _ fun j ↦ by
    simp only [Cofan.IsColimit.fac, comp_zero]
    exact (H j).zero i i' hii'
  comm i := Cofan.IsColimit.hom_ext (hs i) _ _ fun j ↦ by
    have hfac (a b : ι) : (s.inj j).f a ≫ Cofan.IsColimit.desc (hs a)
        (fun j ↦ (H j).hom a b) = (H j).hom a b := Cofan.IsColimit.fac (hs a) _ j
    have h₁ := dNext_comp_left (s.inj j) (fun a b ↦ Cofan.IsColimit.desc (hs a)
      (fun j ↦ (H j).hom a b)) i
    have h₂ := prevD_comp_left (s.inj j) (fun a b ↦ Cofan.IsColimit.desc (hs a)
      (fun j ↦ (H j).hom a b)) i
    simp only [hfac] at h₁ h₂
    have := (H j).comm i
    simp only [HomologicalComplex.comp_f] at this
    simp only [cofan_mk_inj, Preadditive.comp_add, ← h₁, ← h₂, this]

variable (C c) in
/-- The quotient functor to the homotopy category preserves coproducts (computed
degreewise). -/
instance preservesColimitsOfShape_quotient (J : Type*) [HasColimitsOfShape (Discrete J) C] :
    PreservesColimitsOfShape (Discrete J) (quotient C c) := by
  refine Functor.preservesColimitsOfShape_discrete_of_isColimit_cofan _ fun K s hs ↦ ⟨?_⟩
  have hs' (i : ι) : IsColimit (Cofan.mk (s.pt.X i) fun j ↦ (s.inj j).f i) :=
    isColimitCofanMkObjOfIsColimit (HomologicalComplex.eval C c i) K s.inj
      (hs : IsColimit (Cofan.mk s.pt s.inj))
  refine Cofan.isColimitOfBijective _ fun Y ↦ ?_
  obtain ⟨L, rfl⟩ := quotient_obj_surjective Y
  refine ⟨fun φ₁ φ₂ h ↦ ?_, fun ψ ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := (quotient C c).map_surjective φ₁
    obtain ⟨g, rfl⟩ := (quotient C c).map_surjective φ₂
    refine eq_of_homotopy _ _ (homotopyOfCofan s hs' f g fun j ↦ homotopyOfEq _ _ ?_)
    simpa only [Functor.map_comp, cofan_mk_inj] using congrFun h j
  · choose g hg using fun j ↦ (quotient C c).map_surjective (ψ j)
    refine ⟨(quotient C c).map (Cofan.IsColimit.desc hs g), funext fun j ↦ ?_⟩
    simp only [cofan_mk_inj, ← Functor.map_comp, Cofan.IsColimit.fac, hg]

end HomotopyCategory

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- Every object of the derived category is isomorphic to the image of a K-injective
complex. -/
lemma exists_iso_Qh_quotient_obj [HasKInjectiveResolutions C] (Y : DerivedCategory C) :
    ∃ (I : CochainComplex C ℤ) (_ : I.IsKInjective),
      Nonempty (Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj I) ≅ Y) := by
  obtain ⟨I, hI, h⟩ := ((HomotopyCategory.KInjectives.Qh (C := C)).objPreimage Y).mk_surjective
  exact ⟨I, hI, ⟨(HomotopyCategory.KInjectives.Qh (C := C)).mapIso (eqToIso h.symm) ≪≫
    (HomotopyCategory.KInjectives.Qh (C := C)).objObjPreimageIso Y⟩⟩

variable [HasKInjectiveResolutions C]

/-- The functor `Qh : K(C) ⥤ D(C)` preserves coproducts: morphisms from the image of a
coproduct to the image of a K-injective complex are morphisms in the homotopy category. -/
instance preservesColimitsOfShape_Qh (J : Type*) :
    PreservesColimitsOfShape (Discrete J) (Qh (C := C)) := by
  refine Functor.preservesColimitsOfShape_discrete_of_isColimit_cofan _ fun K s hs ↦ ⟨?_⟩
  refine Cofan.isColimitOfBijective _ fun Y ↦ ?_
  obtain ⟨I, _, ⟨e⟩⟩ := exists_iso_Qh_quotient_obj Y
  refine Cofan.bijective_of_iso _ e ?_
  have key : (fun (φ : Qh.obj s.pt ⟶ Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj I))
      (j : J) ↦ (Cofan.mk (Qh.obj s.pt) fun j ↦ Qh.map (s.inj j)).inj j ≫ φ) ∘ Qh.map =
      (fun ψ j ↦ Qh.map (ψ j)) ∘ (fun φ (j : J) ↦ s.inj j ≫ φ) := by
    funext φ j
    simp
  have h₂ : Function.Bijective ((fun (ψ : ∀ j, K j ⟶ (HomotopyCategory.quotient C _).obj I)
      (j : J) ↦ Qh.map (ψ j)) ∘ (fun φ (j : J) ↦ s.inj j ≫ φ)) := by
    refine Function.Bijective.comp ⟨fun ψ₁ ψ₂ h ↦ funext fun j ↦ ?_, fun ψ ↦ ?_⟩
      (Cofan.bijective_of_isColimit hs _)
    · exact (CochainComplex.IsKInjective.Qh_map_bijective (K j) I).1 (congrFun h j)
    · exact ⟨fun j ↦ ((CochainComplex.IsKInjective.Qh_map_bijective (K j) I).2 (ψ j)).choose,
        funext fun j ↦
          ((CochainComplex.IsKInjective.Qh_map_bijective (K j) I).2 (ψ j)).choose_spec⟩
  rw [← key] at h₂
  exact (Function.Bijective.of_comp_iff _
    (CochainComplex.IsKInjective.Qh_map_bijective s.pt I)).1 h₂

/-- The localization functor `Q : CochainComplex C ℤ ⥤ D(C)` preserves coproducts: a
coproduct of complexes is a coproduct in the derived category. -/
instance preservesColimitsOfShape_Q (J : Type*) [HasColimitsOfShape (Discrete J) C] :
    PreservesColimitsOfShape (Discrete J) (Q (C := C)) :=
  preservesColimitsOfShape_of_natIso (quotientCompQhIso C)

/-- Every family of objects of `D(C)` is isomorphic to the image under `Q` of a family of
complexes. -/
noncomputable def discreteFunctorIsoQ {J : Type*} (F : Discrete J ⥤ DerivedCategory C) :
    F ≅ Discrete.functor (fun j ↦ Q.objPreimage (F.obj ⟨j⟩)) ⋙ Q :=
  Discrete.natIso fun j ↦ (Q.objObjPreimageIso (F.obj j)).symm

/-- The derived category has coproducts of shape `J` if `C` does. -/
instance hasColimitsOfShape_discrete (J : Type*) [HasColimitsOfShape (Discrete J) C] :
    HasColimitsOfShape (Discrete J) (DerivedCategory C) where
  has_colimit F := by
    have : HasColimit (Discrete.functor (fun j ↦ Q.objPreimage (F.obj ⟨j⟩)) ⋙ Q) :=
      ⟨⟨⟨_, isColimitOfPreserves Q (colimit.isColimit _)⟩⟩⟩
    exact hasColimit_of_iso (discreteFunctorIsoQ F)

/-- A functor `G` out of the derived category preserves coproducts of shape `J` as soon as
`Q ⋙ G` does. -/
lemma preservesColimitsOfShape_of_Q_comp {E : Type*} [Category* E] (J : Type*)
    [HasColimitsOfShape (Discrete J) C] (G : DerivedCategory C ⥤ E)
    [PreservesColimitsOfShape (Discrete J) (Q ⋙ G)] :
    PreservesColimitsOfShape (Discrete J) G where
  preservesColimit {F} := by
    have : PreservesColimit (Discrete.functor (fun j ↦ Q.objPreimage (F.obj ⟨j⟩)) ⋙ Q) G :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves Q (colimit.isColimit _))
        (isColimitOfPreserves (Q ⋙ G) (colimit.isColimit _))
    exact preservesColimit_of_iso_diagram G (discreteFunctorIsoQ F).symm

end DerivedCategory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
  [HasKInjectiveResolutions D] (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The functor induced on cochain complexes by a functor preserving coproducts of shape `J`
preserves coproducts of shape `J`. -/
instance preservesColimitsOfShape_mapHomologicalComplex {ι : Type*} (c : ComplexShape ι)
    (J : Type*) [HasColimitsOfShape (Discrete J) C] [PreservesColimitsOfShape (Discrete J) F] :
    PreservesColimitsOfShape (Discrete J) (F.mapHomologicalComplex c) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun i ↦
    preservesColimitsOfShape_of_natIso
      (NatIso.ofComponents (fun K ↦ Iso.refl _) (by simp) : HomologicalComplex.eval C c i ⋙ F ≅
        F.mapHomologicalComplex c ⋙ HomologicalComplex.eval D c i)

/-- The functor induced on derived categories by an exact functor preserving coproducts of
shape `J` preserves coproducts of shape `J`. -/
instance preservesColimitsOfShape_mapDerivedCategory (J : Type*)
    [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Discrete J) D]
    [PreservesColimitsOfShape (Discrete J) F] :
    PreservesColimitsOfShape (Discrete J) F.mapDerivedCategory := by
  have : PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesColimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  exact DerivedCategory.preservesColimitsOfShape_of_Q_comp J _

end CategoryTheory.Functor
