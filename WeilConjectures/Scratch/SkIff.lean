module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

lemma singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map_Q_map
    {A : C} {M : CochainComplex C ℤ} (f : (CochainComplex.singleFunctor C 0).obj A ⟶ M) :
    (singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
      (homologyFunctor C 0).map (Q.map f) =
    ((singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
      (homologyFunctorFactors C 0).hom.app _) ≫
      HomologicalComplex.homologyMap f 0 ≫ (homologyFunctorFactors C 0).inv.app M := by
  have := (homologyFunctorFactors C 0).hom.naturality f
  simp only [Functor.comp_map] at this
  simp only [Category.assoc]
  congr 1
  erw [← reassoc_of% this, Iso.hom_inv_id_app, Category.comp_id]


/-- The isomorphism `A ≅ Z⁰(A[0])` from an object to the degree-`0` cycles of the single
complex, through which the homology of the derived single functor is computed. -/
noncomputable def singleCyclesHom (A : C) :
    A ⟶ ((HomologicalComplex.single C (.up ℤ) 0).obj A).cycles 0 :=
  (singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
    (homologyFunctorFactors C 0).hom.app _ ≫
      (HomologicalComplex.singleObjHomologySelfIso _ 0 A).hom ≫
        (HomologicalComplex.singleObjCyclesSelfIso _ 0 A).inv

instance (A : C) : IsIso (singleCyclesHom A) := by
  dsimp [singleCyclesHom]; infer_instance

lemma singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map_Q_map'
    {A : C} {M : CochainComplex C ℤ} (f : (HomologicalComplex.single C (.up ℤ) 0).obj A ⟶ M) :
    (singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
      (homologyFunctor C 0).map (Q.map f) =
    singleCyclesHom A ≫ HomologicalComplex.cyclesMap f 0 ≫ M.homologyπ 0 ≫
      (homologyFunctorFactors C 0).inv.app M := by
  rw [singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map_Q_map f]
  simp only [singleCyclesHom, Category.assoc]
  congr 2
  rw [← cancel_epi (((HomologicalComplex.single C (.up ℤ) 0).obj A).homologyπ 0),
    HomologicalComplex.homologyπ_naturality_assoc]
  simp

lemma singleCyclesHom_naturality {A A' : C} (φ : A' ⟶ A) :
    singleCyclesHom A' ≫ HomologicalComplex.cyclesMap
      ((HomologicalComplex.single C (.up ℤ) 0).map φ) 0 = φ ≫ singleCyclesHom A := by
  have h₁ := (singleFunctorCompHomologyFunctorIso C 0).inv.naturality φ
  have h₂ := (homologyFunctorFactors C 0).hom.naturality
    ((HomologicalComplex.single C (.up ℤ) 0).map φ)
  simp only [Functor.id_map, Functor.comp_map] at h₁ h₂
  simp only [singleCyclesHom, Category.assoc,
    HomologicalComplex.singleObjCyclesSelfIso_inv_naturality]
  rw [← HomologicalComplex.singleObjHomologySelfIso_hom_naturality_assoc, reassoc_of% h₁]
  erw [reassoc_of% h₂]
  rfl

end DerivedCategory

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}

/-- The free sheaf `Λ[W]` corepresents sections over `W`. -/
noncomputable def Etale.freeSheafHomEquiv (W : X.Etale)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((Etale.freeSheaf Λ X).obj W ⟶ G) ≃ G.obj.obj (op W) :=
  ((sheafificationAdjunction _ _).homEquiv _ _).trans <|
    (((ModuleCat.adj Λ).whiskerRight X.Etaleᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv

lemma Etale.freeSheafHomEquiv_apply (W : X.Etale)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : (Etale.freeSheaf Λ X).obj W ⟶ G) :
    Etale.freeSheafHomEquiv Λ W G f = (Etale.freeSheafSections Λ G).app (op W) f := by
  simp [Etale.freeSheafHomEquiv, Etale.freeSheafSections]
  rfl

lemma Etale.freeSheafHomEquiv_comp (W : X.Etale)
    {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : (Etale.freeSheaf Λ X).obj W ⟶ G) (g : G ⟶ G') :
    Etale.freeSheafHomEquiv Λ W G' (f ≫ g) = g.hom.app (op W) (Etale.freeSheafHomEquiv Λ W G f) := by
  simp only [Etale.freeSheafHomEquiv_apply, Etale.freeSheafSections]
  rfl

lemma Etale.freeSheafHomEquiv_map {W W' : X.Etale} (v : W' ⟶ W)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : (Etale.freeSheaf Λ X).obj W ⟶ G) :
    Etale.freeSheafHomEquiv Λ W' G ((Etale.freeSheaf Λ X).map v ≫ f) =
      G.obj.map v.op (Etale.freeSheafHomEquiv Λ W G f) := by
  simp only [Etale.freeSheafHomEquiv_apply]
  exact congrArg (fun k ↦ k f) ((Etale.freeSheafSections Λ G).naturality v.op)


variable {Λ}

/-- For `L ∈ D⁺(X_ét, Λ)`, the map `Hom(Λ[W][0], L) ⟶ Hom(Λ[W], H⁰(L))` induced by the degree-`0`
homology, natural in `W`. -/
noncomputable def Etale.derivedHomToHomology
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.freeSheaf Λ X ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj L ⟶
      (Etale.freeSheaf Λ X).op ⋙ preadditiveYoneda.obj
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj L) where
  app W := AddCommGrpCat.ofHom <|
    (Preadditive.leftComp _
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _)).comp
      (DerivedCategory.Plus.homologyFunctor _ 0).mapAddHom
  naturality W W' g := by
    have hs := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
      (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).inv.naturality
        ((Etale.freeSheaf Λ X).map g.unop)
    dsimp at hs
    ext f
    revert f
    change ∀ f : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶
        L,
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map ((Etale.freeSheaf Λ X).map g.unop) ≫ f) =
      (Etale.freeSheaf Λ X).map g.unop ≫
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
          ((Etale.freeSheaf Λ X).obj W.unop) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map f
    intro f
    rw [Functor.map_comp, ← reassoc_of% hs]

lemma Etale.derivedHomToHomology_app_apply
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (W : X.Etaleᵒᵖ)
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶ L) :
    (Etale.derivedHomToHomology L).app W β =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map β :=
  rfl

/-- The sections map of a morphism of sheaves of `Λ`-modules, on the underlying presheaves of
abelian groups. -/
noncomputable abbrev Etale.sectionsMap {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (g : G ⟶ G') :
    ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G).obj ⟶
    ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G').obj :=
  ((sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map g).hom

lemma Etale.freeSheafSections_naturality
    {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : G ⟶ G') :
    Etale.freeSheafSections Λ G ≫ Etale.sectionsMap g =
      Functor.whiskerLeft (Etale.freeSheaf Λ X).op (preadditiveYoneda.map g) ≫
        Etale.freeSheafSections Λ G' := by
  ext W f
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← Etale.freeSheafHomEquiv_apply, ← Etale.freeSheafHomEquiv_apply]
  exact (Etale.freeSheafHomEquiv_comp Λ W.unop f g).symm

end AlgebraicGeometry
