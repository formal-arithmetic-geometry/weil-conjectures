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


namespace Plus

lemma exists_ι_map_eq {A : C} (M : CochainComplex.Plus C) [M.obj.IsKInjective]
    (β : (singleFunctor C 0).obj A ⟶ Q.obj M) :
    ∃ f : (HomologicalComplex.single C (.up ℤ) 0).obj A ⟶ M.obj,
      ι.map β = DerivedCategory.Q.map f ≫ (quotientCompQhIso C).inv.app M.obj := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj ((HomologicalComplex.single C (.up ℤ) 0).obj A))
      M.obj).2 ((quotientCompQhIso C).hom.app _ ≫ ι.map β)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨f, ?_⟩
  rw [quotientCompQhIso_inv_naturality]
  erw [hg]
  simp

lemma singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map {A : C}
    {M : CochainComplex.Plus C} (β : (singleFunctor C 0).obj A ⟶ Q.obj M)
    (f : (HomologicalComplex.single C (.up ℤ) 0).obj A ⟶ M.obj)
    (hf : ι.map β = DerivedCategory.Q.map f ≫ (quotientCompQhIso C).inv.app M.obj) :
    (singleFunctorCompHomologyFunctorIso 0).inv.app A ≫ (homologyFunctor C 0).map β =
      singleCyclesHom A ≫ HomologicalComplex.cyclesMap f 0 ≫ M.obj.homologyπ 0 ≫
        (homologyFunctorFactors C 0).inv.app M.obj ≫
          (DerivedCategory.homologyFunctor C 0).map ((quotientCompQhIso C).inv.app M.obj) := by
  change (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
    (DerivedCategory.homologyFunctor C 0).map (ι.map β) = _
  rw [hf, Functor.map_comp, ← Category.assoc,
    singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map_Q_map']
  simp

lemma eq_zero_of_homotopy {A : C} {M : CochainComplex.Plus C}
    (β : (singleFunctor C 0).obj A ⟶ Q.obj M)
    (f : (HomologicalComplex.single C (.up ℤ) 0).obj A ⟶ M.obj)
    (hf : ι.map β = DerivedCategory.Q.map f ≫ (quotientCompQhIso C).inv.app M.obj)
    (h : Homotopy f 0) : β = 0 := by
  have h₀ : (HomotopyCategory.quotient _ _).map f = 0 := by
    rw [HomotopyCategory.eq_of_homotopy _ _ h, Functor.map_zero]
  have h₁ : DerivedCategory.Q.map f = 0 := by
    rw [← cancel_epi ((quotientCompQhIso C).hom.app _), ← quotientCompQhIso_hom_naturality, h₀]
    simp
  apply ι.map_injective
  rw [hf, h₁, Functor.map_zero, zero_comp]

end Plus

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


section Key

variable (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

/-- The comparison `H⁰(M) ⟶ H⁰(Q M)` between the homology sheaf of a complex and the homology of
its image in `D⁺`. -/
noncomputable abbrev Etale.homologyComparison :
    M.obj.homology 0 ⟶
      (DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M) :=
  (DerivedCategory.homologyFunctorFactors _ 0).inv.app M.obj ≫
    (DerivedCategory.homologyFunctor _ 0).map
      ((DerivedCategory.quotientCompQhIso _).inv.app M.obj)

lemma Etale.derivedHomToHomology_app_eq {W : X.Etaleᵒᵖ}
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶
      DerivedCategory.Plus.Q.obj M)
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶ M.obj)
    (hf : DerivedCategory.Plus.ι.map β =
      DerivedCategory.Q.map f ≫ (DerivedCategory.quotientCompQhIso _).inv.app M.obj) :
    (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M)).app W β =
      DerivedCategory.singleCyclesHom _ ≫ HomologicalComplex.cyclesMap f 0 ≫
        M.obj.homologyπ 0 ≫ Etale.homologyComparison M :=
  DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map
    β f hf

theorem Etale.isLocallySurjective_derivedHomToHomology [M.obj.IsKInjective] :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        Etale.freeSheafSections Λ
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))) := by
  have : Sheaf.IsLocallySurjective (M.obj.homologyπ 0) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  constructor
  intro W σ
  let σ' : ToType ((M.obj.homology 0).obj.obj (op W)) :=
    (inv (Etale.homologyComparison M)).hom.app (op W) σ
  refine GrothendieckTopology.superset_covering _ ?_
    (Presheaf.imageSieve_mem X.smallEtaleTopology (M.obj.homologyπ 0).hom σ')
  rintro V g ⟨c, hc⟩
  let A := (Etale.freeSheaf Λ X).obj V
  let c' := (Etale.freeSheafHomEquiv Λ V (M.obj.cycles 0)).symm c
  let τ := DerivedCategory.singleCyclesHom A ≫
    (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A).hom
  let fM : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj :=
    HomologicalComplex.mkHomFromSingle (inv τ ≫ c' ≫ M.obj.iCycles 0) (by
      intro k _
      simp)
  have hfM : DerivedCategory.singleCyclesHom A ≫ HomologicalComplex.cyclesMap fM 0 = c' := by
    rw [← cancel_mono (M.obj.iCycles 0), Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.mkHomFromSingle_f]
    have hτ : DerivedCategory.singleCyclesHom A ≫
        ((HomologicalComplex.single _ (.up ℤ) 0).obj A).iCycles 0 ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom = τ := by
      simp [τ, HomologicalComplex.singleObjCyclesSelfIso_hom]
    rw [reassoc_of% hτ, IsIso.hom_inv_id_assoc]
  obtain ⟨β, hβ⟩ : ∃ β : (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶
      DerivedCategory.Plus.Q.obj M, DerivedCategory.Plus.ι.map β =
        DerivedCategory.Q.map fM ≫ (DerivedCategory.quotientCompQhIso _).inv.app M.obj :=
    ⟨DerivedCategory.Plus.ι.preimage _, Functor.map_preimage _ _⟩
  refine ⟨β, ?_⟩
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply,
    Etale.derivedHomToHomology_app_eq M (W := op V) β fM hβ, reassoc_of% hfM,
    ← Etale.freeSheafHomEquiv_apply, Etale.freeSheafHomEquiv_comp, Equiv.apply_symm_apply]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    hc]
  erw [NatTrans.naturality_apply (Etale.homologyComparison M).hom g.op σ']
  have hσ : (Etale.homologyComparison M).hom.app (op W) σ' = σ := by
    simp only [σ']
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, IsIso.inv_hom_id]
    rfl
  rw [hσ]
  rfl

/-- A map from a single complex whose degree-`0` component factors through the differential
`M⁻¹ ⟶ M⁰` is null-homotopic. -/
noncomputable def Etale.homotopyOfSingle {A : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj) (b : A ⟶ M.obj.X (-1))
    (hb : f.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ≫ b ≫ M.obj.d (-1) 0) :
    Homotopy f 0 :=
  (Homotopy.ofEq (HomologicalComplex.from_single_hom_ext (j := 0) (by
    rw [hb, Homotopy.nullHomotopicMap'_f (k₂ := -1) (k₀ := 1) (by simp) (by simp)]
    simp
    rfl)) :
      Homotopy f (Homotopy.nullHomotopicMap' (fun i j (_ : j + 1 = i) ↦
        if hi : i = 0 then
          (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 A i hi).hom ≫ b ≫
            eqToHom (by congr 1; lia)
        else 0))).trans (Homotopy.nullHomotopy' _)

theorem Etale.isLocallyInjective_derivedHomToHomology [M.obj.IsKInjective] :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
      (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        Etale.freeSheafSections Λ
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))) := by
  constructor
  intro W x y hxy
  let β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶
      DerivedCategory.Plus.Q.obj M := x - y
  have hβ : (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
      Etale.freeSheafSections Λ
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))).app W β =
      0 := by
    simp only [β, map_sub]
    exact sub_eq_zero.2 hxy
  have hsieve : Presheaf.equalizerSieve x y = Presheaf.equalizerSieve (x - y) 0 := by
    ext V g
    simp only [Presheaf.equalizerSieve_apply, map_sub, map_zero]
    exact sub_eq_zero.symm
  rw [hsieve]
  let A := (Etale.freeSheaf Λ X).obj W.unop
  obtain ⟨f, hf⟩ := DerivedCategory.Plus.exists_ι_map_eq M β
  let z := DerivedCategory.singleCyclesHom A ≫ HomologicalComplex.cyclesMap f 0
  have hz : z ≫ M.obj.homologyπ 0 = (0 : A ⟶ M.obj.homology 0) := by
    have hm : IsIso (Etale.homologyComparison M) := by
      dsimp only [Etale.homologyComparison]
      infer_instance
    have h2 : z ≫ M.obj.homologyπ 0 ≫ Etale.homologyComparison M = 0 := by
      apply (Etale.freeSheafHomEquiv Λ W.unop
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))).injective
      rw [Etale.freeSheafHomEquiv_apply, Etale.freeSheafHomEquiv_apply, map_zero]
      have := Etale.derivedHomToHomology_app_eq M β f hf
      simp only [z, Category.assoc]
      rw [← this]
      exact hβ
    calc z ≫ M.obj.homologyπ 0 =
        (z ≫ M.obj.homologyπ 0 ≫ Etale.homologyComparison M) ≫ inv (Etale.homologyComparison M) := by
          simp only [Category.assoc, IsIso.hom_inv_id]; erw [Category.comp_id]
      _ = 0 := by rw [h2, Limits.zero_comp]
  let S := ShortComplex.mk (M.obj.toCycles (-1) 0) (M.obj.homologyπ 0) (by simp)
  have hS : S.Exact :=
    ShortComplex.exact_of_g_is_cokernel S (M.obj.homologyIsCokernel (-1) 0 (by simp))
  have : Epi S.toCycles := hS.epi_toCycles
  have : Sheaf.IsLocallySurjective S.toCycles :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  let k' := S.liftCycles z hz
  let k := Etale.freeSheafHomEquiv Λ W.unop S.cycles k'
  refine GrothendieckTopology.superset_covering _ ?_
    (Presheaf.imageSieve_mem X.smallEtaleTopology S.toCycles.hom k)
  rintro V g ⟨b, hb⟩
  let φ := (Etale.freeSheaf Λ X).map g
  let A' := (Etale.freeSheaf Λ X).obj V
  let b' := (Etale.freeSheafHomEquiv Λ V (M.obj.X (-1))).symm b
  have hφz : φ ≫ z = b' ≫ M.obj.toCycles (-1) 0 := by
    apply (Etale.freeSheafHomEquiv Λ V _).injective
    have hz' : z = k' ≫ S.iCycles := (S.liftCycles_i z hz).symm
    rw [hz', Etale.freeSheafHomEquiv_map, Etale.freeSheafHomEquiv_comp,
      Etale.freeSheafHomEquiv_comp, Equiv.apply_symm_apply]
    erw [← NatTrans.naturality_apply S.iCycles.hom g.op k, ← hb,
      ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, S.toCycles_i]
  let f' := (HomologicalComplex.single _ (.up ℤ) 0).map φ ≫ f
  have hf'z : DerivedCategory.singleCyclesHom A' ≫ HomologicalComplex.cyclesMap f' 0 =
      b' ≫ M.obj.toCycles (-1) 0 := by
    rw [HomologicalComplex.cyclesMap_comp, ← Category.assoc,
      DerivedCategory.singleCyclesHom_naturality, Category.assoc]
    exact hφz
  let τ' := DerivedCategory.singleCyclesHom A' ≫
    (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A').hom
  have hτ' : DerivedCategory.singleCyclesHom A' ≫
      ((HomologicalComplex.single _ (.up ℤ) 0).obj A').iCycles 0 =
        τ' ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A').inv := by
    simp [τ', HomologicalComplex.singleObjCyclesSelfIso_hom]
  have hf'0 : f'.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A').hom ≫
      (inv τ' ≫ b') ≫ M.obj.d (-1) 0 := by
    have h := hf'z =≫ M.obj.iCycles 0
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, Category.assoc,
      HomologicalComplex.toCycles_i, ← Category.assoc, hτ', Category.assoc] at h
    simp only [Category.assoc]
    rw [← h]
    simp
  have hβ' : DerivedCategory.Plus.ι.map
      ((DerivedCategory.Plus.singleFunctor _ 0).map φ ≫ β) =
        DerivedCategory.Q.map f' ≫ (DerivedCategory.quotientCompQhIso _).inv.app M.obj := by
    rw [Functor.map_comp, hf, Functor.map_comp, Category.assoc]
    rfl
  have h0 := DerivedCategory.Plus.eq_zero_of_homotopy _ f' hβ'
    (Etale.homotopyOfSingle M f' (inv τ' ≫ b') hf'0)
  simp only [Presheaf.equalizerSieve_apply, map_zero, map_sub]
  have h0' : (ConcreteCategory.hom (((Etale.freeSheaf Λ X ⋙
      DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj (DerivedCategory.Plus.Q.obj M)).map g.op)) (x - y) = 0 := h0
  rw [map_sub] at h0'
  exact h0'

end Key

end AlgebraicGeometry
