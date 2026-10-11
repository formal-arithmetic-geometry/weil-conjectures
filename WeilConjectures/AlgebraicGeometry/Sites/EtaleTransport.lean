/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Transport of étale cohomology along an isomorphism of schemes

-/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category.{v} C] {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
  {T : C} (hT : IsTerminal T)

/-- Morphisms out of the constant sheaf `ℤ` are global sections: the value at `1` over the
terminal object. -/
noncomputable def constantHomEquiv (F : Sheaf J AddCommGrpCat.{u}) :
    ((constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) ≃
      F.obj.obj (op T) :=
  ((constantSheafAdj J AddCommGrpCat.{u} hT).homEquiv _ F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv

lemma constantHomEquiv_comp {F G : Sheaf J AddCommGrpCat.{u}}
    (f : (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F)
    (g : F ⟶ G) :
    constantHomEquiv hT G (f ≫ g) = g.hom.app (op T) (constantHomEquiv hT F f) := by
  simp only [constantHomEquiv, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe,
    Adjunction.homEquiv_naturality_right]
  rfl

lemma constantHomEquiv_naturality {F : Sheaf J AddCommGrpCat.{u}}
    (f : (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) {W : C}
    (ρ : W ⟶ T) :
    f.hom.app (op W) (((constantSheaf J AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))).obj.map ρ.op
          (constantHomEquiv hT _ (𝟙 _))) =
      F.obj.map ρ.op (constantHomEquiv hT F f) := by
  rw [← ConcreteCategory.comp_apply, f.hom.naturality, ConcreteCategory.comp_apply,
    ← constantHomEquiv_comp, Category.id_comp]

lemma H.equiv₀_eq_constantHomEquiv (F : Sheaf J AddCommGrpCat.{u}) [HasExt.{u} (Sheaf J
    AddCommGrpCat.{u})] (x : H F 0) :
    H.equiv₀ F hT x = constantHomEquiv hT F (Ext.addEquiv₀ x) :=
  rfl

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (e : X ≅ Y)

/-- The terminal object `𝟙 : X ⟶ X` of the small étale site. -/
noncomputable abbrev etaleTerminal (X : Scheme.{u}) : X.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)

/-- `𝟙 : X ⟶ X` is terminal in the small étale site. -/
noncomputable def isTerminalEtaleTerminal (X : Scheme.{u}) : IsTerminal (etaleTerminal X) :=
  MorphismProperty.Over.mkIdTerminal @Etale X

/-- The pushforward of abelian étale sheaves along an isomorphism `e : X ≅ Y`. It is an
equivalence, so it is exact and identifies the étale cohomology of `X` and of `Y`. -/
noncomputable abbrev etaleTransport :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Etale.lowerStar AddCommGrpCat.{u + 1} e.hom

/-- The base change `Y ×_Y X` of the terminal object along `e`. -/
noncomputable abbrev etaleTransportTerminal : X.Etale :=
  (MorphismProperty.Over.pullback @Etale ⊤ e.hom).obj (etaleTerminal Y)

/-- The base change of the terminal object of `Y.Etale` along `e` is terminal: the
isomorphism `Y ×_Y X ≅ X`. -/
noncomputable def etaleTransportTerminalIso : etaleTransportTerminal e ≅ etaleTerminal X :=
  MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 Y) e.hom)) (by simp)

lemma bijective_map_etaleTransportTerminalIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (F.obj.map (etaleTransportTerminalIso e).hom.op) :=
  ConcreteCategory.bijective_of_isIso _

/-- The global section `1` of the constant sheaf `ℤ` on `X`, viewed as a global section of its
pushforward along `e`. -/
noncomputable def etaleTransportOne :
    ((etaleTransport e).obj ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)))).obj.obj (op (etaleTerminal Y)) :=
  ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ))).obj.map (etaleTransportTerminalIso e).hom.op
    (Sheaf.constantHomEquiv (isTerminalEtaleTerminal X) _ (𝟙 _))

/-- The map `ℤ_Y ⟶ e_* ℤ_X` sending `1` to `1`. -/
noncomputable def constantSheafToEtaleTransport :
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶
      (etaleTransport e).obj ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) :=
  (Sheaf.constantHomEquiv (isTerminalEtaleTerminal Y) _).symm (etaleTransportOne e)

lemma constantHomEquiv_constantSheafToEtaleTransport_comp
    {F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : (etaleTransport e).obj ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) ⟶ F) :
    Sheaf.constantHomEquiv (isTerminalEtaleTerminal Y) F
        (constantSheafToEtaleTransport e ≫ f) =
      f.hom.app (op (etaleTerminal Y)) (etaleTransportOne e) := by
  rw [Sheaf.constantHomEquiv_comp, constantSheafToEtaleTransport, Equiv.apply_symm_apply]

lemma bijective_app_etaleTransportOne (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (fun f : (etaleTransport e).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift ℤ))) ⟶ (etaleTransport e).obj F ↦
      f.hom.app (op (etaleTerminal Y)) (etaleTransportOne e)) := by
  have h : (fun f : (etaleTransport e).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift ℤ))) ⟶ (etaleTransport e).obj F ↦
      f.hom.app (op (etaleTerminal Y)) (etaleTransportOne e)) =
      (F.obj.map (etaleTransportTerminalIso e).hom.op ∘
        Sheaf.constantHomEquiv (isTerminalEtaleTerminal X) F) ∘
        (Functor.FullyFaithful.ofFullyFaithful (etaleTransport e)).homEquiv.symm := by
    funext f
    obtain ⟨g, rfl⟩ := (Functor.FullyFaithful.ofFullyFaithful (etaleTransport e)).map_surjective f
    simp only [Function.comp_apply, Functor.FullyFaithful.homEquiv_symm_apply,
      Functor.FullyFaithful.preimage_map]
    exact Sheaf.constantHomEquiv_naturality _ g _
  rw [h]
  exact ((ConcreteCategory.bijective_of_isIso _).comp (Equiv.bijective _)).comp
    (Equiv.bijective _)

instance isIso_constantSheafToEtaleTransport : IsIso (constantSheafToEtaleTransport e) := by
  refine isIso_of_coyoneda_map_bijective _ fun F ↦ ?_
  let F' := (etaleTransport e).objPreimage F
  let i : (etaleTransport e).obj F' ≅ F := (etaleTransport e).objObjPreimageIso F
  have h : (fun f ↦ constantSheafToEtaleTransport e ≫ f) =
      (Sheaf.constantHomEquiv (isTerminalEtaleTerminal Y) F).symm ∘
        (i.hom.hom.app (op (etaleTerminal Y))) ∘
        (fun f ↦ f.hom.app (op (etaleTerminal Y)) (etaleTransportOne e)) ∘
        (fun f ↦ f ≫ i.inv) := by
    funext f
    simp only [Function.comp_apply]
    rw [Equiv.eq_symm_apply, constantHomEquiv_constantSheafToEtaleTransport_comp]
    change _ = (f ≫ i.inv ≫ i.hom).hom.app _ _
    rw [Iso.inv_hom_id, Category.comp_id]
  rw [h]
  refine (Equiv.bijective _).comp ((ConcreteCategory.bijective_of_isIso _).comp
    ((bijective_app_etaleTransportOne e F').comp ?_))
  exact ⟨fun f g hfg ↦ by simpa using hfg =≫ i.hom, fun g ↦ ⟨g ≫ i.hom, by simp⟩⟩

/-- The isomorphism `ℤ_Y ≅ e_* ℤ_X` of constant sheaves, sending `1` to `1`. -/
noncomputable def constantSheafEtaleTransportIso :
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ)) ≅
      (etaleTransport e).obj ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) :=
  asIso (constantSheafToEtaleTransport e)

/-- **Transport of étale cohomology along an isomorphism of schemes** `e : X ≅ Y`:
`H^n(X, F) ≃ H^n(Y, e_* F)`. -/
noncomputable def etaleTransportCohomology (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) : Sheaf.H F n ≃+ Sheaf.H ((etaleTransport e).obj F) n :=
  AddEquiv.ofBijective (Sheaf.H.mapFunctor _ (constantSheafEtaleTransportIso e) F n)
    (Sheaf.H.mapFunctor_bijective _ _ F n)

lemma etaleTransportCohomology_apply (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) (x : Sheaf.H F n) :
    etaleTransportCohomology e F n x =
      (Ext.mk₀ (constantSheafToEtaleTransport e)).comp (x.mapExactFunctor (etaleTransport e))
        (zero_add n) :=
  rfl

/-- The transport of cohomology is natural in the sheaf. -/
lemma etaleTransportCohomology_map {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : F ⟶ G) (n : ℕ) (x : Sheaf.H F n) :
    etaleTransportCohomology e G n (Sheaf.H.map φ n x) =
      Sheaf.H.map ((etaleTransport e).map φ) n (etaleTransportCohomology e F n x) :=
  Sheaf.H.mapFunctor_map _ _ _ φ x

/-- In degree `0`, the transport of cohomology is the restriction of global sections along
`Y ×_Y X ≅ X`. -/
lemma equiv₀_etaleTransportCohomology (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : Sheaf.H F 0) :
    Sheaf.H.equiv₀ _ (isTerminalEtaleTerminal Y) (etaleTransportCohomology e F 0 x) =
      F.obj.map (etaleTransportTerminalIso e).hom.op
        (Sheaf.H.equiv₀ F (isTerminalEtaleTerminal X) x) := by
  obtain ⟨f, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  rw [etaleTransportCohomology_apply, Ext.addEquiv₀_symm_apply, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀, Sheaf.H.equiv₀_eq_constantHomEquiv, Sheaf.H.equiv₀_eq_constantHomEquiv,
    Ext.addEquiv₀_symm_apply]
  sorry

end AlgebraicGeometry.Scheme
