/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.WeaklyContractible

/-!
# Products of pro-étale sheaves are exact

The topos of pro-étale sheaves on a scheme has enough weakly contractible objects
(`WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.WeaklyContractible`). Hence products
of epimorphisms of abelian pro-étale sheaves are epimorphisms
(`AlgebraicGeometry.Scheme.ProEt.epi_piMap`; BS, Proposition 3.1.9): sections over weakly
contractible objects detect epimorphisms, and on them epimorphisms are surjective.

Ported from the `proetale` package (`Proetale.Topology.Comparison.RepleteExact`).
-/

@[expose] public section

universe w w' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}}

/-- Limits of shape `ℕᵒᵖ` of abelian pro-étale sheaves. Registered explicitly: typeclass
search for limit shapes in sheaf categories is prohibitively slow. -/
instance : HasLimitsOfShape ℕᵒᵖ (Sheaf (ProEt.topology S) Ab.{u + 1}) :=
  Sheaf.instHasLimitsOfShape

/-- Products indexed by a small type of abelian pro-étale sheaves, registered
explicitly. -/
instance (ι : Type w) [Small.{u + 1} ι] :
    HasLimitsOfShape (Discrete ι) (Sheaf (ProEt.topology S) Ab.{u + 1}) :=
  hasLimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink ι)).symm

/-- Products indexed by a small type of abelian groups, registered explicitly. -/
instance (ι : Type w) [Small.{u + 1} ι] :
    HasLimitsOfShape (Discrete ι) Ab.{u + 1} :=
  hasLimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink ι)).symm

section Ab

/-! ### Elementary statements for abelian groups -/

/-- Subtraction of morphisms of abelian groups acts pointwise. -/
private lemma _root_.AddCommGrpCat.hom_sub_apply' {M N : AddCommGrpCat.{w}}
    (f g : M ⟶ N) (x : ToType M) :
    ConcreteCategory.hom (f - g) x =
      ConcreteCategory.hom f x - ConcreteCategory.hom g x :=
  rfl

/-- The zero morphism of abelian groups acts as zero. -/
private lemma _root_.AddCommGrpCat.hom_zero_apply' {M N : AddCommGrpCat.{w}}
    (x : ToType M) : ConcreteCategory.hom (0 : M ⟶ N) x = 0 :=
  rfl

/-- An element of a limit of abelian groups over a discrete diagram is determined by, and
can be assembled from, its components. -/
private lemma _root_.AddCommGrpCat.bijective_components_of_isLimit
    {ι : Type w} [Small.{w'} ι] {X : Discrete ι ⥤ AddCommGrpCat.{w'}} {c : Cone X}
    (hc : IsLimit c) :
    Function.Bijective (fun (t : ToType c.pt) (i : ι) ↦
      ConcreteCategory.hom (c.π.app ⟨i⟩) t) := by
  have hT : IsLimit ((CategoryTheory.forget AddCommGrpCat.{w'}).mapCone c) :=
    isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{w'}) hc
  -- Extracting the components of a section of the discrete diagram is bijective.
  have hsec : Function.Bijective
      (fun (s : (X ⋙ CategoryTheory.forget AddCommGrpCat.{w'}).sections) (i : ι) ↦ s.1 ⟨i⟩) := by
    constructor
    · intro s₁ s₂ h
      apply Subtype.ext
      funext k
      exact congrFun h k.as
    · intro g
      refine ⟨⟨fun k ↦ g k.as, ?_⟩, rfl⟩
      intro k k' f
      obtain ⟨i⟩ := k
      obtain ⟨j⟩ := k'
      obtain rfl : i = j := Discrete.eq_of_hom f
      have hf : (X ⋙ CategoryTheory.forget AddCommGrpCat.{w'}).map f = 𝟙 _ :=
        Discrete.functor_map_id _ f
      rw [hf]
      exact ConcreteCategory.id_apply _
  have key : (fun (t : ToType c.pt) (i : ι) ↦ ConcreteCategory.hom (c.π.app ⟨i⟩) t) =
      (fun (s : (X ⋙ CategoryTheory.forget AddCommGrpCat.{w'}).sections) (i : ι) ↦ s.1 ⟨i⟩) ∘
        (Types.isLimitEquivSections hT) := by
    funext t i
    exact (Types.isLimitEquivSections_apply hT ⟨i⟩ t).symm
  rw [key]
  exact hsec.comp (Types.isLimitEquivSections hT).bijective

end Ab

section Sheaf

variable (F G : Sheaf (ProEt.topology S) Ab.{u + 1})

/-- The sections functor of abelian pro-étale sheaves over (the image in the pro-étale
site of) an object of the affine pro-étale site. -/
private def secW (W : S.AffineProEt) :
    Sheaf (ProEt.topology S) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  sheafToPresheaf _ _ ⋙
    (CategoryTheory.evaluation (S.ProEt)ᵒᵖ Ab.{u + 1}).obj
      (op ((AffineProEt.toProEt S).obj W))

/-- The sections functor preserves all limits that exist in `Ab`: the forgetful functor
to presheaves creates them and evaluation preserves them. -/
private instance (W : S.AffineProEt) {J : Type w} [Category.{w'} J]
    [HasLimitsOfShape J Ab.{u + 1}] : PreservesLimitsOfShape J (secW W) :=
  inferInstanceAs (PreservesLimitsOfShape J (_ ⋙ _))

/-- The sections functor is additive: addition of morphisms of sheaves is sectionwise. -/
private instance (W : S.AffineProEt) : (secW W).Additive where
  map_add := rfl

/-- Products of epimorphisms of abelian pro-étale sheaves are epimorphisms
(BS, Proposition 3.1.9; the topos of pro-étale sheaves satisfies AB4*). -/
theorem epi_piMap {ι : Type w} [Small.{u + 1} ι]
    (A B : ι → Sheaf (ProEt.topology S) Ab.{u + 1}) (φ : ∀ i, A i ⟶ B i)
    [∀ i, Epi (φ i)] : Epi (Limits.Pi.map φ) := by
  -- By `AffineProEt.epi_of_forall_surjective_app` it suffices to prove surjectivity on
  -- sections over weakly contractible `W`. The sections functor `secW W` preserves
  -- limits, so `secW W (∏ᶜ A) ≅ ∏ (secW W (A i))` compatibly with `Pi.map φ` and the
  -- function-product map; each `secW W (φ i)` is surjective by
  -- `AffineProEt.surjective_app_of_epi`, and products of surjective maps of types are
  -- surjective.
  refine AffineProEt.epi_of_forall_surjective_app _ fun W hW ↦ ?_
  have hA : IsLimit ((secW W).mapCone (limit.cone (Discrete.functor A))) :=
    isLimitOfPreserves (secW W) (limit.isLimit (Discrete.functor A))
  have hB : IsLimit ((secW W).mapCone (limit.cone (Discrete.functor B))) :=
    isLimitOfPreserves (secW W) (limit.isLimit (Discrete.functor B))
  have hbijA := AddCommGrpCat.bijective_components_of_isLimit hA
  have hbijB := AddCommGrpCat.bijective_components_of_isLimit hB
  intro t
  -- Lift the components of `t` along the levelwise surjections.
  have hsec : ∀ i, ∃ u, ConcreteCategory.hom
      ((φ i).hom.app (op ((AffineProEt.toProEt S).obj W))) u =
      ConcreteCategory.hom ((secW W).map (Pi.π B i)) t :=
    fun i ↦ AffineProEt.surjective_app_of_epi (φ i) hW _
  choose u hu using hsec
  -- Reassemble the lifts into a section of the product.
  obtain ⟨s, hs⟩ := hbijA.2 u
  have hsi : ∀ i, ConcreteCategory.hom ((secW W).map (Pi.π A i)) s = u i :=
    fun i ↦ congrFun hs i
  refine ⟨s, hbijB.1 ?_⟩
  funext i
  have e1 : (secW W).map (Limits.Pi.map φ) ≫ (secW W).map (Pi.π B i) =
      (secW W).map (Pi.π A i) ≫ (secW W).map (φ i) := by
    rw [← Functor.map_comp, ← Functor.map_comp, Limits.Pi.map_π]
  calc ConcreteCategory.hom ((secW W).map (Pi.π B i))
        (ConcreteCategory.hom ((secW W).map (Limits.Pi.map φ)) s)
      = ConcreteCategory.hom ((secW W).map (Limits.Pi.map φ) ≫ (secW W).map (Pi.π B i))
          s := (ConcreteCategory.comp_apply _ _ _).symm
    _ = ConcreteCategory.hom ((secW W).map (Pi.π A i) ≫ (secW W).map (φ i)) s :=
        ConcreteCategory.congr_hom e1 s
    _ = ConcreteCategory.hom ((secW W).map (φ i))
          (ConcreteCategory.hom ((secW W).map (Pi.π A i)) s) :=
        ConcreteCategory.comp_apply _ _ _
    _ = ConcreteCategory.hom ((secW W).map (φ i)) (u i) := by rw [hsi i]
    _ = ConcreteCategory.hom ((secW W).map (Pi.π B i)) t := hu i

/-- Products of abelian pro-étale sheaves are exact (AB4*). -/
instance hasExactLimitsOfShape_discrete (ι : Type w) [Small.{u + 1} ι] :
    HasExactLimitsOfShape (Discrete ι) (Sheaf (ProEt.topology S) Ab.{u + 1}) := by
  apply +allowSynthFailures hasExactLimitsOfShape_of_preservesEpi
  refine ⟨fun {X Y} f hf ↦ ?_⟩
  have : ∀ i, Epi (f.app ⟨i⟩) := fun i ↦ (NatTrans.epi_iff_epi_app f).1 hf ⟨i⟩
  let eX : limit X ≅ ∏ᶜ fun i ↦ X.obj ⟨i⟩ := HasLimit.isoOfNatIso Discrete.natIsoFunctor
  let eY : limit Y ≅ ∏ᶜ fun i ↦ Y.obj ⟨i⟩ := HasLimit.isoOfNatIso Discrete.natIsoFunctor
  have hπ : eX.inv ≫ lim.map f ≫ eY.hom = Limits.Pi.map fun i ↦ f.app ⟨i⟩ := by
    refine Pi.hom_ext _ _ fun i ↦ ?_
    simp [eX, eY, Pi.π]
  have : Epi (Limits.Pi.map fun i ↦ f.app ⟨i⟩) :=
    epi_piMap (fun i ↦ X.obj ⟨i⟩) (fun i ↦ Y.obj ⟨i⟩) _
  rw [← hπ] at this
  have h : lim.map f = eX.hom ≫ (eX.inv ≫ lim.map f ≫ eY.hom) ≫ eY.inv := by simp
  rw [h]
  infer_instance

section Module

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Products indexed by a small type of pro-étale sheaves of modules, registered explicitly. -/
instance (ι : Type w) [Small.{u + 1} ι] :
    HasLimitsOfShape (Discrete ι) (Sheaf (ProEt.topology S) (ModuleCat.{u + 1} Λ)) :=
  hasLimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink ι)).symm

/-- Composing with the forgetful functor to abelian groups preserves products of pro-étale
sheaves of modules, since limits of sheaves are computed on presheaves. -/
instance (ι : Type w) [Small.{u + 1} ι] :
    PreservesLimitsOfShape (Discrete ι)
      (sheafCompose (ProEt.topology S) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})) := by
  suffices PreservesLimitsOfShape (Discrete (Shrink.{u + 1} ι))
      (sheafCompose (ProEt.topology S) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})) from
    preservesLimitsOfShape_of_equiv (Discrete.equivalence (equivShrink ι)).symm _
  have : PreservesLimitsOfShape (Discrete (Shrink.{u + 1} ι))
      (sheafCompose (ProEt.topology S) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) ⋙
        sheafToPresheaf (ProEt.topology S) Ab.{u + 1}) :=
    preservesLimitsOfShape_of_natIso (F := sheafToPresheaf (ProEt.topology S) _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}))
      (Iso.refl _)
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (ProEt.topology S) Ab.{u + 1})

/-- A morphism of pro-étale sheaves of `Λ`-modules is an epimorphism if and only if it is one
as a morphism of abelian sheaves: both mean local surjectivity. -/
lemma epi_iff_epi_sheafCompose_forget₂ {F G : Sheaf (ProEt.topology S) (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) :
    Epi φ ↔ Epi ((sheafCompose (ProEt.topology S)
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).map φ) := by
  rw [← Sheaf.isLocallySurjective_iff_epi', ← Sheaf.isLocallySurjective_iff_epi']
  exact ⟨fun h ↦ ⟨h.imageSieve_mem⟩, fun h ↦ ⟨h.imageSieve_mem⟩⟩

/-- Products of epimorphisms of pro-étale sheaves of `Λ`-modules are epimorphisms. -/
theorem epi_piMap_moduleCat {ι : Type w} [Small.{u + 1} ι]
    (A B : ι → Sheaf (ProEt.topology S) (ModuleCat.{u + 1} Λ)) (φ : ∀ i, A i ⟶ B i)
    [∀ i, Epi (φ i)] : Epi (Limits.Pi.map φ) := by
  let Φ := sheafCompose (ProEt.topology S) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})
  rw [epi_iff_epi_sheafCompose_forget₂]
  have : ∀ i, Epi (Φ.map (φ i)) := fun i ↦
    (epi_iff_epi_sheafCompose_forget₂ Λ (φ i)).1 inferInstance
  have hepi := epi_piMap (fun i ↦ Φ.obj (A i)) (fun i ↦ Φ.obj (B i)) fun i ↦ Φ.map (φ i)
  have hcomm : Φ.map (Limits.Pi.map φ) ≫ piComparison Φ B =
      piComparison Φ A ≫ Limits.Pi.map fun i ↦ Φ.map (φ i) :=
    Pi.hom_ext _ _ fun i ↦ by
      simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π,
        piComparison_comp_π_assoc, ← Functor.map_comp]
  have : Epi (Φ.map (Limits.Pi.map φ) ≫ piComparison Φ B) := by
    rw [hcomm]
    infer_instance
  have h : Φ.map (Limits.Pi.map φ) =
      (Φ.map (Limits.Pi.map φ) ≫ piComparison Φ B) ≫ inv (piComparison Φ B) := by simp
  rw [h]
  infer_instance

/-- Products of pro-étale sheaves of `Λ`-modules are exact (AB4*). -/
instance hasExactLimitsOfShape_discrete_moduleCat (ι : Type w) [Small.{u + 1} ι] :
    HasExactLimitsOfShape (Discrete ι) (Sheaf (ProEt.topology S) (ModuleCat.{u + 1} Λ)) := by
  apply +allowSynthFailures hasExactLimitsOfShape_of_preservesEpi
  refine ⟨fun {X Y} f hf ↦ ?_⟩
  have : ∀ i, Epi (f.app ⟨i⟩) := fun i ↦ (NatTrans.epi_iff_epi_app f).1 hf ⟨i⟩
  let eX : limit X ≅ ∏ᶜ fun i ↦ X.obj ⟨i⟩ := HasLimit.isoOfNatIso Discrete.natIsoFunctor
  let eY : limit Y ≅ ∏ᶜ fun i ↦ Y.obj ⟨i⟩ := HasLimit.isoOfNatIso Discrete.natIsoFunctor
  have hπ : eX.inv ≫ lim.map f ≫ eY.hom = Limits.Pi.map fun i ↦ f.app ⟨i⟩ := by
    refine Pi.hom_ext _ _ fun i ↦ ?_
    simp [eX, eY, Pi.π]
  have : Epi (Limits.Pi.map fun i ↦ f.app ⟨i⟩) :=
    epi_piMap_moduleCat Λ (fun i ↦ X.obj ⟨i⟩) (fun i ↦ Y.obj ⟨i⟩) _
  rw [← hπ] at this
  have h : lim.map f = eX.hom ≫ (eX.inv ≫ lim.map f ≫ eY.hom) ≫ eY.inv := by simp
  rw [h]
  infer_instance

end Module

end Sheaf

end AlgebraicGeometry.Scheme.ProEt
