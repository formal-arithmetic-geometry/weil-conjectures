/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs

/-!
# The unit on the pro-étale site of a w-contractible affine scheme

Let `Y ≅ Spec R` with `R` a w-contractible ring, and let `Λ` be a commutative ring. On the small
pro-étale site of `Y`, the terminal object `Y` is weakly contractible, and every covering sieve of
it is refined by a finite cover by pairwise disjoint monomorphisms
(`AlgebraicGeometry.Scheme.ProEt.exists_finite_disjoint_cover_of_iso`). We deduce that the unit
`Λ_Y` of the category of sheaves of `Λ`-modules is projective, and that morphisms out of it are
finite on coproducts and on tensor products
(`CategoryTheory.UnitFactorsThroughFiniteCoproducts`, `CategoryTheory.UnitTensorFinite`), so that
dualizable objects of `D(Y_proét, Λ)` are bounded complexes of finite projective
`Λ_Y`-modules (`DerivedCategory.exists_iso_Q_obj_of_isDualizable`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

namespace Scheme.ProEt

variable (Y : Scheme.{u})

/-- The terminal object `Y` of the small pro-étale site of `Y`. -/
noncomputable abbrev terminal : Y.ProEt := ProEt.mk (𝟙 Y)

variable {Y}

/-- The morphism from an object of the small pro-étale site of `Y` to the terminal object. -/
noncomputable def toTerminal (V : Y.ProEt) : V ⟶ terminal Y :=
  MorphismProperty.Over.homMk V.hom (Category.comp_id _)

noncomputable instance (V : Y.ProEt) : Unique (V ⟶ terminal Y) where
  default := toTerminal V
  uniq a := MorphismProperty.Over.Hom.ext ((Category.comp_id _).symm.trans (MorphismProperty.Over.w a))

end Scheme.ProEt

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] (Y : Scheme.{u})

/-- The constant presheaf `Λ` is the free presheaf on the terminal object. -/
noncomputable def unitPresheafIso :
    𝟙_ (Y.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ) ≅
      uliftYoneda.{u + 1}.obj (Scheme.ProEt.terminal Y) ⋙ ModuleCat.free Λ :=
  (NatIso.ofComponents (fun V ↦ (LinearEquiv.toModuleIso
      (Finsupp.uniqueLinearEquiv Λ Λ (⟨Scheme.ProEt.toTerminal V.unop⟩ :
        ULift.{u + 1} (V.unop ⟶ Scheme.ProEt.terminal Y)))))
    (fun {V V'} g ↦ by
      ext x
      revert x
      intro (x : ULift.{u + 1} (V.unop ⟶ Scheme.ProEt.terminal Y) →₀ Λ)
      change (Finsupp.mapDomain _ x) _ = x _
      rw [← Finsupp.mapDomain_apply (f := (uliftYoneda.{u + 1}.obj (Scheme.ProEt.terminal Y)).map g)
        (fun a b _ ↦ ULift.ext _ _ (Subsingleton.elim (α := _ ⟶ Scheme.ProEt.terminal Y) _ _)) x ⟨Scheme.ProEt.toTerminal V.unop⟩]
      congr 1
      exact ULift.ext _ _ (Subsingleton.elim (α := _ ⟶ Scheme.ProEt.terminal Y) _ _))).symm

/-- The unit `Λ_Y` of sheaves of `Λ`-modules on `Y_proét` is the free sheaf on the terminal
object. -/
noncomputable def unitIsoFreeSheaf :
    𝟙_ (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ≅
      (freeSheaf Λ Y).obj (Scheme.ProEt.terminal Y) :=
  Functor.Monoidal.εIso (presheafToSheaf _ _) ≪≫ (presheafToSheaf _ _).mapIso (unitPresheafIso Λ Y)

variable {Λ Y}

/-- Morphisms out of the unit `Λ_Y` are sections over the terminal object `Y`. -/
noncomputable def unitHomEquiv (F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) :
    (𝟙_ _ ⟶ F) ≃ F.obj.obj (op (Scheme.ProEt.terminal Y)) :=
  ((unitIsoFreeSheaf Λ Y).homCongr (Iso.refl F)).trans (freeSheafHomEquiv Λ _ F)

lemma unitHomEquiv_comp {F G : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)}
    (x : 𝟙_ _ ⟶ F) (g : F ⟶ G) :
    unitHomEquiv G (x ≫ g) = g.hom.app _ (unitHomEquiv F x) := by
  simp [unitHomEquiv, Iso.homCongr_apply, freeSheafHomEquiv_comp]

lemma unitHomEquiv_apply {F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)}
    (x : 𝟙_ _ ⟶ F) : unitHomEquiv F x = x.hom.app _ (unitHomEquiv _ (𝟙 _)) := by
  rw [← unitHomEquiv_comp, Category.id_comp]

lemma unitHomEquiv_add {F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)}
    (x y : 𝟙_ _ ⟶ F) : unitHomEquiv F (x + y) = unitHomEquiv F x + unitHomEquiv F y := by
  rw [unitHomEquiv_apply, unitHomEquiv_apply x, unitHomEquiv_apply y]
  rfl

lemma unitHomEquiv_sum {F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)}
    {ι : Type*} (S : Finset ι) (x : ι → (𝟙_ _ ⟶ F)) :
    unitHomEquiv F (∑ i ∈ S, x i) = ∑ i ∈ S, unitHomEquiv F (x i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, unitHomEquiv_apply]
    rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, unitHomEquiv_add, ih]

/-- On the pro-étale site of the spectrum of a w-contractible ring, the unit `Λ_Y` is projective:
it is the free sheaf on the weakly contractible terminal object. -/
lemma projective_unit {R : CommRingCat.{u}} [IsWContractibleRing R] (e : Y ≅ Spec R) :
    Projective (𝟙_ (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :=
  Projective.of_iso (unitIsoFreeSheaf Λ Y).symm (projective_freeSheaf Λ _
    (Scheme.ProEt.isWeaklyContractible_of_iso (W := Scheme.ProEt.terminal Y) e))

/-- On the pro-étale site of the spectrum of a w-contractible ring, a section over the terminal
object of a sheaf `G` receiving a locally surjective map `φ : P ⟶ G` comes from sections of `P`
over the members of a finite cover of `Y` by pairwise disjoint monomorphisms. -/
lemma exists_finite_disjoint_preimage {R : CommRingCat.{u}} [IsWContractibleRing R]
    (e : Y ≅ Spec R) {P : Y.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ}
    {G : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)} (φ : P ⟶ G.obj)
    [Presheaf.IsLocallySurjective (Scheme.ProEt.topology Y) φ]
    (x : G.obj.obj (op (Scheme.ProEt.terminal Y))) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → Y.ProEt) (f : ∀ i, V i ⟶ Scheme.ProEt.terminal Y),
      Sieve.ofArrows V f ∈ Scheme.ProEt.topology Y _ ∧ (∀ i, Mono (f i)) ∧
      (∀ i j, i ≠ j → ∀ (Z : Y.ProEt) (a : Z ⟶ V i) (b : Z ⟶ V j), a ≫ f i = b ≫ f j →
        ⊥ ∈ Scheme.ProEt.topology Y Z) ∧
      ∃ p : ∀ i, P.obj (op (V i)), ∀ i, φ.app _ (p i) = G.obj.map (f i).op x := by
  obtain ⟨ι, _, V, f, hcov, hS, hmono, hdisj⟩ :=
    Scheme.ProEt.exists_finite_disjoint_cover_of_iso (W := Scheme.ProEt.terminal Y) e
      (Presheaf.imageSieve_mem (Scheme.ProEt.topology Y) φ x)
  choose p hp using hS
  exact ⟨ι, inferInstance, V, f, hcov, hmono, hdisj, p, hp⟩

/-- Sections of a sheaf over the members of a cover by pairwise disjoint monomorphisms glue. -/
lemma exists_glue_of_disjoint {W : Y.ProEt}
    (F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) {ι : Type u}
    {V : ι → Y.ProEt} (f : ∀ i, V i ⟶ W) (hcov : Sieve.ofArrows V f ∈ Scheme.ProEt.topology Y W)
    (hmono : ∀ i, Mono (f i))
    (hdisj : ∀ i j, i ≠ j → ∀ (Z : Y.ProEt) (a : Z ⟶ V i) (b : Z ⟶ V j), a ≫ f i = b ≫ f j →
        ⊥ ∈ Scheme.ProEt.topology Y Z)
    (a : ∀ i, F.obj.obj (op (V i))) :
    ∃ a' : F.obj.obj (op W), ∀ i, F.obj.map (f i).op a' = a i := by
  have hF := ((isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose _ (forget (ModuleCat.{u + 1} Λ))).obj F).2).isSheafFor _ hcov
  rw [Presieve.isSheafFor_arrows_iff] at hF
  obtain ⟨x, hx, -⟩ := hF (fun i ↦ a i) (by
    intro i j Z b c hbc
    by_cases hij : i = j
    · subst hij
      obtain rfl := (cancel_mono (f i)).1 hbc
      rfl
    · exact Sheaf.isSeparated F Z ⊥ (hdisj i j hij Z b c hbc) _ _ (by simp))
  exact ⟨x, hx⟩

/-- A section over `W` vanishes if its restrictions to the members of a cover vanish, and two
sections agree if their restrictions do. -/
lemma eq_of_restrict_eq {W : Y.ProEt}
    {F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)} {ι : Type u}
    {V : ι → Y.ProEt} (f : ∀ i, V i ⟶ W) (hcov : Sieve.ofArrows V f ∈ Scheme.ProEt.topology Y W)
    {x y : F.obj.obj (op W)} (h : ∀ i, F.obj.map (f i).op x = F.obj.map (f i).op y) : x = y := by
  refine Sheaf.isSeparated F W _ hcov x y ?_
  rintro Z g ⟨_, a, _, ⟨i⟩, rfl⟩
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, h i]

/-- A presheaf map `φ : P ⟶ G` to a sheaf is locally surjective as soon as its adjoint
`P^# ⟶ G` is an epimorphism of sheaves. -/
lemma isLocallySurjective_of_epi_homEquiv_symm {P : Y.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ}
    {G : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)} (φ : P ⟶ G.obj)
    (hφ : Epi (((sheafificationAdjunction _ _).homEquiv P G).symm φ)) :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology Y) φ := by
  have : Sheaf.IsLocallySurjective (((sheafificationAdjunction _ _).homEquiv P G).symm φ) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 hφ
  have h : φ = toSheafify _ P ≫ (((sheafificationAdjunction _ _).homEquiv P G).symm φ).hom := by
    conv_lhs => rw [← ((sheafificationAdjunction _ _).homEquiv P G).apply_symm_apply φ]
    rw [Adjunction.homEquiv_unit]
    rfl
  rw [h]
  infer_instance

/-- An element of the coproduct of presheaves of modules is a finite sum of elements of the
summands. -/
lemma exists_eq_sum_sigma_ι {K : Type} (P : K → (Y.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ))
    (V : Y.ProEtᵒᵖ) (y : (∐ P).obj V) :
    ∃ (S : Finset K) (m : ∀ j, (P j).obj V), y = ∑ j ∈ S, (Sigma.ι P j).app V (m j) := by
  classical
  let N : Submodule Λ ((∐ P).obj V) := ⨆ j, LinearMap.range ((Sigma.ι P j).app V).hom
  have hN : N = ⊤ := by
    let q : (∐ P).obj V ⟶ ModuleCat.of Λ (((∐ P).obj V) ⧸ N) := ModuleCat.ofHom N.mkQ
    have hq : q = 0 := by
      have hc := isColimitOfPreserves ((evaluation _ _).obj V)
        (colimit.isColimit (Discrete.functor P))
      refine hc.hom_ext fun ⟨j⟩ ↦ ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
      exact (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_iSup_of_mem j ⟨z, rfl⟩)
    rw [eq_top_iff]
    intro z _
    have : q z = 0 := by rw [hq]; rfl
    exact (Submodule.Quotient.mk_eq_zero N).1 this
  have hy : y ∈ N := hN ▸ Submodule.mem_top
  obtain ⟨c, hc, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hy
  choose m hm using hc
  exact ⟨c.support, m, Finset.sum_congr rfl fun j _ ↦ (hm j).symm⟩

/-- On the pro-étale site of the spectrum of a w-contractible ring, morphisms from the unit to a
coproduct of sheaves factor through finite subcoproducts. -/
theorem unitFactorsThroughFiniteCoproducts {R : CommRingCat.{u}} [IsWContractibleRing R]
    (e : Y ≅ Spec R) :
    UnitFactorsThroughFiniteCoproducts (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) := by
  classical
  intro K X _ x
  let adj := sheafificationAdjunction (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)
  let φ : (∐ fun j ↦ (X j).obj) ⟶ (∐ X).obj := Sigma.desc fun j ↦ (Sigma.ι X j).hom
  have hφ (j : K) : Sigma.ι (fun j ↦ (X j).obj) j ≫ φ = (Sigma.ι X j).hom := Sigma.ι_desc _ _
  have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology Y) φ := by
    refine isLocallySurjective_of_epi_homEquiv_symm φ ⟨fun {Z} a b hab ↦ Sigma.hom_ext _ _
      fun j ↦ ?_⟩
    have h1 : (presheafToSheaf _ _).map (Sigma.ι _ j) ≫ (adj.homEquiv _ _).symm φ =
        adj.counit.app (X j) ≫ Sigma.ι X j := by
      rw [← Adjunction.homEquiv_naturality_left_symm, hφ, Adjunction.homEquiv_counit]
      exact adj.counit.naturality (Sigma.ι X j)
    have := (presheafToSheaf _ _).map (Sigma.ι _ j) ≫= hab
    rw [reassoc_of% h1, reassoc_of% h1] at this
    exact (cancel_epi _).1 this
  obtain ⟨ι, _, V, f, hcov, hmono, hdisj, p, hp⟩ :=
    exists_finite_disjoint_preimage e φ (unitHomEquiv _ x)
  have := Fintype.ofFinite ι
  choose S m hm using fun i ↦ exists_eq_sum_sigma_ι (fun j ↦ (X j).obj) (op (V i)) (p i)
  choose m' hm' using fun j ↦ exists_glue_of_disjoint (X j) f hcov hmono hdisj
    (fun i ↦ if j ∈ S i then m i j else 0)
  refine ⟨Finset.univ.biUnion S, fun j ↦ (unitHomEquiv _).symm (m' j),
    (unitHomEquiv _).injective (eq_of_restrict_eq f hcov fun i ↦ ?_)⟩
  rw [unitHomEquiv_sum, map_sum, ← hp i, hm i, map_sum]
  simp only [unitHomEquiv_comp, Equiv.apply_symm_apply]
  have hS : S i ⊆ Finset.univ.biUnion S := Finset.subset_biUnion_of_mem S (Finset.mem_univ i)
  rw [← Finset.sum_subset hS (fun j _ hj ↦ ?_)]
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [← NatTrans.naturality_apply, hm' j i, if_pos hj, ← hφ j]
    rfl
  · rw [← NatTrans.naturality_apply, hm' j i, if_neg hj, map_zero]

end ProEtale

end AlgebraicGeometry
