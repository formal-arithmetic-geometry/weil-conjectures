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

open scoped TensorProduct

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

omit [CommRing Λ] in
/-- An element of a tensor product of modules is a finite sum of pure tensors. -/
lemma _root_.TensorProduct.exists_eq_sum_tmul' {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (z : M ⊗[R] N) :
    ∃ (n : ℕ) (a : Fin n → M) (b : Fin n → N), z = ∑ i, a i ⊗ₜ b i := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul x y => exact ⟨1, fun _ ↦ x, fun _ ↦ y, by simp⟩
  | add x y hx hy =>
    obtain ⟨n, a, b, rfl⟩ := hx
    obtain ⟨m, c, d, rfl⟩ := hy
    exact ⟨n + m, Fin.append a c, Fin.append b d, by simp [Fin.sum_univ_add]⟩

section Tensor

variable (F G : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))

/-- The canonical map from the objectwise tensor product of the underlying presheaves of two
sheaves to their tensor product as sheaves, the sheafification map. -/
noncomputable def tensorPresheafToSheaf : F.obj ⊗ G.obj ⟶ (F ⊗ G).obj :=
  toSheafify _ (F.obj ⊗ G.obj) ≫
    ((Functor.Monoidal.μIso (presheafToSheaf _ _) F.obj G.obj).inv ≫
      ((sheafificationAdjunction _ _).counit.app F ⊗ₘ
        (sheafificationAdjunction _ _).counit.app G)).hom

instance : Presheaf.IsLocallySurjective (Scheme.ProEt.topology Y) (tensorPresheafToSheaf F G) := by
  have : Sheaf.IsLocallySurjective ((Functor.Monoidal.μIso (presheafToSheaf _ _) F.obj G.obj).inv ≫
      ((sheafificationAdjunction _ _).counit.app F ⊗ₘ
        (sheafificationAdjunction _ _).counit.app G)) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  dsimp only [tensorPresheafToSheaf]
  infer_instance

variable {F G} in
lemma tensorHom_comp_tensorPresheafToSheaf {F' G' : Sheaf (Scheme.ProEt.topology Y)
    (ModuleCat.{u + 1} Λ)} (s : F ⟶ F') (t : G ⟶ G') :
    (s.hom ⊗ₘ t.hom) ≫ tensorPresheafToSheaf F' G' =
      tensorPresheafToSheaf F G ≫ (s ⊗ₘ t).hom := by
  let L := presheafToSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)
  let ε := (sheafificationAdjunction (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).counit
  have h : L.map (s.hom ⊗ₘ t.hom) ≫ (Functor.Monoidal.μIso L F'.obj G'.obj).inv ≫
      (ε.app F' ⊗ₘ ε.app G') =
      ((Functor.Monoidal.μIso L F.obj G.obj).inv ≫ (ε.app F ⊗ₘ ε.app G)) ≫ (s ⊗ₘ t) := by
    rw [Functor.Monoidal.map_tensor, Category.assoc, Category.assoc, Functor.Monoidal.μIso_inv,
      Functor.Monoidal.μ_δ_assoc, Category.assoc, Functor.Monoidal.μIso_inv,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    congr 2
    · exact ε.naturality s
    · exact ε.naturality t
  simp only [tensorPresheafToSheaf, ← Category.assoc, toSheafify_naturality]
  simp only [Category.assoc]
  exact congrArg (fun φ ↦ toSheafify _ (F.obj ⊗ G.obj) ≫ φ.hom) h

end Tensor

/-- On the pro-étale site of the spectrum of a w-contractible ring, morphisms from the unit to a
tensor product of sheaves are finite sums of tensor products of morphisms from the unit. -/
theorem unitTensorFinite {R : CommRingCat.{u}} [IsWContractibleRing R] (e : Y ≅ Spec R) :
    UnitTensorFinite (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) := by
  classical
  intro F G x
  let θ := tensorPresheafToSheaf F G
  obtain ⟨ι, _, V, f, hcov, hmono, hdisj, p, hp⟩ :=
    exists_finite_disjoint_preimage e θ (unitHomEquiv _ x)
  have := Fintype.ofFinite ι
  choose n a b hab using fun i ↦ TensorProduct.exists_eq_sum_tmul' (p i)
  choose a' ha' using fun i (k : Fin (n i)) ↦
    exists_glue_of_disjoint F f hcov hmono hdisj (Pi.single i (a i k))
  choose b' hb' using fun i (k : Fin (n i)) ↦
    exists_glue_of_disjoint G f hcov hmono hdisj (Pi.single i (b i k))
  let one := unitHomEquiv _ (𝟙 (𝟙_ (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))))
  let u := (unitHomEquiv _).symm ((tensorPresheafToSheaf _ _).app _ (one ⊗ₜ one))
  let E := Σ i, Fin (n i)
  let ε := Fintype.equivFin E
  let s (k : E) := (unitHomEquiv F).symm (a' k.1 k.2)
  let t (k : E) := (unitHomEquiv G).symm (b' k.1 k.2)
  have key (k : E) : unitHomEquiv _ (u ≫ (s k ⊗ₘ t k)) = θ.app _ (a' k.1 k.2 ⊗ₜ b' k.1 k.2) := by
    rw [unitHomEquiv_comp, Equiv.apply_symm_apply]
    have h := congrArg (fun φ ↦ φ.app (op (Scheme.ProEt.terminal Y)) (one ⊗ₜ one))
      (tensorHom_comp_tensorPresheafToSheaf (s k) (t k))
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
    rw [← h]
    congr 1
    change (s k).hom.app _ one ⊗ₜ[Λ] (t k).hom.app _ one = _
    rw [← unitHomEquiv_apply, ← unitHomEquiv_apply, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  refine ⟨Fintype.card E, fun _ ↦ u, fun k ↦ s (ε.symm k), fun k ↦ t (ε.symm k),
    (unitHomEquiv _).injective ?_⟩
  rw [unitHomEquiv_sum]
  simp only [key]
  rw [ε.symm.sum_comp (fun k ↦ θ.app _ (a' k.1 k.2 ⊗ₜ b' k.1 k.2))]
  refine eq_of_restrict_eq f hcov fun l ↦ ?_
  rw [map_sum, ← hp l, hab l, map_sum, Fintype.sum_sigma, Finset.sum_eq_single l]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← NatTrans.naturality_apply]
    congr 1
    change _ = F.obj.map (f l).op (a' l k) ⊗ₜ[Λ] G.obj.map (f l).op (b' l k)
    rw [ha' l k, hb' l k, Pi.single_eq_same, Pi.single_eq_same]
  · intro i _ hi
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [← NatTrans.naturality_apply]
    change θ.app _ (F.obj.map (f l).op (a' i k) ⊗ₜ[Λ] G.obj.map (f l).op (b' i k)) = 0
    rw [ha' i k, Pi.single_eq_of_ne (Ne.symm hi), TensorProduct.zero_tmul, map_zero]
  · simp

end ProEtale

end AlgebraicGeometry
