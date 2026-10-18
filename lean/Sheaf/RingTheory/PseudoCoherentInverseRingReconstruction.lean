/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent
public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.ComplexTowerLimitProjectionComparison
import Sheaf.RingTheory.NilpotentFiniteFreeComplexTower
import Sheaf.RingTheory.FiniteFreeComplexTowerInverseLimit
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Pseudo-coherent reconstruction over a tower of nilpotent quotients

Source: Stacks Project, More on Algebra, Tag 0CQF,
lemma-Rlim-pseudo-coherent-gives-pseudo-coherent
(blueprint: lem-weil-pbc-pseudocoherent-inverse-ring-reconstruction).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

private theorem localizedHom_bijective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P H : CochainComplex C ℤ) [P.IsKProjective] :
    Function.Bijective (fun f : (HomotopyCategory.quotient _ _).obj P ⟶
        (HomotopyCategory.quotient _ _).obj H ↦
      (quotientCompQhIso C).inv.app P ≫ Qh.map f ≫
        (quotientCompQhIso C).hom.app H) := by
  exact (Iso.homCongr ((quotientCompQhIso C).app P)
    ((quotientCompQhIso C).app H)).bijective.comp
      (CochainComplex.IsKProjective.Qh_map_bijective P _)

private noncomputable def localizedHomEquiv
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P H : CochainComplex C ℤ) [P.IsKProjective] :
    ((HomotopyCategory.quotient _ _).obj P ⟶ (HomotopyCategory.quotient _ _).obj H) ≃
      (Q.obj P ⟶ Q.obj H) :=
  Equiv.ofBijective _ (localizedHom_bijective P H)

private theorem localizedHomEquiv_map
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {P H : CochainComplex C ℤ} [P.IsKProjective] (f : P ⟶ H) :
    localizedHomEquiv P H ((HomotopyCategory.quotient _ _).map f) = Q.map f := by
  change (quotientCompQhIso C).inv.app P ≫ Qh.map _ ≫
    (quotientCompQhIso C).hom.app H = _
  rw [quotientCompQhIso_hom_naturality]
  simp

private theorem Q_map_surjective_of_projective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P H : CochainComplex C ℤ) [P.IsKProjective] :
    Function.Surjective (Q.map : (P ⟶ H) → (Q.obj P ⟶ Q.obj H)) := by
  intro f
  obtain ⟨g, hg⟩ := (localizedHomEquiv P H).surjective f
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  exact ⟨g, (localizedHomEquiv_map g).symm.trans hg⟩

private theorem localizedUnit_bijective
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (P : CochainComplex C ℤ) [P.IsKProjective]
    [CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj P)]
    (H : CochainComplex D ℤ) :
    Function.Bijective (fun f : Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ⟶
        Q.obj H ↦
      Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        G.mapDerivedCategory.map f ≫ G.mapDerivedCategoryFactors.hom.app H) := by
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let GH := (G.mapHomologicalComplex (.up ℤ)).obj H
  let e := (localizedHomEquiv FP H).symm.trans
    (((a.mapHomotopyCategory (.up ℤ)).homEquiv
      ((HomotopyCategory.quotient _ _).obj P)
      ((HomotopyCategory.quotient _ _).obj H)).trans (localizedHomEquiv P GH))
  have he (f : FP ⟶ H) : e (Q.map f) =
      Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv P H f) := by
    rw [← localizedHomEquiv_map f, Equiv.trans_apply, Equiv.trans_apply,
      Equiv.symm_apply_apply]
    change localizedHomEquiv P GH
      ((a.mapHomotopyCategory (.up ℤ)).homEquiv _ _
        ((HomotopyCategory.quotient _ _).map f)) = _
    rw [Adjunction.homEquiv_unit,
      Adjunction.mapHomotopyCategory_unit_app_quotient,
      Functor.mapHomotopyCategory_map, ← Functor.map_comp]
    exact localizedHomEquiv_map _
  have hfun : (fun f : Q.obj FP ⟶ Q.obj H ↦
      Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        G.mapDerivedCategoryFactors.inv.app FP ≫
        G.mapDerivedCategory.map f ≫ G.mapDerivedCategoryFactors.hom.app H) =
      (e : (Q.obj FP ⟶ Q.obj H) → (Q.obj P ⟶ Q.obj GH)) := by
    funext f
    obtain ⟨g, rfl⟩ := Q_map_surjective_of_projective FP H f
    rw [he]
    rw [G.mapDerivedCategoryFactors_hom_naturality]
    simp only [Iso.inv_hom_id_app_assoc, ← Q.map_comp]
    rfl
  exact hfun.symm ▸ e.bijective

private theorem isIso_of_coyoneda_Q_bijective
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [Category D]
    (F : CochainComplex C ℤ ⥤ D) [F.EssSurj]
    {X Y : D} (f : X ⟶ Y)
    (h : ∀ H, Function.Bijective (fun g : Y ⟶ F.obj H ↦ f ≫ g)) : IsIso f := by
  apply isIso_of_coyoneda_map_bijective
  intro T
  let H := F.objPreimage T
  let e := F.objObjPreimageIso T
  let eY := Iso.homCongr (Iso.refl Y) e
  let eX := Iso.homCongr (Iso.refl X) e
  have hcomp := eX.bijective.comp ((h H).comp eY.symm.bijective)
  simpa [eX, eY, Iso.homCongr, Function.comp_def, Category.assoc] using hcomp

private theorem exists_normalized_projective_baseChange
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G)
    (L : DerivedCategory C ⥤ DerivedCategory D) (adj : L ⊣ G.mapDerivedCategory)
    (P : CochainComplex C ℤ) [P.IsKProjective]
    [CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj P)] :
    ∃ γ : L.obj (Q.obj P) ≅ Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P),
      adj.unit.app (Q.obj P) ≫ G.mapDerivedCategory.map γ.hom ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let η := (a.mapHomologicalComplex (.up ℤ)).unit.app P
  let f := (adj.homEquiv (Q.obj P) (Q.obj FP)).symm
    (Q.map η ≫ G.mapDerivedCategoryFactors.inv.app FP)
  have hf : adj.homEquiv _ _ f =
      Q.map η ≫ G.mapDerivedCategoryFactors.inv.app FP := Equiv.apply_symm_apply _ _
  have hfiso : IsIso f := by
    apply isIso_of_coyoneda_Q_bijective Q
    intro H
    let e := (adj.homEquiv (Q.obj P) (Q.obj H)).trans
      (Iso.homCongr (Iso.refl _) (G.mapDerivedCategoryFactors.app H))
    have hh := localizedUnit_bijective a P H
    have heq : (fun g : Q.obj FP ⟶ Q.obj H ↦ e (f ≫ g)) =
        (fun g ↦ Q.map η ≫ G.mapDerivedCategoryFactors.inv.app FP ≫
          G.mapDerivedCategory.map g ≫ G.mapDerivedCategoryFactors.hom.app H) := by
      funext g
      simp only [e, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv,
        Category.id_comp]
      change adj.homEquiv _ _ (f ≫ g) ≫ _ = _
      rw [adj.homEquiv_naturality_right, hf]
      simp only [Category.assoc]
      rfl
    have hh' : Function.Bijective (e ∘ (fun g : Q.obj FP ⟶ Q.obj H ↦ f ≫ g)) := by
      change Function.Bijective (fun g ↦ e (f ≫ g))
      rw [heq]
      exact hh
    exact (Function.Bijective.of_comp_iff' e.bijective _).mp hh'
  refine ⟨asIso f, ?_⟩
  change adj.unit.app (Q.obj P) ≫ G.mapDerivedCategory.map f ≫ _ = _
  rw [← Category.assoc]
  change adj.homEquiv _ _ f ≫ _ = _
  rw [hf]
  change (Q.map η ≫ G.mapDerivedCategoryFactors.inv.app FP) ≫
    G.mapDerivedCategoryFactors.hom.app FP = Q.map η
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- Reconstruction of a compatible pseudo-coherent tower, including its finite-free models.
The index `0` denotes the paper's index `1`. The ring-limit universal property in `hlim`
is the compatible-tuple construction, invariant under its unique ring isomorphism.
The left adjoints `L` and `M` of derived restriction of scalars denote derived tensor.
The normalization `hχ` specifies the canonical composition of restrictions. The maps
`η` and the equation for `γ` identify ordinary and derived tensor on the free model,
so the last equality identifies the actual projection-induced comparison maps.

Source: Stacks Project, More on Algebra, Tag 0CQF
(blueprint: lem-weil-pbc-pseudocoherent-inverse-ring-reconstruction).

Proof: First construct the marked finite-free tower by the single-step nilpotent lift and
explicit dependent recursion, retaining a common upper cutoff. Construct its finite-free
termwise limit with the literal tuple projections. The surjective complex-tower Roos
triangle and the normalized markings identify its localization with E, respecting all
projections. For the final base-change comparison, use bounded-above projectivity directly:
localization is bijective on homotopy Hom sets out of these complexes. The ordinary
adjunction and these bijections show that the localized chain unit represents the derived
adjunction. Its transpose is therefore an isomorphism, normalized by that unit. Naturality
and the ordinary adjunction equation for the reduction chain isomorphisms identify their
images with the actual projection-induced comparisons. These are composites of
isomorphisms. The constructed model and its marking give pseudo-coherence by definition. -/
theorem isPseudoCoherent_inverse_ring_reconstruction
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hsurj : ∀ n, Function.Surjective (φ n))
    (hnil : ∀ n, IsNilpotent (RingHom.ker (φ n)))
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (hlim : ∀ x : ∀ n, R n, (∀ n, φ n (x (n + 1)) = x n) →
      ∃! a : A, ∀ n, q n a = x n)
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [∀ n, HasDerivedCategory.{w} (ModuleCat.{max u v} (R n))]
    (L : ∀ n, DerivedCategory (ModuleCat.{max u v} (R (n + 1))) ⥤
      DerivedCategory (ModuleCat.{max u v} (R n)))
    (adjφ : ∀ n, L n ⊣ (ModuleCat.restrictScalars (φ n)).mapDerivedCategory)
    (M : ∀ n, DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} (R n)))
    (adjq : ∀ n, M n ⊣ (ModuleCat.restrictScalars (q n)).mapDerivedCategory)
    (χ : ∀ n, (ModuleCat.restrictScalars (q n)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory)
    (hχ : ∀ n (C : CochainComplex (ModuleCat.{max u v} (R n)) ℤ),
      (χ n).hom.app (Q.obj C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map
          ((ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj C) =
      (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app C ≫
        Q.map ((NatIso.mapHomologicalComplex
          (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n))
          (.up ℤ)).hom.app C))
    (Eₙ : ∀ n, DerivedCategory (ModuleCat.{max u v} (R n)))
    (t : ∀ n, Eₙ (n + 1) ⟶
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.obj (Eₙ n))
    (hred : ∀ n, IsIso (((adjφ n).homEquiv (Eₙ (n + 1)) (Eₙ n)).symm (t n)))
    (hpc : IsPseudoCoherent (Eₙ 0))
    [HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))]
    (E : DerivedCategory (ModuleCat.{max u v} A))
    (pE : E ⟶ ∏ᶜ fun n ↦
      (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))
    (δ : (∏ᶜ fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n)) ⟶
      E⟦(1 : ℤ)⟧)
    (hE : IsDerivedLimitTriangle
      (fun n ↦ (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
        (χ n).inv.app (Eₙ n)) E pE δ) :
    IsPseudoCoherent E ∧
    (∀ n, IsIso (((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n))) ∧
    ∃ (Pₙ : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ)
      (b : ℤ) (βₙ : ∀ n, Q.obj (Pₙ n) ≅ Eₙ n)
      (uₙ : ∀ n, Pₙ (n + 1) ⟶
        ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
      (θₙ : ∀ n, ((ModuleCat.extendScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj
        (Pₙ (n + 1)) ≅ Pₙ n)
      (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (β : Q.obj P ≅ E)
      (p : ∀ n, P ⟶
        ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
      (θ : ∀ n, ((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P ≅ Pₙ n)
      (η : ∀ n, P ⟶ ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P))
      (γ : ∀ n, (M n).obj (Q.obj P) ≅
        Q.obj (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P)),
      (∀ n, (Pₙ n).IsStrictlyLE b) ∧
      (∀ n i, Module.Free (R n) ((Pₙ n).X i) ∧ Module.Finite (R n) ((Pₙ n).X i)) ∧
      (∀ n i, Function.Surjective ((uₙ n).f i)) ∧
      (∀ n i, ((ModuleCat.extendRestrictScalarsAdj (φ n)).homEquiv
        ((Pₙ (n + 1)).X i) ((Pₙ n).X i) ((θₙ n).hom.f i)) = (uₙ n).f i) ∧
      (∀ n, Q.map (uₙ n) = (βₙ (n + 1)).hom ≫ t n ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.map (βₙ n).inv ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app (Pₙ n)) ∧
      P.IsStrictlyLE b ∧
      (∀ i, Module.Free A (P.X i) ∧ Module.Finite A (P.X i)) ∧
      (∀ n i (y : P.X i), (uₙ n).f i ((p (n + 1)).f i y) = (p n).f i y) ∧
      (∀ i (x : ∀ n, (Pₙ n).X i), (∀ n, (uₙ n).f i (x (n + 1)) = x n) →
        ∃! y : P.X i, ∀ n, (p n).f i y = x n) ∧
      (∀ n, Q.map (p n) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.inv.app (Pₙ n) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (βₙ n).hom =
        β.hom ≫ pE ≫ Pi.π _ n) ∧
      (∀ n i, ((ModuleCat.extendRestrictScalarsAdj (q n)).homEquiv
        (P.X i) ((Pₙ n).X i) ((θ n).hom.f i)) = (p n).f i) ∧
      (∀ n i, (η n).f i = (ModuleCat.extendRestrictScalarsAdj (q n)).unit.app (P.X i)) ∧
      (∀ n, (adjq n).unit.app (Q.obj P) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (γ n).hom ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P) =
        Q.map (η n)) ∧
      (∀ n, (γ n).hom ≫ Q.map (θ n).hom ≫ (βₙ n).hom =
        (M n).map β.hom ≫ ((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n))  := by
  classical
  obtain ⟨Pₙ, b, βₙ, uₙ, θₙ, hbound, hterms, hsurju, hθₙ, hu⟩ :=
    exists_nilpotent_finiteFree_complexTower R φ hsurj hnil L adjφ Eₙ t hred hpc
  obtain ⟨P, p, θ, hboundP, htermsP, hp, hP, hθ⟩ :=
    exists_finiteFree_complexTower_inverseLimit R φ hsurj hnil A q hq hlim
      Pₙ b uₙ θₙ hbound hterms hsurju hθₙ
  obtain ⟨β, hβ⟩ := exists_complexTower_limit_projection_comparison
    R φ A q hq hlim χ hχ Eₙ t E pE δ hE Pₙ βₙ uₙ hsurju hu P p hp hP
  have : P.IsStrictlyLE b := hboundP
  have (i : ℤ) : Module.Free A (P.X i) := (htermsP i).1
  have (i : ℤ) : Projective (P.X i) := inferInstance
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  have (n : ℕ) : (ModuleCat.extendScalars (q n)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (q n)).left_adjoint_additive
  let η := fun n ↦ ((ModuleCat.extendRestrictScalarsAdj (q n)).mapHomologicalComplex
    (.up ℤ)).unit.app P
  have hγ (n : ℕ) : ∃ γ : (M n).obj (Q.obj P) ≅
      Q.obj (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P),
      (adjq n).unit.app (Q.obj P) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map γ.hom ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P) =
        Q.map (η n) := by
    have : (Pₙ n).IsStrictlyLE b := hbound n
    have (i : ℤ) : Module.Free (R n) ((Pₙ n).X i) := (hterms n i).1
    have (i : ℤ) : Projective ((Pₙ n).X i) := inferInstance
    have : (Pₙ n).IsKProjective := CochainComplex.isKProjective_of_projective (Pₙ n) b
    have := CochainComplex.isKProjective_of_iso (θ n).symm
    exact exists_normalized_projective_baseChange
      (ModuleCat.extendRestrictScalarsAdj (q n)) (M n) (adjq n) P
  choose γ hγ using hγ
  have hcomp (n : ℕ) : (γ n).hom ≫ Q.map (θ n).hom ≫ (βₙ n).hom =
      (M n).map β.hom ≫ ((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n) := by
    apply ((adjq n).homEquiv _ _).injective
    rw [(adjq n).homEquiv_naturality_left, Equiv.apply_symm_apply]
    rw [(adjq n).homEquiv_unit]
    simp only [Functor.map_comp]
    have hγ' : (adjq n).unit.app (Q.obj P) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (γ n).hom =
        Q.map (η n) ≫
          (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.inv.app
            (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P) := by
      apply ((ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.app _).eq_comp_inv.mpr
      exact (Category.assoc _ _ _).trans (hγ n)
    have hηθ : η n ≫
        ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).map
          (θ n).hom = p n := by
      apply HomologicalComplex.Hom.ext
      funext i
      exact hθ n i
    have hn := (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.inv.naturality
      (θ n).hom
    dsimp only [Functor.comp_map] at hn
    calc
      _ = ((adjq n).unit.app (Q.obj P) ≫
          (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (γ n).hom) ≫
          (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (Q.map (θ n).hom) ≫
          (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (βₙ n).hom := by
        simp only [Category.assoc]
      _ = Q.map (η n) ≫
          ((ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.inv.app _ ≫
            (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (Q.map (θ n).hom)) ≫
          (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (βₙ n).hom := by
        rw [hγ']
        simp only [Category.assoc]
      _ = Q.map (η n) ≫
          (Q.map (((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).map
            (θ n).hom) ≫
            (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.inv.app (Pₙ n)) ≫
          (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (βₙ n).hom := by
        rw [hn]
      _ = Q.map (p n) ≫
          (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.inv.app (Pₙ n) ≫
          (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (βₙ n).hom := by
        have hQP : Q.map (η n) ≫
            Q.map (((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).map
              (θ n).hom) = Q.map (p n) := by
          rw [← Functor.map_comp]
          exact congrArg Q.map hηθ
        simp only [← Category.assoc]
        rw [hQP]
      _ = _ := hβ n
  have hiso (n : ℕ) : IsIso (((adjq n).homEquiv E (Eₙ n)).symm
      (pE ≫ Pi.π _ n)) := by
    have : IsIso ((M n).map β.hom ≫ ((adjq n).homEquiv E (Eₙ n)).symm
        (pE ≫ Pi.π _ n)) := by
      rw [← hcomp]
      infer_instance
    exact (isIso_comp_left_iff ((M n).map β.hom) _).mp this
  refine ⟨⟨P, b, hboundP, htermsP, ⟨β⟩⟩, hiso, Pₙ, b, βₙ, uₙ, θₙ, P, β, p, θ, η, γ,
    hbound, hterms, hsurju, hθₙ, hu, hboundP, htermsP, hp, hP, hβ, hθ, ?_, hγ, hcomp⟩
  intro n i
  rfl

end DerivedCategory
