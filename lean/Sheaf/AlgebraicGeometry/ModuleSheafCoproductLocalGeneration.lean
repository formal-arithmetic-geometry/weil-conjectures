/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J6
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Local finite-sum normal form for sections of module-sheaf coproducts

Source: Stacks Project, Modules on Sites, Tag 03DB, lemma-limits-colimits.
(blueprint: lem-pur-module-sheaf-coproduct-local-generation)
-/

@[expose] public section

universe u r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A covering sieve contains an actual covering presieve of the site. -/
private theorem covering_refinement
    {C : Type u} [SmallCategory C] (K : Precoverage C)
    (hK : K.IsSiteForCoverings) {V : C} {S : Sieve V}
    (hS : S ∈ K.toGrothendieck V) : ∃ P ∈ K V, P ≤ S.arrows := by
  classical
  have : K.HasIsos := hK.1
  induction hS with
  | of V P hP => exact ⟨P, hP, Sieve.le_generate P⟩
  | top V =>
    exact ⟨Presieve.singleton (𝟙 V), K.mem_coverings_of_isIso (𝟙 V),
      fun _ _ _ ↦ trivial⟩
  | pullback V S hS W f ih =>
    obtain ⟨P, hP, hPS⟩ := ih
    obtain ⟨A, U, a, rfl⟩ := P.exists_eq_ofArrows
    obtain ⟨Q, p, q, hpq, hp⟩ := hK.2.2 A V U a hP W f
    refine ⟨Presieve.ofArrows Q p, hp, ?_⟩
    rintro Z g ⟨i⟩
    change S (p i ≫ f)
    rw [(hpq i).w]
    exact S.downward_closed (hPS _ _ ⟨i⟩) (q i)
  | transitive V S T hS hT ihS ihT =>
    obtain ⟨P, hP, hPS⟩ := ihS
    choose Q hQ hQT using fun (W : C) (f : W ⟶ V) (hf : P f) ↦ ihT (hPS _ _ hf)
    refine ⟨P.bind (fun W f hf ↦ Q W f hf),
      hK.2.1 V P (fun W f hf ↦ Q W f hf) hP hQ, ?_⟩
    rintro W g ⟨Z, a, b, hb, ha, rfl⟩
    exact hQT Z b hb _ _ ha

/-- The comparison from a presheaf colimit to a sheaf colimit is locally surjective. -/
private theorem colimit_comparison_locally_surjective
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {D : Type u} [SmallCategory D]
    (F : D ⥤ SheafOfModules.{u} R) (c : Cocone F) (hc : IsColimit c) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map
        (colimit.desc (F ⋙ SheafOfModules.forget R)
          ((SheafOfModules.forget R).mapCocone c))) := by
  let U := SheafOfModules.forget R
  let L := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj : L ⊣ U := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let P := colimit.cocone (F ⋙ U)
  let hP := colimit.isColimit (F ⋙ U)
  let hQ := isColimitOfPreserves L hP
  let e : (F ⋙ U) ⋙ L ≅ F := Functor.isoWhiskerLeft F (asIso adj.counit)
  let hcE := (IsColimit.precomposeHomEquiv e c).symm hc
  let θ := hQ.coconePointUniqueUpToIso hcE
  let k := adj.unit.app P.pt ≫ U.map θ.hom
  have hk (i : D) : P.ι.app i ≫ k = U.map (c.ι.app i) := by
    dsimp only [k]
    have hn := adj.unit.naturality (P.ι.app i)
    change P.ι.app i ≫ adj.unit.app P.pt =
      adj.unit.app (U.obj (F.obj i)) ≫ U.map (L.map (P.ι.app i)) at hn
    rw [← Category.assoc, hn, Category.assoc, ← U.map_comp]
    have hθ := hQ.comp_coconePointUniqueUpToIso_hom hcE i
    change L.map (P.ι.app i) ≫ θ.hom = adj.counit.app (F.obj i) ≫ c.ι.app i at hθ
    rw [hθ, U.map_comp, ← Category.assoc, adj.right_triangle_components]
    exact Category.id_comp _
  have heq : colimit.desc (F ⋙ U) (U.mapCocone c) = k := by
    apply hP.hom_ext
    intro i
    exact (hP.fac _ i).trans (hk i).symm
  rw [heq, Functor.map_comp]
  have : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (adj.unit.app P.pt)) := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P.pt.presheaf)
    infer_instance
  infer_instance

/-- Source: Stacks Project, Modules on Sites, Tag 03DB, lemma-limits-colimits,
coproduct construction by sheafifying the sectionwise direct sum.
(blueprint: lem-pur-module-sheaf-coproduct-local-generation).

Proof: Form the coproduct P of the underlying module presheaves. Its sections are
finitely supported families, since evaluation preserves coproducts. Sheafify P;
the sheafification adjunction identifies it with the chosen sheaf coproduct,
compatibly with each insertion. The sheafification unit is locally surjective.
Refine its covering image sieve to a covering family of the given site. On each
member choose a representative in P and its finite support. The representative
is the sum of its coordinate insertions, hence so is its image in the sheaf
coproduct. The coordinate retractions recover exactly these coordinates. Empty
index types give the zero sum; empty covering families impose no local equations.
-/
theorem moduleSheaf_coproduct_localGeneration
    {C : Type u} [SmallCategory C] (K : Precoverage C)
    (hK : K.IsSiteForCoverings) [HasPullbacks C]
    (R : Sheaf K.toGrothendieck RingCat.{r})
    [HasSheafify K.toGrothendieck AddCommGrpCat.{u}]
    [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (I : Type u) [DecidableEq I] (H : I → ringedSiteModules.{u} R)
    (V : C) (s : (∐ H).val.obj (op V)) :
    ∃ (A : Type u) (U : A → C) (a : ∀ α : A, U α ⟶ V),
      Presieve.ofArrows U a ∈ K V ∧
      ∃ B : A → Finset I, ∀ α : A,
        (∐ H).val.map (a α).op s =
          ∑ i ∈ B α, (Sigma.ι H i).val.app (op (U α))
            ((Sigma.π H i).val.app (op (U α)) ((∐ H).val.map (a α).op s))  := by
  classical
  let F := Discrete.functor H ⋙ SheafOfModules.forget R
  let P := colimit F
  let cH := Cofan.mk (∐ H) (Sigma.ι H)
  let k : P ⟶ (∐ H).val := colimit.desc F ((SheafOfModules.forget R).mapCocone cH)
  let q := (PresheafOfModules.toPresheaf R.obj).map k
  have : Presheaf.IsLocallySurjective K.toGrothendieck q :=
    colimit_comparison_locally_surjective R (Discrete.functor H) cH
      (coproductIsCoproduct H)
  obtain ⟨Q, hQ, hQS⟩ := covering_refinement K hK
    (Presheaf.imageSieve_mem K.toGrothendieck q (U := op V) s)
  obtain ⟨A, U, a, rfl⟩ := Q.exists_eq_ofArrows
  have hrep (α : A) : ∃ (B : Finset I) (y : ∀ i, (H i).val.obj (op (U α))),
      (∐ H).val.map (a α).op s =
        ∑ i ∈ B, (Sigma.ι H i).val.app (op (U α)) (y i) := by
    obtain ⟨t, ht⟩ := hQS _ _ ⟨α⟩
    let E := PresheafOfModules.evaluation R.obj (op (U α))
    let c := Cofan.mk (E.obj P) (fun i ↦ E.map (colimit.ι F ⟨i⟩))
    let ec : F ⋙ E ≅ Discrete.functor (fun i ↦ E.obj (H i).val) :=
      Discrete.natIso fun _ ↦ Iso.refl _
    let hc : IsColimit c := by
      apply (IsColimit.precomposeHomEquiv ec c).1
      exact IsColimit.ofIsoColimit (r := E.mapCocone (colimit.cocone F))
        (isColimitOfPreserves E (colimit.isColimit F))
        (Cocone.ext (Iso.refl _) (fun ⟨i⟩ ↦ by simp [ec, c]))
    let Z := fun i ↦ E.obj (H i).val
    let e := (ModuleCat.coproductCoconeIsColimit Z).coconePointUniqueUpToIso hc
    let d : DirectSum I (fun i ↦ Z i) := e.inv t
    have hd : ∑ i ∈ d.support, (E.map (colimit.ι F ⟨i⟩)) (d i) = t := by
      have hsum := congrArg (fun z ↦ e.hom z) (DirectSum.sum_support_of d)
      rw [map_sum] at hsum
      have hleg (i : I) (z : Z i) : e.hom (DirectSum.of (fun i ↦ Z i) i z) =
          (E.map (colimit.ι F ⟨i⟩)) z := by
        exact congrArg (fun f ↦ f z)
          ((ModuleCat.coproductCoconeIsColimit Z).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩)
      simp only [hleg] at hsum
      simpa [d] using hsum
    change k.app (op (U α)) t = (∐ H).val.map (a α).op s at ht
    refine ⟨d.support, fun i ↦ d i, ?_⟩
    change (∐ H).val.map (a α).op s =
      ∑ i ∈ d.support, (Sigma.ι H i).val.app (op (U α)) (d i)
    rw [← ht, ← hd, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun f ↦ f.app (op (U α)) (d i))
      (colimit.ι_desc ((SheafOfModules.forget R).mapCocone cH) ⟨i⟩)
  choose B y hy using hrep
  refine ⟨A, U, a, hQ, B, ?_⟩
  intro α
  rw [hy α]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [map_sum, Finset.sum_eq_single i]
  · have heq := congrArg (fun f ↦ f.val.app (op (U α)) (y α i))
      (Sigma.ι_π_eq_id H i)
    exact heq.symm
  · intro j hj hji
    have heq := congrArg (fun f ↦ f.val.app (op (U α)) (y α j))
      (Sigma.ι_π_of_ne H hji)
    have hz : (0 : H j ⟶ H i).val = 0 := (SheafOfModules.forget R).map_zero _ _
    rw [hz] at heq
    exact heq
  · exact fun hn ↦ (hn hi).elim

end CategoryTheory
