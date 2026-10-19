/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.AlgebraicGeometry.ModuleSheafCoproductLocalGeneration
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Coproducts of module sheaves inside their products

Source: Stacks Project, Modules on Sites, Tag 03DB, lemma-limits-colimits and its proof;
the explicit locally finite-coordinate construction in the DAG proof
(blueprint: lem-pur-module-sheaf-coproduct-local-support).
-/

@[expose] public section

universe u r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Source: Stacks Project, Modules on Sites, Tag 03DB, lemma-limits-colimits;
the explicit local-coordinate construction in the DAG proof
(blueprint: lem-pur-module-sheaf-coproduct-local-support).

The subsheaf is presented by a sectionwise injective module-sheaf map `m` into the
product. Its sectionwise range is exactly the displayed local finite-support predicate.
This determines the subsheaf, including its inherited restrictions and module operations,
up to the unique isomorphism over the product. The diagonal and off-diagonal equations
say that the maps `ι i` factor the coordinate insertions. The last two clauses identify
the monomorphism from the chosen coproduct and its sectionwise image with this subsheaf.

Proof (the nine steps of the node):
1. By lem-weil-pbc-module-sheaves-limits-sectionwise, the product of the sheaves `H i`
is computed sectionwise, with coordinatewise restrictions and module operations.
2. Pulling a witnessing cover back proves stability under restriction. The identity
cover with empty support witnesses zero. Negation and scalar multiplication preserve
a witness. For addition use the common pullback refinement of the two covers and the
union of their finite supports. Thus the specified tuples form a subpresheaf of modules.
3. Glue a matching family in the product. Compose its cover with each section's
witnessing cover; the glued tuple has finite support on each composite member. Uniqueness
comes from the product sheaf. Empty covering families are included by unique gluing.
4. A coordinate insertion has support contained in its singleton on the identity cover,
so it factors through the subsheaf; it is linear and commutes with restrictions.
5. Given maps `H i ⟶ T`, on each witnessing cover member sum their values over its
finite support. On overlaps enlarge both supports to their union; the resulting sums
agree, since the additional coordinates vanish. Glue these sums in `T`.
6. Two witnesses give the same glued section: pass to their common pullback refinement,
enlarge to the union of their supports, and apply separatedness. For empty covers use
the uniqueness of the empty gluing.
7. Pull back witnesses to prove naturality. Common refinements and unions prove
additivity; semilinearity of restriction and linearity of the given maps prove scalar
compatibility. The glued map is therefore a module-sheaf morphism.
8. On a coordinate insertion its value is the prescribed map. Conversely, every section
is locally the finite sum of its coordinate insertions, so linearity and separatedness
force uniqueness. This proves the Hom bijection and the discrete colimit property
of def-weil-pbc-category-colimit, also for an empty index set.
9. The two coproduct universal properties identify the chosen coproduct with this
subsheaf, commuting with insertions. Its canonical map to the product is the composite
of this isomorphism with `m`, hence is monic and has exactly the same sectionwise image.
-/
theorem moduleSheaf_coproduct_localSupport
    {C : Type u} [SmallCategory C] (K : Precoverage C)
    (hK : K.IsSiteForCoverings) [HasPullbacks C]
    (R : Sheaf K.toGrothendieck RingCat.{r})
    (hcomm : ∀ (V : Cᵒᵖ) (a b : R.obj.obj V), a * b = b * a)
    [HasSheafify K.toGrothendieck AddCommGrpCat.{u}]
    [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (I : Type u) (H : I → ringedSiteModules.{u} R) :
    ∃ (S : ringedSiteModules.{u} R) (m : S ⟶ ∏ᶜ H) (ι : ∀ i : I, H i ⟶ S),
      Mono m ∧
      (∀ V : Cᵒᵖ, Function.Injective (m.val.app V)) ∧
      (∀ (V : C) (h : (∏ᶜ H).val.obj (op V)),
        h ∈ Set.range (m.val.app (op V)) ↔
          ∃ (A : Type u) (U : A → C) (a : ∀ α : A, U α ⟶ V),
            Presieve.ofArrows U a ∈ K V ∧
            ∃ B : A → Finset I, ∀ (α : A) (i : I), i ∉ B α →
              (H i).val.map (a α).op ((Pi.π H i).val.app (op V) h) = 0) ∧
      (∀ i : I, ι i ≫ m ≫ Pi.π H i = 𝟙 (H i)) ∧
      (∀ (i j : I), i ≠ j → ι i ≫ m ≫ Pi.π H j = 0) ∧
      Nonempty (IsColimit (Cofan.mk S ι)) ∧
      (∀ T : ringedSiteModules.{u} R,
        Function.Bijective (fun f : S ⟶ T ↦ fun i : I ↦ ι i ≫ f)) ∧
      Mono (Sigma.desc (fun i : I ↦ ι i ≫ m)) ∧
      (∀ V : Cᵒᵖ,
        Set.range ((Sigma.desc (fun i : I ↦ ι i ≫ m)).val.app V) =
          Set.range (m.val.app V)) := by
  classical
  have _ := hcomm
  let m : ∐ H ⟶ ∏ᶜ H := Pi.lift (fun i ↦ Sigma.π H i)
  have hmπ (i : I) : m ≫ Pi.π H i = Sigma.π H i := by simp [m]
  have hdiag (W : Cᵒᵖ) (i : I) (x : (H i).val.obj W) :
      (Sigma.π H i).val.app W ((Sigma.ι H i).val.app W x) = x :=
    congrArg (fun f : H i ⟶ H i ↦ f.val.app W x) (Sigma.ι_π_eq_id H i)
  have hoff (W : Cᵒᵖ) (i j : I) (hij : i ≠ j) (x : (H i).val.obj W) :
      (Sigma.π H j).val.app W ((Sigma.ι H i).val.app W x) = 0 := by
    have heq := congrArg (fun f : H i ⟶ H j ↦ f.val.app W x)
      (Sigma.ι_π_of_ne H hij)
    have hz : (0 : H i ⟶ H j).val = 0 := (SheafOfModules.forget R).map_zero _ _
    rw [hz] at heq
    exact heq
  have hsum (W : Cᵒᵖ) (B : Finset I) (y : ∀ i, (H i).val.obj W) (j : I) :
      (Sigma.π H j).val.app W (∑ i ∈ B, (Sigma.ι H i).val.app W (y i)) =
        if j ∈ B then y j else 0 := by
    rw [map_sum]
    split_ifs with hj
    · rw [Finset.sum_eq_single j]
      · exact hdiag W j (y j)
      · intro i hi hij
        exact hoff W i j hij (y i)
      · exact fun hn ↦ (hn hj).elim
    · apply Finset.sum_eq_zero
      intro i hi
      exact hoff W i j (fun hij ↦ hj (hij ▸ hi)) (y i)
  let F := (∐ H).val.presheaf ⋙ forget AddCommGrpCat
  let G := (∏ᶜ H).val.presheaf ⋙ forget AddCommGrpCat
  let q : F ⟶ G := Functor.whiskerRight
    ((PresheafOfModules.toPresheaf R.obj).map m.val) (forget AddCommGrpCat)
  have hF : Presieve.IsSheaf K.toGrothendieck F :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget AddCommGrpCat) (∐ H).isSheaf)
  have hG : Presieve.IsSheaf K.toGrothendieck G :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget AddCommGrpCat) (∏ᶜ H).isSheaf)
  have hinj : ∀ V : Cᵒᵖ, Function.Injective (m.val.app V) := by
    intro V x y h
    let z := x - y
    have hz (i : I) : (Sigma.π H i).val.app V z = 0 := by
      have hx := congrArg (fun f : ∐ H ⟶ H i ↦ f.val.app V x) (hmπ i)
      have hy := congrArg (fun f : ∐ H ⟶ H i ↦ f.val.app V y) (hmπ i)
      change (Pi.π H i).val.app V (m.val.app V x) = _ at hx
      change (Pi.π H i).val.app V (m.val.app V y) = _ at hy
      simp only [z, map_sub, ← hx, ← hy, h, sub_self]
    obtain ⟨A, U, a, ha, B, hB⟩ :=
      moduleSheaf_coproduct_localGeneration K hK R I H V.unop z
    have hlocal (α : A) : (∐ H).val.map (a α).op z = 0 := by
      rw [hB α]
      apply Finset.sum_eq_zero
      intro i hi
      rw [PresheafOfModules.naturality_apply, hz]
      simp
    have hz0 : z = 0 := by
      have hle : Sieve.generate (Presieve.ofArrows U a) ≤
          Presheaf.equalizerSieve (F := (∐ H).val.presheaf) z 0 := by
        rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
        intro α
        change (∐ H).val.map (a α).op z = (∐ H).val.map (a α).op 0
        simpa using hlocal α
      apply (hF.isSeparated _
        (K.toGrothendieck.superset_covering hle (K.generate_mem_toGrothendieck ha))).ext
      intro W f hf
      exact hf
    exact sub_eq_zero.mp hz0
  have hm : Mono m := by
    constructor
    intro Z f g hfg
    ext V x
    apply hinj V
    exact congrArg (fun f ↦ f.val.app V x) hfg
  have hrange (V : C) (h : (∏ᶜ H).val.obj (op V)) :
      h ∈ Set.range (m.val.app (op V)) ↔
        ∃ (A : Type u) (U : A → C) (a : ∀ α : A, U α ⟶ V),
          Presieve.ofArrows U a ∈ K V ∧
          ∃ B : A → Finset I, ∀ (α : A) (i : I), i ∉ B α →
            (H i).val.map (a α).op ((Pi.π H i).val.app (op V) h) = 0 := by
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨A, U, a, ha, B, hB⟩ :=
        moduleSheaf_coproduct_localGeneration K hK R I H V x
      refine ⟨A, U, a, ha, B, ?_⟩
      intro α i hi
      have heq := congrArg (fun f : ∐ H ⟶ H i ↦ f.val.app (op V) x) (hmπ i)
      change (Pi.π H i).val.app (op V) (m.val.app (op V) x) = _ at heq
      rw [heq, ← PresheafOfModules.naturality_apply, hB α, hsum]
      simp only [hi, ↓reduceIte]
    · rintro ⟨A, U, a, ha, B, hB⟩
      have hlocal (α : A) :
          ∃ t, m.val.app (op (U α)) t = (∏ᶜ H).val.map (a α).op h := by
        refine ⟨∑ i ∈ B α, (Sigma.ι H i).val.app (op (U α))
          ((Pi.π H i).val.app (op (U α)) ((∏ᶜ H).val.map (a α).op h)), ?_⟩
        apply Concrete.Pi.map_ext H (SheafOfModules.evaluation R (op (U α)))
        intro j
        change (Pi.π H j).val.app _ (m.val.app _ _) = _
        have heq := congrArg (fun f : ∐ H ⟶ H j ↦ f.val.app (op (U α))
          (∑ i ∈ B α, (Sigma.ι H i).val.app (op (U α))
            ((Pi.π H i).val.app (op (U α)) ((∏ᶜ H).val.map (a α).op h)))) (hmπ j)
        change (Pi.π H j).val.app _ (m.val.app _ _) = _ at heq
        rw [heq, hsum]
        split_ifs with hj
        · rfl
        · change 0 = (Pi.π H j).val.app (op (U α)) ((∏ᶜ H).val.map (a α).op h)
          rw [PresheafOfModules.naturality_apply, hB α j hj]
      have hcover : Presheaf.imageSieve q h ∈ K.toGrothendieck V := by
        apply K.toGrothendieck.superset_covering _ (K.generate_mem_toGrothendieck ha)
        rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
        exact hlocal
      let t : Presieve.FamilyOfElements F (Presheaf.imageSieve q h).arrows :=
        fun W f hf ↦ Presheaf.localPreimage q h f hf
      have ht : t.Compatible := by
        intro Y₁ Y₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ w
        apply hinj (op W)
        change q.app _ (F.map g₁.op (t f₁ hf₁)) =
          q.app _ (F.map g₂.op (t f₂ hf₂))
        rw [NatTrans.naturality_apply, NatTrans.naturality_apply,
          Presheaf.app_localPreimage, Presheaf.app_localPreimage]
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, w]
      refine ⟨(hF _ hcover).amalgamate t ht, ?_⟩
      apply (hG.isSeparated _ hcover).ext
      intro W f hf
      change G.map f.op (q.app _ _) = G.map f.op h
      rw [← NatTrans.naturality_apply, (hF _ hcover).valid_glue ht]
      exact Presheaf.app_localPreimage q h f hf
  refine ⟨∐ H, m, Sigma.ι H, hm, hinj, hrange, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [hmπ]
  · intro i j hij
    simp [hmπ, Sigma.ι_π_of_ne _ hij]
  · exact ⟨coproductIsCoproduct H⟩
  · intro T
    refine ⟨?_, ?_⟩
    · intro f g h
      apply Sigma.hom_ext
      intro i
      exact congrFun h i
    · intro f
      exact ⟨Sigma.desc f, by funext i; simp⟩
  · have heq : Sigma.desc (fun i ↦ Sigma.ι H i ≫ m) = m := by
      apply Sigma.hom_ext
      intro i
      simp
    rw [heq]
    exact hm
  · intro V
    have heq : Sigma.desc (fun i ↦ Sigma.ι H i ≫ m) = m := by
      apply Sigma.hom_ext
      intro i
      simp
    rw [heq]

end CategoryTheory
