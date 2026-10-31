/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Types.Coequalizers
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# A specified sheafified relation quotient is a coequalizer

Source: Stacks Project, Sites, Tag 00WH; Groupoids, Tag 02VG; Categories, Tag 002F
(blueprint: lem-a1-specified-sheafified-relation-coequalizer).

The presheaf `coequalizer s.hom t.hom` is the sectionwise quotient: evaluation
preserves coequalizers, and `Types.coequalizerIso` identifies its sections with
`Function.Coequalizer`. Since the image relation is already an equivalence relation,
its generated equivalence relation is itself. Under this canonical identification,
`(coequalizer.π s.hom t.hom).app T a` is the class `[a]`; naturality gives the
restriction formula `[a] ↦ [A(f)(a)]`. This is also the interface used in
`AlgebraicGeometry.AlgebraicSpace.etale_atlas_presentation`.

No sheafification functor or `HasWeakSheafify` instance is assumed.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The quotient map into the specified sheafification, with actual data `π ≫ η`.
Source: Stacks Project, Groupoids, Tag 02VG; Sites, Tag 00WH
(blueprint: lem-a1-specified-sheafified-relation-coequalizer). -/
noncomputable def specifiedRelationQuotientMap {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {A B : Sheaf J (Type w)} (s t : B ⟶ A)
    (Q : Sheaf J (Type w)) (η : coequalizer s.hom t.hom ⟶ Q.obj) : A ⟶ Q :=
  ⟨coequalizer.π s.hom t.hom ≫ η⟩

/-- A specified universal sheafification of the sectionwise relation quotient is
its coequalizer, including the representative formula and the unique comparison
with every other coequalizer.
Source: Stacks Project, Sites, Tag 00WH; Groupoids, Tag 02VG; Categories, Tag 002F
(blueprint: lem-a1-specified-sheafified-relation-coequalizer).

Proof:
1. Naturality of s and t sends a witness r for a related pair to B(f)(r).
   Thus restrictions preserve the relation and descend to its quotient; the
   identity and composition laws descend from A. This is the pointwise
   presheaf coequalizer (def-weil-pbc-sites-and-cohomology).
2. The quotient projection identifies s(r) and t(r), so q equalizes s and t.
   An equalizing map b is constant on related pairs, by choosing a witness r.
   Hence d_T([a]) = b_T(a) is well defined.
3. Naturality of b proves naturality of d on representatives. Every class has
   a representative, so d is the unique map from the quotient with dπ = b.
   Conversely every map from the quotient gives an equalizing map from A.
4. Apply hη to d to obtain the unique c with ηc = d. Then qc = b and the
   displayed representative formula holds. If qc' = b, step 3 gives ηc' = d,
   and injectivity of hη gives c' = c (def-weil-pbc-sheafification).
5. A cocone on the parallel pair is determined by its equalizing arrow from A.
   Step 4 is exactly its colimit property (def-weil-pbc-category-colimit).
6. Apply step 4 to p to obtain the unique α. The other coequalizer applied to
   q gives the unique β. Uniqueness after precomposition with p gives βα = 1_Z,
   and uniqueness after precomposition with q gives αβ = 1_Q, in Lean's
   diagrammatic composition order. These identities make α an isomorphism.
-/
theorem specified_sheafified_relation_coequalizer {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (A B : Sheaf J (Type w)) (s t : B ⟶ A)
    (hinj : ∀ T : C, Function.Injective
      (fun r : B.obj.obj (op T) ↦ (s.hom.app (op T) r, t.hom.app (op T) r)))
    (hrel : ∀ T : C, _root_.Equivalence (fun a b : A.obj.obj (op T) ↦
      ∃ r : B.obj.obj (op T), s.hom.app (op T) r = a ∧ t.hom.app (op T) r = b))
    (Q : Sheaf J (Type w)) (η : coequalizer s.hom t.hom ⟶ Q.obj)
    (hη : ∀ H : Sheaf J (Type w),
      Function.Bijective (fun c : Q ⟶ H ↦ η ≫ c.hom)) :
    ∃ hq : s ≫ specifiedRelationQuotientMap s t Q η =
        t ≫ specifiedRelationQuotientMap s t Q η,
      (∀ H : Sheaf J (Type w),
        ∃ e : (Q ⟶ H) ≃ {b : A ⟶ H // s ≫ b = t ≫ b},
          ∀ c : Q ⟶ H, (e c).val = specifiedRelationQuotientMap s t Q η ≫ c) ∧
      (∀ (H : Sheaf J (Type w)) (b : A ⟶ H), s ≫ b = t ≫ b →
        ∃! c : Q ⟶ H, specifiedRelationQuotientMap s t Q η ≫ c = b ∧
          ∀ (T : C) (a : A.obj.obj (op T)),
            (η ≫ c.hom).app (op T) ((coequalizer.π s.hom t.hom).app (op T) a) =
              b.hom.app (op T) a) ∧
      Nonempty (IsColimit (Cofork.ofπ (specifiedRelationQuotientMap s t Q η) hq)) ∧
      (∀ (Z : Sheaf J (Type w)) (p : A ⟶ Z) (hp : s ≫ p = t ≫ p),
        IsColimit (Cofork.ofπ p hp) →
          ∃! α : Q ⟶ Z, specifiedRelationQuotientMap s t Q η ≫ α = p ∧
            IsIso α ∧ ∃! β : Z ⟶ Q, p ≫ β = specifiedRelationQuotientMap s t Q η ∧
              β ≫ α = 𝟙 Z ∧ α ≫ β = 𝟙 Q) := by
  classical
  -- Descent is already supplied by the chosen presheaf coequalizer.
  have _ := hinj
  have _ := hrel
  let q := specifiedRelationQuotientMap s t Q η
  have hq : s ≫ q = t ≫ q := by
    apply Sheaf.hom_ext
    exact coequalizer.condition_assoc s.hom t.hom η
  have hfactor : ∀ (H : Sheaf J (Type w)) (b : A ⟶ H), s ≫ b = t ≫ b →
      ∃! c : Q ⟶ H, q ≫ c = b := by
    intro H b hb
    have hb' : s.hom ≫ b.hom = t.hom ≫ b.hom := congrArg (fun f : B ⟶ H ↦ f.hom) hb
    obtain ⟨c, hc⟩ := (hη H).surjective (coequalizer.desc b.hom hb')
    change η ≫ c.hom = coequalizer.desc b.hom hb' at hc
    have hcb : q ≫ c = b := by
      apply Sheaf.hom_ext
      change (coequalizer.π s.hom t.hom ≫ η) ≫ c.hom = b.hom
      rw [Category.assoc, hc, coequalizer.π_desc]
    refine ⟨c, hcb, ?_⟩
    intro c' hc'
    apply (hη H).injective
    apply coequalizer.hom_ext
    have hc'' := congrArg (fun f : A ⟶ H ↦ f.hom) hc'
    have hcb' := congrArg (fun f : A ⟶ H ↦ f.hom) hcb
    exact (Category.assoc _ _ _).symm.trans
      ((hc''.trans hcb'.symm).trans (Category.assoc _ _ _))
  let hcolim : IsColimit (Cofork.ofπ q hq) :=
    Cofork.IsColimit.ofExistsUnique fun k ↦ hfactor k.pt k.π k.condition
  refine ⟨hq, ?_, ?_, ⟨hcolim⟩, ?_⟩
  · intro H
    exact ⟨Cofork.IsColimit.homIso hcolim H, fun _ ↦ rfl⟩
  · intro H b hb
    obtain ⟨c, hc, huniq⟩ := hfactor H b hb
    refine ⟨c, ⟨hc, ?_⟩, fun c' hc' ↦ huniq c' hc'.1⟩
    intro T a
    have h := congrArg (fun f : A ⟶ H ↦ f.hom) hc
    exact congrArg (fun k : A.obj ⟶ H.obj ↦ k.app (op T) a) h
  · intro Z p hp hpcolim
    obtain ⟨α, hα, hαuniq⟩ := hfactor Z p hp
    obtain ⟨β, hβ, hβuniq⟩ := Cofork.IsColimit.existsUnique hpcolim q hq
    change p ≫ β = q at hβ
    have hβα : β ≫ α = 𝟙 Z := by
      apply Cofork.IsColimit.hom_ext hpcolim
      change p ≫ (β ≫ α) = p ≫ 𝟙 Z
      rw [← Category.assoc, hβ, hα, Category.comp_id]
    have hαβ : α ≫ β = 𝟙 Q := by
      apply Cofork.IsColimit.hom_ext hcolim
      change q ≫ (α ≫ β) = q ≫ 𝟙 Q
      rw [← Category.assoc, hα, hβ, Category.comp_id]
    have hαiso : IsIso α := ⟨⟨β, hαβ, hβα⟩⟩
    exact ⟨α, ⟨hα, hαiso, β, ⟨hβ, hβα, hαβ⟩,
      fun β' hβ' ↦ hβuniq β' hβ'.1⟩, fun α' hα' ↦ hαuniq α' hα'.1⟩

end CategoryTheory
