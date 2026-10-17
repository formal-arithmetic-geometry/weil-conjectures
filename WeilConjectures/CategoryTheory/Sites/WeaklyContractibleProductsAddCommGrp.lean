/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractibleProducts

/-!
# Products of abelian sheaves on sites with enough weakly contractible objects

This is the analogue for abelian sheaves of
`WeilConjectures.CategoryTheory.Sites.WeaklyContractibleProducts`: if every object of a site is
covered by weakly contractible objects, epimorphisms of abelian sheaves are detected by
surjectivity on sections over weakly contractible objects, and for a tower of epimorphisms `F`
the map `1 - t` on a product `∏ Fₙ` is an epimorphism (Stacks 0947, 091J).

## Main results

- `AddCommGrpCat.epi_one_sub_of_epi`: for a tower of surjections of abelian groups, `1 - t` is
  surjective on the product.
- `CategoryTheory.GrothendieckTopology.epi_iff_surjective_of_forall_exists`: epimorphisms of
  abelian sheaves are detected on sections over weakly contractible objects.
- `CategoryTheory.GrothendieckTopology.epi_one_sub_of_forall_exists'`: for a tower of
  epimorphisms of abelian sheaves `F`, the map `1 - t` on a product `∏ Fₙ` is an epimorphism.
-/

@[expose] public section

universe w w' v u

open CategoryTheory Limits Opposite

namespace AddCommGrpCat

/-- For a tower `F` of abelian groups with surjective transitions, the map `1 - t` on a product
`∏ Fₙ` is surjective, where `t` has components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`: given `y`, the components
`xₙ` of a preimage are chosen inductively, `xₙ₊₁` lifting `xₙ - yₙ`. -/
lemma epi_one_sub_of_epi {F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} {P : Fan fun n : ℕ ↦ F.obj (op n)}
    (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE n.le_succ).op)) : Epi (𝟙 P.pt - t) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro y
  have hs (n : ℕ) := (AddCommGrpCat.epi_iff_surjective _).1 (hF n)
  let x : ∀ n : ℕ, F.obj (op n) := fun n ↦ Nat.rec (motive := fun n ↦ F.obj (op n)) 0
    (fun n xn ↦ (hs n (xn - P.proj n y)).choose) n
  have hx (n : ℕ) : F.map (homOfLE n.le_succ).op (x (n + 1)) = x n - P.proj n y :=
    (hs n _).choose_spec
  let hP' := isLimitOfPreserves (forget AddCommGrpCat.{u}) hP
  let z : P.pt := (Types.isLimitEquivSections hP').symm
    ⟨fun j ↦ x j.as, fun {i j} f ↦ by
      obtain ⟨i⟩ := i
      obtain ⟨j⟩ := j
      obtain rfl : i = j := Discrete.eq_of_hom f
      obtain rfl := Subsingleton.elim f (𝟙 _)
      simp⟩
  have hz (n : ℕ) : (P.proj n).hom z = x n :=
    Types.isLimitEquivSections_symm_apply hP' _ ⟨n⟩
  refine ⟨z, Concrete.isLimit_ext _ hP _ _ fun ⟨n⟩ ↦ ?_⟩
  have h₂ : (P.proj n).hom (t.hom z) = x n - (P.proj n).hom y :=
    (congrArg (fun f ↦ f.hom z) (ht n)).trans ((congrArg _ (hz (n + 1))).trans (hx n))
  rw [map_sub]
  exact (congrArg₂ (· - ·) (hz n) h₂).trans (sub_sub_cancel _ _)
end AddCommGrpCat

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] (P : C → Prop)
  (hP : ∀ V : C, ∃ (ι : Type w') (W : ι → C) (f : ∀ i, W i ⟶ V),
    (∀ i, P (W i)) ∧ Sieve.ofArrows W f ∈ J V)
  (hPW : ∀ W, P W → J.IsWeaklyContractible.{w} W)

include hP hPW in
/-- If every object of the site is covered by weakly contractible objects satisfying `P`, a
morphism of abelian sheaves is an epimorphism if and only if it is surjective on sections over
every object satisfying `P`. -/
lemma epi_iff_surjective_of_forall_exists {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) :
    Epi f ↔ ∀ W, P W → Function.Surjective (f.hom.app (op W)) := by
  rw [← Sheaf.isLocallySurjective_iff_epi']
  refine ⟨fun h W hW ↦ hPW W hW ((sheafCompose J (forget _)).map f)
    ((Presheaf.isLocallySurjective_iff_whisker_forget J _).1 h), fun h ↦ ⟨fun {V} s ↦ ?_⟩⟩
  obtain ⟨ι, W, g, hW, hcov⟩ := hP V
  refine J.superset_covering ?_ hcov
  rintro _ _ ⟨_, a, _, ⟨i⟩, rfl⟩
  exact (Presheaf.imageSieve _ s).downward_closed (h _ (hW i) _) a

include hP hPW in
/-- **Mittag-Leffler for towers of epimorphisms of abelian sheaves.** If every object of the
site is covered by weakly contractible objects, then for a tower `F` of abelian sheaves with
epimorphic transitions, the map `1 - t` on a product `∏ Fₙ` is an epimorphism, where `t` has
components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`: on sections over a weakly contractible object this is
`AddCommGrpCat.epi_one_sub_of_epi`. -/
lemma epi_one_sub_of_forall_exists' {F : ℕᵒᵖ ⥤ Sheaf J AddCommGrpCat.{w}}
    {Pf : Fan fun n : ℕ ↦ F.obj (op n)} (hPf : IsLimit Pf) (t : Pf.pt ⟶ Pf.pt)
    (ht : ∀ n : ℕ, t ≫ Pf.proj n = Pf.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE n.le_succ).op)) : Epi (𝟙 Pf.pt - t) := by
  rw [epi_iff_surjective_of_forall_exists P hP hPW]
  intro W hW
  let E := sheafToPresheaf J AddCommGrpCat.{w} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op W)
  have hPf' : IsLimit (Fan.mk Pf.pt Pf.proj) :=
    IsLimit.ofIsoLimit hPf (Cone.ext (Iso.refl _) fun ⟨_⟩ ↦ (Category.id_comp _).symm)
  have := AddCommGrpCat.epi_one_sub_of_epi (F := F ⋙ E)
    (isLimitFanMkObjOfIsLimit E _ _ hPf') (E.map t)
    (fun n ↦ by simpa [E] using congrArg E.map (ht n))
    (fun n ↦ (AddCommGrpCat.epi_iff_surjective _).2
      ((epi_iff_surjective_of_forall_exists P hP hPW _).1 (hF n) W hW))
  rw [AddCommGrpCat.epi_iff_surjective] at this
  exact this

end CategoryTheory.GrothendieckTopology
