/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentAux

/-!
# Matching objects of truncated simplicial objects as finite limits

For an `r`-truncated simplicial object `K` and `n : ℕ`, the `n`-th matching object is the limit
of `K` over the finite category `MatchingIndex r n` of maps `Δ ⟶ [n]` with `Δ` of dimension
`< n`. We relate limit cones of this diagram to the universal property used in
`TruncatedFiniteSplitEtaleHypercover`.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The indexing category of the `n`-th matching object of an `r`-truncated simplicial
object: maps `Δ ⟶ [n]` with `Δ` of dimension `< n`. -/
structure MatchingIndex (r n : ℕ) where
  /-- The source simplex. -/
  obj : SimplexCategory.Truncated r
  lt : obj.obj.len < n
  /-- The map to `[n]`. -/
  hom : obj.obj ⟶ SimplexCategory.mk n

namespace MatchingIndex

variable {r n : ℕ}

instance : SmallCategory (MatchingIndex r n) where
  Hom p q := {α : p.obj ⟶ q.obj // α.hom ≫ q.hom = p.hom}
  id p := ⟨𝟙 _, Category.id_comp _⟩
  comp f g := ⟨f.1 ≫ g.1, by
    rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc, g.2, f.2]⟩
  id_comp f := Subtype.ext (Category.id_comp _)
  comp_id f := Subtype.ext (Category.comp_id _)
  assoc f g h := Subtype.ext (Category.assoc _ _ _)

instance : Finite (MatchingIndex r n) :=
  Finite.of_injective (fun p : MatchingIndex r n ↦
    (⟨p.obj, p.hom⟩ : Σ Δ : SimplexCategory.Truncated r, Δ.obj ⟶ SimplexCategory.mk n)) (by
      rintro ⟨Δ, h, θ⟩ ⟨Δ', h', θ'⟩ e
      simp only [Sigma.mk.injEq] at e
      obtain ⟨rfl, e⟩ := e
      cases e
      rfl)

instance (p q : MatchingIndex r n) : Finite (p ⟶ q) :=
  inferInstanceAs (Finite {α : p.obj ⟶ q.obj // α.hom ≫ q.hom = p.hom})

noncomputable instance : FinCategory (MatchingIndex r n) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

/-- The morphism of `MatchingIndex r n` given by precomposition. -/
def homMk {Δ Δ' : SimplexCategory.Truncated r} (h : Δ.obj.len < n) (h' : Δ'.obj.len < n)
    (α : Δ' ⟶ Δ) (θ : Δ.obj ⟶ SimplexCategory.mk n) :
    (⟨Δ', h', α.hom ≫ θ⟩ : MatchingIndex r n) ⟶ ⟨Δ, h, θ⟩ :=
  ⟨α, rfl⟩

end MatchingIndex

variable {C : Type u} [Category.{v} C] {r : ℕ}

/-- The diagram whose limit is the `n`-th matching object. -/
abbrev matchingDiagram (K : (SimplexCategory.Truncated r)ᵒᵖ ⥤ C) (n : ℕ) :
    (MatchingIndex r n)ᵒᵖ ⥤ C where
  obj p := K.obj (op p.unop.obj)
  map f := K.map f.unop.1.op
  map_id _ := K.map_id _
  map_comp f g := K.map_comp f.unop.1.op g.unop.1.op

/-- The cone over the matching diagram given by compatible projections. -/
abbrev matchingCone (K : (SimplexCategory.Truncated r)ᵒᵖ ⥤ C) (n : ℕ) (M : C)
    (proj : ∀ Δ : SimplexCategory.Truncated r, Δ.obj.len < n →
      (Δ.obj ⟶ SimplexCategory.mk n) → (M ⟶ K.obj (op Δ)))
    (nat : ∀ (Δ Δ' : SimplexCategory.Truncated r) (h : Δ.obj.len < n) (h' : Δ'.obj.len < n)
      (α : Δ' ⟶ Δ) (θ : Δ.obj ⟶ SimplexCategory.mk n),
      proj Δ h θ ≫ K.map α.op = proj Δ' h' (α.hom ≫ θ)) :
    Cone (matchingDiagram K n) where
  pt := M
  π :=
    { app p := proj p.unop.obj p.unop.lt p.unop.hom
      naturality p q f := by
        have := nat p.unop.obj q.unop.obj p.unop.lt q.unop.lt f.unop.1 p.unop.hom
        rw [f.unop.2] at this
        exact (Category.id_comp _).trans this.symm }

/-- The projections of a cone over the matching diagram are compatible. -/
lemma matchingCone_nat {K : (SimplexCategory.Truncated r)ᵒᵖ ⥤ C} {n : ℕ}
    (s : Cone (matchingDiagram K n)) (Δ Δ' : SimplexCategory.Truncated r)
    (h : Δ.obj.len < n) (h' : Δ'.obj.len < n) (α : Δ' ⟶ Δ)
    (θ : Δ.obj ⟶ SimplexCategory.mk n) :
    s.π.app (op ⟨Δ, h, θ⟩) ≫ K.map α.op = s.π.app (op ⟨Δ', h', α.hom ≫ θ⟩) :=
  s.w (MatchingIndex.homMk h h' α θ).op

/-- A limit cone over the matching diagram has the universal property of the matching
object. -/
lemma matchingCone_universal {K : (SimplexCategory.Truncated r)ᵒᵖ ⥤ C} {n : ℕ} {M : C}
    {proj : ∀ Δ : SimplexCategory.Truncated r, Δ.obj.len < n →
      (Δ.obj ⟶ SimplexCategory.mk n) → (M ⟶ K.obj (op Δ))}
    {nat : ∀ (Δ Δ' : SimplexCategory.Truncated r) (h : Δ.obj.len < n) (h' : Δ'.obj.len < n)
      (α : Δ' ⟶ Δ) (θ : Δ.obj ⟶ SimplexCategory.mk n),
      proj Δ h θ ≫ K.map α.op = proj Δ' h' (α.hom ≫ θ)}
    (hM : IsLimit (matchingCone K n M proj nat)) (T : C)
    (p : ∀ Δ : SimplexCategory.Truncated r, Δ.obj.len < n →
      (Δ.obj ⟶ SimplexCategory.mk n) → (T ⟶ K.obj (op Δ)))
    (hp : ∀ (Δ Δ' : SimplexCategory.Truncated r) (h : Δ.obj.len < n) (h' : Δ'.obj.len < n)
      (α : Δ' ⟶ Δ) (θ : Δ.obj ⟶ SimplexCategory.mk n),
      p Δ h θ ≫ K.map α.op = p Δ' h' (α.hom ≫ θ)) :
    ∃! f : T ⟶ M, ∀ (Δ : SimplexCategory.Truncated r) (h : Δ.obj.len < n)
      (θ : Δ.obj ⟶ SimplexCategory.mk n), f ≫ proj Δ h θ = p Δ h θ :=
  ⟨hM.lift (matchingCone K n T p hp), fun Δ h θ ↦ hM.fac (matchingCone K n T p hp) (op ⟨Δ, h, θ⟩),
    fun f hf ↦ hM.uniq (matchingCone K n T p hp) f fun _ ↦ hf _ _ _⟩

/-- Compatible projections with the universal property of the matching object form a limit
cone. -/
noncomputable def isLimitMatchingCone {K : (SimplexCategory.Truncated r)ᵒᵖ ⥤ C} {n : ℕ}
    {M : C} {proj : ∀ Δ : SimplexCategory.Truncated r, Δ.obj.len < n →
      (Δ.obj ⟶ SimplexCategory.mk n) → (M ⟶ K.obj (op Δ))}
    {nat : ∀ (Δ Δ' : SimplexCategory.Truncated r) (h : Δ.obj.len < n) (h' : Δ'.obj.len < n)
      (α : Δ' ⟶ Δ) (θ : Δ.obj ⟶ SimplexCategory.mk n),
      proj Δ h θ ≫ K.map α.op = proj Δ' h' (α.hom ≫ θ)}
    (H : ∀ (T : C) (p : ∀ Δ : SimplexCategory.Truncated r, Δ.obj.len < n →
      (Δ.obj ⟶ SimplexCategory.mk n) → (T ⟶ K.obj (op Δ))),
      (∀ (Δ Δ' : SimplexCategory.Truncated r) (h : Δ.obj.len < n) (h' : Δ'.obj.len < n)
        (α : Δ' ⟶ Δ) (θ : Δ.obj ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ K.map α.op = p Δ' h' (α.hom ≫ θ)) →
      ∃! f : T ⟶ M, ∀ (Δ : SimplexCategory.Truncated r) (h : Δ.obj.len < n)
        (θ : Δ.obj ⟶ SimplexCategory.mk n), f ≫ proj Δ h θ = p Δ h θ) :
    IsLimit (matchingCone K n M proj nat) where
  lift s := (H s.pt (fun Δ h θ ↦ s.π.app (op ⟨Δ, h, θ⟩)) (matchingCone_nat s)).exists.choose
  fac s q := (H s.pt (fun Δ h θ ↦ s.π.app (op ⟨Δ, h, θ⟩)) (matchingCone_nat s)).exists.choose_spec
    q.unop.obj q.unop.lt q.unop.hom
  uniq s _ hm := (H s.pt (fun Δ h θ ↦ s.π.app (op ⟨Δ, h, θ⟩)) (matchingCone_nat s)).unique
    (fun Δ h θ ↦ hm (op ⟨Δ, h, θ⟩))
    (H s.pt (fun Δ h θ ↦ s.π.app (op ⟨Δ, h, θ⟩)) (matchingCone_nat s)).exists.choose_spec

/-- The projections of a cone over the matching diagram. -/
abbrev matchingProj {K : (SimplexCategory.Truncated r)ᵒᵖ ⥤ C} {n : ℕ}
    (s : Cone (matchingDiagram K n)) (Δ : SimplexCategory.Truncated r) (h : Δ.obj.len < n)
    (θ : Δ.obj ⟶ SimplexCategory.mk n) : s.pt ⟶ K.obj (op Δ) :=
  s.π.app (op ⟨Δ, h, θ⟩)

lemma matchingCone_eta {K : (SimplexCategory.Truncated r)ᵒᵖ ⥤ C} {n : ℕ}
    (s : Cone (matchingDiagram K n)) :
    matchingCone K n s.pt (matchingProj s) (matchingCone_nat s) = s := rfl

end AlgebraicGeometry
