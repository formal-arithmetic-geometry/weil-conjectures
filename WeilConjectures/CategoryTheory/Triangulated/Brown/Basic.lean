/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.FiveLemma
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Compact objects and Brown functors in pretriangulated categories

Let `C` be a pretriangulated category whose `Hom`-types live in `Type w`. We set up the
vocabulary for Brown representability (Neeman):

* an object `X` is *compact* if every morphism from `X` to a coproduct (indexed by a type in
  `Type w`) factors through a finite partial sum;
* a *Brown functor* is a cohomological functor `H : Cᵒᵖ ⥤ AddCommGrpCat` sending coproducts to
  products;
* `C` *has Brown representability* if every additive Brown functor is representable.

We show that Brown representability makes every coproduct-preserving triangulated functor a left
adjoint, and that it is inherited by a Bousfield localization `L : C ⥤ D` (a triangulated left
adjoint with fully faithful right adjoint) preserving coproducts.

## Main definitions

- `CategoryTheory.Pretriangulated.IsCompactObject`: compact objects.
- `CategoryTheory.Pretriangulated.IsCompactGeneratingFamily`: a family of compact generators,
  closed under shifts in the sense that all shifts of its members are compact and detect zero.
- `CategoryTheory.Pretriangulated.IsBrownFunctor`: cohomological functors sending coproducts to
  products.
- `CategoryTheory.Pretriangulated.HasBrownRepresentability`: every additive Brown functor is
  representable.

## Main statements

- `CategoryTheory.Pretriangulated.HasBrownRepresentability.isLeftAdjoint`: under Brown
  representability, a triangulated functor preserving coproducts is a left adjoint.
- `CategoryTheory.Pretriangulated.HasBrownRepresentability.of_adjunction`: Brown
  representability descends along a coproduct-preserving triangulated left adjoint whose right
  adjoint is fully faithful.

The representability theorem for compactly generated categories is
`CategoryTheory.Pretriangulated.IsCompactGeneratingFamily.hasBrownRepresentability`, in
`WeilConjectures.CategoryTheory.Triangulated.Brown.Representability`.
-/

@[expose] public section

universe w u u'

namespace CategoryTheory.Pretriangulated

open Limits Opposite Preadditive

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Functoriality of a contravariant functor to abelian groups, applied to an element. -/
lemma _root_.CategoryTheory.Functor.map_op_comp_apply {D : Type*} [Category* D]
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{w}) {A B E : D} (f : A ⟶ B) (g : B ⟶ E) (x : H.obj (op E)) :
    H.map (f ≫ g).op x = H.map f.op (H.map g.op x) := by
  rw [op_comp, H.map_comp, ConcreteCategory.comp_apply]

/-- An object `X` of a pretriangulated category is *compact* if every morphism from `X` to a
coproduct indexed by a type in `Type w` factors through a finite partial sum. -/
def IsCompactObject (X : C) : Prop :=
  ∀ ⦃J : Type w⦄ (f : J → C) (c : Cofan f), IsColimit c → ∀ φ : X ⟶ c.pt,
    ∃ (s : Finset J) (ψ : ∀ j, X ⟶ f j), φ = ∑ j ∈ s, ψ j ≫ c.inj j

/-- A family `S` of objects is a family of *compact generators* if all shifts of its members
are compact and they detect zero objects: an object `Y` with `Hom(S i⟦n⟧, Y) = 0` for all `i`
and `n` is zero. -/
structure IsCompactGeneratingFamily {ι : Type w} (S : ι → C) : Prop where
  isCompactObject (i : ι) (n : ℤ) : IsCompactObject ((S i)⟦n⟧)
  isZero (Y : C) : (∀ (i : ι) (n : ℤ) (φ : (S i)⟦n⟧ ⟶ Y), φ = 0) → IsZero Y

/-- A *Brown functor* is a functor `H : Cᵒᵖ ⥤ AddCommGrpCat` which is cohomological (it sends a
distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` to an exact sequence `H Z ⟶ H Y ⟶ H X`) and sends
coproducts in `C` (indexed by types in `Type w`) to products. -/
structure IsBrownFunctor (H : Cᵒᵖ ⥤ AddCommGrpCat.{w}) : Prop where
  exact (T : Triangle C) (hT : T ∈ distTriang C) (x : H.obj (op T.obj₂))
    (hx : H.map T.mor₁.op x = 0) : ∃ y, H.map T.mor₂.op y = x
  bijective {J : Type w} (f : J → C) (c : Cofan f) (hc : IsColimit c) :
    Function.Bijective (fun (x : H.obj (op c.pt)) (j : J) ↦ H.map (c.inj j).op x)

/-- A pretriangulated category *has Brown representability* if every additive Brown functor
`H` is representable: there are `X` and `u ∈ H X` such that `φ ↦ H φ u` is a bijection
`Hom(Y, X) ≃ H Y` for every `Y`. -/
def HasBrownRepresentability (C : Type u) [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] : Prop :=
  ∀ (H : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (_ : H.Additive), IsBrownFunctor H →
    ∃ (X : C) (u : H.obj (op X)), ∀ Y : C, Function.Bijective (fun φ : Y ⟶ X ↦ H.map φ.op u)

section BrownMap

variable (H : Cᵒᵖ ⥤ AddCommGrpCat.{w}) [H.Additive] {X : C} (u : H.obj (op X))

/-- The additive map `Hom(Y, X) → H Y`, `φ ↦ H φ u`, attached to `u ∈ H X`. -/
noncomputable def brownHom (Y : C) : (Y ⟶ X) →+ H.obj (op Y) where
  toFun φ := H.map φ.op u
  map_zero' := by simp
  map_add' φ ψ := by simp [op_add, H.map_add]

@[simp]
lemma brownHom_apply {Y : C} (φ : Y ⟶ X) : brownHom H u Y φ = H.map φ.op u := rfl

lemma brownHom_comp {Y Y' : C} (g : Y' ⟶ Y) (φ : Y ⟶ X) :
    brownHom H u Y' (g ≫ φ) = H.map g.op (brownHom H u Y φ) := by
  simp

end BrownMap

lemma IsBrownFunctor.map_mor₁_map_mor₂ {H : Cᵒᵖ ⥤ AddCommGrpCat.{w}} [H.Additive]
    (T : Triangle C) (hT : T ∈ distTriang C) (y : H.obj (op T.obj₃)) :
    H.map T.mor₁.op (H.map T.mor₂.op y) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← H.map_comp, ← op_comp, comp_distTriang_mor_zero₁₂ T hT]
  simp

lemma IsBrownFunctor.functionExact {H : Cᵒᵖ ⥤ AddCommGrpCat.{w}} [H.Additive]
    (hH : IsBrownFunctor H) (T : Triangle C) (hT : T ∈ distTriang C) :
    Function.Exact (H.map T.mor₂.op) (H.map T.mor₁.op) := fun x ↦
  ⟨fun hx ↦ hH.exact T hT x hx, fun ⟨y, hy⟩ ↦ hy ▸ map_mor₁_map_mor₂ T hT y⟩

/-- The functor `Hom(-, Y)` is a Brown functor. -/
lemma isBrownFunctor_preadditiveYoneda (Y : C) : IsBrownFunctor (preadditiveYoneda.obj Y) where
  exact T hT x hx := by
    obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ T hT x hx
    exact ⟨y, hy.symm⟩
  bijective f c hc := by
    refine ⟨fun a b h ↦ Cofan.IsColimit.hom_ext hc _ _ fun j ↦ congrFun h j, fun g ↦ ?_⟩
    exact ⟨Cofan.IsColimit.desc hc g, funext fun j ↦ Cofan.IsColimit.fac hc g j⟩

section Functor

variable {D : Type u'} [Category.{w} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- If `F : C ⥤ D` is triangulated and preserves coproducts, then `H ∘ F` is a Brown functor
for every Brown functor `H` on `D`. -/
lemma IsBrownFunctor.comp {H : Dᵒᵖ ⥤ AddCommGrpCat.{w}} (hH : IsBrownFunctor H) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [∀ J : Type w, PreservesColimitsOfShape (Discrete J) F] :
    IsBrownFunctor (F.op ⋙ H) where
  exact T hT x hx := hH.exact (F.mapTriangle.obj T) (F.map_distinguished T hT) x hx
  bijective {J} f c hc := by
    have := hH.bijective (fun j ↦ F.obj (f j)) _ (isColimitCofanMkObjOfIsColimit F f c.inj hc)
    exact this

/-- Under Brown representability, a triangulated functor `F : C ⥤ D` preserving coproducts is a
left adjoint: for every `Y`, the Brown functor `Hom(F -, Y)` is representable. -/
lemma HasBrownRepresentability.isLeftAdjoint (hC : HasBrownRepresentability C) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [∀ J : Type w, PreservesColimitsOfShape (Discrete J) F] :
    F.IsLeftAdjoint := by
  have hrep (Y : D) := hC (F.op ⋙ preadditiveYoneda.obj Y) inferInstance
    ((isBrownFunctor_preadditiveYoneda Y).comp F)
  choose G ε hε using hrep
  let e (X : C) (Y : D) : (X ⟶ G Y) ≃ (F.obj X ⟶ Y) := Equiv.ofBijective _ (hε Y X)
  have he (X : C) (Y : D) (φ : X ⟶ G Y) : e X Y φ = F.map φ ≫ ε Y := rfl
  let adj := Adjunction.adjunctionOfEquivRight (G_obj := G) (fun X Y ↦ (e X Y).symm)
    (fun X' X Y f g ↦ by
      apply (e X' Y).injective
      rw [Equiv.apply_symm_apply, he, F.map_comp, Category.assoc, ← he,
        Equiv.apply_symm_apply])
  exact adj.isLeftAdjoint

/-- **Brown representability descends along Bousfield localizations.** Let `L : C ⥤ D` be a
triangulated functor preserving coproducts, with a fully faithful right adjoint `R` (the counit
of `L ⊣ R` is an isomorphism). If `C` has Brown representability, so does `D`.

For a Brown functor `H` on `D`, `H ∘ L` is represented by some `M`; then `M` is right
orthogonal to the kernel of `L`, hence the unit `M ⟶ R L M` is an isomorphism, and `L M`
represents `H`. -/
lemma HasBrownRepresentability.of_adjunction (hC : HasBrownRepresentability C) {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) [IsIso adj.counit] [L.CommShift ℤ] [L.IsTriangulated]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) L] :
    HasBrownRepresentability D := by
  intro H _ hH
  have : R.IsRightAdjoint := adj.isRightAdjoint
  obtain ⟨M, u, hu⟩ := hC (L.op ⋙ H) inferInstance (hH.comp L)
  -- `M` is right orthogonal to the kernel of `L`.
  have horth (Z : C) (hZ : IsZero (L.obj Z)) (φ : Z ⟶ M) : φ = 0 := by
    apply (hu Z).1
    exact (AddCommGrpCat.subsingleton_of_isZero (H.map_isZero hZ.op)).elim _ _
  have hLη : IsIso (L.map (adj.unit.app M)) := by
    have : L.map (adj.unit.app M) = inv (adj.counit.app (L.obj M)) :=
      by
        rw [← cancel_mono (adj.counit.app (L.obj M)), IsIso.inv_hom_id]
        exact adj.left_triangle_components M
    rw [this]
    infer_instance
  -- The unit at `M` is an isomorphism.
  have hη : IsIso (adj.unit.app M) := by
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (adj.unit.app M)
    have hLZ : IsZero (L.obj Z) :=
      Triangle.isZero₃_of_isIso₁ _ (L.map_distinguished _ hT) hLη
    have hh : h = 0 := by
      have hLZ' : IsZero (L.obj (Z⟦(-1 : ℤ)⟧)) :=
        ((shiftFunctor D (-1 : ℤ)).map_isZero hLZ).of_iso ((L.commShiftIso (-1 : ℤ)).app Z)
      have h0 := horth _ hLZ' (Triangle.invRotate (Triangle.mk (adj.unit.app M) g h)).mor₁
      apply (shiftFunctor C (-1 : ℤ)).map_injective
      simpa [Triangle.invRotate] using h0
    have hZ : IsZero Z := by
      rw [IsZero.iff_id_eq_zero]
      obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₃ _ hT (𝟙 Z) (by simp [hh])
      have ha0 : a = 0 := by
        have : (adj.homEquiv _ _).symm a = 0 := hLZ.eq_of_src _ _
        rw [← (adj.homEquiv _ _).apply_symm_apply a, this, Adjunction.homEquiv_unit,
          Functor.map_zero, comp_zero]
      rw [ha, ha0, zero_comp]
    exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hZ
  refine ⟨L.obj M, u, fun Y ↦ ?_⟩
  have hR := adj.fullyFaithfulROfIsIsoCounit
  have hid (φ : Y ⟶ L.obj M) :
      inv (adj.counit.app Y) ≫ L.map (R.map φ ≫ inv (adj.unit.app M)) = φ := by
    have h₁ : L.map (inv (adj.unit.app M)) = adj.counit.app (L.obj M) := by
      rw [Functor.map_inv, IsIso.inv_eq_of_hom_inv_id (adj.left_triangle_components M)]
    have h₂ := adj.counit.naturality φ
    dsimp at h₂
    rw [L.map_comp, h₁, h₂, IsIso.inv_hom_id_assoc]
  have key : (fun φ : Y ⟶ L.obj M ↦ H.map φ.op u) =
      (fun x ↦ H.map (inv (adj.counit.app Y)).op x) ∘
        (fun ψ : R.obj Y ⟶ M ↦ (L.op ⋙ H).map ψ.op u) ∘
        (fun χ ↦ χ ≫ inv (adj.unit.app M)) ∘ (fun φ ↦ R.map φ) := by
    funext φ
    simp only [Function.comp_apply, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
    erw [← ConcreteCategory.comp_apply, ← H.map_comp, ← op_comp, hid]
    rfl
  rw [key]
  refine (ConcreteCategory.bijective_of_isIso (H.map (inv (adj.counit.app Y)).op)).comp
    ((hu _).comp (Function.Bijective.comp ?_ (hR.map_bijective Y (L.obj M))))
  exact (Function.bijective_iff_has_inverse).2 ⟨fun χ ↦ χ ≫ adj.unit.app M,
    fun χ ↦ by simp, fun χ ↦ by simp⟩

end Functor

end CategoryTheory.Pretriangulated
