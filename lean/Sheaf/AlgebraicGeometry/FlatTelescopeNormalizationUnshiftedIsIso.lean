/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import WeilConjectures.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.BoundedFlatShiftRepresentative
import Sheaf.AlgebraicGeometry.FlatTelescopeSumComparisonIsIso

/-! # Invertibility of normalized telescope morphisms

Source: steps 1--3 of lem-sc-flat-telescope-bounded-normalization-extension. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry


-- The five lemma only needs the four squares of the five-term exact sequences.
-- In particular, the fourth vertical map need not be the shift of the first.
private theorem cone_five_lemma
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T T' : Triangle C} (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (a : T.obj₁ ⟶ T'.obj₁) (b : T.obj₂ ⟶ T'.obj₂) (c : T.obj₃ ⟶ T'.obj₃)
    (d : T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₁⟦(1 : ℤ)⟧)
    (e : T.obj₂⟦(1 : ℤ)⟧ ⟶ T'.obj₂⟦(1 : ℤ)⟧)
    [IsIso a] [IsIso b] [IsIso d] [IsIso e]
    (h₁ : T.mor₁ ≫ b = a ≫ T'.mor₁)
    (h₂ : T.mor₂ ≫ c = b ≫ T'.mor₂)
    (h₃ : T.mor₃ ≫ d = c ≫ T'.mor₃)
    (h₄ : T.mor₁⟦(1 : ℤ)⟧' ≫ e = d ≫ T'.mor₁⟦(1 : ℤ)⟧') : IsIso c := by
  have : Mono c := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro A x hx
    obtain ⟨y, rfl⟩ := T.coyoneda_exact₃ hT x (by
      rw [← cancel_mono d, Category.assoc, h₃, reassoc_of% hx,
        zero_comp, zero_comp])
    have hy : (y ≫ b) ≫ T'.mor₂ = 0 := by
      rw [Category.assoc, ← h₂, ← Category.assoc]
      exact hx
    obtain ⟨z, hz⟩ := T'.coyoneda_exact₂ hT' (y ≫ b) hy
    have heq : y = (z ≫ inv a) ≫ T.mor₁ := by
      apply (cancel_mono b).1
      rw [Category.assoc, h₁]
      simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using hz
    rw [heq, Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]
  apply isIso_of_yoneda_map_bijective c
  intro A
  constructor
  · intro x y h
    exact (cancel_mono c).1 h
  · intro y
    let x₄ := y ≫ T'.mor₃ ≫ inv d
    have hx₄ : x₄ ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
      apply (cancel_mono e).1
      dsimp only [x₄]
      rw [Category.assoc, Category.assoc, h₄]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc,
        comp_distTriang_mor_zero₃₁ T' hT', comp_zero, zero_comp]
    obtain ⟨x, hx⟩ := T.coyoneda_exact₁ hT x₄ hx₄
    have hxc : x ≫ c ≫ T'.mor₃ = y ≫ T'.mor₃ := by
      rw [← h₃, ← Category.assoc, ← hx]
      dsimp only [x₄]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    obtain ⟨z, hz⟩ := T'.coyoneda_exact₃ hT' (y - x ≫ c) (by
      rw [Preadditive.sub_comp, Category.assoc, hxc, sub_self])
    refine ⟨x + (z ≫ inv b) ≫ T.mor₂, ?_⟩
    change (x + (z ≫ inv b) ≫ T.mor₂) ≫ c = y
    rw [Preadditive.add_comp, Category.assoc, h₂]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← hz]
    exact add_sub_cancel _ _


private theorem transport_naturality
    {C D : Type*} [Category C] [Category D] (F G : C ⥤ D) (P : C → Prop)
    (a : ∀ X, P X → (F.obj X ⟶ G.obj X))
    (hn : ∀ X X' hX hX' (s : X ⟶ X'), F.map s ≫ a X' hX' = a X hX ≫ G.map s)
    {X X' S S' : C} (hS : P S) (hS' : P S') (i : X ≅ S) (i' : X' ≅ S')
    (s : X ⟶ X') :
    F.map s ≫ (F.map i'.hom ≫ a S' hS' ≫ G.map i'.inv) =
      (F.map i.hom ≫ a S hS ≫ G.map i.inv) ≫ G.map s := by
  have h := congrArg (fun z ↦ F.map i.hom ≫ z ≫ G.map i'.inv)
    (hn S S' hS hS' (i.inv ≫ s ≫ i'.hom))
  simp only [Functor.map_comp, Category.assoc] at h
  rw [← Category.assoc (F.map i.hom) (F.map i.inv), ← F.map_comp,
    Iso.hom_inv_id, F.map_id, Category.id_comp] at h
  rw [← G.map_comp i'.hom i'.inv, Iso.hom_inv_id, G.map_id, Category.comp_id] at h
  simpa only [Category.assoc] using h



private theorem shifted_transport_comm
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
    {X : C} (s : X ⟶ X) (a : F.obj (X⟦(1 : ℤ)⟧) ⟶ G.obj (X⟦(1 : ℤ)⟧))
    (h : F.map (s⟦(1 : ℤ)⟧') ≫ a = a ≫ G.map (s⟦(1 : ℤ)⟧')) :
    (F.map s)⟦(1 : ℤ)⟧' ≫
        ((F.commShiftIso (1 : ℤ)).inv.app X ≫ a ≫
          (G.commShiftIso (1 : ℤ)).hom.app X) =
      ((F.commShiftIso (1 : ℤ)).inv.app X ≫ a ≫
          (G.commShiftIso (1 : ℤ)).hom.app X) ≫ (G.map s)⟦(1 : ℤ)⟧' := by
  rw [← Category.assoc, F.commShiftIso_inv_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map (s⟦(1 : ℤ)⟧')), h]
  simp only [Category.assoc]
  rw [G.commShiftIso_hom_naturality]

/-- A normalized natural comparison invertible on bounded-flat models
is invertible on each literal unshifted telescope model. This is the invertibility step, not a
construction of the comparison or of its shift equation.

Source: the sum and inverse-cone parts of steps 1--2 of
lem-sc-flat-telescope-bounded-normalization-extension, Stacks Tags 06YS and 06YJ.

Proof. First replace the sum of the bounded-flat stages by the telescope of
its finite partial sums. Every finite partial sum is bounded above and flat;
the standard split telescope augmentation identifies this telescope with the
sum in the homotopy category. Naturality for the finite-stage inclusions and
preservation of coproducts identify the comparison on this sum with the sum
of invertible bounded comparisons, hence it is invertible. The shift identity
identifies its translated component with a composite of isomorphisms.
Now use the triangle of one minus transition. Stage naturality gives its first
two squares; the normalized shift identity gives the connecting square.
Thus the comparison is a morphism between the two distinguished triangles.
Its first two components are invertible, so its cone component is invertible
by the two-out-of-three theorem for morphisms of distinguished triangles.
Use common flat refinements to identify the literal telescope with the
transition cone presentation used in this argument. The zero tower and empty
scheme have zero-object components, which are invertible; no common upper
bound on the whole tower is assumed.
(blueprint: lem-sc-flat-telescope-normalization-unshifted-is-iso). -/
theorem flat_telescope_normalization_unshifted_isIso
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ⟶
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X))
    (hαnat : (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X) (hX' : flatTelescopeShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX') =
            (α X hX) ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s))
    (hαshift :
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩) ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, htel, Or.inl rfl⟩)⟦(1 : ℤ)⟧')
    (hαbounded : ∀ (X : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (hX : flatTelescopeShiftRepresentative Y X),
      boundedFlatShiftRepresentative Y X → IsIso (α X hX)) :
    ∀ (P : CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (htel : isFlatTelescope Y P),
      IsIso (α ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)
        ⟨P, htel, Or.inl rfl⟩) := by
  intro P htel
  obtain ⟨E, t, hb, hf, rfl⟩ := htel
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let H := HomotopyCategory A (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let F := derivedPullback f
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨sF, hF⟩, _⟩ :=
    (derivedPullback_spec f)
  let : F.CommShift ℤ := sF
  have : F.IsTriangulated := hF
  let L : H ⥤ schemeDerivedCategory Z := DerivedCategory.Qh ⋙ F
  let G : H ⥤ schemeDerivedCategory Z :=
    (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Qh : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
        schemeDerivedCategory Z)
  obtain ⟨R, hR, ⟨i⟩, h₀⟩ :=
    exists_flat_telescope_sum_comparison_isIso f α hαnat hαbounded E hb hf
  let X := q.obj (∐ E)
  let S := q.obj R
  let hS : flatTelescopeShiftRepresentative Y S := ⟨R, hR, Or.inl rfl⟩
  let hS' : flatTelescopeShiftRepresentative Y (S⟦(1 : ℤ)⟧) := ⟨R, hR, Or.inr rfl⟩
  let i' : X⟦(1 : ℤ)⟧ ≅ S⟦(1 : ℤ)⟧ := (shiftFunctor H (1 : ℤ)).mapIso i
  let a : L.obj X ⟶ G.obj X := L.map i.hom ≫ α S hS ≫ G.map i.inv
  let a' : L.obj (X⟦(1 : ℤ)⟧) ⟶ G.obj (X⟦(1 : ℤ)⟧) :=
    L.map i'.hom ≫ α (S⟦(1 : ℤ)⟧) hS' ≫ G.map i'.inv
  have : IsIso (α S hS) := h₀
  have : IsIso (α (S⟦(1 : ℤ)⟧) hS') := by
    have : IsIso (α (S⟦(1 : ℤ)⟧) hS' ≫ (G.commShiftIso (1 : ℤ)).hom.app S) := by
      rw [hαshift R hR]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((G.commShiftIso (1 : ℤ)).hom.app S)
  have : IsIso a := by dsimp only [a]; infer_instance
  have : IsIso a' := by dsimp only [a']; infer_instance
  let p := flatTelescopeDifferential E t
  let C := CochainComplex.mappingCone.triangleh p
  let hC : flatTelescopeShiftRepresentative Y C.obj₃ :=
    ⟨CochainComplex.mappingCone p, ⟨E, t, hb, hf, rfl⟩, Or.inl rfl⟩
  let c := α C.obj₃ hC
  let T := L.mapTriangle.obj C
  let T' := G.mapTriangle.obj C
  have hT : T ∈ distTriang (schemeDerivedCategory Z) :=
    L.map_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished p)
  have hT' : T' ∈ distTriang (schemeDerivedCategory Z) :=
    G.map_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished p)
  let d : (L.obj X)⟦(1 : ℤ)⟧ ⟶ (G.obj X)⟦(1 : ℤ)⟧ :=
    (L.commShiftIso (1 : ℤ)).inv.app X ≫ a' ≫ (G.commShiftIso (1 : ℤ)).hom.app X
  have : IsIso d := by dsimp only [d]; infer_instance
  have hn₁ : L.map C.mor₁ ≫ a = a ≫ G.map C.mor₁ :=
    transport_naturality L G _ α hαnat hS hS i i C.mor₁
  have hn₂ : L.map C.mor₂ ≫ c = a ≫ G.map C.mor₂ := by
    simpa only [Iso.refl_hom, Iso.refl_inv, L.map_id, G.map_id, Category.id_comp,
      Category.comp_id] using
      transport_naturality L G _ α hαnat hS hC i (Iso.refl _) C.mor₂
  have hn₃ : L.map C.mor₃ ≫ a' = c ≫ G.map C.mor₃ := by
    simpa only [Iso.refl_hom, Iso.refl_inv, L.map_id, G.map_id, Category.id_comp,
      Category.comp_id] using
      transport_naturality L G _ α hαnat hC hS' (Iso.refl _) i' C.mor₃
  have hn₄ : L.map ((q.map p)⟦(1 : ℤ)⟧') ≫ a' =
      a' ≫ G.map ((q.map p)⟦(1 : ℤ)⟧') :=
    transport_naturality L G _ α hαnat hS' hS' i' i' ((q.map p)⟦(1 : ℤ)⟧')
  have hc : IsIso c := by
    refine cone_five_lemma hT hT' a a c d d hn₁ hn₂ ?_ ?_
    · change (L.map C.mor₃ ≫ (L.commShiftIso (1 : ℤ)).hom.app X) ≫ d =
        c ≫ G.map C.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app X
      dsimp only [d]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
      rw [← Category.assoc, hn₃, Category.assoc]
    · change (L.map (q.map p))⟦(1 : ℤ)⟧' ≫ d = d ≫ (G.map (q.map p))⟦(1 : ℤ)⟧'
      exact shifted_transport_comm L G (q.map p) a' hn₄
  exact hc

end AlgebraicGeometry
