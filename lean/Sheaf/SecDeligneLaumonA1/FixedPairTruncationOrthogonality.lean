/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Authors: SHEAF contributors
-/
module

public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import WeilConjectures.CategoryTheory.Triangulated.TStructure.ShortExact
import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Truncation adjunctions and orthogonality for fixed pairs

Source: BBD, *Faisceaux pervers*, Propositions 1.3.3–1.3.4, printed pp. 29–30
(blueprint: lem-a1-fixed-pair-truncation-orthogonality).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

open Triangulated

set_option linter.unusedVariables false in
/-- The canonical truncations of a t-structure lift to pairs fixed by a
triangulated autoequivalence, and their adjunctions give the right-orthogonality
criterion for the nonnegative part.  Source: BBD, *Faisceaux pervers*,
Propositions 1.3.3–1.3.4, printed pp. 29–30, with the fixed-pair consequence of
uniqueness and naturality made explicit.

Proof (to be formalised in stage 3), following the node's steps:

1. (uses def-weil-t-structure, def-weil-endofunctor-fixed-pair-category,
   lem-weil-heart-short-exact-triangles) Fix `n`.  Since `Φ = E.functor` is exact it
   commutes with the shift, so it preserves `T^{≤n}` and `T^{≥n+1}` for every `n`.
   Applying `Φ` to the truncation triangle `τ^{≤n}X → X → τ^{≥n+1}X →` gives a
   distinguished triangle with outer terms in `T^{≤n}` and `T^{≥n+1}`; uniqueness of
   truncation triangles (lem-weil-heart-short-exact-triangles, clause 1) gives unique
   isomorphisms `c_X : Φ τ^{≤n} X ≅ τ^{≤n} Φ X`, `d_X : Φ τ^{≥n+1} X ≅ τ^{≥n+1} Φ X`
   with `ι_{ΦX} c_X = Φ(ι_X)` and `d_X Φ(π_X) = π_{ΦX}`.  Both are natural by the
   right (resp. left) truncation adjunction.  For a fixed pair `(X, θ)` put
   `θ^{≤n} = τ^{≤n}(θ) ∘ c_X` and `θ^{≥n+1} = τ^{≥n+1}(θ) ∘ d_X`; then
   `ι_X θ^{≤n} = θ Φ(ι_X)`, so `ι_X` (dually `π_X`) is a morphism of fixed pairs, and
   naturality of `c`, `d` shows that `τ^{≤n} f`, `τ^{≥n+1} f` are morphisms of fixed
   pairs when `f` is.  Identities and composites are those of `C`, so these are
   functors on fixed pairs lifting `τ^{≤n}`, `τ^{≥n+1}` (every `τ^{≥m}` is a `τ^{≥n+1}`).
2. (uses def-weil-endofunctor-fixed-pair-category, lem-weil-heart-short-exact-triangles)
   Let `(M, θ_M)` be a fixed pair with `M ∈ T^{≤n}`.  The bijection `h ↦ ι_X h`,
   `Hom(M, τ^{≤n}X) → Hom(M, X)`, sends equivariant maps to equivariant maps; if
   `g = ι_X h` is equivariant, then `h θ_M` and `θ^{≤n} Φ(h)` agree after composing
   with `ι_X`, and since `Φ M ∈ T^{≤n}` injectivity of the adjunction bijection for
   the source `Φ M` makes them equal, so `h` is equivariant.  Dually for
   `M ∈ T^{≥n+1}` and `h ↦ h π_X`, using `Φ(π_X) = d_X⁻¹ π_{ΦX}` and injectivity of
   the left adjunction bijection for `Φ X`, transported along `d_X`.
3. (uses def-weil-t-structure, def-weil-endofunctor-fixed-pair-category,
   lem-weil-heart-short-exact-triangles) If `X ∈ T^{≥0}` and `M ∈ T^{≤-1}`, write
   `M = A[1]` with `A ∈ T^{≤0}`; then `Hom(M, X) ≅ Hom(A, X[-1]) = 0` by axiom 2 of
   def-weil-t-structure, so every equivariant `M → X` has zero underlying map.
   Conversely, if every such map vanishes, step 1 with `n = -1` makes
   `(τ^{≤-1}X, θ^{≤-1})` a test pair and `ι_X` equivariant, so `ι_X = 0`; by the
   bijection of step 2, `id = 0` on `τ^{≤-1}X`, so `τ^{≤-1}X = 0`.  In the truncation
   triangle `τ^{≤-1}X → X → τ^{≥0}X →` the map `π_X` is then an isomorphism, and
   `X ∈ T^{≥0}` by strict fullness.  This is BBD 1.3.4 ((a) ⇔ (b)) with Hom taken in
   the fixed-pair category.
(blueprint: lem-a1-fixed-pair-truncation-orthogonality)
-/
theorem fixedPairTruncationOrthogonality
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : Triangulated.TStructure C) (E : C ≌ C)
    [E.functor.CommShift ℤ] [E.functor.IsTriangulated]
    [E.inverse.CommShift ℤ] [E.inverse.IsTriangulated]
    (hle : ∀ (n : ℤ) (X : C), t.le n X → t.le n (E.functor.obj X))
    (hge : ∀ (n : ℤ) (X : C), t.ge n X → t.ge n (E.functor.obj X))
    (hleInv : ∀ (n : ℤ) (X : C), t.le n X → t.le n (E.inverse.obj X))
    (hgeInv : ∀ (n : ℤ) (X : C), t.ge n X → t.ge n (E.inverse.obj X)) :
    (∀ (n : ℤ),
      ∃ (leTrunc geTrunc :
          ObjectProperty.FullSubcategory (fun A : Endofunctor.Algebra E.functor => IsIso A.str) ⥤
            ObjectProperty.FullSubcategory (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
        ∃ (ι : leTrunc ⟶ 𝟭 _)
          (π : 𝟭 _ ⟶ geTrunc),
          (∀ (X : ObjectProperty.FullSubcategory
              (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
              (leTrunc.obj X).obj.a = (t.truncLE n).obj X.obj.a ∧
              (geTrunc.obj X).obj.a = (t.truncGE n).obj X.obj.a ∧
              HEq (ι.app X).hom.f ((t.truncLEι n).app X.obj.a) ∧
              HEq (π.app X).hom.f ((t.truncGEπ n).app X.obj.a)) ∧
          (∀ (M X : ObjectProperty.FullSubcategory
              (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
            t.le n M.obj.a →
              Function.Bijective (fun h : M ⟶ leTrunc.obj X => h ≫ ι.app X)) ∧
          (∀ (X M : ObjectProperty.FullSubcategory
              (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
            t.ge n M.obj.a →
              Function.Bijective (fun h : geTrunc.obj X ⟶ M => π.app X ≫ h))) ∧
    (∀ (X : ObjectProperty.FullSubcategory (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
      t.ge 0 X.obj.a ↔
        ∀ (M : ObjectProperty.FullSubcategory
            (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
          t.le (-1 : ℤ) M.obj.a → ∀ f : M ⟶ X, f.hom.f = 0) := by
  classical
  let F := E.functor
  have hcompLE (n : ℤ) (X : C) :
      ∃ e : F.obj ((t.truncLE n).obj X) ≅ (t.truncLE n).obj (F.obj X),
        e.hom ≫ (t.truncLEι n).app (F.obj X) = F.map ((t.truncLEι n).app X) := by
    let T := F.mapTriangle.obj ((t.triangleLEGE n (n + 1) rfl).obj X)
    have hT : T ∈ distTriang C :=
      F.map_distinguished _ (t.triangleLEGE_distinguished n (n + 1) rfl X)
    have h₁ : t.IsLE T.obj₁ n := ⟨hle n _ (t.le_of_isLE ((t.truncLE n).obj X) n)⟩
    have h₃ : t.IsGE T.obj₃ (n + 1) := ⟨hge (n + 1) _ (t.ge_of_isGE ((t.truncGE (n + 1)).obj X) _)⟩
    obtain ⟨e, he⟩ := t.exists_iso_truncLE_of_distTriang
      T.mor₁ T.mor₂ T.mor₃ hT n (n + 1) rfl h₁ h₃
    exact ⟨e, he.symm⟩
  have hcompGE (n : ℤ) (X : C) :
      ∃ e : F.obj ((t.truncGE n).obj X) ≅ (t.truncGE n).obj (F.obj X),
        F.map ((t.truncGEπ n).app X) ≫ e.hom = (t.truncGEπ n).app (F.obj X) := by
    let T := F.mapTriangle.obj ((t.triangleLEGE (n - 1) n (by omega)).obj X)
    have hT : T ∈ distTriang C :=
      F.map_distinguished _ (t.triangleLEGE_distinguished (n - 1) n (by omega) X)
    have h₁ : t.IsLE T.obj₁ (n - 1) := ⟨hle (n - 1) _ (t.le_of_isLE ((t.truncLE (n - 1)).obj X) _)⟩
    have h₃ : t.IsGE T.obj₃ n := ⟨hge n _ (t.ge_of_isGE ((t.truncGE n).obj X) _)⟩
    exact t.exists_iso_truncGE_of_distTriang
      T.mor₁ T.mor₂ T.mor₃ hT (n - 1) n (by omega) h₁ h₃
  choose c hc using hcompLE
  choose d hd using hcompGE
  have hFext (n : ℤ) {X Y : C} [t.IsGE Y n]
      {f g : F.obj ((t.truncGE n).obj X) ⟶ Y}
      (h : F.map ((t.truncGEπ n).app X) ≫ f =
        F.map ((t.truncGEπ n).app X) ≫ g) : f = g := by
    rw [← cancel_epi (d n X).inv]
    apply t.from_truncGE_obj_ext
    rw [← hd n X]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h
  have htrunc : (∀ (n : ℤ),
      ∃ (leTrunc geTrunc :
          ObjectProperty.FullSubcategory (fun A : Endofunctor.Algebra E.functor => IsIso A.str) ⥤
            ObjectProperty.FullSubcategory (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
        ∃ (ι : leTrunc ⟶ 𝟭 _)
          (π : 𝟭 _ ⟶ geTrunc),
          (∀ (X : ObjectProperty.FullSubcategory
              (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
              (leTrunc.obj X).obj.a = (t.truncLE n).obj X.obj.a ∧
              (geTrunc.obj X).obj.a = (t.truncGE n).obj X.obj.a ∧
              HEq (ι.app X).hom.f ((t.truncLEι n).app X.obj.a) ∧
              HEq (π.app X).hom.f ((t.truncGEπ n).app X.obj.a)) ∧
          (∀ (M X : ObjectProperty.FullSubcategory
              (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
            t.le n M.obj.a →
              Function.Bijective (fun h : M ⟶ leTrunc.obj X => h ≫ ι.app X)) ∧
          (∀ (X M : ObjectProperty.FullSubcategory
              (fun A : Endofunctor.Algebra E.functor => IsIso A.str)),
            t.ge n M.obj.a →
              Function.Bijective (fun h : geTrunc.obj X ⟶ M => π.app X ≫ h))) := by
    intro n
    let ce : t.truncLE n ⋙ F ≅ F ⋙ t.truncLE n :=
      NatIso.ofComponents (c n) (by
        intro X Y f
        have : t.IsLE (F.obj ((t.truncLE n).obj X)) n :=
          ⟨hle n _ (t.le_of_isLE _ _)⟩
        dsimp
        apply t.to_truncLE_obj_ext
        rw [Category.assoc, hc, Category.assoc, (t.truncLEι n).naturality,
          Functor.id_map, ← Category.assoc, hc, ← F.map_comp, ← F.map_comp,
          (t.truncLEι n).naturality, Functor.id_map])
    let de : t.truncGE n ⋙ F ≅ F ⋙ t.truncGE n :=
      NatIso.ofComponents (d n) (by
        intro X Y f
        dsimp
        apply hFext n
        rw [← Category.assoc, ← F.map_comp, ← (t.truncGEπ n).naturality,
          Functor.id_map, F.map_comp, Category.assoc, hd, ← Category.assoc, hd]
        exact (t.truncGEπ n).naturality (F.map f))
    let L := Endofunctor.IsoAlgebra.mapOfNatIso ce
    let G := Endofunctor.IsoAlgebra.mapOfNatIso de
    let i : L ⟶ 𝟭 _ :=
      { app X := ObjectProperty.homMk
          { f := (t.truncLEι n).app X.obj.a
            h := by
              change F.map ((t.truncLEι n).app X.obj.a) ≫ X.obj.str =
                ((c n X.obj.a).hom ≫ (t.truncLE n).map X.obj.str) ≫
                  (t.truncLEι n).app X.obj.a
              rw [Category.assoc, (t.truncLEι n).naturality, Functor.id_map,
                ← Category.assoc, hc] }
        naturality X Y f := ObjectProperty.hom_ext _
          (Endofunctor.Algebra.Hom.ext ((t.truncLEι n).naturality f.hom.f)) }
    let p : 𝟭 _ ⟶ G :=
      { app X := ObjectProperty.homMk
          { f := (t.truncGEπ n).app X.obj.a
            h := by
              change F.map ((t.truncGEπ n).app X.obj.a) ≫
                (d n X.obj.a).hom ≫ (t.truncGE n).map X.obj.str =
                  X.obj.str ≫ (t.truncGEπ n).app X.obj.a
              rw [← Category.assoc, hd]
              exact ((t.truncGEπ n).naturality X.obj.str).symm }
        naturality X Y f := ObjectProperty.hom_ext _
          (Endofunctor.Algebra.Hom.ext ((t.truncGEπ n).naturality f.hom.f)) }
    have hi (M X : Endofunctor.IsoAlgebra F) (hM : t.le n M.obj.a) :
        Function.Bijective (fun h : M ⟶ L.obj X ↦ h ≫ i.app X) := by
      have : t.IsLE M.obj.a n := ⟨hM⟩
      have : t.IsLE (F.obj M.obj.a) n := ⟨hle n _ hM⟩
      constructor
      · intro f g h
        apply ObjectProperty.hom_ext _
        apply Endofunctor.Algebra.Hom.ext
        apply t.to_truncLE_obj_ext
        exact congrArg (fun k ↦ k.hom.f) h
      · intro f
        let a := t.liftTruncLE f.hom.f n
        have ha : a ≫ (t.truncLEι n).app X.obj.a = f.hom.f := t.liftTruncLE_ι _ _
        have heq : F.map a ≫ (L.obj X).obj.str = M.obj.str ≫ a := by
          apply t.to_truncLE_obj_ext
          change (F.map a ≫ (c n X.obj.a).hom ≫ (t.truncLE n).map X.obj.str) ≫
              (t.truncLEι n).app X.obj.a = _
          rw [Category.assoc, Category.assoc, (t.truncLEι n).naturality,
            Functor.id_map, ← Category.assoc (c n X.obj.a).hom, hc,
            ← Category.assoc, ← F.map_comp, ha, Category.assoc]
          change F.map f.hom.f ≫ X.obj.str =
            M.obj.str ≫ a ≫ (t.truncLEι n).app X.obj.a
          rw [ha]
          exact f.hom.h
        refine ⟨ObjectProperty.homMk ⟨a, heq⟩, ?_⟩
        exact ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext ha)
    have hp (X M : Endofunctor.IsoAlgebra F) (hM : t.ge n M.obj.a) :
        Function.Bijective (fun h : G.obj X ⟶ M ↦ p.app X ≫ h) := by
      have : t.IsGE M.obj.a n := ⟨hM⟩
      constructor
      · intro f g h
        apply ObjectProperty.hom_ext _
        apply Endofunctor.Algebra.Hom.ext
        apply t.from_truncGE_obj_ext
        exact congrArg (fun k ↦ k.hom.f) h
      · intro f
        let a := t.descTruncGE f.hom.f n
        have ha : (t.truncGEπ n).app X.obj.a ≫ a = f.hom.f := t.π_descTruncGE _ _
        have heq : F.map a ≫ M.obj.str = (G.obj X).obj.str ≫ a := by
          apply hFext n
          change F.map ((t.truncGEπ n).app X.obj.a) ≫ (F.map a ≫ M.obj.str) =
            F.map ((t.truncGEπ n).app X.obj.a) ≫
              ((d n X.obj.a).hom ≫ (t.truncGE n).map X.obj.str) ≫ a
          rw [← Category.assoc, ← F.map_comp, ha, f.hom.h,
            ← Category.assoc, ← Category.assoc, hd,
            ← (t.truncGEπ n).naturality, Functor.id_map, Category.assoc, ha]
          rfl
        refine ⟨ObjectProperty.homMk ⟨a, heq⟩, ?_⟩
        exact ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext ha)
    exact ⟨L, G, i, p, (fun X ↦ ⟨rfl, rfl, HEq.rfl, HEq.rfl⟩), hi, hp⟩
  refine ⟨htrunc, ?_⟩
  intro X
  constructor
  · intro hX M hM f
    have : t.IsLE M.obj.a (-1) := ⟨hM⟩
    have : t.IsGE X.obj.a 0 := ⟨hX⟩
    exact t.zero f.hom.f (-1) 0 (by omega)
  · intro hX
    obtain ⟨L, G, i, p, hobj, hi, hp⟩ := htrunc (-1)
    have hL : t.le (-1) (L.obj X).obj.a := by
      rw [(hobj X).1]
      exact t.le_of_isLE _ _
    let z : L.obj X ⟶ L.obj X := ObjectProperty.homMk ⟨0, by simp⟩
    have hid : 𝟙 (L.obj X) = z := (hi (L.obj X) X hL).1 (by
      apply ObjectProperty.hom_ext _
      apply Endofunctor.Algebra.Hom.ext
      change 𝟙 _ ≫ (i.app X).hom.f = 0 ≫ (i.app X).hom.f
      simpa using hX (L.obj X) hL (i.app X))
    have hz : IsZero (L.obj X).obj.a := (IsZero.iff_id_eq_zero _).2
      (congrArg (fun f ↦ f.hom.f) hid)
    rw [(hobj X).1] at hz
    exact (t.ge_iff_isGE _ _).2
      ((t.isGE_iff_isZero_truncLE_obj (-1) 0 (by omega) X.obj.a).2 hz)

end CategoryTheory
