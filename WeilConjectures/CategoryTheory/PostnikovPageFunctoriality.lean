/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PostnikovAdditiveExactCoupleData
import WeilConjectures.CategoryTheory.AdditiveExactCouplePages
import all WeilConjectures.CategoryTheory.PostnikovFiniteCutoffAbutment
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import all Mathlib.CategoryTheory.Triangulated.Basic
import all Mathlib.CategoryTheory.Shift.ShiftSequence

/-! # Additive functoriality of the Postnikov pages

Source: Stacks Project, Homology, Tags 011R and 011T; Derived Categories, Tag 08J5.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w uB vB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

omit [Abelian B] in
private theorem alpha_natural (T : DerivedCategory A ⥤ B) (ρ p q : ℤ)
    {L M : DerivedCategory A} (u : L ⟶ M) :
    (postnikovD T ρ p q).map u ≫ postnikovAlpha T ρ p q M =
      postnikovAlpha T ρ p q L ≫ (postnikovD T ρ (p - 1) (q + 1)).map u := by
  have h := congrArg (postnikovValue T (p + q - ρ)).map
    ((TStructure.t.natTransTruncLEOfLE q (q + 1) (by omega)).naturality u)
  simp only [Functor.map_comp] at h
  dsimp only [postnikovAlpha, Functor.comp_map] at h ⊢
  rw [← Category.assoc, h, Category.assoc]
  have he := eqToHom_naturality (fun n : ℤ ↦
    (postnikovValue T n).map ((TStructure.t.truncLE (q + 1)).map u))
      (show p + q - ρ = p - 1 + (q + 1) - ρ by omega)
  simpa only [postnikovValue, Functor.comp_map, Category.assoc] using congrArg
    (fun k ↦ (postnikovValue T (p + q - ρ)).map
      ((TStructure.t.natTransTruncLEOfLE q (q + 1) (by omega)).app L) ≫ k) he

omit [Abelian B] in
private theorem g_natural (T : DerivedCategory A ⥤ B) (ρ p q : ℤ)
    {L M : DerivedCategory A} (u : L ⟶ M) :
    (postnikovD T ρ p q).map u ≫ postnikovG T ρ p q M =
      postnikovG T ρ p q L ≫ (postnikovE T ρ p q).map u := by
  have h := congrArg (postnikovValue T (p + q - ρ)).map
    ((TStructure.t.truncGEπ q).naturality ((TStructure.t.truncLT (q + 1)).map u))
  simpa only [postnikovG, postnikovD, postnikovE, CategoryTheory.Triangulated.TStructure.truncLE,
    CategoryTheory.Triangulated.TStructure.triangleLTLTGELT, Triangle.functorMk, Triangle.mk,
    Functor.whiskerLeft_app, Functor.map_comp, Functor.comp_map,
    Functor.id_map] using h

omit [Abelian B] in
private theorem f_natural (T : DerivedCategory A ⥤ B) (ρ p q : ℤ)
    {L M : DerivedCategory A} (u : L ⟶ M) :
    (postnikovE T ρ p q).map u ≫ postnikovF T ρ p q M =
      postnikovF T ρ p q L ≫ (postnikovD T ρ (p + 2) (q - 1)).map u := by
  let n := p + q - ρ
  let n' := p + 2 + (q - 1) - ρ
  let δ := (TStructure.t (C := A)).truncGELTδLT q (q + 1)
  have hδ := congrArg (fun f ↦ T.map ((shiftFunctor (DerivedCategory A) n).map f))
    (δ.naturality u)
  have hs := congrArg T.map
    ((shiftFunctorAdd' (DerivedCategory A) 1 n n' (by dsimp [n, n']; omega)).inv.naturality
      ((TStructure.t.truncLT q).map u))
  simp only [Functor.map_comp, Functor.comp_map] at hδ hs
  simp only [postnikovF, Functor.map_comp, Category.assoc]
  dsimp only [postnikovD, postnikovE, CategoryTheory.Triangulated.TStructure.truncLE,
    CategoryTheory.Triangulated.TStructure.triangleLTLTGELT, Triangle.functorMk,
    Triangle.mk, Functor.comp_map]
  change T.map ((shiftFunctor (DerivedCategory A) n).map
      ((TStructure.t.truncGELT q (q + 1)).map u)) ≫
    T.map ((shiftFunctor (DerivedCategory A) n).map (δ.app M)) ≫
      T.map ((shiftFunctorAdd' (DerivedCategory A) 1 n n'
        (by dsimp [n,n']; omega)).inv.app ((TStructure.t.truncLT q).obj M)) ≫
          eqToHom (congrArg (fun k : ℤ ↦ (postnikovValue T n').obj
            ((TStructure.t.truncLT k).obj M)) (show q = q - 1 + 1 by omega)) =
    T.map ((shiftFunctor (DerivedCategory A) n).map (δ.app L)) ≫
      T.map ((shiftFunctorAdd' (DerivedCategory A) 1 n n'
        (by dsimp [n,n']; omega)).inv.app ((TStructure.t.truncLT q).obj L)) ≫
          eqToHom (congrArg (fun k : ℤ ↦ (postnikovValue T n').obj
            ((TStructure.t.truncLT k).obj L)) (show q = q - 1 + 1 by omega)) ≫
              (postnikovValue T n').map ((TStructure.t.truncLT (q - 1 + 1)).map u)
  dsimp only [Functor.comp_map]
  rw [← Category.assoc, hδ, Category.assoc]
  rw [← Category.assoc _ _ (eqToHom _), hs, Category.assoc]
  congr 1
  congr 1
  exact eqToHom_naturality (fun k : ℤ ↦
    (postnikovValue T n').map ((TStructure.t.truncLT k).map u))
      (show q = q - 1 + 1 by omega)

omit [Abelian B] in
private theorem map_transport {F G : ℤ → ℤ → B}
    (t : ∀ p q, F p q ⟶ G p q) {p q p' q' : ℤ} (hp : p = p') (hq : q = q') :
    t p q ≫ eqToHom (congrArg₂ G hp hq) =
      eqToHom (congrArg₂ F hp hq) ≫ t p' q' := by
  subst p'
  subst q'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private noncomputable def initialMap {T : DerivedCategory A ⥤ B}
    (C : PostnikovCoupleData T) (ρ : ℤ) {L M : DerivedCategory A} (u : L ⟶ M) :
    BigradedExactCouple.CoupleMorphism (C.couple ρ L) (C.couple ρ M) where
  tD p q := (C.dIso ρ L p q).hom ≫ (postnikovD T ρ p q).map u ≫ (C.dIso ρ M p q).inv
  tE p q := (C.eIso ρ L p q).hom ≫ (postnikovE T ρ p q).map u ≫ (C.eIso ρ M p q).inv
  alpha_comm p q := by
    apply (cancel_mono (C.dIso ρ M (p - 1) (q + 1)).hom).mp
    simp only [Category.assoc, C.alpha_eq, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
    simpa only [← Category.assoc, ← C.alpha_eq] using
      congrArg (fun k ↦ (C.dIso ρ L p q).hom ≫ k) (alpha_natural T ρ p q u)
  f_comm p q := by
    apply (cancel_mono (C.dIso ρ M (p + 2) (q - 1)).hom).mp
    simp only [Category.assoc, C.f_eq, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
    simpa only [← Category.assoc, ← C.f_eq] using
      congrArg (fun k ↦ (C.eIso ρ L p q).hom ≫ k) (f_natural T ρ p q u)
  g_comm p q := by
    let d := (C.dIso ρ L p q).hom ≫ (postnikovD T ρ p q).map u ≫
      (C.dIso ρ M p q).inv
    let e (p q : ℤ) := (C.eIso ρ L p q).hom ≫ (postnikovE T ρ p q).map u ≫
      (C.eIso ρ M p q).inv
    have h : d ≫ (C.couple ρ M).initialG p q =
        (C.couple ρ L).initialG p q ≫ e p q := by
      apply (cancel_mono (C.eIso ρ M p q).hom).mp
      simp only [d, e, Category.assoc, C.g_eq, Iso.inv_hom_id_assoc,
        Iso.inv_hom_id, Category.comp_id]
      simpa only [← Category.assoc, ← C.g_eq] using
        congrArg (fun k ↦ (C.dIso ρ L p q).hom ≫ k) (g_natural T ρ p q u)
    apply (cancel_mono (eqToHom (show (C.couple ρ M).E (p + 0) (q - 0) =
      (C.couple ρ M).E p q by congr 1 <;> omega))).mp
    change (d ≫ (C.couple ρ M).g p q) ≫ _ =
      ((C.couple ρ L).g p q ≫ e (p + (0 : ℕ)) (q - (0 : ℕ))) ≫ _
    rw [Category.assoc _ (e _ _) _, map_transport e (by omega) (by omega)]
    simpa only [BigradedExactCouple.initialG, Category.assoc] using h

/-- The canonical maps of a Postnikov couple extend to additive functors on all pages.

Source: Stacks Project, Homology, Tags 011R, 011T; Derived Categories, Tag 08J5
(blueprint: lem-per-postnikov-page-functoriality).

Proof: Naturality of the truncation inclusions and quotient gives the alpha and g
squares. Naturality of the boundary transformation and the coherent shift comparison
gives the f square. Conjugate these maps by the prescribed couple comparisons.
The canonical truncation and shifted-value functors are additive; thus these initial
maps preserve identities, composition and sums. Apply the additive iteration theorem,
and retain its defining image and homology squares at every successor page. -/
theorem exists_postnikov_page_data (T : DerivedCategory A ⥤ B) [T.IsHomological]
    (C : PostnikovCoupleData T) : Nonempty (PostnikovPageData C) := by
  classical
  let m (ρ : ℤ) {L M : DerivedCategory A} (u : L ⟶ M) := initialMap C ρ u
  have hidD (ρ : ℤ) (L : DerivedCategory A) (p q : ℤ) :
      (m ρ (𝟙 L)).tD p q = 𝟙 _ := by
    simp [m, initialMap]
  have hidE (ρ : ℤ) (L : DerivedCategory A) (p q : ℤ) :
      (m ρ (𝟙 L)).tE p q = 𝟙 _ := by
    simp [m, initialMap]
  have hcompD (ρ : ℤ) {L M N : DerivedCategory A}
      (u : L ⟶ M) (v : M ⟶ N) (p q : ℤ) :
      (m ρ (u ≫ v)).tD p q = (m ρ u).tD p q ≫ (m ρ v).tD p q := by
    simp [m, initialMap, Functor.map_comp, Category.assoc]
  have hcompE (ρ : ℤ) {L M N : DerivedCategory A}
      (u : L ⟶ M) (v : M ⟶ N) (p q : ℤ) :
      (m ρ (u ≫ v)).tE p q = (m ρ u).tE p q ≫ (m ρ v).tE p q := by
    simp [m, initialMap, Functor.map_comp, Category.assoc]
  have haddD (ρ : ℤ) {L M : DerivedCategory A}
      (u v : L ⟶ M) (p q : ℤ) :
      (m ρ (u + v)).tD p q = (m ρ u).tD p q + (m ρ v).tD p q := by
    simp [m, initialMap, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  have haddE (ρ : ℤ) {L M : DerivedCategory A}
      (u v : L ⟶ M) (p q : ℤ) :
      (m ρ (u + v)).tE p q = (m ρ u).tE p q + (m ρ v).tE p q := by
    simp [m, initialMap, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  let Q (ρ : ℤ) := (BigradedExactCouple.exists_additive_page_data
    (C.couple ρ) (m ρ) (hidD ρ) (hidE ρ) (hcompD ρ) (hcompE ρ)
      (haddD ρ) (haddE ρ)).some
  refine ⟨{
    D := fun ρ ↦ (Q ρ).D
    E := fun ρ ↦ (Q ρ).E
    additiveD := fun ρ ↦ (Q ρ).additiveD
    additiveE := fun ρ ↦ (Q ρ).additiveE
    dIso := fun ρ ↦ (Q ρ).dIso
    eIso := fun ρ ↦ (Q ρ).eIso
    map := fun ρ r {L M} u ↦ (Q ρ).map r u
    mapD := fun ρ r {L M} u p q ↦ (Q ρ).mapD r u p q
    mapE := fun ρ r {L M} u p q ↦ (Q ρ).mapE r u p q
    initialD := ?_
    initialE := ?_
    image_square := fun ρ r {L M} u p q ↦ (Q ρ).image_square r u p q
    homology_square := fun ρ r {L M} u p q ↦ (Q ρ).homology_square r u p q }⟩
  · intro ρ L M u p q
    rw [(Q ρ).initialD]
    simp [m, initialMap, Category.assoc]
  · intro ρ L M u p q
    rw [(Q ρ).initialE]
    simp [m, initialMap, Category.assoc]

end DerivedCategory
