/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Algebra.Homology.SurjectiveModuleComplexTowerLimit
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Triangulated.Triangulated

/-! # Compatible finite-free complex towers

Source: Stacks Project, More on Algebra, Tag 0CQF.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

private noncomputable abbrev ringSequenceCone
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1))) :
    Cone (Functor.ofOpSequence (X := fun n ↦ CommRingCat.of (R n))
      (fun n ↦ CommRingCat.ofHom (φ n))) where
  pt := CommRingCat.of A
  π := NatTrans.ofOpSequence (fun n ↦ CommRingCat.ofHom (q n)) (by
    intro n
    simp only [Functor.const_obj_map,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact congrArg CommRingCat.ofHom (hq n))

private noncomputable def ringSequenceConeIsLimit
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (hlim : ∀ x : ∀ n, R n, (∀ n, φ n (x (n + 1)) = x n) →
      ∃! a : A, ∀ n, q n a = x n) :
    IsLimit (ringSequenceCone R φ A q hq) := by
  have : ReflectsLimit
      (Functor.ofOpSequence (X := fun n ↦ CommRingCat.of (R n))
        (fun n ↦ CommRingCat.ofHom (φ n))) (forget CommRingCat) :=
    reflectsLimit_of_reflectsIsomorphisms _ (forget CommRingCat)
  apply isLimitOfReflects (forget CommRingCat)
  apply Classical.choice
  apply (Types.isLimit_iff _).2
  intro x hx
  have hc : ∀ n, φ n (x ⟨n + 1⟩) = x ⟨n⟩ := by
    intro n
    have h := hx (homOfLE (Nat.le_succ n)).op
    simpa [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ] using h
  obtain ⟨a, ha, huniq⟩ := hlim (fun n ↦ x ⟨n⟩) hc
  refine ⟨a, ?_, ?_⟩
  · intro n
    exact ha n.unop
  · intro b hb
    exact huniq b (fun n ↦ hb ⟨n⟩)

private theorem roos_iso_respecting_projections
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K K' : ℕ → C} [HasProduct K] [HasProduct K']
    (f : ∀ n, K (n + 1) ⟶ K n) (f' : ∀ n, K' (n + 1) ⟶ K' n)
    (X Y : C) (p : X ⟶ ∏ᶜ K) (p' : Y ⟶ ∏ᶜ K')
    (δ : ∏ᶜ K ⟶ X⟦(1 : ℤ)⟧) (δ' : ∏ᶜ K' ⟶ Y⟦(1 : ℤ)⟧)
    (hX : IsDerivedLimitTriangle f X p δ) (hY : IsDerivedLimitTriangle f' Y p' δ')
    (e : ∀ n, K n ≅ K' n)
    (he : ∀ n, (e (n + 1)).hom ≫ f' n = f n ≫ (e n).hom) :
    ∃ β : X ≅ Y, β.hom ≫ p' = p ≫ Limits.Pi.map (fun n ↦ (e n).hom) := by
  let T := Triangle.mk p (towerTransitionEndomorphism f) δ
  let T' := Triangle.mk p' (towerTransitionEndomorphism f') δ'
  let v := Limits.Pi.map (fun n ↦ (e n).hom)
  have hv : IsIso v := by
    let w := Limits.Pi.map (fun n ↦ (e n).inv)
    exact ⟨⟨w, by ext n; simp [v, w], by ext n; simp [v, w]⟩⟩
  obtain ⟨a, ha, hδ⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    T T' hX hY v v (towerTransitionEndomorphism_natural_backward f f'
      (fun n ↦ (e n).hom) he).symm
  let α : T ⟶ T' :=
    { hom₁ := a
      hom₂ := v
      hom₃ := v
      comm₁ := ha
      comm₂ := (towerTransitionEndomorphism_natural_backward f f'
        (fun n ↦ (e n).hom) he).symm
      comm₃ := hδ }
  have ha' : IsIso a := Pretriangulated.isIso₁_of_isIso₂₃ α hX hY hv hv
  exact ⟨asIso a, ha.symm⟩

/-- The literal projections of a surjective tower model agree with a prescribed Roos limit.
Source: Stacks Project, Tags 091D, 0CQD and 0CQF, and Derived Categories Tag 0H9J
(blueprint: lem-weil-pbc-complex-tower-limit-projection-comparison).

Proof: Regard the varying-ring tower as a tower of A-complexes by restriction of scalars,
using the canonical composition comparison. The degreewise compatible-tuple universal
property identifies P and its projections with the termwise categorical limit. Apply
the surjective module-complex tower lemma to obtain its distinguished Roos triangle.
The specified beta markings commute with the transitions by hu and the normalization hχ.
Their product is an isomorphism commuting with one-minus-shift. Transport the Roos
triangle through it. Rotate this triangle and the given triangle so that one-minus-shift
is the first arrow. Complete the identity square on the two product objects by TR3.
Two-out-of-three for triangle morphisms makes the completion an isomorphism. Shift it
back and use the last square to obtain an isomorphism Q(P) to E respecting every
projection. Existence only is asserted; no unique choice of the triangle completion
is used. Empty degrees and zero complexes satisfy the same universal properties. -/
theorem exists_complexTower_limit_projection_comparison
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (hlim : ∀ x : ∀ n, R n, (∀ n, φ n (x (n + 1)) = x n) →
      ∃! a : A, ∀ n, q n a = x n)
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [∀ n, HasDerivedCategory.{w} (ModuleCat.{max u v} (R n))]
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
    [HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))]
    (E : DerivedCategory (ModuleCat.{max u v} A))
    (pE : E ⟶ ∏ᶜ fun n ↦
      (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))
    (δ : (∏ᶜ fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n)) ⟶
      E⟦(1 : ℤ)⟧)
    (hE : IsDerivedLimitTriangle
      (fun n ↦ (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
        (χ n).inv.app (Eₙ n)) E pE δ)
    (Pₙ : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ)
    (βₙ : ∀ n, Q.obj (Pₙ n) ≅ Eₙ n)
    (uₙ : ∀ n, Pₙ (n + 1) ⟶
      ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
    (hsurju : ∀ n i, Function.Surjective ((uₙ n).f i))
    (hu : ∀ n, Q.map (uₙ n) = (βₙ (n + 1)).hom ≫ t n ≫
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.map (βₙ n).inv ≫
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app (Pₙ n))
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (p : ∀ n, P ⟶
      ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
    (hp : ∀ n i (y : P.X i), (uₙ n).f i ((p (n + 1)).f i y) = (p n).f i y)
    (hP : ∀ i (x : ∀ n, (Pₙ n).X i), (∀ n, (uₙ n).f i (x (n + 1)) = x n) →
      ∃! y : P.X i, ∀ n, (p n).f i y = x n) :
    ∃ β : Q.obj P ≅ E, ∀ n, Q.map (p n) ≫
      (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.inv.app (Pₙ n) ≫
      (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (βₙ n).hom =
      β.hom ≫ pE ≫ Pi.π _ n := by
  classical
  let F := Functor.ofOpSequence (X := fun n ↦ CommRingCat.of (R n))
    (fun n ↦ CommRingCat.ofHom (φ n))
  let c := ringSequenceCone R φ A q hq
  let : HasDerivedCategory.{w} (ModuleCat.{max u v} c.pt) :=
    inferInstanceAs (HasDerivedCategory.{w} (ModuleCat.{max u v} A))
  have hc := ringSequenceConeIsLimit R φ A q hq hlim
  have hφ (n : ℕ) : (F.map (homOfLE (Nat.le_succ n)).op).hom = φ n := by
    simp only [F, Functor.ofOpSequence_map_homOfLE_succ, CommRingCat.hom_ofHom]
  have hex (n : ℕ) : ∃ f : Pₙ (n + 1) ⟶
      ((ModuleCat.restrictScalars (F.map (homOfLE (Nat.le_succ n)).op).hom).mapHomologicalComplex
        (.up ℤ)).obj (Pₙ n), ∀ i (x : (Pₙ (n + 1)).X i), f.f i x = (uₙ n).f i x := by
    rw [hφ n]
    exact ⟨uₙ n, fun _ _ ↦ rfl⟩
  choose u' hu' using hex
  have hsurju' : ∀ n i, Function.Surjective ((u' n).f i) := by
    intro n i y
    obtain ⟨x, hx⟩ := hsurju n i y
    exact ⟨x, (hu' n i x).trans hx⟩
  have htower := ModuleCat.surjective_moduleComplexTower_limit F c hc Pₙ u' hsurju'
  let s := fun n ↦
    ((ModuleCat.restrictScalars (q (n + 1))).mapHomologicalComplex (.up ℤ)).map (uₙ n) ≫
      (NatIso.mapHomologicalComplex
        (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n))
        (.up ℤ)).inv.app (Pₙ n)
  let S := Functor.ofOpSequence
    (X := fun n ↦ ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj
      (Pₙ n)) s
  have hs (n : ℕ) : S.map (homOfLE (Nat.le_succ n)).op = s n :=
    by
    dsimp [S]
    exact Functor.ofOpSequence_map_homOfLE_succ
      (X := fun n ↦ ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj
        (Pₙ n)) s n
  have heq : ModuleCat.restrictedComplexTower F c Pₙ u' = S := by
    dsimp only [ModuleCat.restrictedComplexTower, S, c, ringSequenceCone]
    congr 1
    funext n
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact hu' n i x
  rw [heq] at htower
  dsimp only [c, ringSequenceCone] at htower
  have := htower.1
  obtain ⟨δP, hδP⟩ := htower.2
  let cP : Cone S :=
    { pt := P
      π := NatTrans.ofOpSequence p (by
        intro n
        apply HomologicalComplex.Hom.ext
        funext i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        simpa [S, s] using (hp n i y).symm) }
  have hcP : IsLimit cP := by
    apply HomologicalComplex.isLimitOfEval
    intro i
    have : ReflectsLimit (S ⋙ HomologicalComplex.eval _ _ i) (forget (ModuleCat A)) :=
      reflectsLimit_of_reflectsIsomorphisms _ (forget (ModuleCat A))
    apply isLimitOfReflects (forget (ModuleCat A))
    apply Classical.choice
    apply (Types.isLimit_iff _).2
    intro x hx
    have hxc : ∀ n, (uₙ n).f i (x ⟨n + 1⟩) = x ⟨n⟩ := by
      intro n
      have h := hx (homOfLE (Nat.le_succ n)).op
      simpa [S, s] using h
    obtain ⟨y, hy, huniq⟩ := hP i (fun n ↦ x ⟨n⟩) hxc
    exact ⟨y, fun n ↦ hy n.unop, fun z hz ↦ huniq z (fun n ↦ hz ⟨n⟩)⟩
  simp_rw [hs] at hδP
  let eP := hcP.conePointUniqueUpToIso (HomologicalComplex.isLimitConeOfHasLimitEval S)
  have heP (n : ℕ) : eP.hom ≫
      (HomologicalComplex.coneOfHasLimitEval S).π.app ⟨n⟩ = p n :=
    hcP.conePointUniqueUpToIso_hom_comp _ _
  let e := fun n ↦
    ((ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.app (Pₙ n)).symm ≪≫
      (ModuleCat.restrictScalars (q n)).mapDerivedCategory.mapIso (βₙ n)
  have he : ∀ n, (e (n + 1)).hom ≫
        ((ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
          (χ n).inv.app (Eₙ n)) = Q.map (s n) ≫ (e n).hom := by
    intro n
    let H := ModuleCat.restrictScalars (q (n + 1))
    let G := ModuleCat.restrictScalars (q n)
    let V := ModuleCat.restrictScalars (φ n)
    let a := H.mapDerivedCategoryFactors
    let b := G.mapDerivedCategoryFactors
    let d := V.mapDerivedCategoryFactors
    let κ := (Functor.mapHomologicalComplexCompIso
      (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n)).symm (.up ℤ)).symm
    have hn := hχ n (Pₙ n)
    have hnorm : b.inv.app (Pₙ n) ≫ (χ n).hom.app (Q.obj (Pₙ n)) =
        Q.map (κ.hom.app (Pₙ n)) ≫
          a.inv.app ((V.mapHomologicalComplex (.up ℤ)).obj (Pₙ n)) ≫
          H.mapDerivedCategory.map (d.inv.app (Pₙ n)) := by
      change (χ n).hom.app (Q.obj (Pₙ n)) ≫
        H.mapDerivedCategory.map (d.hom.app (Pₙ n)) ≫
        a.hom.app ((V.mapHomologicalComplex (.up ℤ)).obj (Pₙ n)) =
        b.hom.app (Pₙ n) ≫ Q.map (κ.hom.app (Pₙ n)) at hn
      apply (cancel_mono (H.mapDerivedCategory.map (d.hom.app (Pₙ n)) ≫
        a.hom.app ((V.mapHomologicalComplex (.up ℤ)).obj (Pₙ n)))).1
      have hd : H.mapDerivedCategory.map (d.inv.app (Pₙ n)) ≫
          H.mapDerivedCategory.map (d.hom.app (Pₙ n)) = 𝟙 _ :=
        (H.mapDerivedCategory.mapIso (d.app (Pₙ n))).inv_hom_id
      simp only [Category.assoc]
      rw [hn]
      rw [← Category.assoc (H.mapDerivedCategory.map (d.inv.app (Pₙ n))), hd]
      rw [← Category.assoc (b.inv.app (Pₙ n)), Iso.inv_hom_id_app, Category.id_comp,
        Category.id_comp, Iso.inv_hom_id_app]
      exact (Category.comp_id _).symm
    apply (cancel_mono ((χ n).hom.app (Eₙ n))).1
    dsimp [e]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
    change a.inv.app (Pₙ (n + 1)) ≫ H.mapDerivedCategory.map (βₙ (n + 1)).hom ≫
      H.mapDerivedCategory.map (t n) = Q.map (s n) ≫ b.inv.app (Pₙ n) ≫
        G.mapDerivedCategory.map (βₙ n).hom ≫ (χ n).hom.app (Eₙ n)
    rw [(χ n).hom.naturality (βₙ n).hom]
    simp only [Functor.comp_map]
    rw [← Category.assoc (b.inv.app (Pₙ n)), hnorm]
    have hs' : s n = (H.mapHomologicalComplex (.up ℤ)).map (uₙ n) ≫
        κ.inv.app (Pₙ n) := rfl
    rw [hs', Q.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (Q.map (κ.inv.app (Pₙ n))), ← Q.map_comp,
      Iso.inv_hom_id_app, Q.map_id, Category.id_comp]
    have hnat := a.inv.naturality (uₙ n)
    simp only [Functor.comp_map] at hnat
    rw [← Category.assoc (Q.map ((H.mapHomologicalComplex (.up ℤ)).map (uₙ n))), hnat]
    simp only [Category.assoc]
    apply (cancel_epi (a.inv.app (Pₙ (n + 1)))).2
    have hd' : H.mapDerivedCategory.map (d.hom.app (Pₙ n)) ≫
        H.mapDerivedCategory.map (d.inv.app (Pₙ n)) = 𝟙 _ :=
      (H.mapDerivedCategory.mapIso (d.app (Pₙ n))).hom_inv_id
    have hb' : H.mapDerivedCategory.map (V.mapDerivedCategory.map (βₙ n).inv) ≫
        H.mapDerivedCategory.map (V.mapDerivedCategory.map (βₙ n).hom) = 𝟙 _ :=
      (H.mapDerivedCategory.mapIso (V.mapDerivedCategory.mapIso (βₙ n))).inv_hom_id
    rw [hu]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc (H.mapDerivedCategory.map (d.hom.app (Pₙ n))), hd',
      Category.id_comp]
    rw [hb']
    exact congrArg (fun f ↦ H.mapDerivedCategory.map (βₙ (n + 1)).hom ≫ f)
      (Category.comp_id (H.mapDerivedCategory.map (t n))).symm
  obtain ⟨β₀, hβ₀⟩ := roos_iso_respecting_projections
    (fun n ↦ Q.map (s n))
    (fun n ↦ (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
      (χ n).inv.app (Eₙ n))
    _ E _ pE δP δ hδP hE e he
  refine ⟨Q.mapIso eP ≪≫ β₀, ?_⟩
  intro n
  have h := congrArg (fun f ↦ Q.map eP.hom ≫ f ≫ Pi.π _ n) hβ₀
  have hpQ : Q.map eP.hom ≫
      Q.map ((HomologicalComplex.coneOfHasLimitEval S).π.app ⟨n⟩) = Q.map (p n) := by
    rw [← Q.map_comp, heP]
  simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_π_assoc] at h
  rw [← Category.assoc (Q.map eP.hom)
    (Q.map ((HomologicalComplex.coneOfHasLimitEval S).π.app ⟨n⟩)), hpQ] at h
  simpa [Category.assoc, e] using h.symm

end DerivedCategory
