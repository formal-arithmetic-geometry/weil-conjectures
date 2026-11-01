/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
public import WeilConjectures.Algebra.Homology.SixFunctors.SemilinearEvaluationAcyclicLift
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows

/-! # A step in normalized strict compactification comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerShriek

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

private def transposeNatural
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R) {P : C ⥤ A} {Q : C ⥤ B}
    (t : P ⟶ Q ⋙ R) : P ⋙ L ⟶ Q where
  app X := (a.homEquiv _ _).symm (t.app X)
  naturality _ _ f := a.homEquiv_naturality_right_square _ _ _ _ (t.naturality f)

private def openTensorInverse
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (R : B ⥤ A) (a : L ⊣ R)
    (T : B × B ⥤ B) (U : A × A ⥤ A)
    (mu : T ⋙ R ≅ (R.prod R) ⋙ U) :
    (𝟭 A).prod R ⋙ U ⋙ L ⟶ (L.prod (𝟭 B)) ⋙ T := by
  exact transposeNatural a (P := (𝟭 A).prod R ⋙ U)
    (Q := (L.prod (𝟭 B)) ⋙ T) {
    app := fun X ↦ U.map (Prod.mkHom (a.unit.app X.1) (𝟙 _)) ≫
      mu.inv.app (L.obj X.1, X.2)
    naturality := fun X Y f ↦ by
      have hn :
          Prod.mkHom f.1 (R.map f.2) ≫
              Prod.mkHom (a.unit.app Y.1) (𝟙 (R.obj Y.2)) =
            Prod.mkHom (a.unit.app X.1) (𝟙 (R.obj X.2)) ≫
              (R.prod R).map (Prod.mkHom (L.map f.1) f.2) := by
        ext
        · exact a.unit.naturality f.1
        · simp
      dsimp only [Functor.prod_map, Functor.id_map, Functor.comp_map]
      rw [← Category.assoc, ← U.map_comp, hn, U.map_comp,
        Category.assoc, Category.assoc]
      congr 1
      exact mu.inv.naturality (Prod.mkHom (L.map f.1) f.2) }

private theorem openTensor_naturality
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (R : B ⥤ A) (a : L ⊣ R)
    (T : B × B ⥤ B) (U : A × A ⥤ A)
    (mu : T ⋙ R ≅ (R.prod R) ⋙ U)
    (delta : ∀ M N, T.obj (L.obj M, N) ≅ L.obj (U.obj (M, R.obj N)))
    (hd : ∀ M N, a.homEquiv _ _ (delta M N).inv =
      U.map (Prod.mkHom (a.unit.app M) (𝟙 _)) ≫ mu.inv.app (L.obj M, N))
    {M M' : A} {N N' : B} (f : M ⟶ M') (g : N ⟶ N') :
    T.map (Prod.mkHom (L.map f) g) ≫ (delta M' N').hom =
      (delta M N).hom ≫ L.map (U.map (Prod.mkHom f (R.map g))) := by
  have he (M N) : (delta M N).inv = (openTensorInverse L R a T U mu).app (M, N) :=
    (a.homEquiv _ _).injective ((hd M N).trans
      ((a.homEquiv _ _).apply_symm_apply _).symm)
  have hn := (openTensorInverse L R a T U mu).naturality (Prod.mkHom f g)
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map] at hn
  rw [← he, ← he] at hn
  apply (cancel_epi (delta M N).inv).1
  apply (cancel_mono (delta M' N').inv).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using hn.symm

private theorem transpose_evaluation_aux
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    (E₀ : A ⥤ A') (E₁ : B ⥤ B')
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (a : L ⋙ E₁ ≅ E₀ ⋙ L') (b : R ⋙ E₀ ≅ E₁ ⋙ R')
    (hu : ∀ M, E₀.map (adj.unit.app M) ≫ b.hom.app (L.obj M) ≫
      R'.map (a.hom.app M) = adj'.unit.app (E₀.obj M))
    {P : A} {N : B} (h : L.obj P ⟶ N) :
    E₀.map ((adj.homEquiv _ _) h) ≫ b.hom.app N =
      (adj'.homEquiv _ _) (a.inv.app P ≫ E₁.map h) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hr := b.hom.naturality h
  dsimp only [Functor.comp_map] at hr
  rw [hr]
  have hu' : E₀.map (adj.unit.app P) ≫ b.hom.app (L.obj P) =
      adj'.unit.app (E₀.obj P) ≫ R'.map (a.inv.app P) := by
    rw [← hu P]
    have hi := (R'.mapIso (a.app P)).hom_inv_id
    change R'.map (a.hom.app P) ≫ R'.map (a.inv.app P) = 𝟙 _ at hi
    simp only [Category.assoc, hi]
    erw [Category.comp_id]
  rw [← Category.assoc, hu', Category.assoc]

private def inverseOpenComparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R') (H : A ⥤ C) (G : B ⥤ D)
    (s : R ⋙ H ≅ G ⋙ R') : H ⋙ L' ⟶ L ⋙ G :=
  transposeNatural a' {
    app := fun K ↦ H.map (X := K) (Y := R.obj (L.obj K)) (a.unit.app K) ≫ s.hom.app (L.obj K)
    naturality := fun K N f ↦ by
      change H.map f ≫ (H.map (X := N) (Y := R.obj (L.obj N)) (a.unit.app N) ≫
        s.hom.app (L.obj N)) =
        (H.map (X := K) (Y := R.obj (L.obj K)) (a.unit.app K) ≫ s.hom.app (L.obj K)) ≫
          R'.map (G.map (L.map f))
      have hu := a.unit.naturality f
      dsimp only [Functor.id_map, Functor.comp_map] at hu
      rw [← Category.assoc, ← H.map_comp, hu, H.map_comp,
        Category.assoc, Category.assoc]
      exact congrArg (H.map (X := K) (Y := R.obj (L.obj K)) (a.unit.app K) ≫
        ·) (s.hom.naturality (L.map f)) }

private theorem inverseOpenComparison_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R') (H : A ⥤ C) (G : B ⥤ D)
    (s : R ⋙ H ≅ G ⋙ R') [IsIso a.unit]
    (K : A) [IsIso (a'.counit.app (G.obj (L.obj K)))] :
    IsIso ((inverseOpenComparison a a' H G s).app K) := by
  change IsIso ((a'.homEquiv _ _).symm
    (H.map (X := K) (Y := R.obj (L.obj K)) (a.unit.app K) ≫ s.hom.app (L.obj K)))
  rw [Adjunction.homEquiv_counit]
  infer_instance

private theorem counit_isIso_of_support
    {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A}
    (a : L ⊣ R) [IsIso a.unit] {M : B} (h : L.essImage M) :
    IsIso (a.counit.app M) := by
  have : L.Full := a.fullyFaithfulLOfIsIsoUnit.full
  have : L.Faithful := a.fullyFaithfulLOfIsIsoUnit.faithful
  exact a.isIso_counit_app_iff_mem_essImage.mpr h

private def normalizedOpenComparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R') (H : A ⥤ C) (G : B ⥤ D)
    (s : R ⋙ H ≅ G ⋙ R') [IsIso a.unit]
    (hc : ∀ K, IsIso (a'.counit.app (G.obj (L.obj K)))) : L ⋙ G ≅ H ⋙ L' := by
  let v := inverseOpenComparison a a' H G s
  have (K : A) : IsIso (v.app K) := by
    have := hc K
    exact inverseOpenComparison_isIso a a' H G s K
  have : IsIso v := NatIso.isIso_of_isIso_app _
  exact (asIso v).symm

private theorem normalizedOpenComparison_inv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R') (H : A ⥤ C) (G : B ⥤ D)
    (s : R ⋙ H ≅ G ⋙ R') [IsIso a.unit]
    (hc : ∀ K, IsIso (a'.counit.app (G.obj (L.obj K)))) (K : A) :
    (normalizedOpenComparison a a' H G s hc).inv.app K =
      (a'.homEquiv (H.obj K) (G.obj (L.obj K))).symm
        (H.map (X := K) (Y := R.obj (L.obj K)) (a.unit.app K) ≫ s.hom.app (L.obj K)) := rfl

private theorem normalizedOpenComparison_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R') (H : A ⥤ C) (G : B ⥤ D)
    (s : R ⋙ H ≅ G ⋙ R') [IsIso a.unit]
    (hc : ∀ K, IsIso (a'.counit.app (G.obj (L.obj K)))) (K : A) :
    a'.homEquiv (H.obj K) (G.obj (L.obj K))
        ((normalizedOpenComparison a a' H G s hc).inv.app K) =
      H.map (X := K) (Y := R.obj (L.obj K)) (a.unit.app K) ≫ s.hom.app (L.obj K) := by
  rw [normalizedOpenComparison_inv]
  exact (a'.homEquiv _ _).apply_symm_apply _

private theorem normalizedOpenComparison_composite_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R') (H : A ⥤ C) (G : B ⥤ D)
    {P Q : B ⥤ C} (c : R ⋙ H ≅ P) (w : P = Q) (d : G ⋙ R' ≅ Q)
    [IsIso a.unit] (hc : ∀ K, IsIso (a'.counit.app (G.obj (L.obj K)))) (K : A) :
    a'.homEquiv (H.obj K) (G.obj (L.obj K))
        ((normalizedOpenComparison a a' H G (c ≪≫ eqToIso w ≪≫ d.symm) hc).inv.app K) =
      H.map (X := K) (Y := R.obj (L.obj K)) (a.unit.app K) ≫
        (c.hom ≫ eqToHom w ≫ d.inv).app (L.obj K) := by
  simpa only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom] using
    normalizedOpenComparison_mate a a' H G (c ≪≫ eqToIso w ≪≫ d.symm) hc K

private structure OpenComparisonData
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R') (H : A ⥤ C) (G : B ⥤ D)
    {P Q : B ⥤ C} (c : R ⋙ H ≅ P) (w : P = Q) (d : G ⋙ R' ≅ Q) where
  iso : L ⋙ G ≅ H ⋙ L'
  rawMate : ∀ K : A,
    a'.homEquiv (H.obj K) (G.obj (L.obj K)) (iso.inv.app K) =
      H.map (X := K) (Y := R.obj (L.obj K)) (a.unit.app K) ≫
        (c ≪≫ eqToIso w ≪≫ d.symm).hom.app (L.obj K)
  mate : ∀ K : A,
    a'.homEquiv (H.obj K) (G.obj (L.obj K)) (iso.inv.app K) =
      H.map (X := K) (Y := R.obj (L.obj K)) (a.unit.app K) ≫
        (c.hom ≫ eqToHom w ≫ d.inv).app (L.obj K)

private def normalizedOpenComparisonData
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R') (H : A ⥤ C) (G : B ⥤ D)
    {P Q : B ⥤ C} (c : R ⋙ H ≅ P) (w : P = Q) (d : G ⋙ R' ≅ Q)
    [IsIso a.unit] (hc : ∀ K, IsIso (a'.counit.app (G.obj (L.obj K)))) :
    OpenComparisonData a a' H G c w d where
  iso := normalizedOpenComparison a a' H G (c ≪≫ eqToIso w ≪≫ d.symm) hc
  rawMate := normalizedOpenComparison_mate a a' H G (c ≪≫ eqToIso w ≪≫ d.symm) hc
  mate := normalizedOpenComparison_composite_mate a a' H G c w d hc

private def normalizedOpenTensor
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (R : B ⥤ A) (a : L ⊣ R)
    (T : B × B ⥤ B) (U : A × A ⥤ A)
    (mu : T ⋙ R ≅ (R.prod R) ⋙ U) [IsIso a.unit]
    (K : A) (N : B) (hs : L.essImage (T.obj (L.obj K, N))) :
    T.obj (L.obj K, N) ≅ L.obj (U.obj (K, R.obj N)) := by
  let f := (openTensorInverse L R a T U mu).app (K, N)
  have := counit_isIso_of_support a hs
  have : IsIso (Prod.mkHom (a.unit.app K) (𝟙 (R.obj N))) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso f := by
    change IsIso ((a.homEquiv _ _).symm
      (U.map (Prod.mkHom (a.unit.app K) (𝟙 _)) ≫ mu.inv.app (L.obj K, N)))
    rw [Adjunction.homEquiv_counit]
    infer_instance
  exact (asIso f).symm

private theorem normalizedOpenTensor_inv
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (R : B ⥤ A) (a : L ⊣ R)
    (T : B × B ⥤ B) (U : A × A ⥤ A)
    (mu : T ⋙ R ≅ (R.prod R) ⋙ U) [IsIso a.unit]
    (K : A) (N : B) (hs : L.essImage (T.obj (L.obj K, N))) :
    (normalizedOpenTensor L R a T U mu K N hs).inv =
      (a.homEquiv _ _).symm
        (U.map (Prod.mkHom (a.unit.app K) (𝟙 _)) ≫ mu.inv.app (L.obj K, N)) := rfl

private theorem normalizedOpenTensor_mate
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (R : B ⥤ A) (a : L ⊣ R)
    (T : B × B ⥤ B) (U : A × A ⥤ A)
    (mu : T ⋙ R ≅ (R.prod R) ⋙ U) [IsIso a.unit]
    (K : A) (N : B) (hs : L.essImage (T.obj (L.obj K, N))) :
    a.homEquiv _ _ (normalizedOpenTensor L R a T U mu K N hs).inv =
      U.map (Prod.mkHom (a.unit.app K) (𝟙 _)) ≫ mu.inv.app (L.obj K, N) := by
  rw [normalizedOpenTensor_inv]
  exact (a.homEquiv _ _).apply_symm_apply _

private theorem open_projection_evaluation_aux
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    (E₀ : A ⥤ A') (E₁ : B ⥤ B')
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (a : L ⋙ E₁ ≅ E₀ ⋙ L') (b : R ⋙ E₀ ≅ E₁ ⋙ R')
    (hu : ∀ M, E₀.map (adj.unit.app M) ≫ b.hom.app (L.obj M) ≫
      R'.map (a.hom.app M) = adj'.unit.app (E₀.obj M))
    (T₀ : A × A ⥤ A) (T₁ : B × B ⥤ B)
    (t₀ : A' × A' ⥤ A') (t₁ : B' × B' ⥤ B')
    (e₀ : T₀ ⋙ E₀ ≅ (E₀.prod E₀) ⋙ t₀)
    (e₁ : T₁ ⋙ E₁ ≅ (E₁.prod E₁) ⋙ t₁)
    (t : T₁ ⋙ R ≅ (R.prod R) ⋙ T₀)
    (N : A) (P : B)
    (h : L.obj (T₀.obj (N, R.obj P)) ⟶ T₁.obj (L.obj N, P))
    (hm : (adj.homEquiv _ _) h =
      T₀.map (Prod.mkHom (adj.unit.app N) (𝟙 _)) ≫ t.inv.app (L.obj N, P)) :
    E₁.map h ≫ e₁.hom.app (L.obj N, P) ≫
        t₁.map (Prod.mkHom (a.hom.app N) (𝟙 _)) =
      a.hom.app (T₀.obj (N, R.obj P)) ≫
        L'.map (e₀.hom.app (N, R.obj P) ≫
          t₀.map (Prod.mkHom (𝟙 _) (b.hom.app P))) ≫
        (adj'.homEquiv _ _).symm
          (t₀.map (Prod.mkHom
              (adj'.unit.app (E₀.obj N) ≫ R'.map (a.inv.app N)) (𝟙 _)) ≫
            ((R'.mapIso (e₁.app (L.obj N, P))).symm ≪≫
              (b.app (T₁.obj (L.obj N, P))).symm ≪≫
              E₀.mapIso (t.app (L.obj N, P)) ≪≫
              e₀.app (R.obj (L.obj N), R.obj P) ≪≫
              t₀.mapIso ((b.app (L.obj N)).prod (b.app P))).inv ≫
            R'.map (t₁.map (Prod.mkHom (a.hom.app N) (𝟙 _)))) := by
  apply (cancel_epi (a.inv.app (T₀.obj (N, R.obj P)))).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply (adj'.homEquiv _ _).injective
  rw [adj'.homEquiv_naturality_right, adj'.homEquiv_naturality_right,
    ← transpose_evaluation_aux E₀ E₁ adj adj' a b hu, hm,
    adj'.homEquiv_naturality_left, Equiv.apply_symm_apply]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.prod_inv, Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
  have he := e₀.hom.naturality (Prod.mkHom (adj.unit.app N) (𝟙 (R.obj P)))
  dsimp only [Functor.comp_map, Functor.prod_map] at he
  simp only [CategoryTheory.Functor.map_id] at he
  have hu' : E₀.map (adj.unit.app N) ≫ b.hom.app (L.obj N) =
      adj'.unit.app (E₀.obj N) ≫ R'.map (a.inv.app N) := by
    rw [← hu N]
    have hi := (R'.mapIso (a.app N)).hom_inv_id
    change R'.map (a.hom.app N) ≫ R'.map (a.inv.app N) = 𝟙 _ at hi
    simp only [Category.assoc, hi]
    erw [Category.comp_id]
  rw [← hu']
  simp only [← t₀.map_comp_assoc, CategoryTheory.prod_comp,
    Prod.mkHom, Category.id_comp, Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id, ← reassoc_of% he, Iso.hom_inv_id_app_assoc]

private theorem normalized_open_inverse
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R)
    (T : B × B ⥤ B) (U : A × A ⥤ A)
    (mu : T ⋙ R ≅ R.prod R ⋙ U)
    (K : A) (M N : B) (e : M ≅ L.obj K) :
    U.map (Prod.mkHom (a.unit.app K ≫ R.map e.inv) (𝟙 _)) ≫
        mu.inv.app (M, N) ≫ R.map (T.map (Prod.mkHom e.hom (𝟙 N))) =
      U.map (Prod.mkHom (a.unit.app K) (𝟙 _)) ≫ mu.inv.app (L.obj K, N) := by
  have hn := mu.inv.naturality (Prod.mkHom e.hom (𝟙 N))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [← hn, ← Category.assoc, ← U.map_comp]
  congr 2
  ext
  · simp only [prod_comp_fst, Prod.mkHom, Category.assoc, ← R.map_comp,
      Iso.inv_hom_id, R.map_id]
    erw [Category.comp_id]
  · simp

private theorem tensorProjection_naturality
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (mu : T ⋙ L ≅ (L.prod L) ⋙ U)
    {M M' : B} {N N' : A} (f : M ⟶ M') (g : N ⟶ N') :
    T.map (Prod.mkHom (R.map f) g) ≫
        (adj.homEquiv _ _) (mu.hom.app (R.obj M', N') ≫
          U.map (Prod.mkHom (adj.counit.app M') (𝟙 _))) =
      (adj.homEquiv _ _) (mu.hom.app (R.obj M, N) ≫
          U.map (Prod.mkHom (adj.counit.app M) (𝟙 _))) ≫
        R.map (U.map (Prod.mkHom f (L.map g))) := by
  apply adj.homEquiv_naturality_left_square
  have hn := mu.hom.naturality (Prod.mkHom (R.map f) g)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [← Category.assoc, hn, Category.assoc]
  simp only [Category.assoc, ← U.map_comp]
  congr 2
  ext
  · have hc := adj.counit.naturality f
    dsimp only [Functor.id_map, Functor.comp_map] at hc
    exact hc
  · simp

private theorem iso_forward_of_inverse
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {X' Y' : D} (e : X ≅ Y) (e' : X' ≅ Y')
    (a : F.obj X ⟶ X') (b : F.obj Y ⟶ Y')
    (h : F.map e.inv ≫ a = b ≫ e'.inv) :
    F.map e.hom ≫ b = a ≫ e'.hom := by
  apply (cancel_mono e'.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← h, ← Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id,
    Category.id_comp]

private theorem indexedSquare_evaluation
    {Q I J C D : Type*} [Category I] [Category J] [Category C] [Category D]
    (F : C ⥤ D) (L : Q → I ⥤ C) (Ln : Q → J ⥤ D)
    {q₀ q : Q} (w : q₀ = q)
    {X Y : I ⥤ C} {Xn Yn : J ⥤ D}
    (a : X ≅ L q₀) (b : Y ≅ L q)
    (an : Xn ≅ Ln q₀) (bn : Yn ≅ Ln q)
    (s : X ≅ Y) (sn : Xn ≅ Yn)
    (hs : s = a ≪≫ eqToIso (congrArg L w) ≪≫ b.symm)
    (hsn : sn = an ≪≫ eqToIso (congrArg Ln w) ≪≫ bn.symm)
    (K : I) (Kn : J) {P V : D}
    (p₁ : F.obj (X.obj K) ⟶ P) (p₂ : P ⟶ Xn.obj Kn)
    (q₁ : F.obj (Y.obj K) ⟶ V) (q₂ : V ⟶ Yn.obj Kn)
    (r : ∀ q' : Q, F.obj ((L q').obj K) ⟶ (Ln q').obj Kn)
    (ha : F.map (a.hom.app K) ≫ r q₀ = p₁ ≫ p₂ ≫ an.hom.app Kn)
    (hb : F.map (b.hom.app K) ≫ r q = q₁ ≫ q₂ ≫ bn.hom.app Kn) :
    F.map (s.hom.app K) ≫ q₁ ≫ q₂ = p₁ ≫ p₂ ≫ sn.hom.app Kn := by
  subst q
  simp only [eqToIso_refl, Iso.refl_trans] at hs hsn
  subst s
  subst sn
  apply (cancel_mono (bn.hom.app Kn)).1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, F.map_comp,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at ha hb ⊢
  rw [← hb]
  simpa only [← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id,
    Category.id_comp] using ha

private theorem open_inverse_evaluation_aux
    {A B C D An Bn Cn Dn : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category An] [Category Bn] [Category Cn] [Category Dn]
    (E : A ⥤ An) (F : B ⥤ Bn) (E' : C ⥤ Cn) (F' : D ⥤ Dn)
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {l : An ⥤ Bn} {r : Bn ⥤ An} {l' : Cn ⥤ Dn} {r' : Dn ⥤ Cn}
    (a : L ⊣ R) (a' : L' ⊣ R') (an : l ⊣ r) (an' : l' ⊣ r')
    (p : L ⋙ F ≅ E ⋙ l) (q : R ⋙ E ≅ F ⋙ r)
    (p' : L' ⋙ F' ≅ E' ⋙ l') (q' : R' ⋙ E' ≅ F' ⋙ r')
    (hu : ∀ M, E.map (a.unit.app M) ≫ q.hom.app (L.obj M) ≫
      r.map (p.hom.app M) = an.unit.app (E.obj M))
    (hu' : ∀ M, E'.map (a'.unit.app M) ≫ q'.hom.app (L'.obj M) ≫
      r'.map (p'.hom.app M) = an'.unit.app (E'.obj M))
    (H : A ⥤ C) (G : B ⥤ D) (Hn : An ⥤ Cn) (Gn : Bn ⥤ Dn)
    (gamma : H ⋙ E' ≅ E ⋙ Hn) (eta : G ⋙ F' ≅ F ⋙ Gn)
    (s : R ⋙ H ≅ G ⋙ R') (sn : r ⋙ Hn ≅ Gn ⋙ r')
    (hs : ∀ M, E'.map (s.hom.app M) ≫ q'.hom.app (G.obj M) ≫
      r'.map (eta.hom.app M) =
        gamma.hom.app (R.obj M) ≫ Hn.map (q.hom.app M) ≫ sn.hom.app (F.obj M))
    (K : A) (v : L'.obj (H.obj K) ⟶ G.obj (L.obj K))
    (vn : l'.obj (Hn.obj (E.obj K)) ⟶ Gn.obj (l.obj (E.obj K)))
    (hv : a'.homEquiv _ _ v = H.map (X := K) (Y := R.obj (L.obj K)) (a.unit.app K) ≫
      s.hom.app (L.obj K))
    (hvn : an'.homEquiv _ _ vn = Hn.map (X := E.obj K) (Y := r.obj (l.obj (E.obj K)))
      (an.unit.app (E.obj K)) ≫
      sn.hom.app (l.obj (E.obj K))) :
    F'.map v ≫ eta.hom.app (L.obj K) ≫ Gn.map (p.hom.app K) =
      p'.hom.app (H.obj K) ≫ l'.map (gamma.hom.app K) ≫ vn := by
  apply (cancel_epi (p'.inv.app (H.obj K))).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply (an'.homEquiv _ _).injective
  rw [an'.homEquiv_naturality_right, an'.homEquiv_naturality_right,
    ← transpose_evaluation_aux E' F' a' an' p' q' hu', hv,
    an'.homEquiv_naturality_left]
  dsimp only [Functor.comp_obj]
  rw [hvn]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hs]
  have hg := gamma.hom.naturality (a.unit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hg
  rw [reassoc_of% hg]
  have hn := sn.hom.naturality (p.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn]
  simp only [← Hn.map_comp_assoc, hu]

private theorem indexed_open_evaluation_aux
    {Idx A B C D An Bn Cn Dn : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category An] [Category Bn] [Category Cn] [Category Dn]
    (E : A ⥤ An) (F : B ⥤ Bn) (E' : C ⥤ Cn) (F' : D ⥤ Dn)
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {l : An ⥤ Bn} {r : Bn ⥤ An} {l' : Cn ⥤ Dn} {r' : Dn ⥤ Cn}
    (a : L ⊣ R) (a' : L' ⊣ R') (an : l ⊣ r) (an' : l' ⊣ r')
    (p : L ⋙ F ≅ E ⋙ l) (q : R ⋙ E ≅ F ⋙ r)
    (p' : L' ⋙ F' ≅ E' ⋙ l') (q' : R' ⋙ E' ≅ F' ⋙ r')
    (hu : ∀ M, E.map (a.unit.app M) ≫ q.hom.app (L.obj M) ≫
      r.map (p.hom.app M) = an.unit.app (E.obj M))
    (hu' : ∀ M, E'.map (a'.unit.app M) ≫ q'.hom.app (L'.obj M) ≫
      r'.map (p'.hom.app M) = an'.unit.app (E'.obj M))
    (H : A ⥤ C) (G : B ⥤ D) (Hn : An ⥤ Cn) (Gn : Bn ⥤ Dn)
    (gamma : H ⋙ E' ≅ E ⋙ Hn) (eta : G ⋙ F' ≅ F ⋙ Gn)
    (Q : Idx → B ⥤ C) (Qn : Idx → Bn ⥤ Cn)
    (rho : ∀ i (M : B), E'.obj ((Q i).obj M) ⟶ (Qn i).obj (F.obj M))
    {i₀ i : Idx} (w : i₀ = i)
    (c : G ⋙ R' ≅ Q i₀) (d : R ⋙ H ≅ Q i)
    (cn : Gn ⋙ r' ≅ Qn i₀) (dn : r ⋙ Hn ≅ Qn i)
    (s : G ⋙ R' ≅ R ⋙ H)
    (hs : s = c ≪≫ eqToIso (congrArg Q w) ≪≫ d.symm)
    (hc : ∀ M, E'.map (c.hom.app M) ≫ rho i₀ M =
      q'.hom.app (G.obj M) ≫ r'.map (eta.hom.app M) ≫ cn.hom.app (F.obj M))
    (hd : ∀ M, E'.map (d.hom.app M) ≫ rho i M =
      gamma.hom.app (R.obj M) ≫ Hn.map (q.hom.app M) ≫ dn.hom.app (F.obj M))
    (K : A) (v : L ⋙ G ≅ H ⋙ L')
    (data : OpenComparisonData an an' Hn Gn dn (congrArg Qn w.symm) cn)
    (hv : a'.homEquiv _ _ (v.inv.app K) = H.map (a.unit.app K) ≫ s.inv.app (L.obj K))
 :
    F'.map (v.hom.app K) ≫ p'.hom.app (H.obj K) ≫ l'.map (gamma.hom.app K) =
      eta.hom.app (L.obj K) ≫ Gn.map (p.hom.app K) ≫ data.iso.hom.app (E.obj K) := by
  subst i
  simp only [eqToIso_refl, Iso.refl_trans] at hs
  subst s
  have hsq (M : B) :
      E'.map ((c ≪≫ d.symm).inv.app M) ≫ q'.hom.app (G.obj M) ≫
          r'.map (eta.hom.app M) =
        gamma.hom.app (R.obj M) ≫ Hn.map (q.hom.app M) ≫
          (dn ≪≫ cn.symm).hom.app (F.obj M) := by
    simpa only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
      NatTrans.comp_app, Functor.comp_obj] using
      indexedSquare_evaluation E' Q Qn (rfl : i₀ = i₀)
        d c dn cn (d ≪≫ c.symm) (dn ≪≫ cn.symm)
        (by simp only [eqToIso_refl, Iso.refl_trans])
        (by simp only [eqToIso_refl, Iso.refl_trans])
        M (F.obj M) (gamma.hom.app (R.obj M)) (Hn.map (q.hom.app M))
        (q'.hom.app (G.obj M)) (r'.map (eta.hom.app M))
        (fun i ↦ rho i M) (hd M) (hc M)
  have hi := open_inverse_evaluation_aux E F E' F' a a' an an' p q p' q' hu hu'
    H G Hn Gn gamma eta (c ≪≫ d.symm).symm (dn ≪≫ cn.symm)
    (by simpa only [Iso.symm_hom] using hsq) K (v.inv.app K) (data.iso.inv.app (E.obj K)) hv (by
      simpa only [eqToIso_refl, Iso.refl_trans] using data.rawMate (E.obj K))
  simpa only [Iso.app_hom, Iso.app_inv, Category.assoc] using
    iso_forward_of_inverse F' (v.app K) (data.iso.app (E.obj K))
    (eta.hom.app (L.obj K) ≫ Gn.map (p.hom.app K))
    (p'.hom.app (H.obj K) ≫ l'.map (gamma.hom.app K))
    (by simpa only [Iso.app_inv, Functor.comp_obj, Category.assoc] using hi)

private def coordinatesOf
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {E₀ : A ⥤ A'} {E₁ : B ⥤ B'}
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    (a : L ⊣ R) (a' : L' ⊣ R')
    (p : L ⋙ E₁ ≅ E₀ ⋙ L') (q : R ⋙ E₀ ≅ E₁ ⋙ R')
    (hu : ∀ K, E₀.map (a.unit.app K) ≫ q.hom.app (L.obj K) ≫
      R'.map (p.hom.app K) = a'.unit.app (E₀.obj K))
    (hc : ∀ M, L'.map (q.hom.app M) ≫ a'.counit.app (E₁.obj M) =
      p.inv.app (R.obj M) ≫ E₁.map (a.counit.app M)) :
    ComparisonAdjunctionCoordinates E₀ E₁ a a' where
  left := p
  right := q
  unit := hu
  counit := hc

private theorem mate_evaluation_aux
    {X Y Z W x y z w : Type*}
    [Category X] [Category Y] [Category Z] [Category W]
    [Category x] [Category y] [Category z] [Category w]
    {E₁ : X ⥤ x} {F₁ : Y ⥤ y} {E₂ : Z ⥤ z} {F₂ : W ⥤ w}
    {L₁ : X ⥤ Y} {R₁ : Y ⥤ X} {L₂ : Z ⥤ W} {R₂ : W ⥤ Z}
    {l₁ : x ⥤ y} {r₁ : y ⥤ x} {l₂ : z ⥤ w} {r₂ : w ⥤ z}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (level₁ : l₁ ⊣ r₁) (level₂ : l₂ ⊣ r₂)
    (A₁ : ComparisonAdjunctionCoordinates E₁ F₁ adj₁ level₁)
    (A₂ : ComparisonAdjunctionCoordinates E₂ F₂ adj₂ level₂)
    {G : X ⥤ Z} {H : Y ⥤ W} {g : x ⥤ z} {h : y ⥤ w}
    (γ : G ⋙ E₂ ≅ E₁ ⋙ g) (η : H ⋙ F₂ ≅ F₁ ⋙ h)
    (α : TwoSquare G L₁ L₂ H) (a : TwoSquare g l₁ l₂ h)
    (compatible : ∀ A : X,
      F₂.map (α.app A) ≫ η.hom.app (L₁.obj A) ≫ h.map (A₁.left.hom.app A) =
        A₂.left.hom.app (G.obj A) ≫ l₂.map (γ.hom.app A) ≫ a.app (E₁.obj A)) :
    ∀ B : Y,
      E₂.map ((mateEquiv adj₁ adj₂ α).app B) ≫ A₂.right.hom.app (H.obj B) ≫
          r₂.map (η.hom.app B) =
        γ.hom.app (R₁.obj B) ≫ g.map (A₁.right.hom.app B) ≫
          (mateEquiv level₁ level₂ a).app (F₁.obj B) := by
  intro B
  apply (level₂.homEquiv _ _).symm.injective
  change l₂.map _ ≫ level₂.counit.app _ = l₂.map _ ≫ level₂.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  apply (cancel_epi (A₂.left.hom.app (G.obj (R₁.obj B)))).1
  have hleft := A₂.left.hom.naturality ((mateEquiv adj₁ adj₂ α).app B)
  dsimp only [Functor.comp_map] at hleft
  rw [← reassoc_of% hleft]
  have hcounit := level₂.counit.naturality (η.hom.app B)
  dsimp only [Functor.comp_map, Functor.id_map] at hcounit
  rw [hcounit]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% (A₂.counit (H.obj B))]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← F₂.map_comp_assoc, mateEquiv_counit]
  rw [F₂.map_comp, Category.assoc]
  have hη := η.hom.naturality (adj₁.counit.app B)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hη
  rw [hη]
  rw [mateEquiv_counit]
  have ha := a.naturality (A₁.right.hom.app B)
  dsimp only [Functor.comp_map, Functor.comp_obj] at ha
  rw [reassoc_of% ha]
  rw [← reassoc_of% (compatible (R₁.obj B))]
  rw [← h.map_comp, A₁.counit]
  rw [← h.map_comp, Iso.hom_inv_id_app_assoc]

private theorem proper_projection_evaluation_aux
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    (E₀ : A ⥤ A') (E₁ : B ⥤ B')
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (a : L ⋙ E₁ ≅ E₀ ⋙ L') (b : R ⋙ E₀ ≅ E₁ ⋙ R')
    (hu : ∀ M, E₀.map (adj.unit.app M) ≫ b.hom.app (L.obj M) ≫
      R'.map (a.hom.app M) = adj'.unit.app (E₀.obj M))
    (hc : ∀ N, L'.map (b.hom.app N) ≫ adj'.counit.app (E₁.obj N) =
      a.inv.app (R.obj N) ≫ E₁.map (adj.counit.app N))
    (T₀ : A × A ⥤ A) (T₁ : B × B ⥤ B)
    (t₀ : A' × A' ⥤ A') (t₁ : B' × B' ⥤ B')
    (e₀ : T₀ ⋙ E₀ ≅ (E₀.prod E₀) ⋙ t₀)
    (e₁ : T₁ ⋙ E₁ ≅ (E₁.prod E₁) ⋙ t₁)
    (mu : T₀ ⋙ L ≅ (L.prod L) ⋙ T₁)
    (mun : t₀ ⋙ L' ≅ (L'.prod L') ⋙ t₁)
    (ht : ∀ M N, E₁.map (mu.hom.app (M, N)) ≫
        e₁.hom.app (L.obj M, L.obj N) ≫
        t₁.map (Prod.mkHom (a.hom.app M) (a.hom.app N)) =
      a.hom.app (T₀.obj (M, N)) ≫ L'.map (e₀.hom.app (M, N)) ≫
        mun.hom.app (E₀.obj M, E₀.obj N))
    (N : B) (M : A) :
    E₀.map ((adj.homEquiv _ _)
        (mu.hom.app (R.obj N, M) ≫
          T₁.map (Prod.mkHom (adj.counit.app N) (𝟙 (L.obj M))))) ≫
        b.hom.app (T₁.obj (N, L.obj M)) ≫
        R'.map (e₁.hom.app (N, L.obj M) ≫
          t₁.map (Prod.mkHom (𝟙 _) (a.hom.app M))) =
      e₀.hom.app (R.obj N, M) ≫
        t₀.map (Prod.mkHom (b.hom.app N) (𝟙 _)) ≫
        (adj'.homEquiv _ _)
          (mun.hom.app (R'.obj (E₁.obj N), E₀.obj M) ≫
            t₁.map (Prod.mkHom (adj'.counit.app (E₁.obj N)) (𝟙 _))) := by
  dsimp only [Functor.id_obj, Functor.comp_obj] at *
  rw [reassoc_of% (transpose_evaluation_aux E₀ E₁ adj adj' a b hu _)]
  rw [← adj'.homEquiv_naturality_right]
  simp only [← Category.assoc]
  erw [← adj'.homEquiv_naturality_left
    (e₀.hom.app (R.obj N, M) ≫ t₀.map (Prod.mkHom (b.hom.app N) (𝟙 _)))]
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  have hn := e₁.hom.naturality (Prod.mkHom (adj.counit.app N) (𝟙 (L.obj M)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [reassoc_of% hn]
  have hc' : E₁.map (adj.counit.app N) =
      a.hom.app (R.obj N) ≫ L'.map (b.hom.app N) ≫ adj'.counit.app (E₁.obj N) := by
    rw [hc]
    simp only [Iso.hom_inv_id_app_assoc]
  have hm :
      t₁.map (Prod.mkHom (E₁.map (adj.counit.app N)) (E₁.map (𝟙 (L.obj M)))) ≫
        t₁.map (Prod.mkHom (𝟙 (E₁.obj N)) (a.hom.app M)) =
      t₁.map (Prod.mkHom (a.hom.app (R.obj N)) (a.hom.app M)) ≫
        t₁.map (Prod.mkHom (L'.map (b.hom.app N)) (𝟙 _)) ≫
          t₁.map (Prod.mkHom (adj'.counit.app (E₁.obj N)) (𝟙 _)) := by
    simp only [← t₁.map_comp]
    congr 1
    ext <;> simp [hc']
  rw [hm]
  rw [reassoc_of% (ht (R.obj N) M)]
  simp only [Iso.inv_hom_id_app_assoc]
  have hl := mun.hom.naturality (Prod.mkHom (b.hom.app N) (𝟙 (E₀.obj M)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hl
  rw [reassoc_of% hl]
  simp only [CategoryTheory.Functor.map_id]
  rfl

private theorem projection_combine
    {C D Cn Dn : Type*} [Category C] [Category D] [Category Cn] [Category Dn]
    (F : C ⥤ D) (E : C ⥤ Cn) (E' : D ⥤ Dn) (Fn : Cn ⥤ Dn)
    (δ : ∀ Q : C, E'.obj (F.obj Q) ⟶ Fn.obj (E.obj Q))
    {Q Q' : C} {N : D} (u : N ⟶ F.obj Q) (v : Q ⟶ Q')
    {A B W W' : Cn} (p : E.obj Q' ⟶ A) (q : A ⟶ B)
    (w : E.obj Q ⟶ W) (a : W ⟶ W') (t : W' ⟶ B)
    {S S₁ S₂ : Dn} (e : E'.obj N ⟶ S) (s₁ : S ⟶ S₁) (s₂ : S₁ ⟶ S₂)
    (s₁₂ : S ⟶ S₂) (b : S₁ ⟶ Fn.obj W) (b' : S₂ ⟶ Fn.obj W')
    (hnat : E'.map (F.map v) ≫ δ Q' = δ Q ≫ Fn.map (E.map v))
    (ht : E.map v ≫ p ≫ q = w ≫ a ≫ t)
    (hp : E'.map u ≫ δ Q ≫ Fn.map w = e ≫ s₁ ≫ b)
    (hn : s₂ ≫ b' = b ≫ Fn.map a) (hs : s₁₂ = s₁ ≫ s₂) :
    E'.map (u ≫ F.map v) ≫ δ Q' ≫ Fn.map p ≫ Fn.map q =
      e ≫ s₁₂ ≫ b' ≫ Fn.map t := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat]
  rw [← Fn.map_comp, ← Fn.map_comp, ht, Fn.map_comp, Fn.map_comp]
  rw [reassoc_of% hp, ← reassoc_of% hn, hs]
  simp only [Category.assoc]

private def normalizedOpenTensorData
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (R : B ⥤ A) (a : L ⊣ R)
    (T : B × B ⥤ B) (U : A × A ⥤ A)
    (mu : T ⋙ R ≅ (R.prod R) ⋙ U) [IsIso a.unit]
    (K : A) (N : B) (hs : L.essImage (T.obj (L.obj K, N))) :
    { z : T.obj (L.obj K, N) ≅ L.obj (U.obj (K, R.obj N)) //
      a.homEquiv _ _ z.inv =
        U.map (Prod.mkHom (a.unit.app K) (𝟙 _)) ≫ mu.inv.app (L.obj K, N) } :=
  ⟨normalizedOpenTensor L R a T U mu K N hs,
    normalizedOpenTensor_mate L R a T U mu K N hs⟩

private theorem projection_tail_evaluation_aux
    {A B C An Bn Cn : Type*}
    [Category A] [Category B] [Category C]
    [Category An] [Category Bn] [Category Cn]
    (E : A ⥤ An) (F : B ⥤ Bn) (G : C ⥤ Cn)
    (J : A ⥤ B) (Q : B ⥤ A) (P : C ⥤ B) (W : C ⥤ A)
    (Jn : An ⥤ Bn) (Qn : Bn ⥤ An) (Pn : Cn ⥤ Bn) (Wn : Cn ⥤ An)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (t : An × An ⥤ An) (u : Bn × Bn ⥤ Bn)
    (e : T ⋙ E ≅ E.prod E ⋙ t) (d : U ⋙ F ≅ F.prod F ⋙ u)
    (p : J ⋙ F ≅ E ⋙ Jn) (q : Q ⋙ E ≅ F ⋙ Qn)
    (r : P ⋙ F ≅ G ⋙ Pn) (w : W ⋙ E ≅ G ⋙ Wn)
    (v : P ⋙ Q ≅ W) (vn : Pn ⋙ Qn ≅ Wn)
    (delta : ∀ M N, U.obj (J.obj M, N) ≅ J.obj (T.obj (M, Q.obj N)))
    (delta_n : ∀ M N, u.obj (Jn.obj M, N) ≅ Jn.obj (t.obj (M, Qn.obj N)))
    (hv : ∀ L, E.map (v.hom.app L) ≫ w.hom.app L =
      q.hom.app (P.obj L) ≫ Qn.map (r.hom.app L) ≫ vn.hom.app (G.obj L))
    (ho : ∀ M N, F.map (delta M N).hom ≫ p.hom.app (T.obj (M, Q.obj N)) ≫
      Jn.map (e.hom.app (M, Q.obj N) ≫ t.map (Prod.mkHom (𝟙 _) (q.hom.app N))) =
      d.hom.app (J.obj M, N) ≫ u.map (Prod.mkHom (p.hom.app M) (𝟙 _)) ≫
        (delta_n (E.obj M) (F.obj N)).hom)
    (hn : ∀ (M : An) {N N' : Bn} (a : N ⟶ N'),
      u.map (Prod.mkHom (𝟙 (Jn.obj M)) a) ≫ (delta_n M N').hom =
        (delta_n M N).hom ≫ Jn.map (t.map (Prod.mkHom (𝟙 M) (Qn.map a))))
    (K : A) (L : C) :
    F.map ((delta K (P.obj L)).hom ≫ J.map (T.map (Prod.mkHom (𝟙 K) (v.hom.app L)))) ≫
        p.hom.app (T.obj (K, W.obj L)) ≫
        Jn.map (e.hom.app (K, W.obj L) ≫ t.map (Prod.mkHom (𝟙 _) (w.hom.app L))) =
      d.hom.app (J.obj K, P.obj L) ≫
        u.map (Prod.mkHom (p.hom.app K) (r.hom.app L)) ≫
        (delta_n (E.obj K) (Pn.obj (G.obj L))).hom ≫
        Jn.map (t.map (Prod.mkHom (𝟙 _) (vn.hom.app (G.obj L)))) := by
  have he := e.hom.naturality (Prod.mkHom (𝟙 K) (v.hom.app L))
  dsimp only [Functor.comp_map, Functor.prod_map] at he
  have hcomp : E.map (T.map (Prod.mkHom (𝟙 K) (v.hom.app L))) ≫
      e.hom.app (K, W.obj L) ≫ t.map (Prod.mkHom (𝟙 _) (w.hom.app L)) =
    e.hom.app (K, Q.obj (P.obj L)) ≫ t.map (Prod.mkHom (𝟙 _) (q.hom.app (P.obj L))) ≫
      t.map (Prod.mkHom (𝟙 _) (Qn.map (r.hom.app L))) ≫
      t.map (Prod.mkHom (𝟙 _) (vn.hom.app (G.obj L))) := by
    rw [reassoc_of% he]
    simp only [CategoryTheory.Functor.map_id]
    change e.hom.app (K, Q.obj (P.obj L)) ≫
      t.map (Prod.mkHom (𝟙 _) (E.map (v.hom.app L))) ≫
        t.map (Prod.mkHom (𝟙 _) (w.hom.app L)) = _
    simp only [← t.map_comp]
    apply congrArg (fun m ↦ e.hom.app (K, Q.obj (P.obj L)) ≫ t.map m)
    ext
    · simp
    · simpa using hv L
  have hj := p.hom.naturality (T.map (Prod.mkHom (𝟙 K) (v.hom.app L)))
  dsimp only [Functor.comp_map] at hj
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hj]
  simp only [← Functor.map_comp]
  rw [hcomp]
  simp only [Functor.map_comp]
  have hout := ho K (P.obj L)
  simp only [Functor.map_comp] at hout
  rw [reassoc_of% hout]
  rw [← reassoc_of% (hn (E.obj K) (r.hom.app L))]
  simp only [← Functor.map_comp_assoc, CategoryTheory.prod_comp, Prod.mkHom,
    Category.comp_id, Category.id_comp]

private theorem evaluation_lift (T : Scheme.{u}) (n : ℕ)
    (N : proEtaleDerivedCategory T (R l E n)) :
    ∃ M : D l E T, Nonempty ((Ev l E T n).obj M ≅ N) := by
  let Z := DerivedCategory.Q.objPreimage N
  let rings := SemilinearSections.rings.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (B l E T) (tau l E T)
  let e := SheafOfModules.strictSystemSequenceEquivalence rings
  let V := SheafOfModules.rightExtension rings n
  have : V.Additive := SheafOfModules.rightExtension_additive rings n
  have : e.functor.Additive := SheafOfModules.strictSystemToSequenceAdditive rings
  have : (ev l E T n).Additive := inferInstance
  have : (V ⋙ e.functor ⋙ ev l E T n).Additive := inferInstance
  let K := ((V ⋙ e.functor).mapHomologicalComplex (.up ℤ)).obj Z
  refine ⟨DerivedCategory.Q.obj K, ⟨?_⟩⟩
  let a : e.functor ⋙ ev l E T n ≅ SheafOfModules.systemEvaluation rings n :=
    Functor.isoWhiskerLeft e.functor
        (SheafOfModules.semilinearEvaluationIso n (B l E T) (tau l E T)).symm ≪≫
      Functor.isoWhiskerRight e.unitIso.symm (SheafOfModules.systemEvaluation rings n)
  let d : V ⋙ e.functor ⋙ ev l E T n ≅ 𝟭 _ :=
    Functor.isoWhiskerLeft V a ≪≫ SheafOfModules.rightExtension_evaluation rings n
  exact (ev l E T n).mapDerivedCategoryFactors.app K ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex d (.up ℤ)).app Z ≪≫
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app Z) ≪≫
    DerivedCategory.Q.objObjPreimageIso N

private theorem levelOpen_unit_isIso (b : Base l E) {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ) :
    IsIso (comparisonLevelOpenAdjunction l E b j n).unit := by
  have := b.finite n
  let J := sfIntrinsicExtensionByZero j (R l E n)
  let P := proEtaleConstantRingPullback (R l E n) j
  have := sfIntrinsicExtensionByZero_additive j (R l E n)
  have := sfIntrinsicExtensionByZero_preservesFiniteLimits j (R l E n)
  have := sfIntrinsicExtensionByZero_preservesFiniteColimits j (R l E n)
  have : J.Full := by dsimp [J, sfIntrinsicExtensionByZero]; infer_instance
  have : J.Faithful := by dsimp [J, sfIntrinsicExtensionByZero]; infer_instance
  have : IsIso (finiteOpenAdjunction l E b j n).unit :=
    (finiteOpenAdjunction l E b j n).unit_isIso_of_L_fully_faithful
  let a := finiteOpenAdjunction l E b j n
  let e : J.mapDerivedCategory ⋙ P.mapDerivedCategory ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryCompIso J P).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso a.unit).symm ≪≫
      Functor.mapDerivedCategoryIdIso _
  exact (comparisonLevelOpenAdjunction l E b j n).isIso_unit_of_iso e

private theorem open_unit_evaluation (b : Base l E) (o : Operations l E b)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ) (K : D l E U) :
    (Ev l E U n).map ((o.openOp j).derivedAdjunction.unit.app K) ≫
        ((o.geometry j).pullEvaluation n).hom.app ((openD l E b (o.openOp j)).obj K) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) j).map
          ((openEvaluation l E b (o.openOp j) n).hom.app K) =
      (comparisonLevelOpenAdjunction l E b j n).unit.app ((Ev l E U n).obj K) := by
  have := b.finite n
  have h := open_adjunction_unit_evaluation l E b (o.openOp j) n K
  rw [exact_adjunction_eq_local] at h
  exact h

private theorem open_unit_isIso (b : Base l E) (o : Operations l E b)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    IsIso (o.openOp j).derivedAdjunction.unit := by
  have h (K : D l E U) : IsIso ((o.openOp j).derivedAdjunction.unit.app K) := by
    apply (b.calculus U).detects
    intro n
    have := levelOpen_unit_isIso l E b j n
    have ht : IsIso ((Ev l E U n).map ((o.openOp j).derivedAdjunction.unit.app K) ≫
        ((o.geometry j).pullEvaluation n).hom.app ((openD l E b (o.openOp j)).obj K) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) j).map
          ((openEvaluation l E b (o.openOp j) n).hom.app K)) := by
      rw [open_unit_evaluation l E b o j n K]
      infer_instance
    exact IsIso.of_isIso_comp_right
      ((Ev l E U n).map ((o.openOp j).derivedAdjunction.unit.app K))
      (((o.geometry j).pullEvaluation n).hom.app ((openD l E b (o.openOp j)).obj K) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) j).map
          ((openEvaluation l E b (o.openOp j) n).hom.app K))
  exact NatIso.isIso_of_isIso_app _

private theorem open_counit_evaluation (b : Base l E) (o : Operations l E b)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ) (M : D l E T) :
    (sfIntrinsicDerivedOpen (R l E n) j).map
        (((o.geometry j).pullEvaluation n).hom.app M) ≫
        (comparisonLevelOpenAdjunction l E b j n).counit.app ((Ev l E T n).obj M) =
      (openEvaluation l E b (o.openOp j) n).inv.app
          ((pull l E b (o.geometry j)).obj M) ≫
        (Ev l E T n).map ((o.openOp j).derivedAdjunction.counit.app M) := by
  let a := (o.openOp j).derivedAdjunction
  let c := comparisonLevelOpenAdjunction l E b j n
  let q := (o.geometry j).pullEvaluation n
  let p := openEvaluation l E b (o.openOp j) n
  have h := transpose_evaluation_aux (Ev l E U n) (Ev l E T n) a c p q
    (open_unit_evaluation l E b o j n) (a.counit.app M)
  have ht : a.homEquiv _ _ (a.counit.app M) = 𝟙 _ := by
    rw [← a.homEquiv_symm_id M]
    change (a.homEquiv _ M) ((a.homEquiv _ M).symm (𝟙 _)) = 𝟙 _
    exact (a.homEquiv _ M).apply_symm_apply _
  rw [ht, CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact ((c.homEquiv _ _).symm_apply_eq).2 h

private def levelOpenModel {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    StrictTower.moduleJ (ULift.{u + 1, u} A) j ≅ sfIntrinsicExtensionByZero j A :=
  (StrictTower.moduleJAdj (ULift.{u + 1, u} A) j).leftAdjointUniq
    ((sfIntrinsicOpenAdjunction A j).ofNatIsoRight (openSquarePullbackModel A j).symm)

private theorem levelOpen_basechange_image (b : Base l E)
    {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (n : ℕ)
    (K : proEtaleDerivedCategory U (R l E n)) :
    Nonempty ((proEtaleConstantRingDerivedPullback (R l E n) g).obj
      ((sfIntrinsicDerivedOpen (R l E n) j).obj K) ≅
        (sfIntrinsicDerivedOpen (R l E n) j').obj
          ((proEtaleConstantRingDerivedPullback (R l E n) h).obj K)) := by
  have := b.finite n
  have := sfIntrinsicExtensionByZero_additive j (R l E n)
  have := sfIntrinsicExtensionByZero_preservesFiniteLimits j (R l E n)
  have := sfIntrinsicExtensionByZero_preservesFiniteColimits j (R l E n)
  have := sfIntrinsicExtensionByZero_additive j' (R l E n)
  have := sfIntrinsicExtensionByZero_preservesFiniteLimits j' (R l E n)
  have := sfIntrinsicExtensionByZero_preservesFiniteColimits j' (R l E n)
  let d := Functor.mapDerivedCategoryNatIso (levelOpenModel j (R l E n))
  let d' := Functor.mapDerivedCategoryNatIso (levelOpenModel j' (R l E n))
  obtain ⟨e⟩ := VaryingRing.level_basechange_image (ULift.{u + 1} (R l E n))
    h j' j g sq.w sq K
  exact ⟨(proEtaleConstantRingDerivedPullback (R l E n) g).mapIso (d.app K).symm ≪≫
    e ≪≫ d'.app ((proEtaleConstantRingDerivedPullback (R l E n) h).obj K)⟩

private theorem open_basechange_counit_isIso (b : Base l E) (o : Operations l E b)
    {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (K : D l E U) :
    IsIso ((o.openOp j').derivedAdjunction.counit.app
      ((pull l E b (o.geometry g)).obj ((openD l E b (o.openOp j)).obj K))) := by
  let M := (pull l E b (o.geometry g)).obj ((openD l E b (o.openOp j)).obj K)
  apply (b.calculus T').detects
  intro n
  have := levelOpen_unit_isIso l E b j' n
  let c := comparisonLevelOpenAdjunction l E b j' n
  have : (sfIntrinsicDerivedOpen (R l E n) j').Full :=
    c.fullyFaithfulLOfIsIsoUnit.full
  have : (sfIntrinsicDerivedOpen (R l E n) j').Faithful :=
    c.fullyFaithfulLOfIsIsoUnit.faithful
  obtain ⟨e⟩ := levelOpen_basechange_image l E b h j' j g sq n ((Ev l E U n).obj K)
  let t : (Ev l E T' n).obj M ≅
      (sfIntrinsicDerivedOpen (R l E n) j').obj
        ((proEtaleConstantRingDerivedPullback (R l E n) h).obj ((Ev l E U n).obj K)) :=
    ((o.geometry g).pullEvaluation n).app ((openD l E b (o.openOp j)).obj K) ≪≫
      (proEtaleConstantRingDerivedPullback (R l E n) g).mapIso
        ((openEvaluation l E b (o.openOp j) n).app K) ≪≫ e
  have : IsIso (c.counit.app ((Ev l E T' n).obj M)) := c.isIso_counit_app_of_iso t
  have hc := open_counit_evaluation l E b o j' n M
  have : IsIso ((openEvaluation l E b (o.openOp j') n).inv.app
        ((pull l E b (o.geometry j')).obj M) ≫
      (Ev l E T' n).map ((o.openOp j').derivedAdjunction.counit.app M)) := by
    rw [← hc]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((openEvaluation l E b (o.openOp j') n).inv.app
      ((pull l E b (o.geometry j')).obj M))
    ((Ev l E T' n).map ((o.openOp j').derivedAdjunction.counit.app M))

private def towerOpenExchange (b : Base l E) (o : Operations l E b) :
    OpenExchange l E b o where
  exchange h j' j g _ _ sq := by
    have := open_unit_isIso l E b o j
    exact normalizedOpenComparison (o.openOp j).derivedAdjunction
      (o.openOp j').derivedAdjunction (pull l E b (o.geometry h))
      (pull l E b (o.geometry g)) (square l E b o h j' j g sq.w).symm
      (open_basechange_counit_isIso l E b o h j' j g sq)
  mate h j' j g _ _ sq K := by
    have := open_unit_isIso l E b o j
    simpa only [openMate, openD, Iso.symm_hom, Functor.id_obj, Functor.comp_obj] using
      normalizedOpenComparison_inv (o.openOp j).derivedAdjunction
        (o.openOp j').derivedAdjunction (pull l E b (o.geometry h))
        (pull l E b (o.geometry g)) (square l E b o h j' j g sq.w).symm
        (open_basechange_counit_isIso l E b o h j' j g sq) K

private theorem levelTensor_transport (b : Base l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (C : ℕ → Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (τC : ∀ k, C (k + 1) ⟶ C k)
    (A : SemilinearSections.Data.{u + 1, u, u + 1} (Scheme.ProEt.topology X) C τC)
    (hC : C = B l E X) (hτ : HEq τC (tau l E X)) (hA : HEq A (b.calculus X))
    (q : Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (B l E Y n) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (C n),
      Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (C n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ P)
    [q.1.Additive] [PreservesFiniteLimits q.1] [PreservesFiniteColimits q.1]
    (hq : HEq q
      (⟨proEtaleConstantRingPullback (R l E n) f,
        proEtaleConstantRingPushforward (R l E n) f,
        proEtaleConstantRingAdjunction (R l E n) f⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n),
          Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology X) (B l E X n) ⥤
            SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ P))
    (mu : ((b.calculus Y).levelClosed n).tensor ⋙ q.1.mapDerivedCategory ≅
      q.1.mapDerivedCategory.prod q.1.mapDerivedCategory ⋙ (A.levelClosed n).tensor) :
    ∃ t : comparisonLevelTensor l E b Y n ⋙
        proEtaleConstantRingDerivedPullback (R l E n) f ≅
      (proEtaleConstantRingDerivedPullback (R l E n) f).prod
          (proEtaleConstantRingDerivedPullback (R l E n) f) ⋙
        comparisonLevelTensor l E b X n, HEq t mu := by
  subst C
  cases eq_of_heq hτ
  cases eq_of_heq hA
  cases eq_of_heq hq
  exact ⟨mu, HEq.rfl⟩

private theorem levelTensor_exists (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃ t : comparisonLevelTensor l E b Y n ⋙
        proEtaleConstantRingDerivedPullback (R l E n) f ≅
      (proEtaleConstantRingDerivedPullback (R l E n) f).prod
          (proEtaleConstantRingDerivedPullback (R l E n) f) ⋙
        comparisonLevelTensor l E b X n,
      HEq t ((o.geometry f).generic.levelTensorPullback n) := by
  let g := o.geometry f
  exact levelTensor_transport l E b f n g.generic.coefficients
    g.generic.coefficientTransition g.generic.target g.coefficients g.transitions
    g.target ⟨(g.generic.inverseImage n).modules, g.generic.levelPush n,
      g.generic.levelAdjunction n⟩ (g.levelAdjunction_eq n) (g.generic.levelTensorPullback n)

private theorem levelOpen_tensor_supported (b : Base l E) (o : Operations l E b)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ)
    (K : proEtaleDerivedCategory U (R l E n))
    (L : proEtaleDerivedCategory T (R l E n)) :
    (sfIntrinsicDerivedOpen (R l E n) j).essImage
      ((comparisonLevelTensor l E b T n).obj
        ((sfIntrinsicDerivedOpen (R l E n) j).obj K, L)) := by
  obtain ⟨M, ⟨e⟩⟩ := evaluation_lift l E U n K
  obtain ⟨N, ⟨d⟩⟩ := evaluation_lift l E T n L
  let J := sfIntrinsicDerivedOpen (R l E n) j
  let JT := openD l E b (o.openOp j)
  let t := comparisonLevelTensor l E b T n
  let A := (tensor l E b U).obj (M, (pull l E b (o.geometry j)).obj N)
  refine ⟨(Ev l E U n).obj A, ⟨?_⟩⟩
  exact ((openEvaluation l E b (o.openOp j) n).app A).symm ≪≫
    (Ev l E T n).mapIso (o.openTensor j M N).symm ≪≫
    ((b.calculus T).tensorEvaluation n).app (JT.obj M, N) ≪≫
    t.mapIso (((openEvaluation l E b (o.openOp j) n).app M ≪≫ J.mapIso e).prod d)

private theorem levelOpen_basechange_counit_isIso (b : Base l E)
    {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (n : ℕ)
    (K : proEtaleDerivedCategory U (R l E n)) :
    IsIso ((comparisonLevelOpenAdjunction l E b j' n).counit.app
      ((proEtaleConstantRingDerivedPullback (R l E n) g).obj
        ((sfIntrinsicDerivedOpen (R l E n) j).obj K))) := by
  have := levelOpen_unit_isIso l E b j' n
  obtain ⟨e⟩ := levelOpen_basechange_image l E b h j' j g sq n K
  exact counit_isIso_of_support (comparisonLevelOpenAdjunction l E b j' n)
    ⟨_, ⟨e.symm⟩⟩

private def levelOpenTensorData (b : Base l E) (o : Operations l E b)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ)
    (mu : comparisonLevelTensor l E b T n ⋙
        proEtaleConstantRingDerivedPullback (R l E n) j ≅
      (proEtaleConstantRingDerivedPullback (R l E n) j).prod
          (proEtaleConstantRingDerivedPullback (R l E n) j) ⋙
        comparisonLevelTensor l E b U n)
    (K : proEtaleDerivedCategory U (R l E n))
    (L : proEtaleDerivedCategory T (R l E n)) :
    { z : (comparisonLevelTensor l E b T n).obj
          ((sfIntrinsicDerivedOpen (R l E n) j).obj K, L) ≅
        (sfIntrinsicDerivedOpen (R l E n) j).obj
          ((comparisonLevelTensor l E b U n).obj
            (K, (proEtaleConstantRingDerivedPullback (R l E n) j).obj L)) //
      (comparisonLevelOpenAdjunction l E b j n).homEquiv _ _ z.inv =
        (comparisonLevelTensor l E b U n).map
            (Prod.mkHom ((comparisonLevelOpenAdjunction l E b j n).unit.app K) (𝟙 _)) ≫
          mu.inv.app ((sfIntrinsicDerivedOpen (R l E n) j).obj K, L) } := by
  have := levelOpen_unit_isIso l E b j n
  exact normalizedOpenTensorData (sfIntrinsicDerivedOpen (R l E n) j)
    (proEtaleConstantRingDerivedPullback (R l E n) j)
    (comparisonLevelOpenAdjunction l E b j n)
    (comparisonLevelTensor l E b T n) (comparisonLevelTensor l E b U n) mu K L
    (levelOpen_tensor_supported l E b o j n K L)

private def levelOpenTensor (b : Base l E) (o : Operations l E b)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ)
    (mu : comparisonLevelTensor l E b T n ⋙
        proEtaleConstantRingDerivedPullback (R l E n) j ≅
      (proEtaleConstantRingDerivedPullback (R l E n) j).prod
          (proEtaleConstantRingDerivedPullback (R l E n) j) ⋙
        comparisonLevelTensor l E b U n)
    (K : proEtaleDerivedCategory U (R l E n))
    (L : proEtaleDerivedCategory T (R l E n)) :
    (comparisonLevelTensor l E b T n).obj ((sfIntrinsicDerivedOpen (R l E n) j).obj K, L) ≅
      (sfIntrinsicDerivedOpen (R l E n) j).obj
        ((comparisonLevelTensor l E b U n).obj
          (K, (proEtaleConstantRingDerivedPullback (R l E n) j).obj L)) :=
  (levelOpenTensorData l E b o j n mu K L).val

private def levelOpenExchangeData (b : Base l E)
    {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (n : ℕ) := by
  have := levelOpen_unit_isIso l E b j n
  exact normalizedOpenComparisonData (comparisonLevelOpenAdjunction l E b j n)
    (comparisonLevelOpenAdjunction l E b j' n)
    (proEtaleConstantRingDerivedPullback (R l E n) h)
    (proEtaleConstantRingDerivedPullback (R l E n) g)
    (proEtaleConstantRingPullbackComposition h j (R l E n))
    (congrArg (fun f ↦ proEtaleConstantRingDerivedPullback (R l E n) f) sq.w)
    (proEtaleConstantRingPullbackComposition j' g (R l E n))
    (levelOpen_basechange_counit_isIso l E b h j' j g sq n)

private def levelOpenExchange (b : Base l E)
    {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (n : ℕ) :
    sfIntrinsicDerivedOpen (R l E n) j ⋙
        proEtaleConstantRingDerivedPullback (R l E n) g ≅
      proEtaleConstantRingDerivedPullback (R l E n) h ⋙
        sfIntrinsicDerivedOpen (R l E n) j' :=
  (levelOpenExchangeData l E b h j' j g sq n).iso

private theorem levelOpenTensor_mate (b : Base l E) (o : Operations l E b)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ)
    (mu : comparisonLevelTensor l E b T n ⋙
        proEtaleConstantRingDerivedPullback (R l E n) j ≅
      (proEtaleConstantRingDerivedPullback (R l E n) j).prod
          (proEtaleConstantRingDerivedPullback (R l E n) j) ⋙
        comparisonLevelTensor l E b U n)
    (K : proEtaleDerivedCategory U (R l E n))
    (L : proEtaleDerivedCategory T (R l E n)) :
    (comparisonLevelOpenAdjunction l E b j n).homEquiv _ _
        (levelOpenTensor l E b o j n mu K L).inv =
      (comparisonLevelTensor l E b U n).map
          (Prod.mkHom ((comparisonLevelOpenAdjunction l E b j n).unit.app K) (𝟙 _)) ≫
        mu.inv.app ((sfIntrinsicDerivedOpen (R l E n) j).obj K, L) :=
  (levelOpenTensorData l E b o j n mu K L).property

private theorem levelOpenExchange_mate (b : Base l E)
    {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (n : ℕ)
    (K : proEtaleDerivedCategory U (R l E n)) :
    (comparisonLevelOpenAdjunction l E b j' n).homEquiv _ _
        ((levelOpenExchange l E b h j' j g sq n).inv.app K) =
      (proEtaleConstantRingDerivedPullback (R l E n) h).map
          ((comparisonLevelOpenAdjunction l E b j n).unit.app K) ≫
        ((proEtaleConstantRingPullbackComposition h j (R l E n)).hom ≫
          eqToHom (congrArg (fun a ↦ proEtaleConstantRingDerivedPullback (R l E n) a)
            sq.w) ≫
          (proEtaleConstantRingPullbackComposition j' g (R l E n)).inv).app
            ((sfIntrinsicDerivedOpen (R l E n) j).obj K) :=
  (levelOpenExchangeData l E b h j' j g sq n).mate K

private theorem tensor_evaluation_transport (b : Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : Geometry l E b f) (n : ℕ)
    (t : comparisonLevelTensor l E b Y n ⋙
        proEtaleConstantRingDerivedPullback (R l E n) f ≅
      (proEtaleConstantRingDerivedPullback (R l E n) f).prod
          (proEtaleConstantRingDerivedPullback (R l E n) f) ⋙
        comparisonLevelTensor l E b X n)
    (C : ℕ → Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (τC : ∀ k, C (k + 1) ⟶ C k)
    (A : SemilinearSections.Data.{u + 1, u, u + 1} (Scheme.ProEt.topology X) C τC)
    (hC : C = B l E X) (hτ : HEq τC (tau l E X)) (hA : HEq A (b.calculus X))
    (P : S l E Y ⥤ SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) C τC)
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (hP : HEq g.pull P)
    (q : Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (B l E Y n) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (C n),
      Σ Q : SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (C n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ Q)
    [q.1.Additive] [PreservesFiniteLimits q.1] [PreservesFiniteColimits q.1]
    (hq : HEq q
      (⟨proEtaleConstantRingPullback (R l E n) f,
        proEtaleConstantRingPushforward (R l E n) f,
        proEtaleConstantRingAdjunction (R l E n) f⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n),
          Σ Q : SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology X) (B l E X n) ⥤
            SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ Q))
    (p : P.mapDerivedCategory ⋙ SemilinearSections.e.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) C τC n ≅ Ev l E Y n ⋙ q.1.mapDerivedCategory)
    (hp : HEq (g.pullEvaluation n) p)
    (mu : tensor l E b Y ⋙ P.mapDerivedCategory ≅
      P.mapDerivedCategory.prod P.mapDerivedCategory ⋙ A.closed.tensor)
    (hmu : HEq g.tensorPullback mu)
    (tn : comparisonLevelTensor l E b Y n ⋙ q.1.mapDerivedCategory ≅
      q.1.mapDerivedCategory.prod q.1.mapDerivedCategory ⋙ (A.levelClosed n).tensor)
    (ht : HEq t tn)
    (he : ∀ M N : D l E Y,
      (SemilinearSections.e.{u + 1, u, u + 1} (Scheme.ProEt.topology X) C τC n).map
          (mu.hom.app (M, N)) ≫
        (A.tensorEvaluation n).hom.app (P.mapDerivedCategory.obj M, P.mapDerivedCategory.obj N) ≫
        (A.levelClosed n).tensor.map
          (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
      p.hom.app ((tensor l E b Y).obj (M, N)) ≫
        q.1.mapDerivedCategory.map (((b.calculus Y).tensorEvaluation n).hom.app (M, N)) ≫
        tn.hom.app ((Ev l E Y n).obj M, (Ev l E Y n).obj N))
    (M N : D l E Y) :
    (Ev l E X n).map (g.tensorPullback.hom.app (M, N)) ≫
        ((b.calculus X).tensorEvaluation n).hom.app
          ((pull l E b g).obj M, (pull l E b g).obj N) ≫
        (comparisonLevelTensor l E b X n).map
          (Prod.mkHom ((g.pullEvaluation n).hom.app M) ((g.pullEvaluation n).hom.app N)) =
      (g.pullEvaluation n).hom.app ((tensor l E b Y).obj (M, N)) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) f).map
          (((b.calculus Y).tensorEvaluation n).hom.app (M, N)) ≫
        t.hom.app ((Ev l E Y n).obj M, (Ev l E Y n).obj N) := by
  subst C
  cases eq_of_heq hτ
  cases eq_of_heq hA
  cases eq_of_heq hP
  cases eq_of_heq hq
  cases eq_of_heq hp
  cases eq_of_heq hmu
  cases eq_of_heq ht
  exact he M N

private theorem tensor_evaluation (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (t : comparisonLevelTensor l E b Y n ⋙
        proEtaleConstantRingDerivedPullback (R l E n) f ≅
      (proEtaleConstantRingDerivedPullback (R l E n) f).prod
          (proEtaleConstantRingDerivedPullback (R l E n) f) ⋙
        comparisonLevelTensor l E b X n)
    (ht : HEq t ((o.geometry f).generic.levelTensorPullback n)) (M N : D l E Y) :
    (Ev l E X n).map ((o.geometry f).tensorPullback.hom.app (M, N)) ≫
        ((b.calculus X).tensorEvaluation n).hom.app
          ((pull l E b (o.geometry f)).obj M, (pull l E b (o.geometry f)).obj N) ≫
        (comparisonLevelTensor l E b X n).map
          (Prod.mkHom (((o.geometry f).pullEvaluation n).hom.app M)
            (((o.geometry f).pullEvaluation n).hom.app N)) =
      ((o.geometry f).pullEvaluation n).hom.app ((tensor l E b Y).obj (M, N)) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) f).map
          (((b.calculus Y).tensorEvaluation n).hom.app (M, N)) ≫
        t.hom.app ((Ev l E Y n).obj M, (Ev l E Y n).obj N) := by
  let g := o.geometry f
  exact tensor_evaluation_transport l E b g n t g.generic.coefficients
    g.generic.coefficientTransition g.generic.target g.coefficients g.transitions g.target
    g.generic.pull g.pull_eq
    ⟨(g.generic.inverseImage n).modules, g.generic.levelPush n, g.generic.levelAdjunction n⟩
    (g.levelAdjunction_eq n) (g.generic.pullEvaluation n) (g.pullEvaluation_eq n)
    g.generic.tensorPullback g.tensorPullback_eq (g.generic.levelTensorPullback n) ht
    (g.generic.tensorPullback_evaluation n) M N

private def evaluatedPullTensor (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) (M N : D l E Y) :=
  (proEtaleConstantRingDerivedPullback (R l E n) f).mapIso
      (((b.calculus Y).tensorEvaluation n).app (M, N)).symm ≪≫
    (((o.geometry f).pullEvaluation n).app ((tensor l E b Y).obj (M, N))).symm ≪≫
    (Ev l E X n).mapIso ((o.geometry f).tensorPullback.app (M, N)) ≪≫
    ((b.calculus X).tensorEvaluation n).app
      ((pull l E b (o.geometry f)).obj M, (pull l E b (o.geometry f)).obj N) ≪≫
    (comparisonLevelTensor l E b X n).mapIso
      ((((o.geometry f).pullEvaluation n).app M).prod
        (((o.geometry f).pullEvaluation n).app N))

private theorem evaluatedPullTensor_eq (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (M N : D l E Y) :
    evaluatedPullTensor l E b o f n M N =
      (levels.tensorPullback f n).app ((Ev l E Y n).obj M, (Ev l E Y n).obj N) := by
  apply Iso.ext
  have h := tensor_evaluation l E b o f n (levels.tensorPullback f n)
    (levels.tensorPullback_normalized f n) M N
  simp only [evaluatedPullTensor, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.prod, Iso.app_hom, Iso.app_inv]
  rw [h]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id,
    Category.id_comp]

private theorem openTensor_evaluation (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ) (K : D l E U) (L : D l E T) :
    (Ev l E T n).map ((o.openTensor j K L).inv) ≫
        ((b.calculus T).tensorEvaluation n).hom.app
          ((openD l E b (o.openOp j)).obj K, L) ≫
        (comparisonLevelTensor l E b T n).map
          (Prod.mkHom ((openEvaluation l E b (o.openOp j) n).hom.app K) (𝟙 _)) =
      (openEvaluation l E b (o.openOp j) n).hom.app
          ((tensor l E b U).obj (K, (pull l E b (o.geometry j)).obj L)) ≫
        (sfIntrinsicDerivedOpen (R l E n) j).map
          (((b.calculus U).tensorEvaluation n).hom.app
              (K, (pull l E b (o.geometry j)).obj L) ≫
            (comparisonLevelTensor l E b U n).map (Prod.mkHom (𝟙 _)
              (((o.geometry j).pullEvaluation n).hom.app L))) ≫
        (levels.openTensor j n ((Ev l E U n).obj K) ((Ev l E T n).obj L)).inv := by
  let a := comparisonLevelOpenAdjunction l E b j n
  let p := openEvaluation l E b (o.openOp j) n
  let q := (o.geometry j).pullEvaluation n
  let t := comparisonLevelTensor l E b T n
  let v := comparisonLevelTensor l E b U n
  let P := proEtaleConstantRingDerivedPullback (R l E n) j
  let J := sfIntrinsicDerivedOpen (R l E n) j
  have h := open_projection_evaluation_aux (Ev l E U n) (Ev l E T n)
    (o.openOp j).derivedAdjunction a p q (open_unit_evaluation l E b o j n)
    (tensor l E b U) (tensor l E b T) v t
    ((b.calculus U).tensorEvaluation n) ((b.calculus T).tensorEvaluation n)
    (o.geometry j).tensorPullback K L (o.openTensor j K L).inv (o.openTensor_mate j K L)
  have he := evaluatedPullTensor_eq l E b o levels j n
    ((openD l E b (o.openOp j)).obj K) L
  have he' :
      ((P.mapIso (((b.calculus T).tensorEvaluation n).app
          ((openD l E b (o.openOp j)).obj K, L))).symm ≪≫
        (q.app ((tensor l E b T).obj ((openD l E b (o.openOp j)).obj K, L))).symm ≪≫
        (Ev l E U n).mapIso ((o.geometry j).tensorPullback.app
          ((openD l E b (o.openOp j)).obj K, L)) ≪≫
        ((b.calculus U).tensorEvaluation n).app
          ((pull l E b (o.geometry j)).obj ((openD l E b (o.openOp j)).obj K),
            (pull l E b (o.geometry j)).obj L) ≪≫
        v.mapIso ((q.app ((openD l E b (o.openOp j)).obj K)).prod (q.app L))) =
      (levels.tensorPullback j n).app
        ((Ev l E T n).obj ((openD l E b (o.openOp j)).obj K), (Ev l E T n).obj L) := he
  rw [he'] at h
  have hn := normalized_open_inverse a t v (levels.tensorPullback j n)
    ((Ev l E U n).obj K) ((Ev l E T n).obj ((openD l E b (o.openOp j)).obj K))
    ((Ev l E T n).obj L) (p.app K)
  simp only [Iso.app_hom, Iso.app_inv, Functor.comp_obj, Functor.id_obj] at hn h
  rw [hn] at h
  have hm := levels.openTensor_mate j n ((Ev l E U n).obj K) ((Ev l E T n).obj L)
  rw [← hm, Equiv.symm_apply_apply] at h
  exact h

private def properProjection (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : D l E X) (M : D l E Y) :=
  ((adjunction l E b (o.geometry f)).homEquiv _ _)
    ((o.geometry f).tensorPullback.hom.app ((push l E b (o.geometry f)).obj N, M) ≫
      (tensor l E b X).map
        (Prod.mkHom ((adjunction l E b (o.geometry f)).counit.app N) (𝟙 _)))

private def levelProperProjection (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (N : proEtaleDerivedCategory X (R l E n))
    (M : proEtaleDerivedCategory Y (R l E n)) := by
  let a := (proEtaleConstantRingAdjunction (R l E n) f).mapDerivedCategoryRightDerivedAdjunction
  exact (a.homEquiv _ _)
    ((levels.tensorPullback f n).hom.app
        ((proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctor.obj N, M) ≫
      (comparisonLevelTensor l E b X n).map
        (Prod.mkHom (a.counit.app N) (𝟙 _)))

private theorem properProjection_evaluation (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (N : D l E X) (M : D l E Y) :
    (Ev l E Y n).map (properProjection l E b o f N M) ≫
        ((o.geometry f).pushEvaluation n).hom.app
          ((tensor l E b X).obj (N, (pull l E b (o.geometry f)).obj M)) ≫
        (proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctor.map
          (((b.calculus X).tensorEvaluation n).hom.app
              (N, (pull l E b (o.geometry f)).obj M) ≫
            (comparisonLevelTensor l E b X n).map
              (Prod.mkHom (𝟙 _) (((o.geometry f).pullEvaluation n).hom.app M))) =
      ((b.calculus Y).tensorEvaluation n).hom.app ((push l E b (o.geometry f)).obj N, M) ≫
        (comparisonLevelTensor l E b Y n).map
          (Prod.mkHom (((o.geometry f).pushEvaluation n).hom.app N) (𝟙 _)) ≫
        levelProperProjection l E b o levels f n ((Ev l E X n).obj N) ((Ev l E Y n).obj M) := by
  simpa only [properProjection, levelProperProjection, Functor.comp_obj, Functor.id_obj,
    proEtaleConstantRingDerivedPullback] using
    proper_projection_evaluation_aux (Ev l E Y n) (Ev l E X n)
      (adjunction l E b (o.geometry f))
      (proEtaleConstantRingAdjunction (R l E n) f).mapDerivedCategoryRightDerivedAdjunction
      ((o.geometry f).pullEvaluation n) ((o.geometry f).pushEvaluation n)
      (geometry_adjunction_evaluation l E b (o.geometry f) n).1
      (geometry_adjunction_evaluation l E b (o.geometry f) n).2
      (tensor l E b Y) (tensor l E b X)
      (comparisonLevelTensor l E b Y n) (comparisonLevelTensor l E b X n)
      ((b.calculus Y).tensorEvaluation n) ((b.calculus X).tensorEvaluation n)
      (o.geometry f).tensorPullback (levels.tensorPullback f n)
      (tensor_evaluation l E b o f n (levels.tensorPullback f n)
        (levels.tensorPullback_normalized f n)) N M

private theorem projection_naturality (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K K' : D l E X} {L L' : D l E Y} (a : K ⟶ K') (d : L ⟶ L') :
    (tensor l E b Y).map (Prod.mkHom ((F l E b o c).map a) d) ≫
        projection l E b o c K' L' =
      projection l E b o c K L ≫
        (F l E b o c).map ((tensor l E b X).map
          (Prod.mkHom a ((pull l E b (o.geometry f)).map d))) := by
  let J := openD l E b (o.openOp c.i)
  let P := pull l E b (o.geometry c.g)
  let Q := pull l E b (o.geometry c.i)
  let G := push l E b (o.geometry c.g)
  let A := tensor l E b X
  let B := tensor l E b c.Z
  let C := tensor l E b Y
  let v : P ⋙ Q ≅ pull l E b (o.geometry f) :=
    o.comp c.i c.g ≪≫ eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h)) c.comm.symm)
  have hn := openTensor_naturality J Q (o.openOp c.i).derivedAdjunction B A
    (o.geometry c.i).tensorPullback (o.openTensor c.i) (o.openTensor_mate c.i) a (P.map d)
  have hv := v.hom.naturality d
  dsimp only [Functor.comp_map] at hv
  have htail :
      B.map (Prod.mkHom (J.map a) (P.map d)) ≫
          ((o.openTensor c.i K' (P.obj L')).hom ≫
            J.map (A.map (Prod.mkHom (𝟙 K') (v.hom.app L')))) =
        ((o.openTensor c.i K (P.obj L)).hom ≫
            J.map (A.map (Prod.mkHom (𝟙 K) (v.hom.app L)))) ≫
          J.map (A.map (Prod.mkHom a ((pull l E b (o.geometry f)).map d))) := by
    rw [← Category.assoc, hn, Category.assoc]
    simp only [Category.assoc, ← J.map_comp, ← A.map_comp]
    congr 3
    ext
    · simp
    · simpa only [prod_comp_snd, Prod.mkHom] using hv
  have hp := tensorProjection_naturality P G (adjunction l E b (o.geometry c.g)) C B
    (o.geometry c.g).tensorPullback (J.map a) d
  dsimp only [Functor.comp_obj, Functor.id_obj] at hp
  dsimp only [projection, F, Functor.comp_map, Functor.comp_obj, Functor.id_obj]
  simp only [Category.assoc] at hp ⊢
  dsimp only [v, Iso.trans_hom, NatTrans.comp_app] at htail
  rw [reassoc_of% hp, ← G.map_comp, htail, G.map_comp]

private theorem levelSquare_exists
    {X' X Y' Y : Scheme.{u}} (h : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : h ≫ f = f' ≫ g) (n : ℕ) :
  ∃ s : (proEtaleConstantRingDerivedPullback (R l E n) g ⋙
      proEtaleConstantRingDerivedPullback (R l E n) f' ≅
    proEtaleConstantRingDerivedPullback (R l E n) f ⋙
      proEtaleConstantRingDerivedPullback (R l E n) h), s =
    proEtaleConstantRingPullbackComposition f' g (R l E n) ≪≫
    eqToIso (congrArg (fun a ↦ proEtaleConstantRingDerivedPullback (R l E n) a) w.symm) ≪≫
    (proEtaleConstantRingPullbackComposition h f (R l E n)).symm := by
  exact ⟨_, rfl⟩

-- Preserve the exact compositor without unfolding its derived construction in mate naturality.

private def levelSquare
    {X' X Y' Y : Scheme.{u}} (h : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : h ≫ f = f' ≫ g) (n : ℕ) :
    proEtaleConstantRingDerivedPullback (R l E n) g ⋙
      proEtaleConstantRingDerivedPullback (R l E n) f' ≅
    proEtaleConstantRingDerivedPullback (R l E n) f ⋙
      proEtaleConstantRingDerivedPullback (R l E n) h :=
  Classical.choose (levelSquare_exists l E h f' f g w n)

private theorem levelSquare_eq
    {X' X Y' Y : Scheme.{u}} (h : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : h ≫ f = f' ≫ g) (n : ℕ) :
  levelSquare l E h f' f g w n =
    proEtaleConstantRingPullbackComposition f' g (R l E n) ≪≫
    eqToIso (congrArg (fun a ↦ proEtaleConstantRingDerivedPullback (R l E n) a) w.symm) ≪≫
    (proEtaleConstantRingPullbackComposition h f (R l E n)).symm :=
  Classical.choose_spec (levelSquare_exists l E h f' f g w n)

private theorem square_evaluation (b : Base l E) (o : Operations l E b)
    {X' X Y' Y : Scheme.{u}} (h : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : h ≫ f = f' ≫ g) (n : ℕ) (K : D l E Y) :
    (Ev l E X' n).map ((square l E b o h f' f g w).hom.app K) ≫
        ((o.geometry h).pullEvaluation n).hom.app ((pull l E b (o.geometry f)).obj K) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) h).map
          (((o.geometry f).pullEvaluation n).hom.app K) =
      ((o.geometry f').pullEvaluation n).hom.app ((pull l E b (o.geometry g)).obj K) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) f').map
          (((o.geometry g).pullEvaluation n).hom.app K) ≫
        (levelSquare l E h f' f g w n).hom.app ((Ev l E Y n).obj K) := by
  exact indexedSquare_evaluation (Ev l E X' n)
    (fun a ↦ pull l E b (o.geometry a))
    (fun a ↦ proEtaleConstantRingDerivedPullback (R l E n) a) w.symm
    (o.comp f' g)
    (o.comp h f)
    (proEtaleConstantRingPullbackComposition f' g (R l E n))
    (proEtaleConstantRingPullbackComposition h f (R l E n))
    (square l E b o h f' f g w) (levelSquare l E h f' f g w n) rfl
    (levelSquare_eq l E h f' f g w n)
    K ((Ev l E Y n).obj K)
    (((o.geometry f').pullEvaluation n).hom.app ((pull l E b (o.geometry g)).obj K))
    ((proEtaleConstantRingDerivedPullback (R l E n) f').map
      (((o.geometry g).pullEvaluation n).hom.app K))
    (((o.geometry h).pullEvaluation n).hom.app ((pull l E b (o.geometry f)).obj K))
    ((proEtaleConstantRingDerivedPullback (R l E n) h).map
      (((o.geometry f).pullEvaluation n).hom.app K))
    (fun a ↦ ((o.geometry a).pullEvaluation n).hom.app K)
    (o.comp_evaluation f' g n K)
    (o.comp_evaluation h f n K)

private theorem openTensor_hom_evaluation (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ) (K : D l E U) (L : D l E T) :
    (Ev l E T n).map ((o.openTensor j K L).hom) ≫
        (openEvaluation l E b (o.openOp j) n).hom.app
          ((tensor l E b U).obj (K, (pull l E b (o.geometry j)).obj L)) ≫
        (sfIntrinsicDerivedOpen (R l E n) j).map
          (((b.calculus U).tensorEvaluation n).hom.app
              (K, (pull l E b (o.geometry j)).obj L) ≫
            (comparisonLevelTensor l E b U n).map (Prod.mkHom (𝟙 _)
              (((o.geometry j).pullEvaluation n).hom.app L))) =
      ((b.calculus T).tensorEvaluation n).hom.app
          ((openD l E b (o.openOp j)).obj K, L) ≫
        (comparisonLevelTensor l E b T n).map
          (Prod.mkHom ((openEvaluation l E b (o.openOp j) n).hom.app K) (𝟙 _)) ≫
        (levels.openTensor j n ((Ev l E U n).obj K) ((Ev l E T n).obj L)).hom := by
  simpa only [Functor.comp_obj, Functor.id_obj, Category.assoc] using
    iso_forward_of_inverse (Ev l E T n) (o.openTensor j K L)
      (levels.openTensor j n ((Ev l E U n).obj K) ((Ev l E T n).obj L))
      (((b.calculus T).tensorEvaluation n).hom.app
          ((openD l E b (o.openOp j)).obj K, L) ≫
        (comparisonLevelTensor l E b T n).map
          (Prod.mkHom ((openEvaluation l E b (o.openOp j) n).hom.app K) (𝟙 _)))
      ((openEvaluation l E b (o.openOp j) n).hom.app
          ((tensor l E b U).obj (K, (pull l E b (o.geometry j)).obj L)) ≫
        (sfIntrinsicDerivedOpen (R l E n) j).map
          (((b.calculus U).tensorEvaluation n).hom.app
              (K, (pull l E b (o.geometry j)).obj L) ≫
            (comparisonLevelTensor l E b U n).map (Prod.mkHom (𝟙 _)
              (((o.geometry j).pullEvaluation n).hom.app L))))
      (by simpa only [Functor.comp_obj, Functor.id_obj, Category.assoc] using
        openTensor_evaluation l E b o levels j n K L)

private def projectionTail (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : D l E X) (L : D l E Y) :=
  (o.openTensor c.i K ((pull l E b (o.geometry c.g)).obj L)).hom ≫
    (openD l E b (o.openOp c.i)).map ((tensor l E b X).map
      (Prod.mkHom (𝟙 K) ((o.comp c.i c.g).hom.app L ≫
        (eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h)) c.comm.symm)).hom.app L)))

private def levelProjectionTail (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ)
    (K : proEtaleDerivedCategory X (R l E n))
    (L : proEtaleDerivedCategory Y (R l E n)) :=
  (levels.openTensor c.i n K
      ((proEtaleConstantRingDerivedPullback (R l E n) c.g).obj L)).hom ≫
    (sfIntrinsicDerivedOpen (R l E n) c.i).map
      ((comparisonLevelTensor l E b X n).map (Prod.mkHom (𝟙 K)
        (((proEtaleConstantRingPullbackComposition c.i c.g (R l E n)).hom ≫
          eqToHom (congrArg (fun h ↦ proEtaleConstantRingDerivedPullback (R l E n) h)
            c.comm.symm)).app L)))

private theorem projectionTail_evaluation (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) (K : D l E X) (L : D l E Y) :
    (Ev l E c.Z n).map (projectionTail l E b o c K L) ≫
        (openEvaluation l E b (o.openOp c.i) n).hom.app
          ((tensor l E b X).obj (K, (pull l E b (o.geometry f)).obj L)) ≫
        (sfIntrinsicDerivedOpen (R l E n) c.i).map
          (((b.calculus X).tensorEvaluation n).hom.app
              (K, (pull l E b (o.geometry f)).obj L) ≫
            (comparisonLevelTensor l E b X n).map
              (Prod.mkHom (𝟙 _) (((o.geometry f).pullEvaluation n).hom.app L))) =
      ((b.calculus c.Z).tensorEvaluation n).hom.app
          ((openD l E b (o.openOp c.i)).obj K, (pull l E b (o.geometry c.g)).obj L) ≫
        (comparisonLevelTensor l E b c.Z n).map
          (Prod.mkHom ((openEvaluation l E b (o.openOp c.i) n).hom.app K)
            (((o.geometry c.g).pullEvaluation n).hom.app L)) ≫
        levelProjectionTail l E b o levels c n ((Ev l E X n).obj K) ((Ev l E Y n).obj L) := by
  rcases c with ⟨Z, g, i, w, hg, hi⟩
  subst f
  let := hg
  let := hi
  let c : Compactification (i ≫ g) := ⟨Z, g, i, rfl, hg, hi⟩
  have result := projection_tail_evaluation_aux
      (Ev l E X n) (Ev l E c.Z n) (Ev l E Y n)
      (openD l E b (o.openOp c.i)) (pull l E b (o.geometry c.i))
      (pull l E b (o.geometry c.g)) (pull l E b (o.geometry (i ≫ g)))
      (sfIntrinsicDerivedOpen (R l E n) c.i)
      (proEtaleConstantRingDerivedPullback (R l E n) c.i)
      (proEtaleConstantRingDerivedPullback (R l E n) c.g)
      (proEtaleConstantRingDerivedPullback (R l E n) (i ≫ g))
      (tensor l E b X) (tensor l E b c.Z)
      (comparisonLevelTensor l E b X n) (comparisonLevelTensor l E b c.Z n)
      ((b.calculus X).tensorEvaluation n) ((b.calculus c.Z).tensorEvaluation n)
      (openEvaluation l E b (o.openOp c.i) n) ((o.geometry c.i).pullEvaluation n)
      ((o.geometry c.g).pullEvaluation n) ((o.geometry (i ≫ g)).pullEvaluation n)
      (o.comp c.i c.g) (proEtaleConstantRingPullbackComposition c.i c.g (R l E n))
      (o.openTensor c.i) (levels.openTensor c.i n)
      (o.comp_evaluation c.i c.g n)
      (openTensor_hom_evaluation l E b o levels c.i n)
      (by
        intro M N N' a
        simpa only [CategoryTheory.Functor.map_id] using openTensor_naturality
          (sfIntrinsicDerivedOpen (R l E n) c.i)
          (proEtaleConstantRingDerivedPullback (R l E n) c.i)
          (comparisonLevelOpenAdjunction l E b c.i n)
          (comparisonLevelTensor l E b c.Z n) (comparisonLevelTensor l E b X n)
          (levels.tensorPullback c.i n) (levels.openTensor c.i n)
          (levels.openTensor_mate c.i n) (𝟙 M) a) K L
  simp only [c, projectionTail, levelProjectionTail, Functor.comp_obj, eqToIso_refl,
    eqToHom_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id] at result ⊢
  exact result

private theorem projection_evaluation (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) (K : D l E X) (L : D l E Y) :
    (Ev l E Y n).map (projection l E b o c K L) ≫
        (Fcomparison l E b o c n).hom.app
          ((tensor l E b X).obj (K, (pull l E b (o.geometry f)).obj L)) ≫
        (finiteF l E b c n).map
          (((b.calculus X).tensorEvaluation n).hom.app
            (K, (pull l E b (o.geometry f)).obj L) ≫
            (comparisonLevelTensor l E b X n).map
              (Prod.mkHom (𝟙 _) (((o.geometry f).pullEvaluation n).hom.app L))) =
      ((b.calculus Y).tensorEvaluation n).hom.app ((F l E b o c).obj K, L) ≫
        (comparisonLevelTensor l E b Y n).map
          (Prod.mkHom ((Fcomparison l E b o c n).hom.app K) (𝟙 _)) ≫
        comparisonLevelProjection l E b o levels c n ((Ev l E X n).obj K)
          ((Ev l E Y n).obj L) := by
  rcases c with ⟨Z, g, i, w, hg, hi⟩
  subst f
  let := hg
  let := hi
  let c : Compactification (i ≫ g) := ⟨Z, g, i, rfl, hg, hi⟩
  let J : D l E X ⥤ D l E c.Z := openD l E b (o.openOp c.i)
  let G : D l E c.Z ⥤ D l E Y := push l E b (o.geometry c.g)
  let Gn : proEtaleDerivedCategory c.Z (R l E n) ⥤
      proEtaleDerivedCategory Y (R l E n) :=
    (proEtaleConstantRingPushforward (R l E n) c.g).rightDerivedFunctor
  let Jn := sfIntrinsicDerivedOpen (R l E n) c.i
  let Pn := proEtaleConstantRingDerivedPullback (R l E n) c.g
  let t := comparisonLevelTensor l E b c.Z n
  let s := comparisonLevelTensor l E b Y n
  let e := ((b.calculus c.Z).tensorEvaluation n).hom.app
    (J.obj K, (pull l E b (o.geometry c.g)).obj L)
  let a := (openEvaluation l E b (o.openOp c.i) n).hom.app K
  let d := ((o.geometry c.g).pullEvaluation n).hom.app L
  let z := ((o.geometry c.g).pushEvaluation n).hom.app (J.obj K)
  have hnat := ((o.geometry c.g).pushEvaluation n).hom.naturality
    (projectionTail l E b o c K L)
  dsimp only [Functor.comp_map] at hnat
  have ht := projectionTail_evaluation l E b o levels c n K L
  have hp := properProjection_evaluation l E b o levels c.g n (J.obj K) L
  have hn := tensorProjection_naturality Pn Gn
    (proEtaleConstantRingAdjunction (R l E n) c.g).mapDerivedCategoryRightDerivedAdjunction
    s t (levels.tensorPullback c.g n) a (𝟙 ((Ev l E Y n).obj L))
  simp only [CategoryTheory.Functor.map_id] at hn
  dsimp only [levelProperProjection, Functor.id_obj, Functor.comp_obj] at hn
  have hsplit : t.map (Prod.mkHom a d) =
      t.map (Prod.mkHom (𝟙 _) d) ≫ t.map (Prod.mkHom a (𝟙 _)) := by
    rw [← t.map_comp]
    congr 1
    ext <;> simp
  have hs : s.map (Prod.mkHom (z ≫ Gn.map a) (𝟙 ((Ev l E Y n).obj L))) =
      s.map (Prod.mkHom z (𝟙 _)) ≫ s.map (Prod.mkHom (Gn.map a) (𝟙 _)) := by
    rw [← s.map_comp]
    congr 1
    ext <;> simp
  rw [hsplit] at ht
  have result := projection_combine G (Ev l E c.Z n) (Ev l E Y n) Gn
    (fun Q ↦ ((o.geometry c.g).pushEvaluation n).hom.app Q)
    (properProjection l E b o c.g (J.obj K) L) (projectionTail l E b o c K L)
    ((openEvaluation l E b (o.openOp c.i) n).hom.app
      ((tensor l E b X).obj (K, (pull l E b (o.geometry (i ≫ g))).obj L)))
    (Jn.map (((b.calculus X).tensorEvaluation n).hom.app
        (K, (pull l E b (o.geometry (i ≫ g))).obj L) ≫
      (comparisonLevelTensor l E b X n).map
        (Prod.mkHom (𝟙 _) (((o.geometry (i ≫ g)).pullEvaluation n).hom.app L))))
    (e ≫ t.map (Prod.mkHom (𝟙 _) d)) (t.map (Prod.mkHom a (𝟙 _)))
    (levelProjectionTail l E b o levels c n ((Ev l E X n).obj K) ((Ev l E Y n).obj L))
    (((b.calculus Y).tensorEvaluation n).hom.app ((G.obj (J.obj K)), L))
    (s.map (Prod.mkHom z (𝟙 _))) (s.map (Prod.mkHom (Gn.map a) (𝟙 _)))
    (s.map (Prod.mkHom (z ≫ Gn.map a) (𝟙 _)))
    (levelProperProjection l E b o levels c.g n ((Ev l E c.Z n).obj (J.obj K))
      ((Ev l E Y n).obj L))
    (levelProperProjection l E b o levels c.g n (Jn.obj ((Ev l E X n).obj K))
      ((Ev l E Y n).obj L))
    hnat (by
      simpa only [e, J, Jn, pull, Ev, Functor.id_obj, Functor.comp_obj, Category.assoc]
        using ht) hp hn hs
  simpa only [c, projection, properProjection, projectionTail, comparisonLevelProjection,
    levelProperProjection, levelProjectionTail, Fcomparison, F, finiteF,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, CategoryTheory.Functor.map_id, Functor.map_comp, Functor.comp_map,
    Functor.comp_obj, Functor.id_obj,
    eqToIso_refl, eqToHom_refl, Iso.refl_hom, NatTrans.id_app,
    Category.assoc, J, G, Gn, Jn, Pn, e, a, d, z, s, t] using result

private def geometryCoordinates (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : Geometry l E b f) (n : ℕ) :
    ComparisonAdjunctionCoordinates (Ev l E Y n) (Ev l E X n)
      (adjunction l E b g)
      (proEtaleConstantRingAdjunction (R l E n) f).mapDerivedCategoryRightDerivedAdjunction := by
  let c := geometry_adjunction_evaluation l E b g n
  exact coordinatesOf (adjunction l E b g)
    (proEtaleConstantRingAdjunction (R l E n) f).mapDerivedCategoryRightDerivedAdjunction
    (g.pullEvaluation n) (g.pushEvaluation n) c.1 c.2

private theorem properExchange_evaluation (b : Base l E) (o : Operations l E b)
    {X' X Y' Y : Scheme.{u}} (h : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : h ≫ f = f' ≫ g) (n : ℕ) (K : D l E X) :
    (Ev l E Y' n).map
        ((mateEquiv (adjunction l E b (o.geometry f)) (adjunction l E b (o.geometry f'))
          (TwoSquare.mk _ _ _ _ (square l E b o h f' f g w).hom)).natTrans.app K) ≫
        ((o.geometry f').pushEvaluation n).hom.app ((pull l E b (o.geometry h)).obj K) ≫
        (proEtaleConstantRingPushforward (R l E n) f').rightDerivedFunctor.map
          (((o.geometry h).pullEvaluation n).hom.app K) =
      ((o.geometry g).pullEvaluation n).hom.app ((push l E b (o.geometry f)).obj K) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) g).map
          (((o.geometry f).pushEvaluation n).hom.app K) ≫
        ((mateEquiv
          (proEtaleConstantRingAdjunction (R l E n) f).mapDerivedCategoryRightDerivedAdjunction
          (proEtaleConstantRingAdjunction (R l E n) f').mapDerivedCategoryRightDerivedAdjunction
          (TwoSquare.mk _ _ _ _ (levelSquare l E h f' f g w n).hom)).natTrans.app
            ((Ev l E X n).obj K)) :=
  mate_evaluation_aux (adjunction l E b (o.geometry f)) (adjunction l E b (o.geometry f'))
    (proEtaleConstantRingAdjunction (R l E n) f).mapDerivedCategoryRightDerivedAdjunction
    (proEtaleConstantRingAdjunction (R l E n) f').mapDerivedCategoryRightDerivedAdjunction
    (geometryCoordinates l E b (o.geometry f) n) (geometryCoordinates l E b (o.geometry f') n)
    ((o.geometry g).pullEvaluation n) ((o.geometry h).pullEvaluation n)
    (TwoSquare.mk _ _ _ _ (square l E b o h f' f g w).hom)
    (TwoSquare.mk _ _ _ _ (levelSquare l E h f' f g w n).hom)
    (square_evaluation l E b o h f' f g w n) K

private def levelExchangeWord (b : Base l E) (o : Operations l E b)
    (a : ComparisonLevels l E b o) {X' X Y' Y : Scheme.{u}}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback h f' f g) (c : Compactification f) (n : ℕ) :
    finiteF l E b c n ⋙ proEtaleConstantRingDerivedPullback (R l E n) g ⟶
      proEtaleConstantRingDerivedPullback (R l E n) h ⋙
        finiteF l E b (c.ofIsPullback sq) n :=
  CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
    (sfIntrinsicDerivedOpen (R l E n) c.i)
    (sfIntrinsicDerivedOpen (R l E n) (c.ofIsPullback sq).i)
    (proEtaleConstantRingDerivedPullback (R l E n) c.g)
    (proEtaleConstantRingPushforward (R l E n) c.g).rightDerivedFunctor
    (proEtaleConstantRingAdjunction (R l E n) c.g).mapDerivedCategoryRightDerivedAdjunction
    (proEtaleConstantRingDerivedPullback (R l E n) (c.ofIsPullback sq).g)
    (proEtaleConstantRingPushforward (R l E n) (c.ofIsPullback sq).g).rightDerivedFunctor
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (proEtaleConstantRingAdjunction (R l E n) (c.ofIsPullback sq).g))
    (proEtaleConstantRingDerivedPullback (R l E n) g)
    (proEtaleConstantRingDerivedPullback (R l E n) h)
    (proEtaleConstantRingDerivedPullback (R l E n) (pullback.fst c.g g))
    (levelSquare l E (pullback.fst c.g g) (c.ofIsPullback sq).g c.g g
      pullback.condition n)
    (a.openExchange h (c.ofIsPullback sq).i c.i (pullback.fst c.g g)
      (c.isPullback_i_ofIsPullback sq) n)

private theorem comparisonLevelExchange_word (b : Base l E) (o : Operations l E b)
    (a : ComparisonLevels l E b o) {X' X Y' Y : Scheme.{u}}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback h f' f g) (c : Compactification f) (n : ℕ) :
    comparisonLevelExchange l E b o a sq c n = levelExchangeWord l E b o a sq c n := by
  unfold comparisonLevelExchange levelExchangeWord
  rw [levelSquare_eq]

end AlgebraicGeometry.ProEtale.SpTowerShriek
