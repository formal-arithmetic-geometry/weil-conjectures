/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.HomComplexComponents
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Coherent restriction of ordinary internal Hom complexes

Source: Stacks Project, Tags 0A8X and 08JB.
(blueprint: lem-ringed-hom-restriction-ordinary).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedHomRestriction

private abbrev restricted {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J] (R : Sheaf J CommRingCat.{u}) :=
  (F.sheafPushforwardContinuous CommRingCat K J).obj R

private abbrev restrict {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J] (R : Sheaf J CommRingCat.{u}) :
    Modules R ⥤ Modules (restricted (K := K) F R) :=
  SheafOfModules.pushforward.{u} (F := F) (J := K) (K := J) (R := Rings R)
    (𝟙 ((F.sheafPushforwardContinuous RingCat K J).obj (Rings R)))

attribute [local irreducible] rawFactorMap directFactorMap

attribute [local irreducible] factorIso standardIso directRestrict

private theorem factor_differential
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    {Hn Hm A B E : C} {Kn Km A' B' E' : D}
    (dH : Hn ⟶ Hm) (dK : Kn ⟶ Km)
    (a : Hn ⟶ A) (b : Hn ⟶ B) (c : Hm ⟶ E)
    (α : A ⟶ E) (β : B ⟶ E)
    (a' : Kn ⟶ A') (b' : Kn ⟶ B') (c' : Km ⟶ E')
    (α' : A' ⟶ E') (β' : B' ⟶ E')
    (en : F.obj Hn ⟶ Kn) (em : F.obj Hm ⟶ Km)
    (sa : F.obj A ⟶ A') (sb : F.obj B ⟶ B') (sc : F.obj E ⟶ E') (t : ℤ)
    (hH : dH ≫ c = a ≫ α - t • (b ≫ β))
    (hK : dK ≫ c' = a' ≫ α' - t • (b' ≫ β'))
    (ha : en ≫ a' = F.map a ≫ sa) (hb : en ≫ b' = F.map b ≫ sb)
    (hc : em ≫ c' = F.map c ≫ sc)
    (hα : F.map α ≫ sc = sa ≫ α') (hβ : F.map β ≫ sc = sb ≫ β') :
    (en ≫ dK) ≫ c' = (F.map dH ≫ em) ≫ c' := by
  simp only [Category.assoc, hK, Preadditive.comp_sub,
    Preadditive.comp_zsmul]
  rw [← Category.assoc en a', ha, Category.assoc,
    ← Category.assoc en b', hb, Category.assoc]
  rw [hc, ← Category.assoc (F.map dH), ← F.map_comp, hH]
  simp only [Functor.map_sub, Functor.map_zsmul, Functor.map_comp,
    Preadditive.sub_comp, Preadditive.zsmul_comp, Category.assoc, hα, hβ]

private theorem fanIso {E : Type*} [Category E] {ι : Type*}
    {A B : E} {f g : ι → E} (π : ∀ i, A ⟶ f i) (τ : ∀ i, B ⟶ g i)
    (hπ : IsLimit (Fan.mk A π)) (hτ : IsLimit (Fan.mk B τ)) (e : ∀ i, f i ≅ g i) :
    ∃ a : A ≅ B, ∀ i, a.hom ≫ τ i = π i ≫ (e i).hom := by
  let a := Fan.IsLimit.lift hτ (fun i ↦ π i ≫ (e i).hom)
  let b := Fan.IsLimit.lift hπ (fun i ↦ τ i ≫ (e i).inv)
  have ha (i) : a ≫ τ i = π i ≫ (e i).hom := Fan.IsLimit.fac hτ _ i
  have hb (i) : b ≫ π i = τ i ≫ (e i).inv := Fan.IsLimit.fac hπ _ i
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · apply Fan.IsLimit.hom_ext hπ
    intro i
    change (a ≫ b) ≫ π i = (𝟙 A) ≫ π i
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply Fan.IsLimit.hom_ext hτ
    intro i
    change (b ≫ a) ≫ τ i = (𝟙 B) ≫ τ i
    rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

private abbrev termwise {A B : Type*} [Category A] [Category B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] (T : A ⥤ B) [T.PreservesZeroMorphisms] :=
  T.mapHomologicalComplex (.up ℤ)

private structure ComplexHomShape (A : Type*) [Category A] [Preadditive A] where
  H : ((CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ) ⥤ CochainComplex A ℤ
  obj : A → A → A
  map : ∀ {M M' N N' : A}, (M' ⟶ M) → (N ⟶ N') → (obj M N ⟶ obj M' N')

private structure ComplexHomData {A : Type*} [Category A] [Preadditive A]
    (S : ComplexHomShape A) where
  π : ∀ (L M : CochainComplex A ℤ) (n p q : ℤ) (_h : p + n = q),
    (S.H.obj (op L, M)).X n ⟶ S.obj (L.X p) (M.X q)
  isLimit : ∀ L M n,
    IsLimit (Fan.mk ((S.H.obj (op L, M)).X n) (fun p : ℤ ↦ π L M n p (p + n) rfl))
  d_π : ∀ L M n m p q q' p' (_hnm : n + 1 = m) (hpq : p + m = q)
      (hq' : p + n = q') (hp' : p' + n = q),
    (S.H.obj (op L, M)).d n m ≫ π L M m p q hpq =
      π L M n p q' hq' ≫ S.map (𝟙 (L.X p)) (M.d q' q) -
        n.negOnePow • (π L M n p' q hp' ≫ S.map (L.d p p') (𝟙 (M.X q)))
  map_π : ∀ {X Y : (CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ} (f : X ⟶ Y)
      n p q (h : p + n = q),
    (S.H.map f).f n ≫ π Y.1.unop Y.2 n p q h =
      π X.1.unop X.2 n p q h ≫ S.map (f.1.unop.f p) (f.2.f q)

private abbrev ComplexHomData.H {A : Type*} [Category A] [Preadditive A]
    {S : ComplexHomShape A} (_R : ComplexHomData S) := S.H

private abbrev ComplexHomData.obj {A : Type*} [Category A] [Preadditive A]
    {S : ComplexHomShape A} (_R : ComplexHomData S) := S.obj

private abbrev ComplexHomData.map {A : Type*} [Category A] [Preadditive A]
    {S : ComplexHomShape A} (_R : ComplexHomData S) := @S.map

attribute [local irreducible] homComplexFunctor ordinaryData

private def gradedIso
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B) [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
    (L M : (CochainComplex A ℤ)) (n : ℤ) :
    T.obj ((R.H.obj (op L, M)).X n) ≅
      (S.H.obj (op ((termwise T).obj L), (termwise T).obj M)).X n :=
  (fanIso _ _
    (isLimitFanMkObjOfIsLimit T _ _ (R.isLimit L M n))
    (S.isLimit ((termwise T).obj L) ((termwise T).obj M) n)
    (fun p ↦ γ (L.X p) (M.X (p + n)))).choose

attribute [local irreducible] gradedIso

private theorem gradedIso_comm
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B)
      [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
    (hγ : ∀ {M M' N N' : A} (f : M' ⟶ M) (g : N ⟶ N'),
      T.map (R.map f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ S.map (T.map f) (T.map g))
    (L M : (CochainComplex A ℤ))
      (n m : ℤ) (hnm : n + 1 = m) :
      (gradedIso R S T γ L M n).hom ≫
        (S.H.obj (op ((termwise T).obj L), (termwise T).obj M)).d n m =
        T.map ((R.H.obj (op L, M)).d n m) ≫ (gradedIso R S T γ L M m).hom := by
    apply (S.isLimit ((termwise T).obj L) ((termwise T).obj M) m).hom_ext
    rintro ⟨p⟩
    change ((gradedIso R S T γ L M n).hom ≫ _) ≫
      S.π ((termwise T).obj L) ((termwise T).obj M) m p (p + m) rfl =
      (T.map _ ≫ (gradedIso R S T γ L M m).hom) ≫
      S.π ((termwise T).obj L) ((termwise T).obj M) m p (p + m) rfl
    have hH := R.d_π L M n m p (p + m) (p + n) (p + 1)
      hnm rfl rfl (by omega)
    have hK := S.d_π ((termwise T).obj L) ((termwise T).obj M)
      n m p (p + m) (p + n) (p + 1)
      hnm rfl rfl (by omega)
    simp only [Units.smul_def] at hH hK
    have hh := factor_differential (C := A) (D :=
      B) T
      ((R.H.obj (op L, M)).d n m)
      ((S.H.obj (op ((termwise T).obj L), (termwise T).obj M)).d n m)
      (R.π L M n p (p + n) rfl)
      (R.π L M n (p + 1) (p + m) (by omega))
      (R.π L M m p (p + m) rfl)
      (R.map (𝟙 (L.X p)) (M.d (p + n) (p + m)))
      (R.map (L.d p (p + 1)) (𝟙 (M.X (p + m))))
      (S.π ((termwise T).obj L) ((termwise T).obj M) n p (p + n) rfl)
      (S.π ((termwise T).obj L) ((termwise T).obj M) n (p + 1) (p + m) (by omega))
      (S.π ((termwise T).obj L) ((termwise T).obj M) m p (p + m) rfl)
      (S.map (𝟙 (((termwise T).obj L).X p))
        (((termwise T).obj M).d (p + n) (p + m)))
      (S.map (((termwise T).obj L).d p (p + 1))
        (𝟙 (((termwise T).obj M).X (p + m))))
      (gradedIso R S T γ L M n).hom (gradedIso R S T γ L M m).hom
      (γ (L.X p) (M.X (p + n))).hom
      (γ (L.X (p + 1)) (M.X (p + m))).hom
      (γ (L.X p) (M.X (p + m))).hom (n.negOnePow : ℤ) hH hK
      (gradedIso_π R S T γ L M n p (p + n) rfl)
      (gradedIso_π R S T γ L M n (p + 1) (p + m) (by omega))
      (gradedIso_π R S T γ L M m p (p + m) rfl)
    apply hh
    · dsimp only [termwise, Functor.mapHomologicalComplex]
      simpa only [Functor.map_id] using
        hγ (𝟙 (L.X p)) (M.d (p + n) (p + m))
    · dsimp only [termwise, Functor.mapHomologicalComplex]
      simpa only [Functor.map_id] using
        hγ (L.d p (p + 1)) (𝟙 (M.X (p + m)))

private def comparisonObj
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B)
      [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
    (hγ : ∀ {M M' N N' : A} (f : M' ⟶ M) (g : N ⟶ N'),
      T.map (R.map f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ S.map (T.map f) (T.map g))
    (L M : (CochainComplex A ℤ)) :
    (termwise T).obj ((R.H).obj (op L, M)) ≅
      (S.H).obj (op ((termwise T).obj L), (termwise T).obj M) :=
  HomologicalComplex.Hom.isoOfComponents (gradedIso R S T γ L M)
    (gradedIso_comm R S T γ hγ L M)

private theorem comparisonObj_naturality
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B)
      [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
    (hγ : ∀ {M M' N N' : A} (f : M' ⟶ M) (g : N ⟶ N'),
      T.map (R.map f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ S.map (T.map f) (T.map g))
    {X Y : ((CochainComplex A ℤ))ᵒᵖ × (CochainComplex A ℤ)} (f : X ⟶ Y) :
      (R.H ⋙ termwise T).map f ≫ (comparisonObj R S T γ hγ Y.1.unop Y.2).hom =
        (comparisonObj R S T γ hγ X.1.unop X.2).hom ≫
          (((termwise T).op.prod (termwise T)) ⋙ S.H).map f := by
    rcases X with ⟨⟨L⟩, M⟩
    rcases Y with ⟨⟨L'⟩, M'⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply (S.isLimit ((termwise T).obj L') ((termwise T).obj M') n).hom_ext
    rintro ⟨p⟩
    change (T.map (((R.H).map f).f n) ≫ (gradedIso R S T γ L' M' n).hom) ≫
        S.π ((termwise T).obj L') ((termwise T).obj M') n p (p + n) rfl =
      ((gradedIso R S T γ L M n).hom ≫
          ((S.H).map (((termwise T).op.prod (termwise T)).map f)).f n) ≫
        S.π ((termwise T).obj L') ((termwise T).obj M') n p (p + n) rfl
    have hR := R.map_π f n p (p + n) rfl
    have hS := S.map_π (((termwise T).op.prod (termwise T)).map f)
      n p (p + n) rfl
    change (S.H.map (((termwise T).op.prod (termwise T)).map f)).f n ≫
        S.π ((termwise T).obj L') ((termwise T).obj M') n p (p + n) rfl =
      S.π ((termwise T).obj L) ((termwise T).obj M) n p (p + n) rfl ≫
        S.map (T.map (f.1.unop.f p)) (T.map (f.2.f (p + n))) at hS
    rw [Category.assoc, gradedIso_π, ← Category.assoc, ← T.map_comp, hR,
      T.map_comp, Category.assoc, hγ, ← Category.assoc, ← gradedIso_π, Category.assoc]
    simpa only [Category.assoc] using
      congrArg ((gradedIso R S T γ L M n).hom ≫ ·) hS.symm

attribute [local irreducible] comparisonObj

private def comparison
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B)
      [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
    (hγ : ∀ {M M' N N' : A} (f : M' ⟶ M) (g : N ⟶ N'),
      T.map (R.map f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ S.map (T.map f) (T.map g)) :
    R.H ⋙ termwise T ≅ ((termwise T).op.prod (termwise T)) ⋙ S.H :=
  NatIso.ofComponents (fun X ↦ comparisonObj R S T γ hγ X.1.unop X.2)
    (fun f ↦ comparisonObj_naturality R S T γ hγ f)

attribute [local irreducible] comparison

where
  iso : R.H ⋙ termwise T ≅ ((termwise T).op.prod (termwise T)) ⋙ S.H
  π : ∀ (L M : CochainComplex A ℤ) (n p q : ℤ) (h : p + n = q),
    (iso.hom.app (op L, M)).f n ≫
        S.π ((termwise T).obj L) ((termwise T).obj M) n p q h =
      T.map (R.π L M n p q h) ≫ (γ (L.X p) (M.X q)).hom

attribute [local irreducible] sliceComparisonData mapComparisonData

end CategoryTheory.RingedHomRestriction
