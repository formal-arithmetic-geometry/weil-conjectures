/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.DerivedInternalHomSectionsModel.DerivedInternalHomSectionsModel
public import WeilConjectures.CategoryTheory.SmoothPurity.HomComplexGlobalHomotopyOfUniverses

/-! # The ordinary-to-resolved global Hom roof

Source: Stacks Project, dga.tex, Example 09L9 (example-category-complexes),
derived.tex, Lemma 070I (lemma-K-injective), and sites-cohomology.tex, Section 0B6E.
(blueprint: lem-sf-global-hom-resolution-roof)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.HomComplex

namespace CategoryTheory

variable (B : Type v) [CommRing B] {A : Type u} [Category.{v} A] [Abelian A] [Linear B A]

/-- Product Hom with scalars retained, using Mathlib's cochains and exact signed differential.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHom (X Y : CochainComplex A ℤ) : CochainComplex (ModuleCat.{v} B) ℤ where
  X n := ModuleCat.of B (Cochain X Y n)
  d n m := ModuleCat.ofHom (δ_hom B X Y n m)
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_shape n m h z
  d_comp_d' n m k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_δ n m k z

/-- The degreewise pre/postcomposition map on the existing linear cochains.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHomMapTerm {X X' Y Y' : CochainComplex A ℤ}
    (a : X' ⟶ X) (b : Y ⟶ Y') (n : ℤ) :
    (globalLinearHom B X Y).X n ⟶ (globalLinearHom B X' Y').X n :=
  ModuleCat.ofHom
    { toFun := fun f ↦ (Cochain.ofHom a).comp (f.comp (Cochain.ofHom b) (add_zero n))
        (zero_add n)
      map_add' := by intros; simp
      map_smul' := by intros; simp }

/-- The pre/postcomposition maps commute with the Hom differential.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof).
Proof: expand both differentials as `d_Y f - (-1)^n f d_X`, and use the chain-map
identities for `a` and `b`. The two expressions agree componentwise. -/
theorem globalLinearHomMap_comm {X X' Y Y' : CochainComplex A ℤ}
    (a : X' ⟶ X) (b : Y ⟶ Y') (n m : ℤ) :
    globalLinearHomMapTerm B a b n ≫ (globalLinearHom B X' Y').d n m =
      (globalLinearHom B X Y).d n m ≫ globalLinearHomMapTerm B a b m := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change δ n m ((Cochain.ofHom a).comp
      (z.comp (Cochain.ofHom b) (add_zero n)) (zero_add n)) =
    (Cochain.ofHom a).comp
      ((δ n m z).comp (Cochain.ofHom b) (add_zero m)) (zero_add m)
  rw [δ_ofHom_comp, δ_comp_ofHom]

/-- Actual pre/postcomposition chain map, with its prescribed component formula.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHomMap {X X' Y Y' : CochainComplex A ℤ} (a : X' ⟶ X) (b : Y ⟶ Y') :
    globalLinearHom B X Y ⟶ globalLinearHom B X' Y' where
  f := globalLinearHomMapTerm B a b
  comm' n m _ := globalLinearHomMap_comm B a b n m

/-- A resolution is only a complex and its given quasi-isomorphism, with the usual
K-injectivity predicate; no linear or functorial choice is part of this input.
Source: Stacks 070I (blueprint: lem-sf-global-hom-resolution-roof). -/
structure GlobalHomResolution (X : CochainComplex A ℤ) where
  I : CochainComplex A ℤ
  ι : X ⟶ I
  injective : I.IsKInjective
  quasiIso : QuasiIso ι

/-- The identity resolution of a K-injective complex.
Source: Stacks 070I (blueprint: lem-sf-global-hom-resolution-roof). -/
def GlobalHomResolution.self (X : CochainComplex A ℤ) [X.IsKInjective] :
    GlobalHomResolution X := ⟨X, 𝟙 X, inferInstance, inferInstance⟩

/-- Shift the actual augmentation, using the standard signed cochain shift.
Source: Stacks 09L9, 070I (blueprint: lem-sf-global-hom-resolution-roof). -/
def GlobalHomResolution.shift {X : CochainComplex A ℤ} (R : GlobalHomResolution X) (n : ℤ) :
    GlobalHomResolution (X⟦n⟧) :=
  ⟨R.I⟦n⟧, (shiftFunctor _ n).map R.ι, inferInstance, inferInstance⟩

/-- The resolved Hom object on the specified resolutions, exactly `q H(I_X,I_Y)`.
Source: Stacks 0B6E (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalResolvedHom {X Y : CochainComplex A ℤ}
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) :
    DerivedCategory (ModuleCat.{v} B) :=
  DerivedCategory.Q.obj (globalLinearHom B R.I S.I)

/-- The actual class of an abstract cycle in the cohomology of the localized complex.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHomClass (X Y : CochainComplex A ℤ) (n : ℤ)
    (z : (globalLinearHom B X Y).cycles n) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj
      (DerivedCategory.Q.obj (globalLinearHom B X Y)) :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} B) n).inv.app
    (globalLinearHom B X Y) ((globalLinearHom B X Y).homologyπ n z)

private def roof_forgetIso (X Y : CochainComplex A ℤ) :
    ((forget₂ (ModuleCat B) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
      (globalLinearHom B X Y) ≅ CochainComplex.HomComplex X Y :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro n m h
    ext z
    rfl)

private theorem roof_precomp_quasiIso
    {X X' J : CochainComplex A ℤ} (a : X' ⟶ X) [QuasiIso a] [J.IsKInjective] :
    QuasiIso (globalLinearHomMap B a (𝟙 J)) := by
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (globalLinearHomMap B a (𝟙 J)) (forget₂ (ModuleCat B) AddCommGrpCat)).mp
  have h : ((forget₂ (ModuleCat B) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
      (globalLinearHomMap B a (𝟙 J)) =
      (roof_forgetIso B X J).hom ≫ externalMap a (𝟙 J) ≫
        (roof_forgetIso B X' J).inv := by
    ext n z
    change (Cochain.ofHom a).comp (z.comp (Cochain.ofHom (𝟙 J)) (add_zero n))
      (zero_add n) = ((Cochain.ofHom a).comp z (zero_add n)).comp
        (Cochain.ofHom (𝟙 J)) (add_zero n)
    exact (Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ _).symm
  rw [h]
  have := DerivedInternalHomSectionsModel.externalMap_quasiIso a (B := J)
  infer_instance

private theorem roof_precomp_quotient
    {K L T : CochainComplex A ℤ} (a : K ⟶ L) [QuasiIso a] [T.IsKInjective] :
    Function.Bijective (fun f :
      (HomotopyCategory.quotient A (.up ℤ)).obj L ⟶
        (HomotopyCategory.quotient A (.up ℤ)).obj T ↦
      (HomotopyCategory.quotient A (.up ℤ)).map a ≫ f) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let b := DerivedCategory.Qh.map (q.map a)
  have hb : IsIso b := by
    change IsIso ((q ⋙ DerivedCategory.Qh).map a)
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) a).2 inferInstance
  have hK := CochainComplex.IsKInjective.Qh_map_bijective (q.obj K) T
  have hL := CochainComplex.IsKInjective.Qh_map_bijective (q.obj L) T
  constructor
  · intro f g h
    apply hL.injective
    apply (cancel_epi b).mp
    simpa only [b, q, Functor.map_comp] using congrArg DerivedCategory.Qh.map h
  · intro g
    obtain ⟨f, hf⟩ := hL.surjective (inv b ≫ DerivedCategory.Qh.map g)
    refine ⟨f, hK.injective ?_⟩
    rw [Functor.map_comp, hf]
    exact IsIso.hom_inv_id_assoc b _

private theorem roof_lifts (X Y : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (a : X ⟶ Y) :
    ∃ a' : R.I ⟶ S.I, Nonempty (Homotopy (R.ι ≫ a') (a ≫ S.ι)) ∧
      ∀ a'' : R.I ⟶ S.I, Nonempty (Homotopy (R.ι ≫ a'') (a ≫ S.ι)) →
        Nonempty (Homotopy a' a'') := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  obtain ⟨f, hf⟩ := (roof_precomp_quotient R.ι).surjective (q.map (a ≫ S.ι))
  obtain ⟨a', rfl⟩ := q.map_surjective f
  have ha : q.map (R.ι ≫ a') = q.map (a ≫ S.ι) := by
    rw [Functor.map_comp]
    exact hf
  refine ⟨a', ⟨HomotopyCategory.homotopyOfEq _ _ ha⟩, ?_⟩
  intro a'' ⟨ha''⟩
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  apply (roof_precomp_quotient R.ι).injective
  dsimp [q]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact ha.trans (HomotopyCategory.eq_of_homotopy _ _ ha'').symm

private theorem roof_comparison_lifts (X : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) :
    ∃ a : HomotopyEquiv R.I R'.I, Nonempty (Homotopy (R.ι ≫ a.hom) R'.ι) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  obtain ⟨a, ⟨ha⟩, _⟩ := roof_lifts X X R R' (𝟙 X)
  obtain ⟨b, ⟨hb⟩, _⟩ := roof_lifts X X R' R (𝟙 X)
  have ha' : q.map R.ι ≫ q.map a = q.map R'.ι := by
    simpa using HomotopyCategory.eq_of_homotopy _ _ ha
  have hb' : q.map R'.ι ≫ q.map b = q.map R.ι := by
    simpa using HomotopyCategory.eq_of_homotopy _ _ hb
  refine ⟨⟨a, b, HomotopyCategory.homotopyOfEq _ _ ?_,
    HomotopyCategory.homotopyOfEq _ _ ?_⟩, ?_⟩
  · apply (roof_precomp_quotient R.ι).injective
    simp only [Functor.map_comp, Functor.map_id, Category.comp_id, ← Category.assoc]
    rw [ha', hb']
  · apply (roof_precomp_quotient R'.ι).injective
    simp only [Functor.map_comp, Functor.map_id, Category.comp_id, ← Category.assoc]
    rw [hb', ha']
  · simpa using Nonempty.intro ha

private theorem roof_map_id (X Y : CochainComplex A ℤ) :
    globalLinearHomMap B (𝟙 X) (𝟙 Y) = 𝟙 (globalLinearHom B X Y) := by
  ext n z
  change (Cochain.ofHom (𝟙 X)).comp (z.comp (Cochain.ofHom (𝟙 Y)) (add_zero n))
    (zero_add n) = z
  simp

private theorem roof_map_comp
    {X X' X'' Y Y' Y'' : CochainComplex A ℤ}
    (a : X' ⟶ X) (a' : X'' ⟶ X') (b : Y ⟶ Y') (b' : Y' ⟶ Y'') :
    globalLinearHomMap B a b ≫ globalLinearHomMap B a' b' =
      globalLinearHomMap B (a' ≫ a) (b ≫ b') := by
  ext n z
  change (Cochain.ofHom a').comp
    (((Cochain.ofHom a).comp (z.comp (Cochain.ofHom b) (add_zero n))
      (zero_add n)).comp (Cochain.ofHom b') (add_zero n)) (zero_add n) =
    (Cochain.ofHom (a' ≫ a)).comp (z.comp (Cochain.ofHom (b ≫ b'))
      (add_zero n)) (zero_add n)
  ext p q hpq
  simp [Category.assoc]

private def roof_precomp_homotopy {X X' Y : CochainComplex A ℤ}
    {a a' : X' ⟶ X} (h : Homotopy a a') :
    Homotopy (globalLinearHomMap B a (𝟙 Y)) (globalLinearHomMap B a' (𝟙 Y)) := by
  let s : Cochain (globalLinearHom B X Y) (globalLinearHom B X' Y) (-1) :=
    Cochain.mk fun j k hjk ↦ ModuleCat.ofHom
      { toFun := fun φ ↦ j.negOnePow • (Cochain.ofHomotopy h).comp φ (by omega)
        map_add' := fun φ ψ ↦ by simp [smul_add]
        map_smul' := fun b φ ↦ by simp [smul_comm b j.negOnePow] }
  refine (Cochain.equivHomotopy _ _).symm ⟨s, ?_⟩
  apply Cochain.ext₀
  intro j
  simp only [Cochain.add_v]
  rw [δ_v (-1) 0 (by omega) s j j (by omega) (j - 1) (j + 1)
    (by omega) (by omega)]
  simp only [Cochain.ofHom_v]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  dsimp [s, globalLinearHomMap, globalLinearHomMapTerm, globalLinearHom, δ_hom]
  simp only [one_smul]
  change (Cochain.ofHom a).comp (φ.comp (Cochain.ofHom (𝟙 Y)) (add_zero j))
      (zero_add j) =
    δ (j - 1) j (j.negOnePow • (Cochain.ofHomotopy h).comp φ (by omega)) +
      (j + 1).negOnePow • (Cochain.ofHomotopy h).comp (δ j (j + 1) φ) (by omega) +
      (Cochain.ofHom a').comp (φ.comp (Cochain.ofHom (𝟙 Y)) (add_zero j))
        (zero_add j)
  rw [δ_units_smul, δ_comp (Cochain.ofHomotopy h) φ (by omega)
    0 (j + 1) j (by omega) (by omega) rfl, δ_ofHomotopy]
  simp only [smul_add, smul_smul, Int.units_mul_self, one_smul,
    Int.negOnePow_succ, Units.neg_smul, Cochain.sub_comp, Cochain.comp_id]
  abel

private def roof_postcomp_homotopy {X Y Y' : CochainComplex A ℤ}
    {b b' : Y ⟶ Y'} (h : Homotopy b b') :
    Homotopy (globalLinearHomMap B (𝟙 X) b) (globalLinearHomMap B (𝟙 X) b') := by
  let s : Cochain (globalLinearHom B X Y) (globalLinearHom B X Y') (-1) :=
    Cochain.mk fun j k hjk ↦ ModuleCat.ofHom
      { toFun := fun φ ↦ φ.comp (Cochain.ofHomotopy h) (by omega)
        map_add' := fun φ ψ ↦ by simp
        map_smul' := fun b φ ↦ by simp }
  refine (Cochain.equivHomotopy _ _).symm ⟨s, ?_⟩
  apply Cochain.ext₀
  intro j
  simp only [Cochain.add_v]
  rw [δ_v (-1) 0 (by omega) s j j (by omega) (j - 1) (j + 1)
    (by omega) (by omega)]
  simp only [Cochain.ofHom_v]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  dsimp [s, globalLinearHomMap, globalLinearHomMapTerm, globalLinearHom, δ_hom]
  simp only [one_smul]
  change (Cochain.ofHom (𝟙 X)).comp (φ.comp (Cochain.ofHom b) (add_zero j))
      (zero_add j) =
    δ (j - 1) j (φ.comp (Cochain.ofHomotopy h) (by omega)) +
      (δ j (j + 1) φ).comp (Cochain.ofHomotopy h) (by omega) +
      (Cochain.ofHom (𝟙 X)).comp (φ.comp (Cochain.ofHom b') (add_zero j))
        (zero_add j)
  rw [δ_comp φ (Cochain.ofHomotopy h) (by omega)
    (j + 1) 0 j (by omega) rfl (by omega), δ_ofHomotopy]
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    Cochain.comp_sub, Cochain.id_comp]
  abel

private theorem roof_homotopy_invariance
    {X X' Y Y' : CochainComplex A ℤ} (a a' : X' ⟶ X) (b b' : Y ⟶ Y')
    (ha : Nonempty (Homotopy a a')) (hb : Nonempty (Homotopy b b')) :
    DerivedCategory.Q.map (globalLinearHomMap B a b) =
      DerivedCategory.Q.map (globalLinearHomMap B a' b') := by
  have he (a : X' ⟶ X) (b : Y ⟶ Y') :
      globalLinearHomMap B a b =
        globalLinearHomMap B a (𝟙 Y) ≫ globalLinearHomMap B (𝟙 X') b := by
    rw [roof_map_comp]
    simp
  rw [he a b, he a' b', Functor.map_comp, Functor.map_comp]
  rw [DerivedCategory.Q_map_eq_of_homotopy (C := ModuleCat B)
      (roof_precomp_homotopy B ha.some),
    DerivedCategory.Q_map_eq_of_homotopy (C := ModuleCat B)
      (roof_postcomp_homotopy B hb.some)]

private noncomputable def roof_c
    (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) :
    DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S :=
  letI := roof_precomp_quasiIso B R.ι (J := S.I)
  DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) S.ι) ≫
    inv (DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)))

private theorem roof_c_roof
    (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) :
    roof_c B X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)) =
      DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) S.ι) := by
  letI := roof_precomp_quasiIso B R.ι (J := S.I)
  dsimp [roof_c]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

private theorem roof_Q_comp
    {X X' X'' Y Y' Y'' : CochainComplex A ℤ}
    (a : X' ⟶ X) (a' : X'' ⟶ X') (b : Y ⟶ Y') (b' : Y' ⟶ Y'') :
    DerivedCategory.Q.map (globalLinearHomMap B a b) ≫
        DerivedCategory.Q.map (globalLinearHomMap B a' b') =
      DerivedCategory.Q.map (globalLinearHomMap B (a' ≫ a) (b ≫ b')) := by
  rw [← Functor.map_comp, roof_map_comp]

private theorem roof_naturality
    (X X' Y Y' : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (R' : GlobalHomResolution X')
    (S : GlobalHomResolution Y) (S' : GlobalHomResolution Y')
    (a : X' ⟶ X) (b : Y ⟶ Y') (a' : R'.I ⟶ R.I) (b' : S.I ⟶ S'.I)
    (ha : Nonempty (Homotopy (R'.ι ≫ a') (a ≫ R.ι)))
    (hb : Nonempty (Homotopy (S.ι ≫ b') (b ≫ S'.ι))) :
    DerivedCategory.Q.map (globalLinearHomMap B a b) ≫ roof_c B X' Y' R' S' =
      roof_c B X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B a' b') := by
  haveI := roof_precomp_quasiIso B R'.ι (J := S'.I)
  have hj : DerivedCategory.Q.map (globalLinearHomMap B a' b') ≫
      DerivedCategory.Q.map (globalLinearHomMap B R'.ι (𝟙 S'.I)) =
      DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)) ≫
        DerivedCategory.Q.map (globalLinearHomMap B a b') := by
    rw [roof_Q_comp, roof_Q_comp]
    simpa only [Category.id_comp, Category.comp_id] using
      roof_homotopy_invariance B (R'.ι ≫ a') (a ≫ R.ι) b' b' ha
        ⟨Homotopy.refl _⟩
  apply (cancel_mono (DerivedCategory.Q.map (globalLinearHomMap B R'.ι (𝟙 S'.I)))).mp
  rw [Category.assoc, roof_c_roof, Category.assoc, hj,
    ← Category.assoc, roof_c_roof, roof_Q_comp, roof_Q_comp]
  simpa only [Category.id_comp, Category.comp_id] using
    (roof_homotopy_invariance B a a (S.ι ≫ b') (b ≫ S'.ι)
      ⟨Homotopy.refl _⟩ hb).symm

private def roof_homIso {X X' Y Y' : CochainComplex A ℤ}
    (a : HomotopyEquiv X X') (b : HomotopyEquiv Y Y') :
    DerivedCategory.Q.obj (globalLinearHom B X Y) ≅
      DerivedCategory.Q.obj (globalLinearHom B X' Y') where
  hom := DerivedCategory.Q.map (globalLinearHomMap B a.inv b.hom)
  inv := DerivedCategory.Q.map (globalLinearHomMap B a.hom b.inv)
  hom_inv_id := by
    rw [roof_Q_comp, roof_homotopy_invariance B _ (𝟙 X) _ (𝟙 Y)
      ⟨a.homotopyHomInvId⟩ ⟨b.homotopyHomInvId⟩, roof_map_id, Functor.map_id]
  inv_hom_id := by
    rw [roof_Q_comp, roof_homotopy_invariance B _ (𝟙 X') _ (𝟙 Y')
      ⟨a.homotopyInvHomId⟩ ⟨b.homotopyInvHomId⟩, roof_map_id, Functor.map_id]

private def roof_e {X : CochainComplex A ℤ} (R R' : GlobalHomResolution X) :
    HomotopyEquiv R.I R'.I := (roof_comparison_lifts X R R').choose

private theorem roof_e_comm {X : CochainComplex A ℤ} (R R' : GlobalHomResolution X) :
    Nonempty (Homotopy (R.ι ≫ (roof_e R R').hom) R'.ι) :=
  (roof_comparison_lifts X R R').choose_spec

private theorem roof_lift_unique {X : CochainComplex A ℤ}
    (R R' : GlobalHomResolution X) (a b : R.I ⟶ R'.I)
    (ha : Nonempty (Homotopy (R.ι ≫ a) R'.ι))
    (hb : Nonempty (Homotopy (R.ι ≫ b) R'.ι)) : Nonempty (Homotopy a b) := by
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ((roof_precomp_quotient R.ι).injective ?_)⟩
  simpa only [Functor.map_comp] using
    (HomotopyCategory.eq_of_homotopy _ _ ha.some).trans
      (HomotopyCategory.eq_of_homotopy _ _ hb.some).symm

private theorem roof_inv_homotopy {X Y : CochainComplex A ℤ}
    (a b : HomotopyEquiv X Y) (h : Nonempty (Homotopy a.hom b.hom)) :
    Nonempty (Homotopy a.inv b.inv) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let e := HomotopyCategory.isoOfHomotopyEquiv a
  have hh : q.map a.hom = q.map b.hom := HomotopyCategory.eq_of_homotopy _ _ h.some
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  apply (cancel_epi e.hom).mp
  change q.map a.hom ≫ q.map a.inv = q.map a.hom ≫ q.map b.inv
  have hiA : q.map a.hom ≫ q.map a.inv = 𝟙 _ := by
    simpa only [Functor.map_comp, Functor.map_id] using
      HomotopyCategory.eq_of_homotopy _ _ a.homotopyHomInvId
  have hiB : q.map b.hom ≫ q.map b.inv = 𝟙 _ := by
    simpa only [Functor.map_comp, Functor.map_id] using
      HomotopyCategory.eq_of_homotopy _ _ b.homotopyHomInvId
  rw [hiA, hh, hiB]

private def roof_comparison (X Y : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y) :
    globalResolvedHom B R S ≅ globalResolvedHom B R' S' :=
  roof_homIso B (roof_e R R') (roof_e S S')

private theorem roof_comparison_formula (X Y : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y)
    (a : HomotopyEquiv R.I R'.I) (b : HomotopyEquiv S.I S'.I)
    (ha : Nonempty (Homotopy (R.ι ≫ a.hom) R'.ι))
    (hb : Nonempty (Homotopy (S.ι ≫ b.hom) S'.ι)) :
    (roof_comparison B X Y R R' S S').hom =
      DerivedCategory.Q.map (globalLinearHomMap B a.inv b.hom) := by
  apply roof_homotopy_invariance B
  · exact roof_inv_homotopy _ _ (roof_lift_unique R R' _ _ (roof_e_comm R R') ha)
  · exact roof_lift_unique S S' _ _ (roof_e_comm S S') hb

private theorem roof_equiv_inv_comm {X : CochainComplex A ℤ}
    (R R' : GlobalHomResolution X) (a : HomotopyEquiv R.I R'.I)
    (ha : Nonempty (Homotopy (R.ι ≫ a.hom) R'.ι)) :
    Nonempty (Homotopy (R'.ι ≫ a.inv) R.ι) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  have hh : q.map R.ι ≫ q.map a.hom = q.map R'.ι := by
    simpa only [Functor.map_comp] using HomotopyCategory.eq_of_homotopy _ _ ha.some
  have hi : q.map a.hom ≫ q.map a.inv = 𝟙 _ := by
    simpa only [Functor.map_comp, Functor.map_id] using
      HomotopyCategory.eq_of_homotopy _ _ a.homotopyHomInvId
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  change q.map (R'.ι ≫ a.inv) = q.map R.ι
  rw [Functor.map_comp, ← hh, Category.assoc, hi, Category.comp_id]

private theorem roof_comparison_roof (X Y : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y) :
    roof_c B X Y R S ≫ (roof_comparison B X Y R R' S S').hom =
      roof_c B X Y R' S' := by
  have h := roof_naturality B X X Y Y R R' S S' (𝟙 X) (𝟙 Y)
    (roof_e R R').inv (roof_e S S').hom
    (by simpa using roof_equiv_inv_comm R R' (roof_e R R') (roof_e_comm R R'))
    (by simpa using roof_e_comm S S')
  simpa only [roof_comparison, roof_homIso, roof_map_id, Functor.map_id,
    Category.id_comp] using h.symm

private theorem roof_comparison_refl (X Y : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) :
    (roof_comparison B X Y R R S S).hom = 𝟙 _ := by
  have h := roof_comparison_formula B X Y R R S S
    (HomotopyEquiv.refl R.I) (HomotopyEquiv.refl S.I)
    (by exact ⟨Homotopy.ofEq (by simp [HomotopyEquiv.refl])⟩)
    (by exact ⟨Homotopy.ofEq (by simp [HomotopyEquiv.refl])⟩)
  simpa only [roof_comparison, HomotopyEquiv.refl_hom, HomotopyEquiv.refl_inv,
    roof_map_id, Functor.map_id, globalResolvedHom] using h

private theorem roof_equiv_trans_comm {X : CochainComplex A ℤ}
    (R R' R'' : GlobalHomResolution X) (a : HomotopyEquiv R.I R'.I)
    (b : HomotopyEquiv R'.I R''.I)
    (ha : Nonempty (Homotopy (R.ι ≫ a.hom) R'.ι))
    (hb : Nonempty (Homotopy (R'.ι ≫ b.hom) R''.ι)) :
    Nonempty (Homotopy (R.ι ≫ (a.trans b).hom) R''.ι) := by
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  have h₁ := HomotopyCategory.eq_of_homotopy _ _ ha.some
  have h₂ := HomotopyCategory.eq_of_homotopy _ _ hb.some
  simp only [Functor.map_comp] at h₁ h₂ ⊢
  simpa only [HomotopyEquiv.trans_hom, Functor.map_comp, ← Category.assoc, h₁]
    using h₂

private theorem roof_comparison_cocycle (X Y : CochainComplex A ℤ)
    (R R' R'' : GlobalHomResolution X) (S S' S'' : GlobalHomResolution Y) :
    (roof_comparison B X Y R R' S S').hom ≫
        (roof_comparison B X Y R' R'' S' S'').hom =
      (roof_comparison B X Y R R'' S S'').hom := by
  rw [roof_comparison_formula B X Y R R'' S S''
    ((roof_e R R').trans (roof_e R' R''))
    ((roof_e S S').trans (roof_e S' S''))
    (roof_equiv_trans_comm _ _ _ _ _ (roof_e_comm R R') (roof_e_comm R' R''))
    (roof_equiv_trans_comm _ _ _ _ _ (roof_e_comm S S') (roof_e_comm S' S''))]
  exact roof_Q_comp B _ _ _ _

private theorem roof_normalization (X Y : CochainComplex A ℤ)
    [X.IsKInjective] [Y.IsKInjective] :
    roof_c B X Y (GlobalHomResolution.self X) (GlobalHomResolution.self Y) = 𝟙 _ := by
  simp [roof_c, GlobalHomResolution.self, roof_map_id, Functor.map_id]

private def roof_targetShift (X Y : CochainComplex A ℤ) (n : ℤ) :
    globalLinearHom B X (Y⟦n⟧) ≅ (globalLinearHom B X Y)⟦n⟧ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun s ↦ (Cochain.rightShiftLinearEquiv B X Y (s + n) n s rfl).symm.toModuleIso)
    (by
      intro s t h
      ext f
      change n.negOnePow • δ (s + n) (t + n) (f.rightUnshift (s + n) rfl) =
        (δ s t f).rightUnshift (t + n) rfl
      rw [Cochain.δ_rightUnshift _ _ rfl _ _ rfl]
      simp only [smul_smul, Int.units_mul_self, one_smul])

private theorem roof_targetShift_formula (X Y : CochainComplex A ℤ) (n s : ℤ)
    (f : Cochain X (Y⟦n⟧) s) :
    ((globalLinearHom B X Y).shiftFunctorObjXIso n s (s + n) rfl).hom
      ((roof_targetShift B X Y n).hom.f s f) = f.rightUnshift (s + n) rfl := by
  rfl

private noncomputable def roof_unit (X : CochainComplex A ℤ) :
    (CochainComplex.singleFunctor (ModuleCat.{v} B) 0).obj (ModuleCat.of B B) ⟶
      globalLinearHom B X X := by
  change (HomologicalComplex.single (ModuleCat B) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of B B) ⟶ globalLinearHom B X X
  let φ : ModuleCat.of B B ⟶ (globalLinearHom B X X).X 0 := ModuleCat.ofHom
    { toFun := fun b ↦ b • Cochain.ofHom (𝟙 X)
      map_add' := by intro b c; simp [add_smul]
      map_smul' := by intro b c; simp [smul_smul] }
  exact HomologicalComplex.mkHomFromSingle φ (by
    intro k hk
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change δ 0 k (b • Cochain.ofHom (𝟙 X)) = 0
    simp [globalLinearHom, δ_hom])

private theorem roof_unit_formula (X : CochainComplex A ℤ) (b : B) :
    (roof_unit B X).f 0
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of B B)).inv b) = b • Cochain.ofHom (𝟙 X) := by
  change (roof_unit B X).f 0
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of B B)).inv b) = _
  dsimp [roof_unit]
  rw [HomologicalComplex.mkHomFromSingle_f]
  change ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (ModuleCat.of B B)).hom ((HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 (ModuleCat.of B B)).inv b)) • Cochain.ofHom (𝟙 X) = _
  simp

/-- The target-shift square of `GlobalHomResolutionRoof.targetShift_roof`, for any `c` satisfying
the roof equation and any `targetShift` given by the family identification.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof-shift-fields). -/
structure GlobalHomResolutionRoofShiftFields
    (c : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
      (S : GlobalHomResolution Y),
      DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S)
    (targetShift : ∀ (X Y : CochainComplex A ℤ) (n : ℤ),
      globalLinearHom B X (Y⟦n⟧) ≅ (globalLinearHom B X Y)⟦n⟧) where
  targetShift_roof :
    (∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X) (S : GlobalHomResolution Y),
      c X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)) =
        DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) S.ι)) →
    (∀ (X Y : CochainComplex A ℤ) (n s : ℤ) (f : Cochain X (Y⟦n⟧) s),
      ((globalLinearHom B X Y).shiftFunctorObjXIso n s (s + n) rfl).hom
        ((targetShift X Y n).hom.f s f) = f.rightUnshift (s + n) rfl) →
    ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) (n : ℤ),
    c X (Y⟦n⟧) R (S.shift n) ≫ DerivedCategory.Q.map (targetShift R.I S.I n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (globalLinearHom B R.I S.I) =
      DerivedCategory.Q.map (targetShift X Y n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (globalLinearHom B X Y) ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{v} B)) n).map (c X Y R S)

/-- Ordinary composition and its two coherences, for any `c` satisfying the roof equation and
any `comparison` given by conjugation with representing homotopy equivalences.
Source: Stacks 09L9, 06XY (blueprint: lem-sf-global-hom-resolution-roof-composition-fields). -/
structure GlobalHomResolutionRoofCompositionFields
    (c : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
      (S : GlobalHomResolution Y),
      DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S)
    (comparison : ∀ (X Y : CochainComplex A ℤ) (R R' : GlobalHomResolution X)
      (S S' : GlobalHomResolution Y), globalResolvedHom B R S ≅ globalResolvedHom B R' S')
    where
  comp : ∀ (X Y Z : CochainComplex A ℤ),
    globalLinearHom B Y Z ⊗ globalLinearHom B X Y ⟶ globalLinearHom B X Z
  comp_formula : ∀ (X Y Z : CochainComplex A ℤ) (r s n : ℤ) (h : r + s = n)
    (g : Cochain Y Z r) (f : Cochain X Y s),
    (comp X Y Z).f n
        (HomologicalComplex.ιTensorObj (globalLinearHom B Y Z) (globalLinearHom B X Y)
          r s n h (g ⊗ₜ[B] f)) = f.comp g (by omega)
  composition_roof :
    (∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X) (S : GlobalHomResolution Y),
      c X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)) =
        DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) S.ι)) →
    ∀ (X Y Z : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (S : GlobalHomResolution Y) (T : GlobalHomResolution Z),
    (c Y Z S T ⊗ₘ c X Y R S) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B S.I T.I)
          (globalLinearHom B R.I S.I) ≫ DerivedCategory.Q.map (comp R.I S.I T.I) =
      Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B Y Z)
        (globalLinearHom B X Y) ≫ DerivedCategory.Q.map (comp X Y Z) ≫ c X Z R T
  composition_comparison :
    (∀ (X Y : CochainComplex A ℤ) (R R' : GlobalHomResolution X)
      (S S' : GlobalHomResolution Y) (a : HomotopyEquiv R.I R'.I) (b : HomotopyEquiv S.I S'.I),
      Nonempty (Homotopy (R.ι ≫ a.hom) R'.ι) →
      Nonempty (Homotopy (S.ι ≫ b.hom) S'.ι) →
      (comparison X Y R R' S S').hom =
        DerivedCategory.Q.map (globalLinearHomMap B a.inv b.hom)) →
    ∀ (X Y Z : CochainComplex A ℤ)
    (R R' : GlobalHomResolution X) (S S' : GlobalHomResolution Y)
    (T T' : GlobalHomResolution Z),
    ((comparison Y Z S S' T T').hom ⊗ₘ (comparison X Y R R' S S').hom) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B S'.I T'.I)
          (globalLinearHom B R'.I S'.I) ≫ DerivedCategory.Q.map (comp R'.I S'.I T'.I) =
      Functor.LaxMonoidal.μ DerivedCategory.Q (globalLinearHom B S.I T.I)
        (globalLinearHom B R.I S.I) ≫ DerivedCategory.Q.map (comp R.I S.I T.I) ≫
        (comparison X Z R R' T T').hom

/-- The unit roof and the cohomology interpretation, for any `c` satisfying the roof equation
and any `unit` given by the scalar formula.
Source: Stacks 070I, 0B6E (blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
structure GlobalHomResolutionRoofCohomologyFields
    (c : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
      (S : GlobalHomResolution Y),
      DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S)
    (unit : ∀ (X : CochainComplex A ℤ),
      (CochainComplex.singleFunctor (ModuleCat.{v} B) 0).obj (ModuleCat.of B B) ⟶
        globalLinearHom B X X) where
  unit_roof :
    (∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X) (S : GlobalHomResolution Y),
      c X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)) =
        DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) S.ι)) →
    (∀ (X : CochainComplex A ℤ) (b : B),
      (unit X).f 0
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of B B)).inv b) = b • Cochain.ofHom (𝟙 X)) →
    ∀ (X : CochainComplex A ℤ) (R : GlobalHomResolution X),
    DerivedCategory.Q.map (unit X) ≫ c X X R R = DerivedCategory.Q.map (unit R.I)
  cohomology : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) (n : ℤ),
    (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj (globalResolvedHom B R S) ≃+
      (DerivedCategory.Q.obj X ⟶ (DerivedCategory.Q.obj Y)⟦n⟧)
  cohomology_resolved : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) (n : ℤ)
    (z : (globalLinearHom B R.I S.I).cycles n) (f : Cocycle R.I S.I n),
    (f : Cochain R.I S.I n) = (globalLinearHom B R.I S.I).iCycles n z →
    cohomology X Y R S n (globalLinearHomClass B R.I S.I n z) ≫
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Q.map S.ι) =
      DerivedCategory.Q.map R.ι ≫ DerivedCategory.Q.map (Cocycle.equivHomShift.symm f) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app S.I
  cohomology_roof :
    (∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X) (S : GlobalHomResolution Y),
      c X Y R S ≫ DerivedCategory.Q.map (globalLinearHomMap B R.ι (𝟙 S.I)) =
        DerivedCategory.Q.map (globalLinearHomMap B (𝟙 X) S.ι)) →
    ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
    (S : GlobalHomResolution Y) (n : ℤ)
    (z : (globalLinearHom B X Y).cycles n) (f : Cocycle X Y n),
    (f : Cochain X Y n) = (globalLinearHom B X Y).iCycles n z →
    cohomology X Y R S n
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).map (c X Y R S)
          (globalLinearHomClass B X Y n z)) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm f) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app Y
  cohomology_naturality : ∀ (X X' Y Y' : CochainComplex A ℤ)
    (R : GlobalHomResolution X) (R' : GlobalHomResolution X')
    (S : GlobalHomResolution Y) (S' : GlobalHomResolution Y')
    (a : X' ⟶ X) (b : Y ⟶ Y') (a' : R'.I ⟶ R.I) (b' : S.I ⟶ S'.I),
    Nonempty (Homotopy (R'.ι ≫ a') (a ≫ R.ι)) →
    Nonempty (Homotopy (S.ι ≫ b') (b ≫ S'.ι)) →
    ∀ (n : ℤ) (z : (DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).obj
      (globalResolvedHom B R S)),
    cohomology X' Y' R' S' n
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} B) n).map
          (DerivedCategory.Q.map (globalLinearHomMap B a' b')) z) =
      DerivedCategory.Q.map a ≫ cohomology X Y R S n z ≫
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Q.map b)

/-- The shift square holds for every `c` satisfying the roof equation and every `targetShift`
given by the family identification (both hypotheses of the field).
Source: Stacks 09L9 and step 7 of lem-sf-global-hom-resolution-roof.
Proof: the roof equation determines `c`, since `Q (globalLinearHomMap B R.ι (𝟙 S.I))` is
invertible (precomposition by a quasi-isomorphism into a K-injective is a quasi-isomorphism),
and the family formula determines `targetShift`. Pre- and postcomposition by degree-0 chain
maps commute with `rightUnshift`, so the family identification is natural for the
precomposition leg `j` (by `R.ι`) and the postcomposition leg `p` (by `S.ι`, resp. its shift).
Apply `Q` and naturality of `Q.commShiftIso`. Postcompose both sides with the shift of the
invertible `Q.map j`; by the roof equation both become the image of `Q.map p`; cancel.
(blueprint: lem-sf-global-hom-resolution-roof-shift-fields). -/
theorem globalHom_resolution_roof_shift_fields
    (c : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
      (S : GlobalHomResolution Y),
      DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S)
    (targetShift : ∀ (X Y : CochainComplex A ℤ) (n : ℤ),
      globalLinearHom B X (Y⟦n⟧) ≅ (globalLinearHom B X Y)⟦n⟧) :
    Nonempty (GlobalHomResolutionRoofShiftFields B c targetShift) := by
  -- The graded shift calculation is isolated in this named interface.
  sorry

/-- Ordinary composition out of the total tensor exists, and is compatible with every `c`
satisfying the roof equation and every `comparison` given by conjugation with representing
homotopy equivalences (the hypotheses of the two coherence fields).
Source: Stacks 09L9, 06XY and steps 1, 8-10 of lem-sf-global-hom-resolution-roof.
Proof: composition is bilinear and satisfies `d(gf) = d(g)f + (-1)^|g| g d(f)`, so it
descends through the total-tensor coproduct, with the pure-tensor formula by construction.
For `composition_roof` use the mixed pairings `A : H(I_Y,I_Z) ⊗ H(X,I_Y) → H(X,I_Z)` and
`B' : H(Y,I_Z) ⊗ H(X,Y) → H(X,I_Z)`: associativity gives `j comp = A(1 ⊗ j)`,
`A(1 ⊗ p) = B'(j ⊗ 1)`, `B'(p ⊗ 1) = p comp`; apply `Q`, naturality of `μ`, the roof
equation twice, and cancel the invertible final `Q.map j`. For `composition_comparison`,
choose representing homotopy equivalences `a, b` (they exist by the K-injective lifting);
the hypothesis makes the comparison conjugation by them, with `b a - 1 = dh + hd`;
`S(g ⊗ f) = (-1)^|g| a g h f b` is a homotopy on the total tensor, so the inserted
middle factor disappears after `Q`.
(blueprint: lem-sf-global-hom-resolution-roof-composition-fields). -/
theorem globalHom_resolution_roof_composition_fields
    (c : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
      (S : GlobalHomResolution Y),
      DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S)
    (comparison : ∀ (X Y : CochainComplex A ℤ) (R R' : GlobalHomResolution X)
      (S S' : GlobalHomResolution Y), globalResolvedHom B R S ≅ globalResolvedHom B R' S') :
    Nonempty (GlobalHomResolutionRoofCompositionFields B c comparison) := by
  -- The signed total-tensor coherence is isolated in this named interface.
  sorry

/-- The unit roof (for every `c` satisfying the roof equation and every `unit` given by the
scalar formula) and the cohomology interpretation of resolved Hom.
Source: Stacks 070I, 0B6E and steps 10-11 of lem-sf-global-hom-resolution-roof.
Proof: by the scalar formula `p (unit X) = R.ι = j (unit R.I)` on the generator, so the roof
equation and cancellation of the invertible `Q.map j` give `unit_roof`. Cohomology of
`H(R.I,S.I)` is maps `R.I → S.I⟦n⟧` modulo homotopy
(`CochainComplex.HomComplex.CohomologyClass.toHom_bijective`), and maps into the K-injective
`S.I⟦n⟧` in the homotopy category are maps in `D(A)` (`IsKInjective.Qh_map_bijective`);
conjugating by `Q.map R.ι` and `Q.map S.ι` defines `cohomology` and gives
`cohomology_resolved`. The roof equation on a cocycle `f : X → Y⟦n⟧` gives `cohomology_roof`;
naturality follows on representatives from the homotopy squares of the lifts.
(blueprint: lem-sf-global-hom-resolution-roof-cohomology-fields). -/
theorem globalHom_resolution_roof_cohomology_fields
    (c : ∀ (X Y : CochainComplex A ℤ) (R : GlobalHomResolution X)
      (S : GlobalHomResolution Y),
      DerivedCategory.Q.obj (globalLinearHom B X Y) ⟶ globalResolvedHom B R S)
    (unit : ∀ (X : CochainComplex A ℤ),
      (CochainComplex.singleFunctor (ModuleCat.{v} B) 0).obj (ModuleCat.of B B) ⟶
        globalLinearHom B X X) :
    Nonempty (GlobalHomResolutionRoofCohomologyFields B c unit) := by
  -- The unit and cohomology transport calculation is isolated here.
  sorry

attribute [instance] GlobalHomResolution.injective GlobalHomResolution.quasiIso

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)]

end CategoryTheory
