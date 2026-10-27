/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc

/-! # Strict cosimplicial injective replacements and alternating totals

Source: Stacks Project, derived.tex Tag 0141, lemma-functorial-injective-resolutions
and remark-match; injectives.tex Tag 079H, theorem-injective-embedding-grothendieck;
homology.tex Tags 012X and 0133, finite-total comparison and signed transposition.
(blueprint: lem-sfb-cosimplicial-injective-total-replacement).

Nonnegative complexes are represented with natural indices, equivalently extended by zero
in negative integer degrees. The alternating-coface complex in the category of complexes
has outer degree n and inner degree q. Mathlib's total therefore has differential
δ + (-1)^n d, and its flipped total has differential d + (-1)^q δ.
Postcomposition and whiskering retain every simplex operator and augmentation arrow.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory.Limits AlgebraicTopology HomologicalComplex HomologicalComplex₂

namespace CategoryTheory

open ZeroObject
open scoped Simplicial

private theorem restrict_quasiIso {A : Type u} [Category.{v} A] [Abelian A]
    {K L : CochainComplex A ℤ} (f : K ⟶ L)
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0] [QuasiIso f] :
    QuasiIso (restrictionMap f ComplexShape.embeddingUpNat) := by
  let e := ComplexShape.embeddingUpNat
  have hK : K.IsStrictlySupported e := ⟨fun n hn ↦
    K.isZero_of_isStrictlyGE 0 n (by
      by_contra h
      exact hn n.toNat (by change (n.toNat : ℤ) = n; omega))⟩
  have hL : L.IsStrictlySupported e := ⟨fun n hn ↦
    L.isZero_of_isStrictlyGE 0 n (by
      by_contra h
      exact hn n.toNat (by change (n.toNat : ℤ) = n; omega))⟩
  rw [← quasiIso_extendMap_iff _ e]
  change QuasiIso (stupidTruncMap f e)
  rw [← quasiIso_iff_comp_right _ (L.ιStupidTrunc e), ιStupidTrunc_naturality]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extendRestrictIso {A : Type u} [Category.{v} A] [Abelian A]
    (K : CochainComplex A ℕ) :
    K ≅ (K.extend ComplexShape.embeddingUpNat).restriction ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).symm)
    (by
      intro i j hij
      change (K.extendXIso _ rfl).inv ≫
        (K.extend ComplexShape.embeddingUpNat).d _ _ = _
      rw [extend_d_eq _ _ rfl rfl]
      simp)

set_option backward.isDefEq.respectTransparency false in
private theorem exists_nonnegative_resolution
    (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A] :
    ∃ (I : CochainComplex A ℕ ⥤ CochainComplex A ℕ)
      (η : 𝟭 (CochainComplex A ℕ) ⟶ I),
      (∀ K, QuasiIso (η.app K)) ∧
      (∀ (K : CochainComplex A ℕ) (q : ℕ), Injective ((I.obj K).X q)) := by
  let D := MorphismProperty.functorialFactorizationData
    (MorphismProperty.monomorphisms A) (MorphismProperty.monomorphisms A).rlp
  let Z : A ⥤ Arrow A :=
    { obj X := Arrow.mk (0 : X ⟶ 0)
      map f := Arrow.homMk f (𝟙 _) (by simp) }
  let J := Z ⋙ D.Z
  let j : 𝟭 A ⟶ J :=
    { app X := D.i.app (Z.obj X)
      naturality _ _ f := D.i.naturality (Z.map f) }
  have hj (X : A) : Mono (j.app X) := D.hi (Z.obj X)
  have hJ (X : A) : Injective (J.obj X) :=
    inferInstanceAs (Injective (IsGrothendieckAbelian.monoMapFactorizationDataRlp
      (0 : X ⟶ 0)).Z)
  obtain ⟨R, α, hα, hR, hb⟩ :=
    CochainComplex.exists_functorial_bounded_injective_resolution J j hj hJ
  let F : CochainComplex A ℕ ⥤ CochainComplex.Plus A :=
    ObjectProperty.lift _ (ComplexShape.embeddingUpNat.extendFunctor A)
      (fun K ↦ ⟨0, by
        change CochainComplex.IsStrictlyGE (K.extend ComplexShape.embeddingUpNat) 0
        infer_instance⟩)
  let I := F ⋙ R ⋙ CochainComplex.Plus.ι A ⋙
    ComplexShape.embeddingUpNat.restrictionFunctor A
  let η : 𝟭 (CochainComplex A ℕ) ⟶ I :=
    { app K := (extendRestrictIso K).hom ≫
        restrictionMap (α.app (F.obj K)) ComplexShape.embeddingUpNat
      naturality {K L} f := by
        have hαf : extendMap f ComplexShape.embeddingUpNat ≫ α.app (F.obj L) =
            α.app (F.obj K) ≫ (R.map (F.map f)).hom := α.naturality (F.map f)
        have h := congrArg (fun g ↦ restrictionMap g ComplexShape.embeddingUpNat) hαf
        dsimp [I]
        rw [← Category.assoc]
        have hu : f ≫ (extendRestrictIso L).hom =
            (extendRestrictIso K).hom ≫
              restrictionMap (extendMap f ComplexShape.embeddingUpNat)
                ComplexShape.embeddingUpNat := by
          ext n
          simp [extendRestrictIso, restrictionMap, extendMap_f _ _ rfl]
        rw [hu, Category.assoc]
        rw [Category.assoc]
        change (extendRestrictIso K).hom ≫
          restrictionMap (extendMap f ComplexShape.embeddingUpNat)
            ComplexShape.embeddingUpNat ≫
          restrictionMap (α.app (F.obj L)) ComplexShape.embeddingUpNat =
          (extendRestrictIso K).hom ≫
          restrictionMap (α.app (F.obj K)) ComplexShape.embeddingUpNat ≫
          restrictionMap (R.map (F.map f)).hom ComplexShape.embeddingUpNat
        simpa only [restrictionMap_comp, Category.assoc] using
          congrArg (fun g ↦ (extendRestrictIso K).hom ≫ g) h }
  refine ⟨I, η, ?_, ?_⟩
  · intro K
    have := hα (F.obj K)
    have hK : (F.obj K).obj.IsStrictlyGE 0 := by
      change CochainComplex.IsStrictlyGE (K.extend ComplexShape.embeddingUpNat) 0
      infer_instance
    have := hb (F.obj K) 0 hK
    have hsrc : ((CochainComplex.Plus.ι A).obj (F.obj K)).IsStrictlyGE 0 := hK
    have htgt : ((R ⋙ CochainComplex.Plus.ι A).obj (F.obj K)).IsStrictlyGE 0 :=
      hb (F.obj K) 0 hK
    have := restrict_quasiIso (α.app (F.obj K))
    dsimp [η]
    infer_instance
  · intro K q
    exact hR (F.obj K) (q : ℤ)

set_option backward.isDefEq.respectTransparency false in
private theorem totalFlip_naturality {A : Type u} [Category.{v} A] [Abelian A]
    {K L : HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : K ⟶ L) :
    total.map ((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map f)
        (ComplexShape.up ℕ) ≫ (L.totalFlipIso (ComplexShape.up ℕ)).hom =
      (K.totalFlipIso (ComplexShape.up ℕ)).hom ≫ total.map f (ComplexShape.up ℕ) := by
  ext r q n h
  simp only [HomologicalComplex.comp_f]
  rw [ιTotal_map_assoc]
  change (f.f n).f q ≫ L.flip.ιTotal (ComplexShape.up ℕ) q n r h ≫
    (L.totalFlipIso (ComplexShape.up ℕ)).hom.f r =
    K.flip.ιTotal (ComplexShape.up ℕ) q n r h ≫
      (K.totalFlipIso (ComplexShape.up ℕ)).hom.f r ≫
        (total.map f (ComplexShape.up ℕ)).f r
  rw [ιTotal_totalFlipIso_f_hom,
    ιTotal_totalFlipIso_f_hom_assoc, Linear.units_smul_comp, ιTotal_map]
  rw [Linear.comp_units_smul]

/-- One strict resolution functor resolves all nonnegative cosimplicial complexes and
whole augmented diagrams; alternating totals preserve all componentwise quasi-isomorphisms,
and signed transposition is a natural chain isomorphism.

Source: Stacks Project, derived.tex Tag 0141 (lemma-functorial-injective-resolutions and
remark-match), injectives.tex Tag 079H, and homology.tex Tags 012X, 0132 and 0133.
(blueprint: lem-sfb-cosimplicial-injective-total-replacement).

Proof:
1. Use lem-weil-pbc-grothendieck-functorial-injective-embedding and then
   lem-weil-pbc-functorial-bounded-injective-resolution. Restrict the resulting functor
   to complexes zero below zero; lower-bound preservation permits restriction, and
   restriction to natural degrees is inverse to extension by zero on these complexes.
   This gives I, η, the componentwise quasi-isomorphisms and injective terms.
2. Postcompose each strict diagram with I and whisker η on the left. Functor identities
   and composition give all strict simplex operators and the lift I(f_n). Naturality
   of η gives the displayed map square and the augmentation square, using the same I
   on the nonnegative augmentation object. Whiskering also resolves maps of whole
   augmented diagrams, including maps of their augmentation objects.
3. The alternating coface differential squares to zero: pair d^j d^i with d^i d^(j-1)
   for i < j; their signs are opposite and each composite appears once. Cofaces are
   chain maps, so δ commutes with d. Thus both index orders give first-quadrant
   bicomplexes, and every diagonal sum is finite.
4. The map S with summand sign (-1)^(n*q) intertwines the transposed differential
   d + (-1)^q δ with δ + (-1)^n d: on d the signs are n*(q+1) and n*q+n;
   on δ they are q+(n+1)*q and n*q, equal modulo two. The same signs give its inverse.
   Scalar multiplication commutes with each component of a strict map, proving the
   final naturality equation. This is Mathlib's totalFlipIso, with the stated signs.
5. Apply lem-sc-first-quadrant-total-column-comparison to the transposed map. Its
   resolution columns are precisely the original complexes, hence the assumed
   quasi-isomorphisms imply a total quasi-isomorphism. Conjugate by S to obtain the
   assertion for the alternating total. Apply it to the whiskered η to obtain the
   replacement's total quasi-isomorphism. -/
theorem exists_cosimplicial_injective_total_replacement
    (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A] :
    (∃ (I : CochainComplex A ℕ ⥤ CochainComplex A ℕ)
      (η : 𝟭 (CochainComplex A ℕ) ⟶ I),
      (∀ K : CochainComplex A ℕ, QuasiIso (η.app K)) ∧
      (∀ (K : CochainComplex A ℕ) (q : ℕ), Injective ((I.obj K).X q)) ∧
      (∀ K : CosimplicialObject (CochainComplex A ℕ),
        QuasiIso (total.map ((alternatingCofaceMapComplex _).map
          (Functor.whiskerLeft K η)) (ComplexShape.up ℕ))) ∧
      (∀ (K L : CosimplicialObject (CochainComplex A ℕ)) (f : K ⟶ L),
        Functor.whiskerLeft K η ≫ Functor.whiskerRight f I =
          f ≫ Functor.whiskerLeft L η) ∧
      (∀ (B : CochainComplex A ℕ) (K : CosimplicialObject (CochainComplex A ℕ))
        (b : (Functor.const SimplexCategory).obj B ⟶ K),
        b ≫ Functor.whiskerLeft K η =
          (Functor.const SimplexCategory).map (η.app B) ≫
            (Functor.constComp (J := SimplexCategory) B I).inv ≫ Functor.whiskerRight b I)) ∧
    (∀ (K L : CosimplicialObject (CochainComplex A ℕ)) (f : K ⟶ L),
      (∀ n : SimplexCategory, QuasiIso (f.app n)) →
        QuasiIso (total.map ((alternatingCofaceMapComplex _).map f) (ComplexShape.up ℕ))) ∧
    (∀ (K : CosimplicialObject (CochainComplex A ℕ)) (n q : ℕ),
      HomologicalComplex₂.ιTotal
          (HomologicalComplex₂.flip ((alternatingCofaceMapComplex _).obj K))
          (ComplexShape.up ℕ) q n (n + q) (Nat.add_comm q n) ≫
          (HomologicalComplex₂.totalFlipIso ((alternatingCofaceMapComplex _).obj K)
            (ComplexShape.up ℕ)).hom.f
            (n + q) =
        (-1 : ℤ) ^ (n * q) • HomologicalComplex₂.ιTotal
          ((alternatingCofaceMapComplex _).obj K) (ComplexShape.up ℕ) n q (n + q) rfl) ∧
    (∀ (K L : CosimplicialObject (CochainComplex A ℕ)) (f : K ⟶ L),
      total.map ((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map
          ((alternatingCofaceMapComplex _).map f)) (ComplexShape.up ℕ) ≫
          (HomologicalComplex₂.totalFlipIso ((alternatingCofaceMapComplex _).obj L)
            (ComplexShape.up ℕ)).hom =
        (HomologicalComplex₂.totalFlipIso ((alternatingCofaceMapComplex _).obj K)
            (ComplexShape.up ℕ)).hom ≫
          total.map ((alternatingCofaceMapComplex _).map f) (ComplexShape.up ℕ)) := by
  have htotal (K L : CosimplicialObject (CochainComplex A ℕ)) (f : K ⟶ L)
      (hf : ∀ n : SimplexCategory, QuasiIso (f.app n)) :
      QuasiIso (total.map ((alternatingCofaceMapComplex _).map f)
        (ComplexShape.up ℕ)) := by
    let g := (alternatingCofaceMapComplex _).map f
    let F := HomologicalComplex₂.flipFunctor A (ComplexShape.up ℕ) (ComplexShape.up ℕ)
    have hg : QuasiIso (total.map (F.map g) (ComplexShape.up ℕ)) := by
      apply quasiIso_totalMap_of_columns
      intro n
      change QuasiIso (f.app ⦋n⦌)
      exact hf _
    apply (quasiIso_iff_of_arrow_mk_iso (total.map (F.map g) (ComplexShape.up ℕ)) _
      (Arrow.isoMk (HomologicalComplex₂.totalFlipIso
        ((alternatingCofaceMapComplex _).obj K) (ComplexShape.up ℕ))
        (HomologicalComplex₂.totalFlipIso
          ((alternatingCofaceMapComplex _).obj L) (ComplexShape.up ℕ))
        (totalFlip_naturality g).symm)).mp hg
  obtain ⟨I, η, hη, hI⟩ := exists_nonnegative_resolution A
  refine ⟨⟨I, η, hη, hI, ?_, ?_, ?_⟩, htotal, ?_, ?_⟩
  · intro K
    apply htotal
    intro n
    exact hη (K.obj n)
  · intro K L f
    apply NatTrans.ext
    funext n
    exact (η.naturality (f.app n)).symm
  · intro B K b
    apply NatTrans.ext
    funext n
    simpa using η.naturality (b.app n)
  · intro K n q
    rw [ιTotal_totalFlipIso_f_hom]
    rfl
  · intro K L f
    exact totalFlip_naturality ((alternatingCofaceMapComplex _).map f)

end CategoryTheory
