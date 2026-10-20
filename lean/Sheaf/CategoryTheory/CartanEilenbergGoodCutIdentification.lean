/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.FilteredComplexDecalageComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.TotalComplexSymmetry

import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import Sheaf.CategoryTheory.MapGoodUpperTruncation
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.UpperTruncationStepSES
import Sheaf.CategoryTheory.CartanEilenbergAugmentationQuasiIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
import Sheaf.CategoryTheory.CartanEilenbergGoodCutDecalage

/-! # Identification of the good-cut total

Source: Stacks Project, Derived Categories, Tag 015X.
-/

@[expose] public section

universe uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false

namespace GoodCutIdentification

variable {B : Type uB} [Category.{vB} B] [Abelian B]

private theorem cut_columns {K I : CochainComplex (CochainComplex B ℕ) ℤ}
    (e : K ⟶ I) (he : ∀ p, QuasiIso (e.f p))
    (hc : ∀ p, QuasiIso (HomologicalComplex.cyclesMap e p)) (q p : ℤ) :
    QuasiIso ((CochainComplex.truncLEMap e q).f p) := by
  rcases lt_trichotomy p q with hp | hp | hp
  · -- Below the cut, use naturality and the invertible truncation inclusions.
    have : IsIso ((K.ιTruncLE q).f p) := K.isIso_ιTruncLE_f q p hp
    have : IsIso ((I.ιTruncLE q).f p) := I.isIso_ιTruncLE_f q p hp
    have : QuasiIso (e.f p) := he p
    have hw := congrArg (fun f ↦ f.f p) (CochainComplex.ιTruncLE_naturality e q)
    simp only [HomologicalComplex.comp_f] at hw
    apply (quasiIso_iff_comp_right
      ((CochainComplex.truncLEMap e q).f p) ((I.ιTruncLE q).f p)).mp
    rw [hw]
    infer_instance
  · -- At the cut, the natural cycles identifications give an isomorphism of arrows.
    subst p
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (K.truncLEXIsoCycles q) (I.truncLEXIsoCycles q)
        (CochainComplex.truncLEXIsoCycles_naturality e q).symm)).mpr (hc q)
  · -- Above the cut, the map is between zero complexes.
    have : IsIso ((CochainComplex.truncLEMap e q).f p) :=
      IsZero.isIso ((K.truncLE q).isZero_of_isStrictlyLE q p hp)
        ((I.truncLE q).isZero_of_isStrictlyLE q p hp) _
    infer_instance

private theorem augmentation_exists
    {A : Type uB} [Category.{vB} A] [Abelian A] [IsGrothendieckAbelian.{vB} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s))
    (hrows : ∀ s : ℤ, QuasiIso (a.f s)) :
    ∃ (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
        (ComplexShape.up ℤ)),
          (∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
            (HomologicalComplex.extendXIso
              (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
              ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
            (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
              (ComplexShape.up ℤ) 0 n n (zero_add n)) ∧
      QuasiIso aug := by
  classical
  let J := ((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip
  let f (n : ℤ) : K.X n ⟶ (J.total (ComplexShape.up ℤ)).X n :=
    (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      J.ιTotal (ComplexShape.up ℤ) 0 n n (zero_add n)
  -- Only the complex-degree differential survives on the resolution-degree-zero summand.
  have hf (n m : ℤ) (hnm : (ComplexShape.up ℤ).Rel n m) :
      f n ≫ (J.total (ComplexShape.up ℤ)).d n m = K.d n m ≫ f m := by
    have hm : m = n + 1 := by simpa using hnm.symm
    subst m
    dsimp only [f, HomologicalComplex₂.total]
    simp only [Preadditive.comp_add, Category.assoc, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂]
    rw [J.d₁_eq (ComplexShape.up ℤ) (by simp : (ComplexShape.up ℤ).Rel 0 1) n (n + 1)
        (by dsimp [ComplexShape.π]; omega),
      J.d₂_eq (ComplexShape.up ℤ) 0 (by simp : (ComplexShape.up ℤ).Rel n (n + 1)) (n + 1) (by simp)]
    simp only [ComplexShape.ε₁, ComplexShape.ε₂]
    dsimp only [TotalComplexShape.ε₁, TotalComplexShape.ε₂]
    simp only [ComplexShape.ε_zero, one_smul]
    change (a.f n).f 0 ≫ _ ≫
        (((I.X n).extend ComplexShape.embeddingUpNat).d 0 1 ≫ _) +
      (a.f n).f 0 ≫ _ ≫
        ((HomologicalComplex.extendMap (I.d n (n + 1))
          ComplexShape.embeddingUpNat).f 0 ≫ _) = _
    rw [HomologicalComplex.extend_d_eq (I.X n) ComplexShape.embeddingUpNat
        (i := 0) (j := 1) (i' := 0) (j' := 1) rfl rfl,
      HomologicalComplex.extendMap_f (I.d n (n + 1)) ComplexShape.embeddingUpNat
        (i := 0) (i' := 0) rfl]
    simp only [Category.assoc]
    have hv := (a.f n).comm 0 1
    change (a.f n).f 0 ≫ (I.X n).d 0 1 = 0 ≫ (a.f n).f 1 at hv
    simp only [zero_comp] at hv
    simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
      eqToIso]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc ((a.f n).f 0), hv, zero_comp, zero_add]
    have hh := congrArg (fun g ↦ g.f 0) (a.comm n (n + 1))
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_obj_d,
      CochainComplex.single₀_map_f_zero] at hh
    rw [← Category.assoc ((a.f n).f 0), hh, Category.assoc]
  let aug : K ⟶ J.total (ComplexShape.up ℤ) := { f := f, comm' := hf }
  refine ⟨aug, fun n ↦ rfl, ?_⟩
  · exact Functor.cartanEilenberg_augmentation_quasiIso K I a hbelow hrows aug (fun n ↦ rfl)

private noncomputable def mapTotal
    [IsGrothendieckAbelian.{vB} B]
    {I I' : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ)}
    (f : I ⟶ I') :
    (((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).total
        (ComplexShape.up ℤ) ⟶
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I').flip).total
        (ComplexShape.up ℤ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor B (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
      ((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).map f)) (ComplexShape.up ℤ)

private theorem augmentation_naturality
    [IsGrothendieckAbelian.{vB} B]
    {K K' : CochainComplex B ℤ}
    {I I' : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ)}
    (e : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (e' : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K' ⟶ I') (f : K ⟶ K') (α : I ⟶ I')
    (he : e ≫ α = ((CochainComplex.single₀ B).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f ≫ e')
    (a : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).total
      (ComplexShape.up ℤ))
    (a' : K' ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I').flip).total
      (ComplexShape.up ℤ))
    (ha : ∀ m : ℤ, a.f m = (e.f m).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 B).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X m))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 m m (zero_add m))
    (ha' : ∀ m : ℤ, a'.f m = (e'.f m).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 B).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I'.X m))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I').flip).ιTotal
        (ComplexShape.up ℤ) 0 m m (zero_add m)) :
    a ≫ mapTotal α = f ≫ a' := by
  ext m
  simp only [HomologicalComplex.comp_f, ha, ha', Category.assoc]
  dsimp only [mapTotal]
  erw [HomologicalComplex₂.ιTotal_map]
  change (e.f m).f 0 ≫ _ ≫
      (HomologicalComplex.extendMap
        (((𝟭 B).mapHomologicalComplex (ComplexShape.up ℕ)).map (α.f m))
        ComplexShape.embeddingUpNat).f 0 ≫ _ = _
  erw [HomologicalComplex.extendMap_f
    (((𝟭 B).mapHomologicalComplex (ComplexShape.up ℕ)).map (α.f m))
    ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hh := congrArg (fun u ↦ (u.f m).f 0) he
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    CochainComplex.single₀_map_f_zero] at hh
  simp only [Functor.mapHomologicalComplex_map_f, Functor.id_map]
  erw [← Category.assoc ((e.f m).f 0), hh, Category.assoc]
  rfl

private theorem derived_cut_iso [HasDerivedCategory B]
    (K : CochainComplex.Plus B) (q : ℤ)
    (h : CochainComplex.plus B (K.obj.truncLE q)) :
    ∃ r : (DerivedCategory.Plus.TStructure.t.truncLT (q + 1)).obj
        (DerivedCategory.Plus.Q.obj K) ≅ DerivedCategory.Plus.Q.obj ⟨K.obj.truncLE q, h⟩,
      r.hom ≫ DerivedCategory.Plus.Q.map
          (ObjectProperty.homMk (K.obj.ιTruncLE q) : ⟨K.obj.truncLE q, h⟩ ⟶ K) =
        (DerivedCategory.Plus.TStructure.t.truncLTι (q + 1)).app
          (DerivedCategory.Plus.Q.obj K) := by
  let Q := DerivedCategory.Plus.Q (C := B)
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let Kq : CochainComplex.Plus B := ⟨K.obj.truncLE q, h⟩
  let j : Kq ⟶ K := ObjectProperty.homMk (K.obj.ιTruncLE q)
  have : t.IsLE (Q.obj Kq) q := by
    apply (DerivedCategory.Plus.isLE_ι_obj_iff _ _).mp
    change (DerivedCategory.Q.obj (K.obj.truncLE q)).IsLE q
    infer_instance
  let l := t.liftTruncLT (Q.map j) q (q + 1) rfl
  have hl : l ≫ (t.truncLTι (q + 1)).app (Q.obj K) = Q.map j :=
    t.liftTruncLT_ι _ _ _ _
  have : IsIso l := by
    apply (DerivedCategory.Plus.isIso_iff _).mpr
    intro m
    let H := DerivedCategory.Plus.homologyFunctor B m
    by_cases hm : m ≤ q
    · have : QuasiIsoAt j.hom m := K.obj.quasiIsoAt_ιTruncLE q m hm
      have : IsIso (H.map ((t.truncLTι (q + 1)).app (Q.obj K))) :=
        DerivedCategory.Plus.isIso_homologyFunctor_map_truncLTι_app _ _ _ (by omega)
      have : IsIso (H.map (Q.map j)) := by
        have hn := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality j m
        have : IsIso (HomologicalComplex.homologyMap j.hom m) := inferInstance
        have : IsIso (H.map (Q.map j) ≫
            (DerivedCategory.Plus.homologyFunctorObjQIso K m).hom) := by
          rw [hn]
          infer_instance
        exact IsIso.of_isIso_comp_right _
          (DerivedCategory.Plus.homologyFunctorObjQIso K m).hom
      have : IsIso (H.map l ≫ H.map ((t.truncLTι (q + 1)).app (Q.obj K))) := by
        rw [← H.map_comp, hl]
        infer_instance
      exact IsIso.of_isIso_comp_right _
        (H.map ((t.truncLTι (q + 1)).app (Q.obj K)))
    · exact IsZero.isIso
        (DerivedCategory.Plus.isZero_homology_of_isLE (Q.obj Kq) q m (by omega))
        (DerivedCategory.Plus.isZero_homology_of_isLE
          ((t.truncLT (q + 1)).obj (Q.obj K)) q m (by omega)) _
  refine ⟨(asIso l).symm, ?_⟩
  change inv l ≫ Q.map j = _
  rw [← hl, IsIso.inv_hom_id_assoc]
private theorem cut_represents_truncation
    [IsGrothendieckAbelian.{vB} B] [HasDerivedCategory B]
    (K : CochainComplex.Plus B)
    (I : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (e : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K.obj ⟶ I)
    (hzero : ∀ p : ℤ, p < 0 → IsZero (I.X p))
    (hcolumns : ∀ p : ℤ, QuasiIso (e.f p))
    (hcycles : ∀ p : ℤ, QuasiIso (HomologicalComplex.cyclesMap e p))
    (q : ℤ) (hq : 0 ≤ q)
    (hT : CochainComplex.plus B
      ((((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).total
        (ComplexShape.up ℤ)))
    (hS : CochainComplex.plus B
      ((((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj
        (CochainComplex.truncLE I q)).flip).total (ComplexShape.up ℤ)))
    (b : K ⟶ ⟨(((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).total
      (ComplexShape.up ℤ), hT⟩)
    (haug : ∀ m : ℤ, b.hom.f m = (e.f m).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 B).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X m))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 m m (zero_add m)) :
    let S : CochainComplex.Plus B :=
      ⟨(((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj
        (CochainComplex.truncLE I q)).flip).total (ComplexShape.up ℤ), hS⟩
    ∃ r : (DerivedCategory.Plus.TStructure.t.truncLT (q + 1)).obj
        (DerivedCategory.Plus.Q.obj K) ≅ DerivedCategory.Plus.Q.obj S,
      r.hom ≫ DerivedCategory.Plus.Q.map (ObjectProperty.homMk
        (mapTotal (CochainComplex.ιTruncLE I q)) : S ⟶
        ⟨(((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).total
          (ComplexShape.up ℤ), hT⟩) =
        (DerivedCategory.Plus.TStructure.t.truncLTι (q + 1)).app
          (DerivedCategory.Plus.Q.obj K) ≫ DerivedCategory.Plus.Q.map b := by
  classical
  let Q := DerivedCategory.Plus.Q (C := B)
  let Iq := CochainComplex.truncLE I q
  let H := CochainComplex.single₀ B
  let Hc := H.mapHomologicalComplex (ComplexShape.up ℤ)
  let ecut : Hc.obj (K.obj.truncLE q) ⟶ Iq :=
    CochainComplex.mapTruncLEComparison H K.obj q ≫ CochainComplex.truncLEMap e q
  have hcutcols (p : ℤ) : QuasiIso (ecut.f p) := by
    have : IsIso ((CochainComplex.mapTruncLEComparison H K.obj q).f p) := by
      change IsIso ((HomologicalComplex.eval _ _ p).map
        (CochainComplex.mapTruncLEComparison H K.obj q))
      infer_instance
    have : QuasiIso ((CochainComplex.truncLEMap e q).f p) :=
      cut_columns e hcolumns hcycles q p
    change QuasiIso (_ ≫ _)
    infer_instance
  have hcutzero (p : ℤ) (hp : p < 0) : IsZero (Iq.X p) :=
    IsZero.of_iso (hzero p hp) (CochainComplex.truncLEXIso I q p (by omega))
  have hplus : CochainComplex.plus B (K.obj.truncLE q) := by
    obtain ⟨a, ha⟩ := K.property
    refine ⟨a, ?_⟩
    rw [CochainComplex.isStrictlyGE_iff]
    intro p hp
    have : Mono ((K.obj.ιTruncLE q).f p) := by
      dsimp only [CochainComplex.ιTruncLE]
      infer_instance
    exact IsZero.of_mono ((K.obj.ιTruncLE q).f p)
      (CochainComplex.isZero_of_isStrictlyGE K.obj a p hp)
  let Kq : CochainComplex.Plus B := ⟨K.obj.truncLE q, hplus⟩
  let S : CochainComplex.Plus B :=
    ⟨(((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj Iq).flip).total
      (ComplexShape.up ℤ), hS⟩
  obtain ⟨aug, haugq, haq⟩ := augmentation_exists (K.obj.truncLE q) Iq ecut
    ⟨0, hcutzero⟩ hcutcols
  let bq : Kq ⟶ S := ObjectProperty.homMk aug
  let j : Kq ⟶ K := ObjectProperty.homMk (K.obj.ιTruncLE q)
  have hecut : ecut ≫ CochainComplex.ιTruncLE I q = Hc.map j.hom ≫ e := by
    dsimp only [ecut]
    rw [Category.assoc, CochainComplex.ιTruncLE_naturality, ← Category.assoc,
      CochainComplex.mapTruncLEComparison_ι]
    rfl
  have hsq : bq ≫ (ObjectProperty.homMk (mapTotal (CochainComplex.ιTruncLE I q)) : S ⟶
      ⟨(((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).total
        (ComplexShape.up ℤ), hT⟩) =
      j ≫ b := by
    apply ObjectProperty.hom_ext
    exact augmentation_naturality ecut e j.hom (CochainComplex.ιTruncLE I q)
      hecut aug b.hom haugq haug
  have : IsIso (Q.map bq) := by
    apply (DerivedCategory.Plus.isIso_iff _).mpr
    intro m
    have : QuasiIso bq.hom := haq
    have hn := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality bq m
    have : IsIso ((DerivedCategory.Plus.homologyFunctor B m).map (Q.map bq) ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso S m).hom) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (DerivedCategory.Plus.homologyFunctorObjQIso S m).hom
  obtain ⟨r₀, hr₀⟩ := derived_cut_iso K q hplus
  refine ⟨r₀ ≪≫ asIso (Q.map bq), ?_⟩
  dsimp only [Iso.trans_hom, asIso_hom]
  rw [Category.assoc, ← Q.map_comp, hsq, Q.map_comp, ← Category.assoc, hr₀]
end GoodCutIdentification

/-- The specified good-cut total represents canonical truncation and its mapped
inclusion is the shifted-cycle subcomplex inclusion.
Source: Stacks Project, Derived Categories, Tag 015X, second filtration.
(blueprint: lem-sp-ce-good-cut-identification).

Proof. Apply horizontal good truncation to e. Below q its columns are the given
column quasi-isomorphisms; at q the column is the horizontal cycles comparison,
which is a quasi-isomorphism by hcycles; above q both columns are zero. The source
is the degree-zero resolution embedding of the good truncation of K: that embedding
is exact and hence preserves the kernel in the last column. Both cut bicomplexes
have horizontal support [0,q]. The finite-column total quasi-isomorphism theorem
therefore shows that the cut augmentation is a quasi-isomorphism. Its source total
is canonically the good truncation of K. Localize and use the canonical equivalence
between good complex truncation and the t-structure truncation to obtain r. The
component equation haug identifies the given b with the full total augmentation;
the inclusion of the cut commutes with these augmentations, giving the first square.
To obtain d, examine the canonical total inclusion in degree m. Its summands are
all full terms with horizontal degree below q, the horizontal cycles at q, and zero
above q. In the full total this is exactly the vertical filtration m-q intersected
with the inverse image under d of vertical filtration m-q+1: the only prohibited
component of the differential is the outgoing horizontal differential at q. The
finite coproduct universal property and the kernel universal property give an
isomorphism onto this intersection, compatible with the differential. Apply G,
which preserves finite sums and kernels. The specified component equations hu
identify the comparison with c on every diagonal summand, including the symmetry
sign for exchanging totalization order. Thus the inclusion becomes d followed by
the actual decalage inclusion, giving the second square. This argument covers
zero and empty diagonals; q=0 uses only the horizontal cycle column. -/
theorem cartanEilenberg_good_cut_identification
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory B]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    (K : CochainComplex.Plus B)
    (I : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (e : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K.obj ⟶ I)
    (hzero : ∀ p : ℤ, p < 0 → IsZero (I.X p))
    (hcolumns : ∀ p : ℤ, QuasiIso (e.f p))
    (hcycles : ∀ p : ℤ, QuasiIso (HomologicalComplex.cyclesMap e p))
    (q : ℤ) (hq : 0 ≤ q)
    (hT : CochainComplex.plus B
      ((((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).total
        (ComplexShape.up ℤ)))
    (hS : CochainComplex.plus B
      ((((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj
        (CochainComplex.truncLE I q)).flip).total (ComplexShape.up ℤ)))
    (b : K ⟶ ⟨(((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).total
      (ComplexShape.up ℤ), hT⟩) (_hb : QuasiIso b.hom)
    (haug : ∀ m : ℤ, b.hom.f m = (e.f m).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 B).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X m))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 m m (zero_add m))
    (L : DecreasingFiltration
      (((CartanEilenbergPresentation.mappedFunctor G).obj I).total (ComplexShape.up ℤ)))
    (hL : ∀ p m : ℤ, L.complexStep p m =
      ((((CartanEilenbergPresentation.mappedFunctor G).obj I).secondFiltration m).step p))
    (u : (((CartanEilenbergPresentation.mappedFunctor G).obj I).flip).total
      (ComplexShape.up ℤ) ≅
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).total
          (ComplexShape.up ℤ)))
    (hu : ∀ (r : ℕ) (p n : ℤ) (h : (r : ℤ) + p = n),
      (((CartanEilenbergPresentation.mappedFunctor G).obj I).flip).ιTotal
          (ComplexShape.up ℤ) (r : ℤ) p n h ≫ u.hom.f n =
        (HomologicalComplex.extendXIso
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
          ComplexShape.embeddingUpNat (i := r) (i' := (r : ℤ)) rfl).hom ≫
        G.map ((HomologicalComplex.extendXIso
            (((𝟭 B).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
            ComplexShape.embeddingUpNat (i := r) (i' := (r : ℤ)) rfl).inv ≫
          (((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).flip).ιTotal
            (ComplexShape.up ℤ) (r : ℤ) p n h)) :
    let J := (CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I
    let Jq := (CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj
      (CochainComplex.truncLE I q)
    let M := (CartanEilenbergPresentation.mappedFunctor G).obj I
    let T : CochainComplex.Plus B := ⟨J.flip.total (ComplexShape.up ℤ), hT⟩
    let S : CochainComplex.Plus B := ⟨Jq.flip.total (ComplexShape.up ℤ), hS⟩
    let i : S ⟶ T := ObjectProperty.homMk (HomologicalComplex₂.total.map
      ((HomologicalComplex₂.flipFunctor B (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
        ((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).map
          (CochainComplex.ιTruncLE I q))) (ComplexShape.up ℤ))
    let c : (G.mapCochainComplexPlus.obj T).obj ≅ M.total (ComplexShape.up ℤ) :=
      u.symm ≪≫ M.totalFlipIso (ComplexShape.up ℤ)
    ∃ (r : (DerivedCategory.Plus.TStructure.t.truncLT (q + 1)).obj
          (DerivedCategory.Plus.Q.obj K) ≅ DerivedCategory.Plus.Q.obj S)
      (d : (G.mapCochainComplexPlus.obj S).obj ≅ L.decalageComplex (-q)),
      r.hom ≫ DerivedCategory.Plus.Q.map i =
        (DerivedCategory.Plus.TStructure.t.truncLTι (q + 1)).app
          (DerivedCategory.Plus.Q.obj K) ≫ DerivedCategory.Plus.Q.map b ∧
      (G.mapCochainComplexPlus.map i).hom ≫ c.hom = d.hom ≫ L.decalageι (-q)  := by
  dsimp only
  obtain ⟨r, hr⟩ := GoodCutIdentification.cut_represents_truncation K I e
    hzero hcolumns hcycles q hq hT hS b haug
  obtain ⟨d, hd⟩ := cartanEilenberg_good_cut_decalage G I hzero q hq L hL u hu
  exact ⟨r, d, hr, hd⟩

end CategoryTheory
