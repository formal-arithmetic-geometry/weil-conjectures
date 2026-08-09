/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Precylinder
public import Mathlib.CategoryTheory.Abelian.Monomorphisms
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.OfQuotient
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-!
# The K-projective derivability structure

This is the dual of `DerivabilityStructureKInjectives.lean`, which was migrated
from the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848).

If `C` is an abelian category which has K-projective resolutions (see
`CategoryTheory.Abelian.HasKProjectiveResolutions`), we show that the inclusion
of the full subcategory `CochainComplex.KProjectives C` of K-projective cochain
complexes into `CochainComplex C ℤ` is a left derivability structure
(both categories being equipped with quasi-isomorphisms).

In mathlib, this file would be
`Mathlib/Algebra/Homology/DerivedCategory/DerivabilityStructureKProjectives.lean`.

-/

@[expose] public section

universe w

open CategoryTheory Abelian Limits ZeroObject HomotopicalAlgebra

variable {C : Type*} [Category C] [Abelian C]

namespace CategoryTheory.Abelian

open HomologicalComplex in
lemma quasiIso_g_iff_of_shortExact {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    QuasiIso S.g ↔ S.X₁.Acyclic := by
  refine ⟨fun _ n ↦ ?_, fun h ↦ ⟨fun n ↦ ?_⟩⟩
  · rw [HomologicalComplex.exactAt_iff_isZero_homology]
    refine (hS.homology_exact₁ (n - 1) n (by simp)).isZero_X₂ ?_ ?_
    · simp [← cancel_epi (homologyMap S.g (n - 1))]
    · rw [← cancel_mono (homologyMap S.g n), zero_comp, ← homologyMap_comp,
        S.zero, homologyMap_zero]
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    have := (hS.homology_exact₂ n).mono_g (by
      apply IsZero.eq_of_src
      simpa [← exactAt_iff_isZero_homology] using h n)
    have := (hS.homology_exact₃ n (n + 1) (by simp)).epi_f (by
      apply IsZero.eq_of_tgt
      simpa [← exactAt_iff_isZero_homology] using h (n + 1))
    exact Balanced.isIso_of_mono_of_epi _

instance :
    (HomologicalComplex.quasiIso C (.up ℤ) ⊓
      (MorphismProperty.epimorphisms _)).IsStableUnderBaseChange where
  of_isPullback {X Y Y' S f g f' g'} sq h := by
    have : Epi g := h.2
    have : Epi g' := (MorphismProperty.epimorphisms _).of_isPullback sq h.2
    refine ⟨?_, by simpa⟩
    have hK : (ShortComplex.mk (kernel.ι g') g' (by simp)).ShortExact :=
      { exact := ShortComplex.exact_kernel g' }
    have hL : (ShortComplex.mk (kernel.ι g) g (by simp)).ShortExact :=
      { exact := ShortComplex.exact_kernel g }
    let e : kernel g' ≅ kernel g :=
      { hom := kernel.map _ _ f' f sq.w.symm
        inv := kernel.lift _ (sq.lift (kernel.ι g) 0 (by simp)) (by simp)
        hom_inv_id := equalizer.hom_ext (by apply sq.hom_ext <;> simp)
        inv_hom_id := equalizer.hom_ext (by simp) }
    replace hK := quasiIso_g_iff_of_shortExact hK
    replace hL := quasiIso_g_iff_of_shortExact hL
    dsimp at hK hL
    simp only [HomologicalComplex.mem_quasiIso_iff]
    rw [hK]
    exact HomologicalComplex.Acyclic.of_iso (by simpa [← hL] using h.1) e.symm

instance {K₁ K₂ L₁ : CochainComplex C ℤ} (f : K₁ ⟶ K₂) (p : L₁ ⟶ K₂) [Epi p] [QuasiIso p] :
    QuasiIso (pullback.fst f p) :=
  (MorphismProperty.of_isPullback
    (P := (HomologicalComplex.quasiIso C (.up ℤ) ⊓
      (MorphismProperty.epimorphisms _))) (IsPullback.of_hasPullback f p).flip
        ⟨by simpa, by simpa⟩).1

variable (C) in
/-- An abelian category `C` has K-projective resolutions if any cochain complex
in `C` is the target of a quasi-isomorphism which is an epimorphism and whose
source is K-projective. -/
class HasKProjectiveResolutions : Prop where
  exists_isKProjective (K : CochainComplex C ℤ) :
    ∃ (L : CochainComplex C ℤ) (_ : L.IsKProjective) (p : L ⟶ K), Epi p ∧ QuasiIso p

end CategoryTheory.Abelian

namespace CochainComplex

variable (C) in
/-- The full subcategory of K-projective cochain complexes. -/
abbrev KProjectives :=
  ObjectProperty.FullSubcategory (fun (K : CochainComplex C ℤ) ↦ K.IsKProjective)

namespace KProjectives

/-- The object of `CochainComplex.KProjectives C` attached to a K-projective
cochain complex. -/
abbrev mk (K : CochainComplex C ℤ) [K.IsKProjective] : KProjectives C := ⟨K, inferInstance⟩

lemma mk_surjective (X : KProjectives C) :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsKProjective),
      X = mk K :=
  ⟨X.obj, X.property, rfl⟩

/-- The inclusion of the K-projective cochain complexes in all cochain complexes. -/
abbrev ι : KProjectives C ⥤ CochainComplex C ℤ := ObjectProperty.ι _

variable (C) in
/-- Quasi-isomorphisms between K-projective cochain complexes. -/
def quasiIso : MorphismProperty (KProjectives C) :=
  (HomologicalComplex.quasiIso C (.up ℤ)).inverseImage ι

variable (C) in
/-- The localizer morphism given by the inclusion of the K-projective cochain
complexes in all cochain complexes. -/
@[simps]
def localizerMorphism :
    LocalizerMorphism (KProjectives.quasiIso C) (HomologicalComplex.quasiIso C (.up ℤ)) where
  functor := ι
  map := by rfl

variable [HasKProjectiveResolutions C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (K : CochainComplex C ℤ) :
    IsConnected ((localizerMorphism C).LeftResolution K) := by
  obtain ⟨L, _, p, _, _⟩ := HasKProjectiveResolutions.exists_isKProjective K
  let R : (localizerMorphism C).LeftResolution K := { X₁ := .mk L, w := p, hw := by simpa }
  have : Nonempty ((localizerMorphism C).LeftResolution K) := ⟨R⟩
  have : ∀ R', ∃ R'', Nonempty (R'' ⟶ R) ∧ Nonempty (R'' ⟶ R') := by
    intro R'
    obtain ⟨M, _, q, _, _⟩ := HasKProjectiveResolutions.exists_isKProjective (pullback R'.w p)
    have : QuasiIso R'.w := R'.hw
    refine ⟨{ X₁ := .mk M, w := q ≫ pullback.fst R'.w p ≫ R'.w, hw := ?_ }, ⟨?_⟩, ⟨?_⟩⟩
    · dsimp
      simp only [HomologicalComplex.mem_quasiIso_iff]
      infer_instance
    · exact
        { f := ObjectProperty.homMk (q ≫ pullback.snd R'.w p)
          comm := by simp [← pullback.condition, R] }
    · exact { f := ObjectProperty.homMk (q ≫ pullback.fst R'.w p) }
  refine zigzag_isConnected (fun R₁ R₂ ↦ ?_)
  obtain ⟨R₁', ⟨f₁⟩, ⟨g₁⟩⟩ := this R₁
  obtain ⟨R₂', ⟨f₂⟩, ⟨g₂⟩⟩ := this R₂
  exact (Zigzag.of_inv g₁).trans ((Zigzag.of_hom f₁).trans
    ((Zigzag.of_inv f₂).trans (Zigzag.of_hom g₂)))

set_option backward.defeqAttrib.useBackward true in
instance : (localizerMorphism C).arrow.HasLeftResolutions := by
  intro f
  obtain ⟨K₁, K₂, f, rfl⟩ := Arrow.mk_surjective f
  obtain ⟨L₂, _, p₂, _, _⟩ := HasKProjectiveResolutions.exists_isKProjective K₂
  have : QuasiIso (pullback.fst f p₂) := inferInstance
  obtain ⟨M, _, q, _, _⟩ := HasKProjectiveResolutions.exists_isKProjective (pullback f p₂)
  refine ⟨{
    X₁ := Arrow.mk (X := .mk M) (Y := .mk L₂) (ObjectProperty.homMk (q ≫ pullback.snd f p₂))
    w := Arrow.homMk (q ≫ pullback.fst f p₂) p₂ (by simp [← pullback.condition])
    hw := ⟨by
      dsimp
      simp only [HomologicalComplex.mem_quasiIso_iff]
      infer_instance, by simpa⟩
  }⟩

end KProjectives

end CochainComplex

namespace HomotopyCategory

variable (C) in
/-- The full subcategory of the homotopy category consisting of K-projective
cochain complexes. -/
abbrev KProjectives :=
  (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal.FullSubcategory

namespace KProjectives

/-- The object of `HomotopyCategory.KProjectives C` attached to a K-projective
cochain complex. -/
abbrev mk (K : CochainComplex C ℤ) [K.IsKProjective] :
    KProjectives C :=
  ⟨(HomotopyCategory.quotient _ _).obj K, by
    rwa [← CochainComplex.isKProjective_iff_leftOrthogonal]⟩

lemma mk_surjective (X : KProjectives C) :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsKProjective),
      X = mk K := by
  obtain ⟨X, hX⟩ := X
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  rw [← CochainComplex.isKProjective_iff_leftOrthogonal] at hX
  exact ⟨K, inferInstance, rfl⟩

/-- The inclusion of the K-projective complexes in the homotopy category. -/
def ι : KProjectives C ⥤ HomotopyCategory C (.up ℤ) :=
  ObjectProperty.ι _

section

variable [HasDerivedCategory C]

/-- The functor from the K-projective complexes in the homotopy category to
the derived category. -/
noncomputable def Qh : KProjectives C ⥤ DerivedCategory C :=
  ι ⋙ DerivedCategory.Qh

instance : (Qh (C := C)).Full where
  map_surjective {K L} f := by
    obtain ⟨K, _, rfl⟩ := K.mk_surjective
    obtain ⟨L, _, rfl⟩ := L.mk_surjective
    obtain ⟨f, rfl⟩ := (CochainComplex.IsKProjective.Qh_map_bijective
      K ((HomotopyCategory.quotient _ _).obj L)).2 f
    exact ⟨ObjectProperty.homMk f, rfl⟩

instance : (Qh (C := C)).Faithful where
  map_injective {K L f g} h := by
    obtain ⟨K, _, rfl⟩ := K.mk_surjective
    obtain ⟨L, _, rfl⟩ := L.mk_surjective
    ext
    exact (CochainComplex.IsKProjective.Qh_map_bijective
      K ((HomotopyCategory.quotient _ _).obj L)).1 h

variable [HasKProjectiveResolutions C]

instance : (Qh (C := C)).EssSurj where
  mem_essImage X := by
    obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Qh) X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L, _, p, _, _⟩ := HasKProjectiveResolutions.exists_isKProjective K
    have := Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
      ((HomotopyCategory.quotient _ _).map p)
        (by simpa [quotient_map_mem_quasiIso_iff])
    exact ⟨mk L,
      ⟨asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map p)) ≪≫ e⟩⟩

instance : (Qh (C := C)).IsEquivalence where

instance : Qh.IsLocalization (.isomorphisms (KProjectives C)) := by
  let l : LocalizerMorphism (.isomorphisms (KProjectives C))
      (HomotopyCategory.quasiIso C (.up ℤ)) :=
    { functor := ι
      map := by
        intro K L f (hf : IsIso f)
        simp only [MorphismProperty.inverseImage_iff, quasiIso]
        infer_instance }
  have : CatCommSq l.functor (𝟭 (KProjectives C)) DerivedCategory.Qh Qh :=
    ⟨(Functor.leftUnitor _).symm⟩
  have : l.IsLocalizedEquivalence :=
    LocalizerMorphism.IsLocalizedEquivalence.mk' l (𝟭 _) (DerivedCategory.Qh) Qh
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    l DerivedCategory.Qh

end

end KProjectives

end HomotopyCategory

namespace CochainComplex

namespace KProjectives

/-- The functor from K-projective cochain complexes to the K-projective objects
of the homotopy category. -/
def toHomotopyCategory : KProjectives C ⥤ HomotopyCategory.KProjectives C :=
  ObjectProperty.lift _ (KProjectives.ι ⋙ HomotopyCategory.quotient _ _) (fun K ↦ by
    simpa [← CochainComplex.isKProjective_iff_leftOrthogonal] using K.property)

@[simp]
lemma toHomotopyCategory_obj (K : CochainComplex C ℤ) [K.IsKProjective] :
    toHomotopyCategory.obj (mk K) = HomotopyCategory.KProjectives.mk K := rfl

instance : (toHomotopyCategory (C := C)).Full where
  map_surjective {K L} f := by
    obtain ⟨K, _, rfl⟩ := K.mk_surjective
    obtain ⟨L, _, rfl⟩ := L.mk_surjective
    obtain ⟨f, rfl⟩ := ObjectProperty.homMk_surjective f
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    exact ⟨ObjectProperty.homMk f, rfl⟩

instance : (toHomotopyCategory (C := C)).EssSurj where
  mem_essImage X := by
    obtain ⟨K, _, rfl⟩ := X.mk_surjective
    exact ⟨mk K, ⟨Iso.refl _⟩⟩

lemma isIso_toHomotopyCategory_map_iff {K L : KProjectives C} (f : K ⟶ L) :
    IsIso (toHomotopyCategory.map f) ↔ QuasiIso f.hom := by
  have := HasDerivedCategory.standard C
  rw [← isIso_iff_of_reflects_iso _ HomotopyCategory.KProjectives.Qh]
  obtain ⟨K, _, rfl⟩ := K.mk_surjective
  obtain ⟨L, _, rfl⟩ := L.mk_surjective
  obtain ⟨f, rfl⟩ := ObjectProperty.homMk_surjective f
  exact DerivedCategory.isIso_Q_map_iff_quasiIso C f

set_option backward.defeqAttrib.useBackward true in
instance (K : CochainComplex C ℤ) [K.IsKProjective] :
    CochainComplex.IsKProjective (HomologicalComplex.cylinder K) := by
  rw [CochainComplex.isKProjective_iff_leftOrthogonal]
  refine ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished _) ?_ ?_
  · dsimp
    rwa [← CochainComplex.isKProjective_iff_leftOrthogonal]
  · dsimp
    rw [← CochainComplex.isKProjective_iff_leftOrthogonal]
    infer_instance

variable [HasKProjectiveResolutions C]

set_option backward.defeqAttrib.useBackward true in
instance : toHomotopyCategory.IsLocalization (KProjectives.quasiIso C) := by
  refine Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _ ?_ ?_
  · intro K L f hf
    rwa [isIso_toHomotopyCategory_map_iff]
  · intro K L f₀ f₁ h
    obtain ⟨K, _, rfl⟩ := K.mk_surjective
    obtain ⟨L, _, rfl⟩ := L.mk_surjective
    obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjective f₀
    obtain ⟨f₁, rfl⟩ := ObjectProperty.homMk_surjective f₁
    dsimp at f₀ f₁ h
    let H : Homotopy f₀ f₁ :=
      HomotopyCategory.homotopyOfEq _ _ (HomotopyCategory.KProjectives.ι.congr_map h)
    refine ⟨K.precylinder.toFullSubcategory (by dsimp; infer_instance),
      Precylinder.LeftHomotopy.fullSubcategoryEquiv.symm
        { h := HomologicalComplex.cylinder.desc _ _ H  }, ?_⟩
    · exact (HomologicalComplex.cylinder.homotopyEquiv K
        (fun n ↦ ⟨n - 1, by simp⟩)).quasiIso_hom

set_option backward.defeqAttrib.useBackward true in
instance [HasDerivedCategory C] :
    (ι ⋙ DerivedCategory.Q).IsLocalization (quasiIso C) := by
  change (toHomotopyCategory ⋙ (HomotopyCategory.KProjectives.Qh (C := C))).IsLocalization _
  refine Functor.IsLocalization.comp toHomotopyCategory
    (HomotopyCategory.KProjectives.Qh) (W₂ := .isomorphisms _) _ _ ?_ le_rfl ?_
  · intro K L f hf
    have : IsIso (toHomotopyCategory.map f) := by rwa [isIso_toHomotopyCategory_map_iff]
    dsimp
    infer_instance
  · intro K L f hf
    obtain ⟨K, _, rfl⟩ := K.mk_surjective
    obtain ⟨L, _, rfl⟩ := L.mk_surjective
    obtain ⟨f, rfl⟩ := ObjectProperty.homMk_surjective f
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    refine ⟨mk K, mk L, ObjectProperty.homMk f, ?_, ⟨Iso.refl _⟩⟩
    have : IsIso ((HomotopyCategory.quotient _ _).map f) := by
      simp only [MorphismProperty.isomorphisms.iff] at hf
      exact (Functor.mapIso HomotopyCategory.KProjectives.ι (@asIso _ _ _ _ _ hf)).isIso_hom
    have : QuasiIso f := by
      rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
      exact
      (DerivedCategory.Qh.mapIso
        (asIso ((HomotopyCategory.quotient _ _).map f))).isIso_hom
    simpa [quasiIso]

set_option backward.defeqAttrib.useBackward true in
instance [HasDerivedCategory C] :
    ((localizerMorphism C).functor ⋙ DerivedCategory.Q).IsLocalization (quasiIso C) := by
  dsimp
  infer_instance

instance : (localizerMorphism C).IsLocalizedEquivalence := by
  have := HasDerivedCategory.standard C
  exact .of_isLocalization_of_isLocalization _ (DerivedCategory.Q)

instance : (localizerMorphism C).IsLeftDerivabilityStructure :=
  .mk' _

end KProjectives

end CochainComplex

namespace HomotopyCategory

namespace KProjectives

variable (C) in
/-- The localizer morphism that is given by the "inclusion functor"
`HomotopyCategory.KProjectives C ⥤ HomotopyCategory C (ComplexShape.up ℤ)`.
The target category is equipped with the class of quasi-isomorphisms while
the source category `HomotopyCategory.KProjectives C` is equipped with the
class of isomorphisms (which is exactly the same as quasi-isomorphisms). -/
abbrev localizerMorphism : LocalizerMorphism
    (MorphismProperty.isomorphisms (KProjectives C))
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) where
  functor := ι
  map K L f (hf : IsIso f) := by
    rw [MorphismProperty.inverseImage_iff, mem_quasiIso_iff]
    intro n
    infer_instance

variable [HasKProjectiveResolutions C]

instance [HasDerivedCategory C] :
    ((localizerMorphism C).functor ⋙ DerivedCategory.Qh).IsLocalization
      (MorphismProperty.isomorphisms (KProjectives C)) :=
  inferInstanceAs ((Qh (C := C)).IsLocalization _)

instance : (localizerMorphism C).IsLocalizedEquivalence := by
  have := HasDerivedCategory.standard C
  exact .of_isLocalization_of_isLocalization _ DerivedCategory.Qh

instance (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    IsConnected ((localizerMorphism C).LeftResolution X) := by
  have := HasDerivedCategory.standard C
  obtain ⟨K, rfl⟩ := quotient_obj_surjective X
  obtain ⟨L, _, p, _, _⟩ := HasKProjectiveResolutions.exists_isKProjective K
  have : Nonempty ((localizerMorphism C).LeftResolution ((quotient _ _).obj K)) :=
    ⟨{ X₁ := .mk L
       w := (quotient _ _).map p
       hw := by
        simpa [quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
          using inferInstanceAs (QuasiIso p) }⟩
  refine zigzag_isConnected (fun R₁ R₂ => ?_)
  obtain ⟨X₁, w₁, hw₁, rfl⟩ := R₁.mk_surjective
  obtain ⟨X₂, w₂, hw₂, rfl⟩ := R₂.mk_surjective
  obtain ⟨L₁, _, rfl⟩ := X₁.mk_surjective
  obtain ⟨L₂, _, rfl⟩ := X₂.mk_surjective
  have := Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ)) w₂ hw₂
  obtain ⟨f, hf⟩ := (Qh (C := C)).map_surjective
    (DerivedCategory.Qh.map w₁ ≫ inv (DerivedCategory.Qh.map w₂))
  exact Zigzag.of_hom
    { f := f
      comm := (CochainComplex.IsKProjective.Qh_map_bijective L₁ _).injective (by
        rw [Functor.map_comp]
        change (Qh (C := C)).map f ≫ _ = _
        rw [hf, Category.assoc, IsIso.inv_hom_id, Category.comp_id]) }

/-- Auxiliary localizer morphism for the proof that
`HomotopyCategory.KProjectives.localizerMorphism` has left resolutions of arrows:
the quotient functor `CochainComplex.KProjectives C ⥤ HomotopyCategory.KProjectives C`
sends quasi-isomorphisms to isomorphisms. -/
private abbrev toHomotopyCategoryLocalizerMorphism :
    LocalizerMorphism (CochainComplex.KProjectives.quasiIso C)
      (MorphismProperty.isomorphisms (KProjectives C)) where
  functor := CochainComplex.KProjectives.toHomotopyCategory
  map _ _ f hf :=
    (CochainComplex.KProjectives.isIso_toHomotopyCategory_map_iff f).2 (by
      simpa [CochainComplex.KProjectives.quasiIso, MorphismProperty.inverseImage_iff,
        HomologicalComplex.mem_quasiIso_iff] using hf)

/-- Auxiliary localizer morphism for the proof that
`HomotopyCategory.KProjectives.localizerMorphism` has left resolutions of arrows:
the quotient functor `CochainComplex C ℤ ⥤ HomotopyCategory C (ComplexShape.up ℤ)`
sends quasi-isomorphisms to quasi-isomorphisms. -/
private abbrev quotientLocalizerMorphism :
    LocalizerMorphism (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) where
  functor := quotient C (ComplexShape.up ℤ)
  map _ _ f hf := by simpa [quotient_map_mem_quasiIso_iff] using hf

instance : (localizerMorphism C).arrow.HasLeftResolutions :=
  LocalizerMorphism.hasLeftResolutions_arrow_of_essSurj_of_full
    (T := CochainComplex.KProjectives.localizerMorphism C)
    (L := toHomotopyCategoryLocalizerMorphism)
    (R := quotientLocalizerMorphism)
    (B := localizerMorphism C)
    (Iso.refl _)

instance : (localizerMorphism C).IsLeftDerivabilityStructure := .mk' _

end KProjectives

end HomotopyCategory
