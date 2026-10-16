/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import all WeilConjectures.Algebra.Homology.UpperTruncationStepQuotient

/-! # Comparing cochain and derived upper truncations

Source: Stacks Project, Tag 0118; Mathlib, canonical t-structure truncation triangles.
(blueprint: lem-sp-derived-upper-truncation-comparison).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- The upper smart truncation of a complex realizes the canonical derived truncation,
by the unique isomorphism commuting with its inclusion.
Source: Stacks Project, Tag 0118; Mathlib, TStructure.triangle_iso_exists
(blueprint: lem-sp-derived-upper-truncation-comparison).

Proof. The short exact truncation sequence gives a distinguished triangle whose
first object is at most q and whose third object is quasi-isomorphic to the lower
truncation at q+1. Hence its third object is at least q+1. Uniqueness of t-structure
triangles extends the identity on Q(K) to an isomorphism with the canonical
truncation triangle. Its first component is the asserted isomorphism. Maps from
an object at most q into the upper truncation are determined by composition with
the truncation inclusion, which proves the asserted uniqueness. -/
theorem exists_unique_truncLE_Q_iso (K : CochainComplex C ℤ) (q : ℤ) :
    ∃! e : Q.obj (K.truncLE q) ≅
        (TStructure.t.truncLT (q + 1)).obj (Q.obj K),
      e.hom ≫ (TStructure.t.truncLTι (q + 1)).app (Q.obj K) =
        Q.map (K.ιTruncLE q) := by
  let t := TStructure.t (C := C)
  let hS := K.shortComplexTruncLE_shortExact q
  let T := triangleOfSES hS
  let U := (t.triangleLTGE (q + 1)).obj (Q.obj K)
  have h₀ : t.IsLE T.obj₁ q := by
    change t.IsLE (Q.obj (K.truncLE q)) q
    infer_instance
  have h₁ : t.IsGE T.obj₃ (q + 1) := by
    let e := asIso (Q.map (K.shortComplexTruncLEX₃ToTruncGE q (q + 1) rfl))
    exact t.isGE_of_iso e.symm (q + 1)
  have h₀' : t.IsLE U.obj₁ q := by
    change t.IsLE ((t.truncLT (q + 1)).obj (Q.obj K)) q
    exact t.isLE_truncLT_obj _ _ _ (by omega)
  have h₁' : t.IsGE U.obj₃ (q + 1) := by
    change t.IsGE ((t.truncGE (q + 1)).obj (Q.obj K)) (q + 1)
    infer_instance
  obtain ⟨e, he⟩ := t.triangle_iso_exists (triangleOfSES_distinguished hS)
    (t.triangleLTGE_distinguished (q + 1) (Q.obj K)) (Iso.refl _) q (q + 1)
      h₀ h₁ h₀' h₁'
  let i : Q.obj (K.truncLE q) ≅ (t.truncLT (q + 1)).obj (Q.obj K) :=
    Triangle.π₁.mapIso e
  have hi : i.hom ≫ (t.truncLTι (q + 1)).app (Q.obj K) =
      Q.map (K.ιTruncLE q) := by
    simpa [i, he, CochainComplex.truncLE, CochainComplex.ιTruncLE] using e.hom.comm₁.symm
  refine ⟨i, hi, ?_⟩
  intro i' hi'
  have : t.IsLE (Q.obj (K.truncLE q)) (q + 1 - 1) := by
    simp only [add_sub_cancel_right]
    infer_instance
  exact Iso.ext (t.to_truncLT_obj_ext (hi'.trans hi.symm))

/-- The comparison is chosen from a proved unique characterization, rather than
from an unspecified existence theorem. -/
noncomputable def truncLEQIso (K : CochainComplex C ℤ) (q : ℤ) :
    Q.obj (K.truncLE q) ≅ (TStructure.t.truncLT (q + 1)).obj (Q.obj K) :=
  (exists_unique_truncLE_Q_iso K q).choose

@[reassoc]
theorem truncLEQIso_hom_ι (K : CochainComplex C ℤ) (q : ℤ) :
    (truncLEQIso K q).hom ≫ (TStructure.t.truncLTι (q + 1)).app (Q.obj K) =
      Q.map (K.ιTruncLE q) :=
  (exists_unique_truncLE_Q_iso K q).choose_spec.1

/-- The unique normalized truncation comparison commutes with every complex map. -/
@[reassoc]
theorem truncLEQIso_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) (q : ℤ) :
    Q.map (CochainComplex.truncLEMap f q) ≫ (truncLEQIso L q).hom =
      (truncLEQIso K q).hom ≫ (TStructure.t.truncLT (q + 1)).map (Q.map f) := by
  let t := TStructure.t (C := C)
  have : t.IsLE (Q.obj (K.truncLE q)) (q + 1 - 1) := by
    simp only [add_sub_cancel_right]
    infer_instance
  apply t.to_truncLT_obj_ext
  rw [Category.assoc, truncLEQIso_hom_ι]
  rw [Category.assoc, (t.truncLTι (q + 1)).naturality, ← Category.assoc,
    truncLEQIso_hom_ι, Functor.id_map, ← Q.map_comp, ← Q.map_comp]
  exact congrArg Q.map (CochainComplex.ιTruncLE_naturality f q)

/-- Any map between the cochain upper truncations commuting with their inclusions
corresponds to the canonical map between the derived upper truncations. -/
@[reassoc]
theorem truncLEQIso_of_le (K : CochainComplex C ℤ) (q r : ℤ) (h : q ≤ r)
    (u : K.truncLE q ⟶ K.truncLE r)
    (hu : u ≫ K.ιTruncLE r = K.ιTruncLE q) :
    Q.map u ≫ (truncLEQIso K r).hom =
      (truncLEQIso K q).hom ≫
        (TStructure.t.natTransTruncLTOfLE (q + 1) (r + 1) (by omega)).app (Q.obj K) := by
  let t := TStructure.t (C := C)
  have : t.IsLE (Q.obj (K.truncLE q)) (r + 1 - 1) := by
    simp only [add_sub_cancel_right]
    exact t.isLE_of_le _ q r h
  apply t.to_truncLT_obj_ext
  rw [Category.assoc, truncLEQIso_hom_ι, Category.assoc,
    t.natTransTruncLTOfLE_ι_app, truncLEQIso_hom_ι, ← Q.map_comp, hu]

section Cutoff

omit [HasDerivedCategory C]

/-- Upper smart truncations have unique cutoff maps commuting with their inclusions.
Source: Stacks Project, Tag 0118
(blueprint: lem-sp-derived-upper-truncation-comparison).

Proof. For strict cutoffs, below the larger cutoff lift the smaller inclusion
through the coordinate isomorphism of the larger truncation. At or above the
larger cutoff the source is zero. Cancel the larger inclusion to prove the
chain-map equation. The same cancellation proves uniqueness. Equal cutoffs use
the identity. -/
theorem exists_unique_truncLECutoffMap (K : CochainComplex C ℤ)
    (q r : ℤ) (h : q ≤ r) :
    ∃! u : K.truncLE q ⟶ K.truncLE r, u ≫ K.ιTruncLE r = K.ιTruncLE q := by
  have : Mono (K.ιTruncLE r) :=
    inferInstanceAs (Mono (HomologicalComplex.ιTruncLE K (ComplexShape.embeddingUpIntLE r)))
  by_cases hqr : q = r
  · subst r
    refine ⟨𝟙 _, by simp, ?_⟩
    intro u hu
    exact (cancel_mono (K.ιTruncLE q)).1 (by simpa using hu)
  have hlt : q < r := lt_of_le_of_ne h hqr
  let f (n : ℤ) : (K.truncLE q).X n ⟶ (K.truncLE r).X n :=
    if hn : n < r then
      (K.ιTruncLE q).f n ≫ (K.truncLEXIso r n hn).inv
    else 0
  have hf (n : ℤ) : f n ≫ (K.ιTruncLE r).f n = (K.ιTruncLE q).f n := by
    dsimp only [f]
    split_ifs with hn
    · rw [(CochainComplex.truncLE_inclusion_coordinates K r).2 n hn]
      simp
    · exact ((K.truncLE q).isZero_of_isStrictlyLE q n (by omega)).eq_of_src _ _
  let u : K.truncLE q ⟶ K.truncLE r :=
    { f := f
      comm' := by
        intro i j hij
        have : Mono ((K.ιTruncLE r).f j) :=
          inferInstanceAs (Mono ((HomologicalComplex.ιTruncLE K
            (ComplexShape.embeddingUpIntLE r)).f j))
        apply (cancel_mono ((K.ιTruncLE r).f j)).1
        rw [Category.assoc, ← (K.ιTruncLE r).comm, ← Category.assoc, hf,
          Category.assoc, hf, (K.ιTruncLE q).comm] }
  refine ⟨u, ?_, ?_⟩
  · ext n
    exact hf n
  · intro u' hu'
    apply (cancel_mono (K.ιTruncLE r)).1
    exact hu'.trans (by ext n; exact (hf n).symm)

/-- The actual cutoff inclusion, chosen from a proved unique characterization. -/
noncomputable def truncLECutoffMap (K : CochainComplex C ℤ)
    {q r : ℤ} (h : q ≤ r) : K.truncLE q ⟶ K.truncLE r :=
  (exists_unique_truncLECutoffMap K q r h).choose

@[reassoc]
theorem truncLECutoffMap_ι (K : CochainComplex C ℤ) {q r : ℤ} (h : q ≤ r) :
    truncLECutoffMap K h ≫ K.ιTruncLE r = K.ιTruncLE q :=
  (exists_unique_truncLECutoffMap K q r h).choose_spec.1

/-- Cutoff inclusions commute with all complex maps. -/
@[reassoc]
theorem truncLECutoffMap_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L)
    {q r : ℤ} (h : q ≤ r) :
    truncLECutoffMap K h ≫ CochainComplex.truncLEMap f r =
      CochainComplex.truncLEMap f q ≫ truncLECutoffMap L h := by
  have : Mono (L.ιTruncLE r) :=
    inferInstanceAs (Mono (HomologicalComplex.ιTruncLE L (ComplexShape.embeddingUpIntLE r)))
  apply (cancel_mono (L.ιTruncLE r)).1
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality, ← Category.assoc,
    truncLECutoffMap_ι, Category.assoc, truncLECutoffMap_ι,
    CochainComplex.ιTruncLE_naturality]

end Cutoff

namespace Plus

/-- A bounded-below smart upper truncation, with its actual underlying complex. -/
noncomputable def cochainTruncLE (K : CochainComplex.Plus C) (q : ℤ) :
    CochainComplex.Plus C :=
  ⟨K.obj.truncLE q, by
    obtain ⟨n, hn⟩ := K.property
    exact ⟨n, inferInstance⟩⟩

/-- The actual inclusion of the bounded-below upper truncation. -/
noncomputable def cochainTruncLEι (K : CochainComplex.Plus C) (q : ℤ) :
    cochainTruncLE K q ⟶ K :=
  ObjectProperty.homMk (K.obj.ιTruncLE q)

/-- The cochain/derived truncation comparison also holds in the bounded-below
categories used by the right derived functor.
Source: Stacks Project, Tag 0118; Mathlib canonical t-structure uniqueness
(blueprint: lem-sp-derived-upper-truncation-comparison).

Proof. Compare the distinguished cochain truncation triangle in D(C) with the
image of the canonical triangle in D+(C), using the canonical localization
comparison as middle isomorphism. Their bounds give a triangle isomorphism.
Its first component, composed with the localization comparison, lifts uniquely
through the fully faithful inclusion D+(C) to D(C). Its inclusion equation follows
from the triangle square and naturality of the localization comparison.
The upper-truncation extensionality principle gives uniqueness in D+(C). -/
theorem exists_unique_cochainTruncLE_Q_iso (K : CochainComplex.Plus C) (q : ℤ) :
    ∃! e : Q.obj (cochainTruncLE K q) ≅
        (TStructure.t.truncLT (q + 1)).obj (Q.obj K),
      e.hom ≫ (TStructure.t.truncLTι (q + 1)).app (Q.obj K) =
        Q.map (cochainTruncLEι K q) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let t' := TStructure.t (C := C)
  let hS := K.obj.shortComplexTruncLE_shortExact q
  let T := triangleOfSES hS
  let U := ι.mapTriangle.obj ((t'.triangleLTGE (q + 1)).obj (Q.obj K))
  have h₀ : t.IsLE T.obj₁ q := by
    change t.IsLE (DerivedCategory.Q.obj (K.obj.truncLE q)) q
    infer_instance
  have h₁ : t.IsGE T.obj₃ (q + 1) := by
    let e := asIso (DerivedCategory.Q.map
      (K.obj.shortComplexTruncLEX₃ToTruncGE q (q + 1) rfl))
    exact t.isGE_of_iso e.symm (q + 1)
  have h₀' : t.IsLE U.obj₁ q := by
    change t.IsLE (ι.obj ((t'.truncLT (q + 1)).obj (Q.obj K))) q
    have : t'.IsLE ((t'.truncLT (q + 1)).obj (Q.obj K)) q :=
      t'.isLE_truncLT_obj _ _ _ (by omega)
    infer_instance
  have h₁' : t.IsGE U.obj₃ (q + 1) := by
    change t.IsGE (ι.obj ((t'.truncGE (q + 1)).obj (Q.obj K))) (q + 1)
    infer_instance
  let eK : DerivedCategory.Q.obj K.obj ≅ ι.obj (Q.obj K) :=
    (quotientCompQhIso C).symm.app K.obj
  obtain ⟨e, he⟩ := t.triangle_iso_exists (triangleOfSES_distinguished hS)
    (ι.map_distinguished _ (t'.triangleLTGE_distinguished (q + 1) (Q.obj K)))
    eK q (q + 1) h₀ h₁ h₀' h₁'
  let i : DerivedCategory.Q.obj (K.obj.truncLE q) ≅
      ι.obj ((t'.truncLT (q + 1)).obj (Q.obj K)) := Triangle.π₁.mapIso e
  let j : ι.obj (Q.obj (cochainTruncLE K q)) ≅
      ι.obj ((t'.truncLT (q + 1)).obj (Q.obj K)) :=
    (quotientCompQhIso C).app (K.obj.truncLE q) ≪≫ i
  let k := ι.preimageIso j
  have hi : i.hom ≫ ι.map ((t'.truncLTι (q + 1)).app (Q.obj K)) =
      DerivedCategory.Q.map (K.obj.ιTruncLE q) ≫ eK.hom := by
    simpa [i, he, CochainComplex.truncLE, CochainComplex.ιTruncLE] using e.hom.comm₁.symm
  have hk : k.hom ≫ (t'.truncLTι (q + 1)).app (Q.obj K) =
      Q.map (cochainTruncLEι K q) := by
    apply ι.map_injective
    rw [Functor.map_comp]
    simp only [k, Functor.preimageIso_hom, Functor.map_preimage]
    dsimp only [j, Iso.trans_hom]
    rw [Category.assoc, hi, ← Category.assoc]
    have hn := (quotientCompQhIso C).hom.naturality (K.obj.ιTruncLE q)
    dsimp only [Functor.comp_map] at hn
    erw [← hn]
    simp [eK]
    rfl
  refine ⟨k, hk, ?_⟩
  intro k' hk'
  have : t'.IsLE (Q.obj (cochainTruncLE K q)) (q + 1 - 1) := by
    simp only [add_sub_cancel_right]
    apply (isLE_ι_obj_iff _ q).1
    exact t.isLE_of_iso ((quotientCompQhIso C).app (K.obj.truncLE q)).symm q
  exact Iso.ext (t'.to_truncLT_obj_ext (hk'.trans hk.symm))

/-- The normalized comparison is chosen from its proved unique characterization. -/
noncomputable def cochainTruncLEQIso (K : CochainComplex.Plus C) (q : ℤ) :
    Q.obj (cochainTruncLE K q) ≅ (TStructure.t.truncLT (q + 1)).obj (Q.obj K) :=
  (exists_unique_cochainTruncLE_Q_iso K q).choose

@[reassoc]
theorem cochainTruncLEQIso_hom_ι (K : CochainComplex.Plus C) (q : ℤ) :
    (cochainTruncLEQIso K q).hom ≫ (TStructure.t.truncLTι (q + 1)).app (Q.obj K) =
      Q.map (cochainTruncLEι K q) :=
  (exists_unique_cochainTruncLE_Q_iso K q).choose_spec.1

/-- Restrict a bounded-below complex map to its upper smart truncation. -/
noncomputable def cochainTruncLEMap {K L : CochainComplex.Plus C} (f : K ⟶ L) (q : ℤ) :
    cochainTruncLE K q ⟶ cochainTruncLE L q :=
  ObjectProperty.homMk (CochainComplex.truncLEMap f.hom q)

/-- The bounded-below normalized comparison commutes with every complex map. -/
@[reassoc]
theorem cochainTruncLEQIso_naturality {K L : CochainComplex.Plus C} (f : K ⟶ L) (q : ℤ) :
    Q.map (cochainTruncLEMap f q) ≫ (cochainTruncLEQIso L q).hom =
      (cochainTruncLEQIso K q).hom ≫ (TStructure.t.truncLT (q + 1)).map (Q.map f) := by
  let t := TStructure.t (C := C)
  have : t.IsLE (Q.obj (cochainTruncLE K q)) (q + 1 - 1) := by
    simp only [add_sub_cancel_right]
    apply (isLE_ι_obj_iff _ q).1
    exact DerivedCategory.TStructure.t.isLE_of_iso
      ((quotientCompQhIso C).app (K.obj.truncLE q)).symm q
  apply t.to_truncLT_obj_ext
  rw [Category.assoc, cochainTruncLEQIso_hom_ι, Category.assoc,
    (t.truncLTι (q + 1)).naturality, ← Category.assoc,
    cochainTruncLEQIso_hom_ι, Functor.id_map, ← Q.map_comp, ← Q.map_comp]
  apply congrArg Q.map
  apply ObjectProperty.hom_ext
  exact CochainComplex.ιTruncLE_naturality f.hom q

/-- The bounded-below comparison also commutes with maps between cutoffs. -/
@[reassoc]
theorem cochainTruncLEQIso_of_le (K : CochainComplex.Plus C) (q r : ℤ) (h : q ≤ r)
    (u : cochainTruncLE K q ⟶ cochainTruncLE K r)
    (hu : u ≫ cochainTruncLEι K r = cochainTruncLEι K q) :
    Q.map u ≫ (cochainTruncLEQIso K r).hom =
      (cochainTruncLEQIso K q).hom ≫
        (TStructure.t.natTransTruncLTOfLE (q + 1) (r + 1) (by omega)).app (Q.obj K) := by
  let t := TStructure.t (C := C)
  have : t.IsLE (Q.obj (cochainTruncLE K q)) q := by
    apply (isLE_ι_obj_iff _ q).1
    exact DerivedCategory.TStructure.t.isLE_of_iso
      ((quotientCompQhIso C).app (K.obj.truncLE q)).symm q
  have : t.IsLE (Q.obj (cochainTruncLE K q)) (r + 1 - 1) := by
    simp only [add_sub_cancel_right]
    exact t.isLE_of_le _ q r h
  apply t.to_truncLT_obj_ext
  rw [Category.assoc, cochainTruncLEQIso_hom_ι, Category.assoc,
    t.natTransTruncLTOfLE_ι_app, cochainTruncLEQIso_hom_ι, ← Q.map_comp, hu]

section PlusCutoff

omit [HasDerivedCategory C]

/-- The actual bounded-below map between two upper cutoff complexes. -/
noncomputable def cochainTruncLECutoffMap (K : CochainComplex.Plus C)
    {q r : ℤ} (h : q ≤ r) : cochainTruncLE K q ⟶ cochainTruncLE K r :=
  ObjectProperty.homMk (truncLECutoffMap K.obj h)

@[reassoc]
theorem cochainTruncLECutoffMap_ι (K : CochainComplex.Plus C) {q r : ℤ} (h : q ≤ r) :
    cochainTruncLECutoffMap K h ≫ cochainTruncLEι K r = cochainTruncLEι K q := by
  apply ObjectProperty.hom_ext
  exact truncLECutoffMap_ι K.obj h

/-- The entire finite-cutoff cochain tower, with upper bound q at index q. -/
noncomputable def cochainTruncationTower (K : CochainComplex.Plus C) :
    ℤ ⥤ CochainComplex.Plus C where
  obj q := cochainTruncLE K q
  map f := cochainTruncLECutoffMap K (leOfHom f)
  map_id q := by
    apply ObjectProperty.hom_ext
    change truncLECutoffMap K.obj (le_refl q) = 𝟙 _
    have : Mono (K.obj.ιTruncLE q) :=
      inferInstanceAs (Mono (HomologicalComplex.ιTruncLE K.obj
        (ComplexShape.embeddingUpIntLE q)))
    apply (cancel_mono (K.obj.ιTruncLE q)).1
    rw [truncLECutoffMap_ι, Category.id_comp]
  map_comp {q r s} f g := by
    apply ObjectProperty.hom_ext
    change truncLECutoffMap K.obj ((leOfHom f).trans (leOfHom g)) =
      truncLECutoffMap K.obj (leOfHom f) ≫ truncLECutoffMap K.obj (leOfHom g)
    have : Mono (K.obj.ιTruncLE s) :=
      inferInstanceAs (Mono (HomologicalComplex.ιTruncLE K.obj
        (ComplexShape.embeddingUpIntLE s)))
    apply (cancel_mono (K.obj.ιTruncLE s)).1
    rw [truncLECutoffMap_ι, Category.assoc, truncLECutoffMap_ι, truncLECutoffMap_ι]

/-- A bounded-below complex map restricts to a natural map on its entire cutoff tower. -/
noncomputable def cochainTruncationTowerMap {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    cochainTruncationTower K ⟶ cochainTruncationTower L where
  app q := cochainTruncLEMap f q
  naturality q r g := by
    apply ObjectProperty.hom_ext
    exact truncLECutoffMap_naturality f.hom (leOfHom g)

end PlusCutoff

/-- The canonical derived tower with upper bound q at index q. -/
noncomputable def derivedTruncationTower (X : Plus C) : ℤ ⥤ Plus C where
  obj q := (TStructure.t.truncLT (q + 1)).obj X
  map {q r} f :=
    (TStructure.t.natTransTruncLTOfLE (q + 1) (r + 1) (by
      have := leOfHom f
      omega)).app X
  map_id q := TStructure.t.natTransTruncLTOfLE_refl_app (q + 1) X
  map_comp {q r s} f g :=
    (TStructure.t.natTransTruncLTOfLE_trans_app (q + 1) (r + 1) (s + 1) _ _ X).symm

/-- A derived map acts naturally on the canonical cutoff towers. -/
noncomputable def derivedTruncationTowerMap {X Y : Plus C} (f : X ⟶ Y) :
    derivedTruncationTower X ⟶ derivedTruncationTower Y where
  app q := (TStructure.t.truncLT (q + 1)).map f
  naturality q r g :=
    (TStructure.t.natTransTruncLTOfLE (q + 1) (r + 1) (by
      have := leOfHom g
      omega)).naturality f |>.symm

/-- Localization identifies the whole upper-truncation tower with its derived
counterpart, through the normalized cutoff comparisons.
Source: Stacks Project, Tag 0118
(blueprint: lem-sp-derived-upper-truncation-comparison).

Proof. Use the normalized comparison at every cutoff. Its proved compatibility
with any inclusion between cutoffs gives naturality for every tower arrow. -/
noncomputable def cochainTruncationTowerQIso (K : CochainComplex.Plus C) :
    cochainTruncationTower K ⋙ Q ≅ derivedTruncationTower (Q.obj K) :=
  NatIso.ofComponents (fun q ↦ cochainTruncLEQIso K q) (fun {q r} f ↦
    cochainTruncLEQIso_of_le K q r (leOfHom f) _ (cochainTruncLECutoffMap_ι K _))

/-- The comparison of whole truncation towers commutes with every complex map. -/
@[reassoc]
theorem cochainTruncationTowerQIso_naturality {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    Functor.whiskerRight (cochainTruncationTowerMap f) Q ≫
        (cochainTruncationTowerQIso L).hom =
      (cochainTruncationTowerQIso K).hom ≫ derivedTruncationTowerMap (Q.map f) := by
  apply NatTrans.ext
  funext q
  exact cochainTruncLEQIso_naturality f q

end Plus

end DerivedCategory
