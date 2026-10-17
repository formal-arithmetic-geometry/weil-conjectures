/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import WeilConjectures.CategoryTheory.Triangulated.HomologicalFilteredColimit

/-!
# Continuity of homological functors on bounded-below colimits in derived categories

Let `H : D(𝒜) ⥤ A` be a homological functor on the derived category of an abelian category,
with values in an abelian category in which colimits of shape `I` are exact, such that
`H_n(X) = 0` for `X ∈ D^{≥ n+1}`. For a cocone `s` in `D(𝒜)` over objects of `D^{≥ b}`, whose
cohomology objects form colimits (`DerivedCategory.IsHomologyContinuousOn`), `H` is
continuous on `s` (`DerivedCategory.isContinuousOn_of_isGE`) as soon as it is continuous on such
cocones concentrated in a single degree. The proof is by induction on the truncations
`τ^{≤ m}`: the triangles `τ^{≤ m} X ⟶ τ^{≤ m+1} X ⟶ τ^{≥ m+1} τ^{≤ m+1} X ⟶` are functorial, and
continuity on two vertices gives continuity on the third
(`CategoryTheory.Functor.IsContinuousOn.of_triangle₂`); finally `H_n(τ^{≤ n} X) ≅ H_n(X)`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

open TStructure

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-- `H^q(τ^{≤ m} X) ⟶ H^q(X)` is an isomorphism for `q ≤ m`. -/
lemma isIso_homologyMap_truncLEι (m q : ℤ) (hq : q ≤ m) (X : DerivedCategory 𝒜) :
    IsIso ((homologyFunctor 𝒜 q).map ((t.truncLEι m).app X)) := by
  have hT := t.triangleLEGT_distinguished m X
  have h3 (r : ℤ) (hr : r ≤ m) :
      IsZero ((homologyFunctor 𝒜 r).obj ((t.truncGT m).obj X)) :=
    isZero_of_isGE _ (m + 1) r (by omega)
  have hm : Mono ((homologyFunctor 𝒜 q).map ((t.truncLEι m).app X)) :=
    (HomologySequence.mono_homologyMap_mor₁_iff _ hT (q - 1) q (by omega)).2
      ((h3 (q - 1) (by omega)).eq_of_src _ _)
  have he : Epi ((homologyFunctor 𝒜 q).map ((t.truncLEι m).app X)) :=
    (HomologySequence.epi_homologyMap_mor₁_iff _ hT q).2 ((h3 q hq).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- `H^q(X) ⟶ H^q(τ^{≥ m} X)` is an isomorphism for `m ≤ q`. -/
lemma isIso_homologyMap_truncGEπ (m q : ℤ) (hq : m ≤ q) (X : DerivedCategory 𝒜) :
    IsIso ((homologyFunctor 𝒜 q).map ((t.truncGEπ m).app X)) := by
  have hT := t.triangleLEGE_distinguished (m - 1) m (by omega) X
  have h1 (r : ℤ) (hr : m ≤ r) :
      IsZero ((homologyFunctor 𝒜 r).obj ((t.truncLE (m - 1)).obj X)) :=
    isZero_of_isLE _ (m - 1) r (by omega)
  have hm : Mono ((homologyFunctor 𝒜 q).map ((t.truncGEπ m).app X)) :=
    (HomologySequence.mono_homologyMap_mor₂_iff _ hT q).2 ((h1 q hq).eq_of_src _ _)
  have he : Epi ((homologyFunctor 𝒜 q).map ((t.truncGEπ m).app X)) :=
    (HomologySequence.epi_homologyMap_mor₂_iff _ hT q (q + 1) rfl).2
      ((h1 (q + 1) (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

variable {I : Type*} [Category I] [HasColimitsOfShape I 𝒜]

/-- The cohomology objects of a cocone `s` in `D(𝒜)` form colimits: for every `q`,
`colim_i H^q(G i) ⟶ H^q(s.pt)` is an isomorphism. -/
abbrev IsHomologyContinuousOn {G : I ⥤ DerivedCategory 𝒜} (s : Cocone G) : Prop :=
  (homologyFunctor 𝒜 0).IsContinuousOn s

section Transport

variable {A : Type*} [Category A] [HasColimitsOfShape I A]

/-- Transport of the comparison map along an isomorphism of diagrams and cocones. -/
lemma isIso_colimitDesc_iff_of_iso' {F₁ F₂ : I ⥤ A} (α : F₁ ≅ F₂) {c₁ : Cocone F₁}
    {c₂ : Cocone F₂} (β : c₁.pt ≅ c₂.pt) (hβ : ∀ i, c₁.ι.app i ≫ β.hom = α.hom.app i ≫ c₂.ι.app i) :
    IsIso (colimit.desc F₁ c₁) ↔ IsIso (colimit.desc F₂ c₂) := by
  have h : colimit.desc F₁ c₁ =
      (HasColimit.isoOfNatIso α).hom ≫ colimit.desc F₂ c₂ ≫ β.inv := by
    apply colimit.hom_ext
    intro i
    simp only [colimit.ι_desc, HasColimit.isoOfNatIso_ι_hom_assoc, colimit.ι_desc_assoc]
    rw [← Category.assoc, ← hβ, Category.assoc, β.hom_inv_id]
    exact (Category.comp_id _).symm
  rw [h]
  constructor
  · intro _
    have : IsIso (colimit.desc F₂ c₂ ≫ β.inv) :=
      IsIso.of_isIso_comp_left (HasColimit.isoOfNatIso α).hom _
    exact IsIso.of_isIso_comp_right _ β.inv
  · intro _
    infer_instance

lemma isIso_colimitDesc_of_isZero [Abelian A] {F : I ⥤ A} (c : Cocone F)
    (hF : ∀ i, IsZero (F.obj i)) (hc : IsZero c.pt) : IsIso (colimit.desc F c) := by
  have hz : IsZero (colimit F) := (IsZero.iff_id_eq_zero _).2
    (colimit.hom_ext fun i ↦ (hF i).eq_of_src _ _)
  exact isIso_of_source_target_iso_zero _ hz.isoZero hc.isoZero

end Transport

/-- Truncation `τ^{≤ m}` preserves the continuity of cohomology. -/
lemma IsHomologyContinuousOn.truncLE {G : I ⥤ DerivedCategory 𝒜} {s : Cocone G}
    (hs : IsHomologyContinuousOn s) (m : ℤ) : IsHomologyContinuousOn ((t.truncLE m).mapCocone s) := by
  intro q
  change IsIso (colimit.desc ((G ⋙ t.truncLE m) ⋙ homologyFunctor 𝒜 q)
    ((homologyFunctor 𝒜 q).mapCocone ((t.truncLE m).mapCocone s)))
  by_cases hq : q ≤ m
  · have h (X : DerivedCategory 𝒜) := isIso_homologyMap_truncLEι m q hq X
    refine (isIso_colimitDesc_iff_of_iso' (I := I) (F₁ := (G ⋙ t.truncLE m) ⋙ homologyFunctor 𝒜 q)
      (F₂ := G ⋙ homologyFunctor 𝒜 q)
      (c₁ := (homologyFunctor 𝒜 q).mapCocone ((t.truncLE m).mapCocone s))
      (c₂ := (homologyFunctor 𝒜 q).mapCocone s)
      (NatIso.ofComponents (fun i ↦ asIso ((homologyFunctor 𝒜 q).map ((t.truncLEι m).app
        (G.obj i)))) (fun f ↦ by
          simp only [Functor.comp_obj, Functor.comp_map, asIso_hom, ← Functor.map_comp]
          congr 1
          exact (t.truncLEι m).naturality (G.map f)))
      (asIso ((homologyFunctor 𝒜 q).map ((t.truncLEι m).app s.pt))) (fun i ↦ ?_)).2 (hs q)
    simp only [Functor.mapCocone_ι_app, asIso_hom, NatIso.ofComponents_hom_app,
      ← Functor.map_comp]
    congr 1
    exact (t.truncLEι m).naturality (s.ι.app i)
  · exact isIso_colimitDesc_of_isZero _
      (fun i ↦ isZero_of_isLE ((t.truncLE m).obj (G.obj i)) m q (by omega))
      (isZero_of_isLE ((t.truncLE m).obj s.pt) m q (by omega))

/-- Truncation `τ^{≥ m}` preserves the continuity of cohomology. -/
lemma IsHomologyContinuousOn.truncGE {G : I ⥤ DerivedCategory 𝒜} {s : Cocone G}
    (hs : IsHomologyContinuousOn s) (m : ℤ) : IsHomologyContinuousOn ((t.truncGE m).mapCocone s) := by
  intro q
  change IsIso (colimit.desc ((G ⋙ t.truncGE m) ⋙ homologyFunctor 𝒜 q)
    ((homologyFunctor 𝒜 q).mapCocone ((t.truncGE m).mapCocone s)))
  by_cases hq : m ≤ q
  · have h (X : DerivedCategory 𝒜) := isIso_homologyMap_truncGEπ m q hq X
    refine (isIso_colimitDesc_iff_of_iso' (I := I) (F₁ := (G ⋙ t.truncGE m) ⋙ homologyFunctor 𝒜 q)
      (F₂ := G ⋙ homologyFunctor 𝒜 q)
      (c₁ := (homologyFunctor 𝒜 q).mapCocone ((t.truncGE m).mapCocone s))
      (c₂ := (homologyFunctor 𝒜 q).mapCocone s)
      (NatIso.ofComponents (F := G ⋙ homologyFunctor 𝒜 q)
        (G := (G ⋙ t.truncGE m) ⋙ homologyFunctor 𝒜 q)
        (fun i ↦ asIso ((homologyFunctor 𝒜 q).map ((t.truncGEπ m).app
        (G.obj i)))) (fun f ↦ by
          simp only [Functor.comp_obj, Functor.comp_map, asIso_hom, ← Functor.map_comp]
          congr 1
          exact (t.truncGEπ m).naturality (G.map f))).symm
      (asIso ((homologyFunctor 𝒜 q).map ((t.truncGEπ m).app s.pt))).symm (fun i ↦ ?_)).2 (hs q)
    simp only [Functor.mapCocone_ι_app, Iso.symm_hom, asIso_inv, NatIso.ofComponents_inv_app,
      IsIso.eq_inv_comp, ← Functor.map_comp_assoc, IsIso.comp_inv_eq]
    simp only [← Functor.map_comp]
    congr 1
    exact ((t.truncGEπ m).naturality (s.ι.app i)).symm
  · exact isIso_colimitDesc_of_isZero _
      (fun i ↦ isZero_of_isGE ((t.truncGE m).obj (G.obj i)) m q (by omega))
      (isZero_of_isGE ((t.truncGE m).obj s.pt) m q (by omega))

section Induction

variable {A : Type*} [Category A] [Abelian A] [HasColimitsOfShape I A]
  [HasExactColimitsOfShape I A] (H : DerivedCategory 𝒜 ⥤ A) [H.IsHomological]
  [H.ShiftSequence ℤ]

omit [HasColimitsOfShape I 𝒜] [HasColimitsOfShape I A] [HasExactColimitsOfShape I A] in
lemma isZero_shift_obj_of_isZero {X : DerivedCategory 𝒜} (hX : IsZero X) (n : ℤ) :
    IsZero ((H.shift n).obj X) :=
  (H.map_isZero ((shiftFunctor _ n).map_isZero hX)).of_iso ((H.isoShift n).app X).symm

variable {H}

omit [HasColimitsOfShape I 𝒜] [HasColimitsOfShape I A] [HasExactColimitsOfShape I A] in
/-- If `H_n` vanishes on `D^{≥ n+1}`, then `H_n(τ^{≤ n} X) ⟶ H_n(X)` is an isomorphism. -/
lemma isIso_shift_map_truncLEι
    (hvan : ∀ (n : ℤ) (X : DerivedCategory 𝒜), X.IsGE (n + 1) → IsZero ((H.shift n).obj X))
    (n : ℤ) (X : DerivedCategory 𝒜) : IsIso ((H.shift n).map ((t.truncLEι n).app X)) := by
  have hT := t.triangleLEGT_distinguished n X
  have h3 (r : ℤ) (hr : r ≤ n) : IsZero ((H.shift r).obj ((t.truncGT n).obj X)) :=
    hvan r _ (t.isGE_of_ge _ (r + 1) (n + 1) (by omega))
  have hm : Mono ((H.shift n).map ((t.truncLEι n).app X)) :=
    (H.homologySequence_mono_shift_map_mor₁_iff _ hT (n - 1) n (by omega)).2
      ((h3 (n - 1) (by omega)).eq_of_src _ _)
  have he : Epi ((H.shift n).map ((t.truncLEι n).app X)) :=
    (H.homologySequence_epi_shift_map_mor₁_iff _ hT n).2 ((h3 n le_rfl).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- **Continuity on bounded-below colimits.** Let `H` be a homological functor with `H_n = 0` on
`D^{≥ n+1}`, continuous on cocones concentrated in a single degree whose cohomology objects form
colimits. Then `H` is continuous on every cocone of objects of `D^{≥ b}` whose cohomology objects
form colimits. -/
theorem isContinuousOn_of_isGE
    (hvan : ∀ (n : ℤ) (X : DerivedCategory 𝒜), X.IsGE (n + 1) → IsZero ((H.shift n).obj X))
    (hbase : ∀ (m : ℤ) {G : I ⥤ DerivedCategory 𝒜} (s : Cocone G), (∀ i, (G.obj i).IsGE m) →
      (∀ i, (G.obj i).IsLE m) → s.pt.IsGE m → s.pt.IsLE m → IsHomologyContinuousOn s →
        H.IsContinuousOn s)
    (b : ℤ) {G : I ⥤ DerivedCategory 𝒜} (s : Cocone G) (hG : ∀ i, (G.obj i).IsGE b)
    (hpt : s.pt.IsGE b) (hs : IsHomologyContinuousOn s) : H.IsContinuousOn s := by
  have key (m : ℤ) (hm : b - 1 ≤ m) : ∀ {G : I ⥤ DerivedCategory 𝒜} (s : Cocone G),
      (∀ i, (G.obj i).IsGE b) → (∀ i, (G.obj i).IsLE m) → s.pt.IsGE b → s.pt.IsLE m →
        IsHomologyContinuousOn s → H.IsContinuousOn s := by
    induction m, hm using Int.le_induction with
    | base =>
      intro G s hG hG' hpt hpt' _ n
      have hz (X : DerivedCategory 𝒜) (h₁ : X.IsGE b) (h₂ : X.IsLE (b - 1)) : IsZero X :=
        t.isZero X (b - 1) b (by omega)
      exact isIso_colimitDesc_of_isZero _
        (fun i ↦ isZero_shift_obj_of_isZero H (hz _ (hG i) (hG' i)) n)
        (isZero_shift_obj_of_isZero H (hz _ hpt hpt') n)
    | succ m hm ih =>
      intro G s hG hG' hpt hpt' hs
      have h₁ : H.IsContinuousOn ((t.truncLE m).mapCocone s) :=
        ih ((t.truncLE m).mapCocone s) (fun i ↦ by haveI := hG i; dsimp; infer_instance)
          (fun i ↦ by dsimp; infer_instance) (by haveI := hpt; dsimp; infer_instance)
          (by dsimp; infer_instance) (hs.truncLE m)
      have h₃ : H.IsContinuousOn ((t.truncGE (m + 1)).mapCocone s) :=
        hbase (m + 1) ((t.truncGE (m + 1)).mapCocone s) (fun i ↦ by dsimp; infer_instance)
          (fun i ↦ by haveI := hG' i; dsimp; infer_instance) (by dsimp; infer_instance)
          (by haveI := hpt'; dsimp; infer_instance) (hs.truncGE (m + 1))
      exact Functor.IsContinuousOn.of_triangle₂ (G ⋙ t.triangleLEGE m (m + 1) rfl)
        (fun i ↦ t.triangleLEGE_distinguished m (m + 1) rfl _)
        ((t.triangleLEGE m (m + 1) rfl).mapCocone s)
        (t.triangleLEGE_distinguished m (m + 1) rfl _) h₁ h₃
  intro n
  by_cases hn : n + 1 ≤ b
  · exact isIso_colimitDesc_of_isZero _
      (fun i ↦ hvan n _ (by haveI := hG i; exact t.isGE_of_ge _ (n + 1) b hn))
      (hvan n _ (by haveI := hpt; exact t.isGE_of_ge _ (n + 1) b hn))
  · have h := key n (by omega) ((t.truncLE n).mapCocone s)
      (fun i ↦ by haveI := hG i; dsimp; infer_instance) (fun i ↦ by dsimp; infer_instance)
      (by haveI := hpt; dsimp; infer_instance) (by dsimp; infer_instance) (hs.truncLE n) n
    have hι (X : DerivedCategory 𝒜) := isIso_shift_map_truncLEι hvan n X
    refine (isIso_colimitDesc_iff_of_iso' (I := I) (F₁ := (G ⋙ t.truncLE n) ⋙ H.shift n)
      (F₂ := G ⋙ H.shift n)
      (c₁ := (H.shift n).mapCocone ((t.truncLE n).mapCocone s))
      (c₂ := (H.shift n).mapCocone s)
      (NatIso.ofComponents (fun i ↦ asIso ((H.shift n).map ((t.truncLEι n).app (G.obj i))))
        (fun f ↦ by
          simp only [Functor.comp_obj, Functor.comp_map, asIso_hom, ← Functor.map_comp]
          congr 1
          exact (t.truncLEι n).naturality (G.map f)))
      (asIso ((H.shift n).map ((t.truncLEι n).app s.pt))) (fun i ↦ ?_)).1 h
    simp only [Functor.mapCocone_ι_app, asIso_hom, NatIso.ofComponents_hom_app,
      ← Functor.map_comp]
    congr 1
    exact (t.truncLEι n).naturality (s.ι.app i)

section Single

omit [HasColimitsOfShape I 𝒜] in
/-- An object `X` concentrated in degree `m` is isomorphic to `H^m(X)` placed in degree `m`, by an
isomorphism inducing the identity on `H^m`. -/
lemma exists_iso_singleFunctor_obj_homology (m : ℤ) (X : DerivedCategory 𝒜) [X.IsGE m]
    [X.IsLE m] : ∃ e : X ≅ (singleFunctor 𝒜 m).obj ((homologyFunctor 𝒜 m).obj X),
      (homologyFunctor 𝒜 m).map e.hom ≫
        (singleFunctorCompHomologyFunctorIso 𝒜 m).hom.app _ = 𝟙 _ := by
  obtain ⟨Y, ⟨e₀⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE m
  let ε := singleFunctorCompHomologyFunctorIso 𝒜 m
  let α : (homologyFunctor 𝒜 m).obj X ≅ Y := (homologyFunctor 𝒜 m).mapIso e₀ ≪≫ ε.app Y
  refine ⟨e₀ ≪≫ (singleFunctor 𝒜 m).mapIso α.symm, ?_⟩
  have h := ε.hom.naturality α.inv
  dsimp at h
  rw [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  change _ ≫ _ ≫ ε.hom.app _ = _
  rw [h, ← Category.assoc]
  exact α.hom_inv_id

omit [HasColimitsOfShape I 𝒜] in
/-- Morphisms out of an object concentrated in degree `m` into a single complex in degree `m` are
determined by their effect on `H^m`. -/
lemma hom_ext_of_isGE_of_isLE (m : ℤ) {X : DerivedCategory 𝒜} [X.IsGE m] [X.IsLE m] {B : 𝒜}
    {f g : X ⟶ (singleFunctor 𝒜 m).obj B}
    (h : (homologyFunctor 𝒜 m).map f = (homologyFunctor 𝒜 m).map g) : f = g := by
  obtain ⟨e, -⟩ := exists_iso_singleFunctor_obj_homology m X
  have hf : (singleFunctor 𝒜 m ⋙ homologyFunctor 𝒜 m).Faithful :=
    Functor.Faithful.of_iso (singleFunctorCompHomologyFunctorIso 𝒜 m).symm
  rw [← cancel_epi e.inv]
  rw [← (singleFunctor 𝒜 m).map_preimage (e.inv ≫ f),
    ← (singleFunctor 𝒜 m).map_preimage (e.inv ≫ g)]
  congr 1
  apply (singleFunctor 𝒜 m ⋙ homologyFunctor 𝒜 m).map_injective
  simp only [Functor.comp_map, Functor.map_preimage, Functor.map_comp, h]

variable {A : Type*} [Category A] [Abelian A] [HasColimitsOfShape I A]
  [HasExactColimitsOfShape I A] {H : DerivedCategory 𝒜 ⥤ A} [H.IsHomological]
  [H.ShiftSequence ℤ]

/-- Continuity on cocones concentrated in a single degree `m` follows from continuity on the
images under `singleFunctor 𝒜 m` of colimit cocones in `𝒜`. -/
lemma isContinuousOn_of_isGE_of_isLE
    (hsingle : ∀ (m : ℤ) {F : I ⥤ 𝒜} (c : Cocone F), IsColimit c →
      H.IsContinuousOn ((singleFunctor 𝒜 m).mapCocone c))
    (m : ℤ) {G : I ⥤ DerivedCategory 𝒜} (s : Cocone G) (hG : ∀ i, (G.obj i).IsGE m)
    (hG' : ∀ i, (G.obj i).IsLE m) (hpt : s.pt.IsGE m) (hpt' : s.pt.IsLE m)
    (hs : IsHomologyContinuousOn s) : H.IsContinuousOn s := by
  have hc : IsColimit ((homologyFunctor 𝒜 m).mapCocone s) :=
    IsColimit.ofPointIso (colimit.isColimit (G ⋙ homologyFunctor 𝒜 m)) (i := hs m)
  have h₁ := hsingle m _ hc
  let ε := singleFunctorCompHomologyFunctorIso 𝒜 m
  let e (X : DerivedCategory 𝒜) (h₁ : X.IsGE m) (h₂ : X.IsLE m) :=
    (exists_iso_singleFunctor_obj_homology m X).choose
  have he (X : DerivedCategory 𝒜) (h₁ : X.IsGE m) (h₂ : X.IsLE m) :
      (homologyFunctor 𝒜 m).map (e X h₁ h₂).hom ≫ ε.hom.app _ = 𝟙 _ :=
    (exists_iso_singleFunctor_obj_homology m X).choose_spec
  -- compatibility of the isomorphisms `e` with morphisms
  have hcomm {X Y : DerivedCategory 𝒜} (h₁ : X.IsGE m) (h₂ : X.IsLE m) (h₃ : Y.IsGE m)
      (h₄ : Y.IsLE m) (f : X ⟶ Y) :
      f ≫ (e Y h₃ h₄).hom = (e X h₁ h₂).hom ≫ (singleFunctor 𝒜 m).map
        ((homologyFunctor 𝒜 m).map f) := by
    haveI := h₁
    haveI := h₂
    refine hom_ext_of_isGE_of_isLE (X := X) m ?_
    rw [← cancel_mono (ε.hom.app _)]
    have hn := ε.hom.naturality ((homologyFunctor 𝒜 m).map f)
    dsimp at hn
    simp only [Functor.map_comp, Category.assoc]
    rw [he Y h₃ h₄, hn, ← Category.assoc, he X h₁ h₂]
    simp
  intro n
  refine (Functor.isIso_colimitDesc_iff_of_iso
    (NatIso.ofComponents (fun i ↦ e _ (hG i) (hG' i))
      (fun {i j} f ↦ hcomm (hG i) (hG' i) (hG j) (hG' j) _))
    (e _ hpt hpt') (fun i ↦ hcomm (hG i) (hG' i) hpt hpt' _) (H.shift n)).2 (h₁ n)

/-- **Continuity on bounded-below colimits**, with the base case reduced to single complexes. -/
theorem isContinuousOn_of_isGE'
    (hvan : ∀ (n : ℤ) (X : DerivedCategory 𝒜), X.IsGE (n + 1) → IsZero ((H.shift n).obj X))
    (hsingle : ∀ (m : ℤ) {F : I ⥤ 𝒜} (c : Cocone F), IsColimit c →
      H.IsContinuousOn ((singleFunctor 𝒜 m).mapCocone c))
    (b : ℤ) {G : I ⥤ DerivedCategory 𝒜} (s : Cocone G) (hG : ∀ i, (G.obj i).IsGE b)
    (hpt : s.pt.IsGE b) (hs : IsHomologyContinuousOn s) : H.IsContinuousOn s :=
  isContinuousOn_of_isGE hvan
    (fun m _ s hG hG' hpt hpt' hs ↦ isContinuousOn_of_isGE_of_isLE hsingle m s hG hG' hpt hpt' hs)
    b s hG hpt hs

end Single

end Induction

end DerivedCategory
