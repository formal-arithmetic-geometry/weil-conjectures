/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.Algebra.Homology.HomComplexComponents

/-!
# Derived Hom from a bounded-above projective complex

Source: literature/stacks-project/cohomology.tex, Tag 0GM8, case (2), together with
Tag 06XR (blueprint: lem-sc-affine-projective-complex-derived-hom).

The ring is a commutative ring with identity, as in the Stacks conventions.
Modules are encoded on the one-point site using the shared `onePointRingSheaf`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

attribute [local irreducible] homComplexFunctor derivedInternalHom

namespace SheafOfModules

variable [pointCompose : (⊥ : GrothendieckTopology (Discrete PUnit.{u + 1})).HasSheafCompose
  (forget₂ CommRingCat.{u} RingCat.{u})]

private abbrev point : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨PUnit.unit⟩

omit pointCompose in
private lemma point_unique (X : (Discrete PUnit.{u + 1})ᵒᵖ) : X = point :=
  Subsingleton.elim _ _

/-- On the bottom topology every presheaf is already a sheaf. -/
private noncomputable def bottomEquivalence
    {C : Type u} [SmallCategory C] (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{u}) :
    SheafOfModules.{u} R ≌ PresheafOfModules.{u} R.obj where
  functor := forget R
  inverse :=
    { obj := fun N => ⟨N, Presheaf.isSheaf_bot _⟩
      map := fun f => ⟨f⟩ }
  unitIso := NatIso.ofComponents (fun _ =>
    { hom := ⟨𝟙 _⟩
      inv := ⟨𝟙 _⟩ })
  counitIso := Iso.refl _

/-- Extend a linear map at the sole object to a morphism of presheaves. -/
private noncomputable def pointPreimage
    {A : Type u} [CommRing A]
    {M N : PresheafOfModules.{u}
      (((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)).obj)}
    (f : M.obj point ⟶ N.obj point) : M ⟶ N where
  app X := by
    obtain rfl := point_unique X
    exact f
  naturality {X Y} g := by
    obtain rfl := point_unique X
    obtain rfl := point_unique Y
    have hg : g = 𝟙 point := Subsingleton.elim _ _
    subst g
    ext x
    simp

omit pointCompose in
/-- The singleton discrete category has a singleton slice as well. -/
private lemma slice_unique (U : Discrete PUnit.{u + 1})
    (W : Over U) : W = Over.mk (𝟙 U) := by
  cases U with
  | mk U =>
    cases U
    cases W
    aesop

private lemma point_hom_ext
    {A : Type u} [CommRing A]
    {M N : PresheafOfModules.{u}
      (((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)).obj)}
    {f g : M ⟶ N} (h : f.app point = g.app point) : f = g := by
  apply PresheafOfModules.hom_ext
  intro X
  obtain rfl := point_unique X
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Internal Hom acts on its point value by postcomposition on the slice. -/
private lemma homPointMap_apply
    {A : Type u} [CommRing A]
    (M N N' : SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)))
    (g : N ⟶ N') (φ : (homObj (R := CochainComplex.onePointRingSheaf A) M N).val.obj
      point) :
    ((homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) g).val.app point).hom
      φ = φ ≫ (PresheafOfModules.restrictOver
        (CochainComplex.onePointRingSheaf A).obj point.unop).map g.val := by
  change (PresheafOfModules.restrictOver _ _).map (𝟙 M.val) ≫ φ ≫
    (PresheafOfModules.restrictOver _ _).map g.val = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Internal Hom from a projective module on the one-object bottom-topology site
preserves short exact sequences. No finite-generation assumption is needed.
Source: Stacks Project, more-algebra.tex, Tag 0A6A, projective Hom computation;
algebra.tex, projective modules and exactness of Hom.
(blueprint: lem-pc-ring-projective-internal-hom-exact).

Proof: evaluation at the unique object identifies sheaves of modules on this site
with modules over A: there are only identity restriction maps, and the bottom topology
imposes no additional condition. The slice over the unique object is again this site,
so evaluation of the shared internal Hom is Hom_A(M(*),N(*)), with homObjMap acting
by pre- and postcomposition. A short exact sequence evaluates to a short exact
sequence of A-modules. Hom_A(M(*),-) preserves kernels, giving injectivity and
exactness at the middle term. Extend a map at the point to a sheaf morphism.
Projectivity of M lifts it through the original epimorphism S.g. Restricting this
lift to the point gives surjectivity. The composite
is zero since the original composite is zero. Evaluation reflects these three
properties, so the internal-Hom sequence is short exact. This also covers the zero
ring, the zero source, and projectives of infinite rank. -/
private theorem pointProjectiveInternalHomExact {A : Type u} [CommRing A]
    (M : SheafOfModules.{u} ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf A)))
    [Projective M]
    (S : ShortComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)))) (hS : S.ShortExact) :
    ∃ hz : homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.f ≫
        homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.g = 0,
      (ShortComplex.mk
        (homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.f)
        (homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.g) hz).ShortExact := by
  let R := (sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (CochainComplex.onePointRingSheaf A)
  have : (forget R).IsEquivalence := (bottomEquivalence R).isEquivalence_functor
  let E := evaluation R point
  have : E.Faithful := ⟨fun h => hom_ext (point_hom_ext h)⟩
  have : PreservesFiniteColimits (forget R) := inferInstance
  have : PreservesFiniteColimits E :=
    inferInstanceAs (PreservesFiniteColimits
      (forget R ⋙ PresheafOfModules.evaluation R.obj point))
  have : Epi S.g := hS.epi_g
  have hs := hS.map_of_exact E
  have : Mono (S.map E).f := hs.mono_f
  have : Epi (S.map E).g := hs.epi_g
  have : Mono (E.map S.f) := hs.mono_f
  have : Epi (E.map S.g) := hs.epi_g
  have hz : homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.f ≫
      homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.g = 0 := by
    rw [homObjMap_comp_homObjMap (R := CochainComplex.onePointRingSheaf A),
      Category.id_comp, S.zero]
    apply hom_ext
    ext X φ : 3
    rfl
  let T := ShortComplex.mk
    (homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.f)
    (homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.g) hz
  have ht : (T.map E).ShortExact := by
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.moduleCat_exact_iff]
      intro φ hφ
      let p : M.val.obj point ⟶ S.X₂.val.obj point :=
        φ.app (op (Over.mk (𝟙 point.unop)))
      change ((homObjMap (R := CochainComplex.onePointRingSheaf A)
        (𝟙 M) S.g).val.app point).hom φ = 0 at hφ
      rw [homPointMap_apply] at hφ
      have hp : p ≫ E.map S.g = 0 := by
        exact congrArg (fun ψ => ψ.app (op (Over.mk (𝟙 point.unop)))) hφ
      let q := hs.exact.lift p hp
      refine ⟨(PresheafOfModules.restrictOver
        (CochainComplex.onePointRingSheaf A).obj point.unop).map (pointPreimage q), ?_⟩
      change ((homObjMap (R := CochainComplex.onePointRingSheaf A)
        (𝟙 M) S.f).val.app point).hom _ = φ
      rw [homPointMap_apply]
      apply PresheafOfModules.hom_ext
      intro W
      obtain ⟨W⟩ := W
      obtain rfl := slice_unique point.unop W
      change q ≫ S.f.val.app point = p
      exact hs.exact.lift_f p hp
    · rw [ModuleCat.mono_iff_injective]
      intro φ ψ h
      apply PresheafOfModules.hom_ext
      intro W
      obtain ⟨W⟩ := W
      obtain rfl := slice_unique point.unop W
      apply (cancel_mono (E.map S.f)).1
      change ((homObjMap (R := CochainComplex.onePointRingSheaf A)
        (𝟙 M) S.f).val.app point).hom φ =
        ((homObjMap (R := CochainComplex.onePointRingSheaf A)
          (𝟙 M) S.f).val.app point).hom ψ at h
      rw [homPointMap_apply, homPointMap_apply] at h
      exact congrArg (fun χ => χ.app (op (Over.mk (𝟙 point.unop)))) h
    · rw [ModuleCat.epi_iff_surjective]
      intro φ
      let p : M.val.obj point ⟶ S.X₃.val.obj point :=
        φ.app (op (Over.mk (𝟙 point.unop)))
      let q := Projective.factorThru (show M ⟶ S.X₃ from ⟨pointPreimage p⟩) S.g
      refine ⟨(PresheafOfModules.restrictOver
        (CochainComplex.onePointRingSheaf A).obj point.unop).map q.val, ?_⟩
      change ((homObjMap (R := CochainComplex.onePointRingSheaf A)
        (𝟙 M) S.g).val.app point).hom _ = φ
      rw [homPointMap_apply]
      apply PresheafOfModules.hom_ext
      intro W
      obtain ⟨W⟩ := W
      obtain rfl := slice_unique point.unop W
      change q.val.app point ≫ S.g.val.app point = p
      exact congrArg (fun f : M ⟶ S.X₃ ↦ f.val.app point)
        (Projective.factorThru_comp (show M ⟶ S.X₃ from ⟨pointPreimage p⟩) S.g)
  refine ⟨hz, ?_⟩
  change T.ShortExact
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact (T.exact_map_iff_of_faithful E).1 ht.exact
  · have : Mono (E.map T.f) := ht.mono_f
    exact E.mono_of_mono_map inferInstance
  · have : Epi (E.map T.g) := ht.epi_g
    exact E.epi_of_epi_map inferInstance

end SheafOfModules

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {R : Sheaf J CommRingCat.{u}}

private theorem homObjMap_zero_target
    {E M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} :
    SheafOfModules.homObjMap (R := R) (𝟙 E) (0 : M ⟶ N) = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  rfl

private theorem homObjMap_zero_source
    {E F N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} :
    SheafOfModules.homObjMap (R := R) (0 : E ⟶ F) (𝟙 N) = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver R.obj U.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj U.unop).map (𝟙 N : N ⟶ N).val = 0
  ext W x
  change ((φ.app W).hom) (0) = 0
  exact map_zero _

private theorem homObj_zero_target
    (E N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hz : IsZero N) : IsZero (SheafOfModules.homObj (R := R) E N) := by
  rw [IsZero.iff_id_eq_zero,
    ← SheafOfModules.homObjMap_id (R := R) (M := E) (N := N),
    hz.eq_of_tgt (𝟙 N) 0, homObjMap_zero_target]

private theorem homObj_zero_source
    (E N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hz : IsZero E) : IsZero (SheafOfModules.homObj (R := R) E N) := by
  rw [IsZero.iff_id_eq_zero,
    ← SheafOfModules.homObjMap_id (R := R) (M := E) (N := N),
    hz.eq_of_src (𝟙 E) 0, homObjMap_zero_source]

set_option backward.isDefEq.respectTransparency false in
private lemma exact_homObj_of_iso
    {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}}
    {A B : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (e : A ≅ B)
    (S : ShortComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (hB : ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 B) S.f ≫
        SheafOfModules.homObjMap (R := R) (𝟙 B) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 B) S.f)
        (SheafOfModules.homObjMap (R := R) (𝟙 B) S.g) hz).ShortExact) :
    ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 A) S.f ≫
        SheafOfModules.homObjMap (R := R) (𝟙 A) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 A) S.f)
        (SheafOfModules.homObjMap (R := R) (𝟙 A) S.g) hz).ShortExact := by
  obtain ⟨hz, hS⟩ := hB
  have hzA : SheafOfModules.homObjMap (R := R) (𝟙 A) S.f ≫
      SheafOfModules.homObjMap (R := R) (𝟙 A) S.g = 0 := by
    rw [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp, S.zero,
      homObjMap_zero_target]
  refine ⟨hzA, ShortComplex.shortExact_of_iso ?_ hS⟩
  let i (D : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
      SheafOfModules.homObj (R := R) B D ≅ SheafOfModules.homObj (R := R) A D :=
    { hom := SheafOfModules.homObjMap (R := R) e.hom (𝟙 D)
      inv := SheafOfModules.homObjMap (R := R) e.inv (𝟙 D)
      hom_inv_id := by
        rw [SheafOfModules.homObjMap_comp_homObjMap, e.inv_hom_id,
          Category.id_comp, SheafOfModules.homObjMap_id]
      inv_hom_id := by
        rw [SheafOfModules.homObjMap_comp_homObjMap, e.hom_inv_id,
          Category.id_comp, SheafOfModules.homObjMap_id] }
  exact ShortComplex.isoMk (i S.X₁) (i S.X₂) (i S.X₃) (by
    change SheafOfModules.homObjMap (R := R) e.hom (𝟙 S.X₁) ≫
        SheafOfModules.homObjMap (R := R) (𝟙 A) S.f =
      SheafOfModules.homObjMap (R := R) (𝟙 B) S.f ≫
        SheafOfModules.homObjMap (R := R) e.hom (𝟙 S.X₂)
    simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp, Category.comp_id])
    (by
      change SheafOfModules.homObjMap (R := R) e.hom (𝟙 S.X₂) ≫
          SheafOfModules.homObjMap (R := R) (𝟙 A) S.g =
        SheafOfModules.homObjMap (R := R) (𝟙 B) S.g ≫
          SheafOfModules.homObjMap (R := R) e.hom (𝟙 S.X₃)
      simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp,
        Category.comp_id])

private theorem isIso_of_fan_maps
    {A : Type*} [Category A] {X Y : ℤ → A} {T U : A}
    (π : ∀ p, T ⟶ X p) (ρ : ∀ p, U ⟶ Y p)
    (hπ : IsLimit (Fan.mk T π)) (hρ : IsLimit (Fan.mk U ρ))
    (e : ∀ p, X p ⟶ Y p) [∀ p, IsIso (e p)] (f : T ⟶ U)
    (hf : ∀ p, f ≫ ρ p = π p ≫ e p) : IsIso f := by
  let g : U ⟶ T := Fan.IsLimit.lift hπ (fun p ↦ ρ p ≫ inv (e p))
  have hg (p : ℤ) : g ≫ π p = ρ p ≫ inv (e p) := Fan.IsLimit.fac hπ _ p
  have hfg : f ≫ g = 𝟙 T := by
    apply Fan.IsLimit.hom_ext hπ
    intro p
    change (f ≫ g) ≫ π p = 𝟙 T ≫ π p
    rw [Category.assoc, hg, ← Category.assoc, hf]
    simp
  have hgf : g ≫ f = 𝟙 U := by
    apply Fan.IsLimit.hom_ext hρ
    intro p
    change (g ≫ f) ≫ ρ p = 𝟙 U ≫ ρ p
    rw [Category.assoc, hf, ← Category.assoc, hg]
    simp
  exact (Iso.mk f g hfg hgf).isIso_hom

set_option backward.isDefEq.respectTransparency true in
private theorem homComplex_cut_isIso
    (P M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (k a d : ℤ) (hM : ∀ j : ℤ, j < a → IsZero (M.X j)) (hkd : k + d ≤ a) :
    IsIso ((((homComplexFunctor (R := R)).map
      (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)).op).app M).f d) := by
  let : Abelian (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  classical
  let T := P.stupidTrunc (ComplexShape.embeddingUpIntGE k)
  let i := P.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)
  obtain ⟨π, hπ, _, hmap⟩ := homComplex_projections_exists (R := R)
  let e (p : ℤ) := SheafOfModules.homObjMap (R := R) (i.f p) (𝟙 (M.X (p + d)))
  have he (p : ℤ) : IsIso (e p) := by
    by_cases hp : p < k
    · have hz := hM (p + d) (by omega)
      exact (homObj_zero_target (R := R) (P.X p) (M.X (p + d)) hz).isIso
        (homObj_zero_target (R := R) (T.X p) (M.X (p + d)) hz) (e p)
    · obtain ⟨j, hj⟩ := Int.le.dest (show k ≤ p by omega)
      have hj' : (ComplexShape.embeddingUpIntGE k).f j = p := by simpa using hj
      have : IsIso (i.f p) := P.isIso_ιStupidTrunc_f _ hj'
      change IsIso (((SheafOfModules.homFunctor R).flip.obj (M.X (p + d))).map
        (i.f p).op)
      infer_instance
  apply isIso_of_fan_maps (fun p ↦ π P M d p (p + d) rfl)
    (fun p ↦ π T M d p (p + d) rfl) (Classical.choice (hπ P M d))
    (Classical.choice (hπ T M d)) e _
  intro p
  have hm := hmap P T M M i (𝟙 M) d p (p + d) rfl
  simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] using hm

set_option backward.isDefEq.respectTransparency true in
private theorem homComplex_cut_quasiIsoAt
    (P M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (k a n : ℤ) (hM : ∀ j : ℤ, j < a → IsZero (M.X j)) (hkn : k + n + 1 ≤ a) :
    QuasiIsoAt (((homComplexFunctor (R := R)).map
      (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)).op).app M) n := by
  let : Abelian (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  let f := ((homComplexFunctor (R := R)).map
    (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)).op).app M
  have : IsIso (f.f (n - 1)) := homComplex_cut_isIso P M k a _ hM (by omega)
  have : IsIso (f.f n) := homComplex_cut_isIso P M k a _ hM (by omega)
  have : IsIso (f.f (n + 1)) := homComplex_cut_isIso P M k a _ hM (by omega)
  rw [quasiIsoAt_iff' f (n - 1) n (n + 1) (by simp) (by simp)]
  have : IsIso ((HomologicalComplex.shortComplexFunctor' _ (ComplexShape.up ℤ)
      (n - 1) n (n + 1)).map f) := by
    rw [ShortComplex.isIso_iff]
    change IsIso (f.f (n - 1)) ∧ IsIso (f.f n) ∧ IsIso (f.f (n + 1))
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  exact ShortComplex.quasiIso_of_isIso _

set_option backward.isDefEq.respectTransparency true in
private theorem exact_homObj_zero
    (E : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hz : IsZero E)
    (S : ShortComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :
    ∃ h : SheafOfModules.homObjMap (R := R) (𝟙 E) S.f ≫
        SheafOfModules.homObjMap (R := R) (𝟙 E) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 E) S.f)
        (SheafOfModules.homObjMap (R := R) (𝟙 E) S.g) h).ShortExact := by
  let : Abelian (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  have h₁ := homObj_zero_source (R := R) E S.X₁ hz
  have h₂ := homObj_zero_source (R := R) E S.X₂ hz
  have h₃ := homObj_zero_source (R := R) E S.X₃ hz
  exact ⟨h₁.eq_of_src _ _,
    { exact := ShortComplex.exact_of_isZero_X₂ _ h₂
      mono_f := h₁.mono _
      epi_g := h₃.epi _ }⟩

set_option backward.isDefEq.respectTransparency true in
private theorem homComplex_map_boundedBelow
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hP : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hexact : ∀ (p : ℤ) (S : ShortComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))),
      S.ShortExact → ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.f ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.f)
          (SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.g) hz).ShortExact)
    (M N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hM : ∃ a : ℤ, ∀ j : ℤ, j < a → IsZero (M.X j))
    (hN : ∃ a : ℤ, ∀ j : ℤ, j < a → IsZero (N.X j))
    (α : M ⟶ N) [QuasiIso α] :
    QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map α) := by
  let : Abelian (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  obtain ⟨b, hb⟩ := hP
  obtain ⟨aM, haM⟩ := hM
  obtain ⟨aN, haN⟩ := hN
  rw [quasiIso_iff]
  intro n
  let k := min aM aN - n - 1
  let T := P.stupidTrunc (ComplexShape.embeddingUpIntGE k)
  let i := P.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)
  have hT : ∃ a b : ℤ, ∀ p : ℤ, p < a ∨ b < p → IsZero (T.X p) := by
    refine ⟨k, b, ?_⟩
    intro p hp
    by_cases hpk : p < k
    · exact P.isZero_stupidTrunc_X _ p
        ((ComplexShape.notMem_range_embeddingUpIntGE_iff k p).2 hpk)
    · obtain ⟨j, hj⟩ := Int.le.dest (show k ≤ p by omega)
      have hj' : (ComplexShape.embeddingUpIntGE k).f j = p := by simpa using hj
      exact (hb p (by omega)).of_iso (P.stupidTruncXIso _ hj')
  have hTexact : ∀ (p : ℤ) (S : ShortComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))),
      S.ShortExact → ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 (T.X p)) S.f ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (T.X p)) S.g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 (T.X p)) S.f)
          (SheafOfModules.homObjMap (R := R) (𝟙 (T.X p)) S.g) hz).ShortExact := by
    intro p S hS
    by_cases hpk : p < k
    · exact exact_homObj_zero (R := R) _
        (P.isZero_stupidTrunc_X _ p
          ((ComplexShape.notMem_range_embeddingUpIntGE_iff k p).2 hpk)) S
    · obtain ⟨j, hj⟩ := Int.le.dest (show k ≤ p by omega)
      have hj' : (ComplexShape.embeddingUpIntGE k).f j = p := by simpa using hj
      let e := P.stupidTruncXIso _ hj'
      exact exact_homObj_of_iso e S (hexact p S hS)
  have : QuasiIso (((homComplexFunctor (R := R)).obj (op T)).map α) :=
    quasiIso_homComplex_map_of_bounded_exact_terms J R T hT hTexact α
  have : QuasiIsoAt (((homComplexFunctor (R := R)).map i.op).app M) n :=
    homComplex_cut_quasiIsoAt P M k aM n haM (by dsimp [k]; omega)
  have : QuasiIsoAt (((homComplexFunctor (R := R)).map i.op).app N) n :=
    homComplex_cut_quasiIsoAt P N k aN n haN (by dsimp [k]; omega)
  apply (quasiIsoAt_iff_comp_right
    (((homComplexFunctor (R := R)).obj (op P)).map α)
    (((homComplexFunctor (R := R)).map i.op).app N) n).mp
  rw [((homComplexFunctor (R := R)).map i.op).naturality α]
  exact quasiIsoAt_comp _ _ n

set_option backward.isDefEq.respectTransparency true in
private theorem homComplex_map_KInjective
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    {I I' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    [I.IsKInjective] [I'.IsKInjective] (s : I ⟶ I') [QuasiIso s] :
    QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map s) := by
  let : Abelian (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  simpa only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp] using
    quasiIso_homComplex_map (R := R) s (𝟙 P)

set_option backward.isDefEq.respectTransparency true in
/-- A bounded-above complex with exact internal Hom in every degree computes Hom
into any K-injective replacement of a bounded-below complex.

Source: Stacks Project, Cohomology on Sites, Tag 08JI.
(blueprint: lem-weil-pbc-ringed-site-bounded-free-rhom-quasi-iso).

Proof:
1. Assume each term of P has exact internal Hom.
2. For bounded-below targets M,N and a fixed homology degree n, cut P below
   k = min(aM,aN)-n-1. The inclusion of this stupid truncation induces isomorphisms
   of Hom terms in degrees n-1,n,n+1: below k the target terms vanish; at and above
   k the source inclusion is an isomorphism. Thus it preserves degree-n homology.
   The truncated source is bounded and has exact internal Hom in every term, so
   the existing bounded exact-term Hom comparison applies. Naturality and
   two-out-of-three prove the comparison for P in degree n, and hence in all degrees.
3. Choose a bounded-below K-injective resolution of M. Step 2 applies to its map.
   Compare it with the functorial K-injective resolution using its naturality
   square. Hom sends quasi-isomorphisms between K-injective complexes to
   quasi-isomorphisms, so two-out-of-three proves the comparison into the
   functorial resolution. Apply the same naturality square to the given map
   M→I to obtain its Hom comparison, even when I is unbounded below. -/
private theorem exactTermHomReplacement
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hP : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hexact : ∀ (p : ℤ) (S : ShortComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))),
      S.ShortExact → ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.f ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.f)
          (SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.g) hz).ShortExact)
    (I : CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    [I.IsKInjective]
    (M : CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hM : ∃ a : ℤ, ∀ j : ℤ, j < a → IsZero (M.X j))
    (α : M ⟶ I)
    [QuasiIso α] :
    QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map α) := by
  let : Abelian (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  classical
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let H := (homComplexFunctor (R := R)).obj (op P)
  obtain ⟨a, ha⟩ := hM
  have : M.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff M a).2 (fun j hj ↦ ha j hj)
  obtain ⟨T, β, hβ, ⟨b, hT⟩, _, hTK⟩ :=
    SheafOfModules.exists_boundedBelow_injective_resolution J R M ⟨a, inferInstance⟩
  have : T.IsStrictlyGE b := hT
  have : T.IsKInjective := hTK
  have : QuasiIso β := hβ
  have hβ : QuasiIso (H.map β) :=
    homComplex_map_boundedBelow (R := R) P hP hexact M T ⟨a, ha⟩
      ⟨b, fun j hj ↦ T.isZero_of_isStrictlyGE b j hj⟩ β
  let F := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  have hη (X : CochainComplex A ℤ) : QuasiIso (η.app X) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app A X).2
  have hF {X Y : CochainComplex A ℤ} (f : X ⟶ Y) [QuasiIso f] :
      QuasiIso (F.map f) := by
    have := hη X
    have := hη Y
    apply (quasiIso_iff_comp_left (η.app X) (F.map f)).mp
    rw [← η.naturality f]
    change QuasiIso (f ≫ η.app Y)
    exact quasiIso_comp _ _
  have hηT : QuasiIso (H.map (η.app T)) := by
    have := hη T
    exact homComplex_map_KInjective (R := R) P
      (show T ⟶ F.obj T from η.app T)
  have hFβ : QuasiIso (H.map (F.map β)) := by
    have := hF β
    exact homComplex_map_KInjective (R := R) P _
  have hηM : QuasiIso (H.map (η.app M)) := by
    apply (quasiIso_iff_comp_right (H.map (η.app M)) (H.map (F.map β))).mp
    rw [← H.map_comp, ← η.naturality β]
    change QuasiIso (H.map (β ≫ η.app T))
    rw [H.map_comp]
    exact quasiIso_comp _ _
  have hηI : QuasiIso (H.map (η.app I)) := by
    have := hη I
    exact homComplex_map_KInjective (R := R) P (show I ⟶ F.obj I from η.app I)
  have hFα : QuasiIso (H.map (F.map α)) := by
    have := hF α
    exact homComplex_map_KInjective (R := R) P _
  change QuasiIso (H.map α)
  apply (quasiIso_iff_comp_right (H.map α) (H.map (η.app I))).mp
  rw [← H.map_comp]
  have hn : α ≫ η.app I = η.app M ≫ F.map α := η.naturality α
  rw [hn, H.map_comp]
  exact quasiIso_comp _ _


set_option backward.isDefEq.respectTransparency true in
/-- A bounded-above projective complex computes derived Hom into a bounded-below complex:
`Q Hom^•(P, L) ≅ R Hom(P, L)`, the comparison being the image under `Q` of the canonical
map `Hom^•(P, L) → Hom^•(P, I(L))` for any functorial K-injective replacement `L → I(L)`,
and the cohomology of `Hom^•(P, L)` vanishes in all sufficiently negative degrees.

Source: literature/stacks-project/cohomology.tex, Tag 0GM8, case (2), together with
Tag 06XR (blueprint: lem-sc-affine-projective-complex-derived-hom).

Proof:
1. Choose the functorial K-injective resolution `L → I(L)` supplied by
   `def-pur-derived-internal-hom`. The bounded-above projective complex `P` is K-projective
   by `lem-sc-bounded-above-projective-kprojective` (`isKProjective_of_projective`).
2. Applying `Hom(P, -)` to the cone of `L → I(L)` gives an acyclic complex. Hence
   `Hom(P, L) → Hom(P, I(L))` is a quasi-isomorphism and becomes an isomorphism under `Q`.
   By `derivedInternalHom_comparison`, the latter complex represents derived internal Hom.
3. The product terms of `homComplex` (`def-pur-derived-internal-hom`, through
   `def-pur-hom-complex`) are `∏ p, Hom(P^p, L^(p+n))`. A nonzero factor requires
   `p ≤ d` and `e ≤ p+n`, which is impossible when `n < e-d`. Thus the terms, and then
   their cohomology, vanish in all sufficiently negative degrees. -/
theorem affineProjectiveComplexDerivedHom
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf R)))]
    (P L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf R))) ℤ)
    (d e : ℤ)
    [P.IsStrictlyLE d] [L.IsStrictlyGE e]
    [∀ n : ℤ, Projective (P.X n)] :
    Nonempty (DerivedCategory.Q.obj
        (homComplex (R := CochainComplex.onePointRingSheaf R) P L) ≅
      (derivedInternalHom ⊥ (CochainComplex.onePointRingSheaf R)).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L)) ∧
    (∀ (I : CochainComplex (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf R))) ℤ ⥤
        CochainComplex (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf R))) ℤ)
      (η : 𝟭 (CochainComplex (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf R))) ℤ) ⟶ I),
      (∀ N : CochainComplex (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf R))) ℤ,
        QuasiIso (η.app N) ∧ (I.obj N).IsKInjective) →
        IsIso (DerivedCategory.Q.map
          (((homComplexFunctor (R := CochainComplex.onePointRingSheaf R)).obj (op P)).map
            (η.app L)))) ∧
    ∃ a : ℤ, ∀ n : ℤ, n < a →
      IsZero ((homComplex (R := CochainComplex.onePointRingSheaf R) P L).homology n) := by
  let S := CochainComplex.onePointRingSheaf R
  let A := SheafOfModules.{u}
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj S)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  have hP : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i) :=
    ⟨d, fun i hi ↦ P.isZero_of_isStrictlyLE d i hi⟩
  have hL : ∃ a : ℤ, ∀ i : ℤ, i < a → IsZero (L.X i) :=
    ⟨e, fun i hi ↦ L.isZero_of_isStrictlyGE e i hi⟩
  have hexact := fun n T hT ↦
    SheafOfModules.pointProjectiveInternalHomExact (P.X n) T hT
  have hreplacement (I : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
      (η : 𝟭 _ ⟶ I) (hI : ∀ N, QuasiIso (η.app N) ∧ (I.obj N).IsKInjective) :
      IsIso (DerivedCategory.Q.map
        (((homComplexFunctor (R := S)).obj (op P)).map (η.app L))) := by
    have : (I.obj L).IsKInjective := (hI L).2
    have : QuasiIso (η.app L) := (hI L).1
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    exact exactTermHomReplacement ⊥ S P hP hexact (I.obj L) L hL (η.app L)
  refine ⟨?_, hreplacement, ?_⟩
  · let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
    let η := CochainComplex.toKInjectiveResolution.{u} A
    have hI : ∀ N, QuasiIso (η.app N) ∧ (I.obj N).IsKInjective := fun N ↦
      ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A N).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A N⟩
    let f := ((homComplexFunctor (R := S)).obj (op P)).map (η.app L)
    have hf : IsIso (DerivedCategory.Q.{w}.map f) := hreplacement I η hI
    obtain ⟨c⟩ := derivedInternalHom_comparison ⊥ S I η hI
    exact ⟨@asIso _ _ _ _ (DerivedCategory.Q.{w}.map f) hf ≪≫ (c.app (op P, L)).symm⟩
  · refine ⟨e - d, fun n hn ↦ ?_⟩
    have hz : IsZero ((homComplex (R := S) P L).X n) := by
      rw [IsZero.iff_id_eq_zero]
      apply homComplex_hom_ext
      intro p q hpq
      have hfactor : IsZero (SheafOfModules.homObj (R := S) (P.X p) (L.X q)) := by
        by_cases hp : d < p
        · exact homObj_zero_source (R := S) _ _ (P.isZero_of_isStrictlyLE d p hp)
        · exact homObj_zero_target (R := S) _ _ (L.isZero_of_isStrictlyGE e q (by omega))
      exact hfactor.eq_of_tgt _ _
    exact (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology

end CategoryTheory
