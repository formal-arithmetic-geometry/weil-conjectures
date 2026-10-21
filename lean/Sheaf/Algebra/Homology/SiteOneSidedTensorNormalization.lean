/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Normalized one-sided K-flat tensor comparison

Source: Stacks Project, sites-cohomology.tex, Tag 06YU (definition-derived-tor),
the construction preceding the definition and the signed symmetry following it.
(blueprint: lem-trf-site-one-sided-tensor-normalization)

The parameters `P`, `B`, `D` and `δ` unpack the resolving subcategory, homotopy tensor,
derived tensor and specified two-sided comparison of site-derived-tensor descent.
They are supplied as data, so the normalization retains the specified comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory MonoidalCategory
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules

private theorem uncurry_map_left
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    (F : A ⥤ B ⥤ E) {X : A} {Y Z : B} (f : Y ⟶ Z) :
    (Functor.uncurry.obj F).map (X := (X, Y)) (Y := (X, Z)) (𝟙 X, f) = (F.obj X).map f := by
  change (F.map (𝟙 X)).app Y ≫ _ = _
  rw [F.map_id, NatTrans.id_app, Category.id_comp]

private theorem uncurry_map_right
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    (F : A ⥤ B ⥤ E) {X Y : A} {Z : B} (f : X ⟶ Y) :
    (Functor.uncurry.obj F).map (X := (X, Z)) (Y := (Y, Z)) (f, 𝟙 Z) = (F.flip.obj Z).map f := by
  change (F.map f).app Z ≫ (F.obj Y).map (𝟙 Z) = _
  rw [(F.obj Y).map_id, Category.comp_id]
  rfl

private theorem extend_comparison
    {A : Type*} [Category* A] {E : Type*} [Category* E]
    {D₀ : Type*} [Category* D₀]
    (W : MorphismProperty A) (Q : A ⥤ D₀) [Q.IsLocalization W]
    (P : ObjectProperty A) [(P.ι ⋙ Q).IsLocalization (W.inverseImage P.ι)]
    (F : D₀ ⥤ E) (H : A ⥤ E) (hH : W.IsInvertedBy H)
    (e : P.ι ⋙ Q ⋙ F ≅ P.ι ⋙ H) :
    ∃ c : Q ⋙ F ≅ H, ∀ V : P.FullSubcategory, c.app V.obj = e.app V := by
  let H' := Localization.lift H hH Q
  let φ := Localization.fac H hH Q
  let L := P.ι ⋙ Q
  let V := W.inverseImage P.ι
  let b : L ⋙ F ≅ L ⋙ H' := e ≪≫ (Functor.isoWhiskerLeft P.ι φ).symm
  let ff := Localization.fullyFaithfulWhiskeringLeft L V E
  let b' : F ≅ H' := ff.preimageIso b
  refine ⟨Functor.isoWhiskerLeft Q b' ≪≫ φ, ?_⟩
  intro X
  apply Iso.ext
  have hb := congr_app (ff.map_preimage b.hom) X
  change b'.hom.app (Q.obj X.obj) ≫ φ.hom.app X.obj = (e.app X).hom
  rw [show b'.hom.app (Q.obj X.obj) = b.hom.app X from hb]
  simp [b]

private theorem resolving_trans_ext
    {A : Type*} [Category* A] {E : Type*} [Category* E]
    {D₀ : Type*} [Category* D₀]
    (W : MorphismProperty A) (Q : A ⥤ D₀) [Q.IsLocalization W]
    (P : ObjectProperty A)
    (res : ∀ X : A, ∃ (V : P.FullSubcategory) (r : V.obj ⟶ X), W r)
    {F : D₀ ⥤ E} {H : A ⥤ E} (α β : Q ⋙ F ⟶ H)
    (h : ∀ V : P.FullSubcategory, α.app V.obj = β.app V.obj) : α = β := by
  ext X
  obtain ⟨V, r, hr⟩ := res X
  have : IsIso (Q.map r) := Localization.inverts Q W r hr
  apply (cancel_epi (F.map (Q.map r))).1
  change (Q ⋙ F).map r ≫ α.app X = (Q ⋙ F).map r ≫ β.app X
  rw [α.naturality, β.naturality, h V]

set_option backward.isDefEq.respectTransparency false in
/-- The normalized one-sided comparison, in both tensor orders, with uniqueness among
all families natural in the unrestricted argument. The last equations express naturality
in every homotopy-category map of the fixed K-flat argument. `NatIso` includes the first
naturality equation for every map, in particular every flat-term K-flat resolution.
The final conjunct records the signed chain interchange on every direct-sum summand.

Source: Stacks Project, sites-cohomology.tex, Tags 06YM, 06YP, 06YS and the construction
preceding Tag 06YU (definition-derived-tor); Categories, Tag 04VK.
(blueprint: lem-trf-site-one-sided-tensor-normalization)

Proof:
1. Tensor homotopies are h tensor 1 and (-1)^i 1 tensor h; their cross terms cancel.
   The signed interchange (-1)^(ij) commutes with the differential and squares to one.
   Balanced maps descend to sheafification, summandwise even for unbounded totals.
2. For a quasi-isomorphism f its cone is acyclic (lem-pur-quasi-iso-cone-acyclic).
   K-flatness kills tensor of that cone. Signed interchange and the tensor-cone
   isomorphism (lem-pc-tensor-mapping-cone-iso) imply that both tensor maps are
   quasi-isomorphisms. Every homotopy arrow has a chain representative.
3. By lem-weil-pbc-site-derived-tensor-descent, Q restricted to P is a localization.
   Fix T. The functor H(M)=Q Tot(T tensor M) inverts quasi-isomorphisms by step 2.
   Extend H along Q using clause (1) of lem-weil-pbc-localization-universal-property,
   obtaining Hbar and phi:Hbar Q ≅ H.
4. On P, phi inverse followed by delta inverse gives a natural isomorphism from
   D(QT,-) to Hbar. Extend it and its inverse by clause (2) of that universal
   property. Uniqueness makes the extensions inverse. Compose with phi to get c.
   At V in P the two phi factors cancel, so c(T,V)=delta(T,V) inverse.
5. For every M choose a flat-term K-flat quasi-isomorphism r:V→M by
   lem-pc-kflat-resolution. Naturality forces c(T,M) to be Q(1 tensor r), after
   delta(T,V) inverse, after D(1,Qr) inverse. Both outside maps are invertible.
   Thus every normalized natural family equals c, independently of all choices.
6. For any g:T→T', compare Q(g tensor 1)c(T,-) and c(T',-)D(Qg,1).
   They agree on P by naturality of delta. Naturality at r:V→M and cancellation
   of the invertible D(1,Qr) extends equality to every M, without inverting g.
7. Repeat steps 3–6 with H(M)=Q Tot(M tensor T), normalized by delta(V,T) inverse.
   Naturality at r gives the analogous formula with Q(r tensor 1) and D(Qr,1).
   This proves uniqueness and naturality in both arguments in the reversed order.
   No flatness or boundedness of the arbitrary argument is used.
-/
theorem site_one_sided_tensor_normalization
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (Modules R)]
    (P : ObjectProperty (HomotopyCategory (Modules R) (.up ℤ)))
    (hP : ∀ X, P X ↔ CochainComplex.IsKFlatIndependentCoefficients X.as ∧
      ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (X.as.X n))
    (B : HomotopyCategory (Modules R) (.up ℤ) ⥤
      HomotopyCategory (Modules R) (.up ℤ) ⥤ HomotopyCategory (Modules R) (.up ℤ))
    (hB : Nonempty (((HomotopyCategory.quotient (Modules R) (.up ℤ)).prod
        (HomotopyCategory.quotient (Modules R) (.up ℤ))) ⋙ Functor.uncurry.obj B ≅
      Functor.uncurry.obj (totalTensor R) ⋙ HomotopyCategory.quotient (Modules R) (.up ℤ)))
    (D : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (δ : (P.ι.prod P.ι) ⋙ Functor.uncurry.obj B ⋙ DerivedCategory.Qh ≅
      ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) ⋙ Functor.uncurry.obj D) :
    (∀ (T : P.FullSubcategory)
      (M M' : HomotopyCategory (Modules R) (.up ℤ)) (f : M ⟶ M'),
      HomotopyCategory.quasiIso (Modules R) (.up ℤ) f →
        HomotopyCategory.quasiIso (Modules R) (.up ℤ) ((B.obj T.obj).map f) ∧
        HomotopyCategory.quasiIso (Modules R) (.up ℤ) ((B.flip.obj T.obj).map f)) ∧
    (∃ c : ∀ T : P.FullSubcategory,
        DerivedCategory.Qh ⋙ D.obj (DerivedCategory.Qh.obj T.obj) ≅
          B.obj T.obj ⋙ DerivedCategory.Qh,
      (∀ T V : P.FullSubcategory, (c T).app V.obj = (δ.app (T, V)).symm) ∧
      (∀ c' : ∀ T : P.FullSubcategory,
          DerivedCategory.Qh ⋙ D.obj (DerivedCategory.Qh.obj T.obj) ≅
            B.obj T.obj ⋙ DerivedCategory.Qh,
        (∀ T V : P.FullSubcategory, (c' T).app V.obj = (δ.app (T, V)).symm) → c' = c) ∧
      (∀ (T T' : P.FullSubcategory) (g : T ⟶ T')
        (M : HomotopyCategory (Modules R) (.up ℤ)),
        (c T).hom.app M ≫ DerivedCategory.Qh.map ((B.map g.hom).app M) =
          (D.map (DerivedCategory.Qh.map g.hom)).app (DerivedCategory.Qh.obj M) ≫
            (c T').hom.app M)) ∧
    (∃ c : ∀ T : P.FullSubcategory,
        DerivedCategory.Qh ⋙ D.flip.obj (DerivedCategory.Qh.obj T.obj) ≅
          B.flip.obj T.obj ⋙ DerivedCategory.Qh,
      (∀ T V : P.FullSubcategory, (c T).app V.obj = (δ.app (V, T)).symm) ∧
      (∀ c' : ∀ T : P.FullSubcategory,
          DerivedCategory.Qh ⋙ D.flip.obj (DerivedCategory.Qh.obj T.obj) ≅
            B.flip.obj T.obj ⋙ DerivedCategory.Qh,
        (∀ T V : P.FullSubcategory, (c' T).app V.obj = (δ.app (V, T)).symm) → c' = c) ∧
      (∀ (T T' : P.FullSubcategory) (g : T ⟶ T')
        (M : HomotopyCategory (Modules R) (.up ℤ)),
        (c T).hom.app M ≫ DerivedCategory.Qh.map ((B.flip.map g.hom).app M) =
          (D.flip.map (DerivedCategory.Qh.map g.hom)).app (DerivedCategory.Qh.obj M) ≫
            (c T').hom.app M)) ∧
    (∀ (K L : CochainComplex (Modules R) ℤ) (i j n : ℤ) (h : i + j = n),
      HomologicalComplex.ιTensorObj K L i j n h ≫
          (CochainComplex.Monoidal.braiding K L).hom.f n =
        ((i * j).negOnePow : ℤ) • ((β_ (K.X i) (L.X j)).hom ≫
          HomologicalComplex.ιTensorObj L K j i n (add_comm j i |>.trans h))) := by
  classical
  let A := Modules R
  let Q := HomotopyCategory.quotient A (.up ℤ)
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  have res : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (V : P.FullSubcategory) (r : V.obj ⟶ X), W r := by
    intro X
    obtain ⟨K, f, hK, hflat, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    have hs : ∀ n, IsFlatOnSite (J := J) (R := R) (K.X n) := fun n ↦
      (CategoryTheory.exactFunctor _ _).prop_of_iso
        (siteSheafTensorRightIso R (K.X n)).symm (hflat n)
    exact ⟨⟨Q.obj K, (hP _).2 ⟨hK, hs⟩⟩, Q.map f,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have hloc : (P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory A (.up ℤ) ⥤
      DerivedCategory A)).IsLocalization (W.inverseImage P.ι) := by
    obtain ⟨P₀, hP₀, ⟨F, hF, ⟨e⟩⟩, _⟩ :=
      site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R
    have hp : P₀ = P := funext fun X ↦ propext ((hP₀ X).trans (hP X).symm)
    subst P₀
    let := hF
    exact Functor.IsLocalization.of_iso (W.inverseImage P.ι) e
  let := hloc
  have hpres : ∀ (T : P.FullSubcategory)
      (M M' : HomotopyCategory A (.up ℤ)) (f : M ⟶ M'), W f →
      W ((B.obj T.obj).map f) ∧ W ((B.flip.obj T.obj).map f) := by
    intro T M M' f hf
    obtain ⟨g, hg⟩ := Q.map_surjective f
    have hq : QuasiIso g :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff g).1 (hg ▸ hf)
    obtain ⟨_, ht⟩ := kFlat_fixed_tensor_triangulated R
    have ht' := (ht T.obj.as (hP _ |>.1 T.property).1
      (hP _ |>.1 T.property).2).1 M.as M'.as g hq
    obtain ⟨e⟩ := hB
    constructor
    · have he := (W.arrow_mk_iso_iff (Arrow.isoMk
          (e.app (T.obj.as, M.as)) (e.app (T.obj.as, M'.as))
          (e.hom.naturality (X := (T.obj.as, M.as))
            (Y := (T.obj.as, M'.as)) (𝟙 T.obj.as, g)).symm)).2
          ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (by
            rw [uncurry_map_left]
            exact ht'.1))
      change W ((B.map (Q.map (𝟙 T.obj.as))).app M ≫ (B.obj T.obj).map (Q.map g))
        at he
      rw [Q.map_id, B.map_id, NatTrans.id_app, Category.id_comp, hg] at he
      exact he
    · have he := (W.arrow_mk_iso_iff (Arrow.isoMk
          (e.app (M.as, T.obj.as)) (e.app (M'.as, T.obj.as))
          (e.hom.naturality (X := (M.as, T.obj.as))
            (Y := (M'.as, T.obj.as)) (g, 𝟙 T.obj.as)).symm)).2
          ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (by
            rw [uncurry_map_right]
            exact ht'.2))
      change W ((B.map (Q.map g)).app T.obj ≫ (B.obj M').map (Q.map (𝟙 T.obj.as)))
        at he
      erw [Q.map_id, (B.obj M').map_id, Category.comp_id, hg] at he
      exact he
  have oneOrder
      (B : HomotopyCategory A (.up ℤ) ⥤ HomotopyCategory A (.up ℤ) ⥤
        HomotopyCategory A (.up ℤ))
      (D : DerivedCategory A ⥤ DerivedCategory A ⥤ DerivedCategory A)
      (δ : (P.ι.prod P.ι) ⋙ Functor.uncurry.obj B ⋙ DerivedCategory.Qh ≅
        ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) ⋙
          Functor.uncurry.obj D)
      (hp : ∀ (T : P.FullSubcategory) {M M' : HomotopyCategory A (.up ℤ)}
        (f : M ⟶ M'), W f → W ((B.obj T.obj).map f)) :
    ∃ c : ∀ T : P.FullSubcategory,
        DerivedCategory.Qh ⋙ D.obj (DerivedCategory.Qh.obj T.obj) ≅
          B.obj T.obj ⋙ DerivedCategory.Qh,
      (∀ T V : P.FullSubcategory, (c T).app V.obj = (δ.app (T, V)).symm) ∧
      (∀ c' : ∀ T : P.FullSubcategory,
          DerivedCategory.Qh ⋙ D.obj (DerivedCategory.Qh.obj T.obj) ≅
            B.obj T.obj ⋙ DerivedCategory.Qh,
        (∀ T V : P.FullSubcategory, (c' T).app V.obj = (δ.app (T, V)).symm) → c' = c) ∧
      (∀ (T T' : P.FullSubcategory) (g : T ⟶ T')
        (M : HomotopyCategory (Modules R) (.up ℤ)),
        (c T).hom.app M ≫ DerivedCategory.Qh.map ((B.map g.hom).app M) =
          (D.map (DerivedCategory.Qh.map g.hom)).app (DerivedCategory.Qh.obj M) ≫
            (c T').hom.app M) := by
    have hc (T : P.FullSubcategory) :
        ∃ c : DerivedCategory.Qh ⋙ D.obj (DerivedCategory.Qh.obj T.obj) ≅
          B.obj T.obj ⋙ DerivedCategory.Qh,
        ∀ V : P.FullSubcategory, c.app V.obj = (δ.app (T, V)).symm := by
      let e : P.ι ⋙ DerivedCategory.Qh ⋙ D.obj (DerivedCategory.Qh.obj T.obj) ≅
          P.ι ⋙ B.obj T.obj ⋙ DerivedCategory.Qh :=
        NatIso.ofComponents (fun V ↦ (δ.app (T, V)).symm) (by
          intro V V' f
          simpa using δ.inv.naturality (X := (T, V)) (Y := (T, V')) (𝟙 T, f))
      exact extend_comparison W DerivedCategory.Qh P
        (D.obj (DerivedCategory.Qh.obj T.obj)) (B.obj T.obj ⋙ DerivedCategory.Qh)
        (fun _ _ f hf ↦ Localization.inverts DerivedCategory.Qh W _ (hp T f hf)) e
    choose c hc using hc
    refine ⟨c, hc, ?_, ?_⟩
    · intro c' hc'
      funext T
      apply Iso.ext
      apply resolving_trans_ext W DerivedCategory.Qh P res
      intro V
      exact congrArg Iso.hom ((hc' T V).trans (hc T V).symm)
    · intro T T' g M
      let α := (c T).hom ≫ Functor.whiskerRight (B.map g.hom) DerivedCategory.Qh
      let β := Functor.whiskerLeft DerivedCategory.Qh (D.map (DerivedCategory.Qh.map g.hom)) ≫
        (c T').hom
      have he : α = β := by
        apply resolving_trans_ext W DerivedCategory.Qh P res
        intro V
        change (c T).hom.app V.obj ≫ DerivedCategory.Qh.map ((B.map g.hom).app V.obj) =
          (D.map (DerivedCategory.Qh.map g.hom)).app (DerivedCategory.Qh.obj V.obj) ≫
            (c T').hom.app V.obj
        rw [show (c T).hom.app V.obj = (δ.app (T, V)).inv from
          congrArg Iso.hom (hc T V)]
        rw [show (c T').hom.app V.obj = (δ.app (T', V)).inv from
          congrArg Iso.hom (hc T' V)]
        simpa using (δ.inv.naturality (X := (T, V)) (Y := (T', V)) (g, 𝟙 V)).symm
      exact congr_app he M
  refine ⟨hpres, oneOrder B D δ (fun T _ _ f hf ↦ (hpres T _ _ f hf).1), ?_, ?_⟩
  · apply oneOrder B.flip D.flip
      (NatIso.ofComponents (fun X ↦ δ.app (X.2, X.1)) (by
        intro X Y f
        simpa using δ.hom.naturality (X := (X.2, X.1)) (Y := (Y.2, Y.1)) (f.2, f.1)))
      (fun T _ _ f hf ↦ (hpres T _ _ f hf).2)
  · intro K L i j n h
    exact CochainComplex.Monoidal.ι_braiding_hom (K := K) (L := L) i j n h

end SheafOfModules
