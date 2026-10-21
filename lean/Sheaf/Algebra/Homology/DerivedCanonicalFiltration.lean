module

import Sheaf.Algebra.Homology.FilteredTensorLocalization
public import Sheaf.Algebra.Homology.CanonicalTruncationFiltration
public import Sheaf.Algebra.Homology.BoundedDerivedRoofs

/-!
# Canonical truncations lift bounded derived modules to finite filtered localization

Source: Stacks Project, `more-algebra.tex`, Tag 0H7Z; `homology.tex`, Tag 0118;
Derived Categories, Tags 05RW, 05S2 and 05S6
(blueprint: lem-kun-derived-canonical-filtration).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits
open CochainComplex

namespace DerivedCategory

variable (R : Type u) [CommRing R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem filtered_ext {K L : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)}
    {f g : FilteredObject.Hom K L} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

private theorem paste_squares {C : Type*} [Category C]
    {A B D E F G : C} {f : A ⟶ B} {g : D ⟶ E} {h : F ⟶ G}
    {a : A ⟶ D} {b : B ⟶ E} {c : D ⟶ F} {d : E ⟶ G}
    (h₁ : f ≫ b = a ≫ g) (h₂ : g ≫ d = c ≫ h) :
    f ≫ (b ≫ d) = (a ≫ c) ≫ h := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

private theorem localization_of_roofs
    {A B : Type*} [Category A] [Category B] (Q : A ⥤ B) [Q.EssSurj]
    (W : MorphismProperty A) [W.IsMultiplicative]
    (hinv : W.IsInvertedBy Q)
    (hroof : ∀ (X Y : A) (f : Q.obj X ⟶ Q.obj Y),
      ∃ (M : A) (s : M ⟶ X) (g : M ⟶ Y) (hs : W s),
        f = @inv _ _ _ _ (Q.map s) (hinv s hs) ≫ Q.map g)
    (heq : ∀ {X Y : A} (f g : X ⟶ Y), Q.map f = Q.map g →
      ∃ (M : A) (s : M ⟶ X), W s ∧ s ≫ f = s ≫ g) :
    Q.IsLocalization W := by
  have hcalc : W.HasRightCalculusOfFractions :=
    { exists_rightFraction := by
        intro X Y φ
        have hs := hinv φ.s φ.hs
        obtain ⟨M, s, g, hs', h⟩ := hroof X Y (Q.map φ.f ≫ inv (Q.map φ.s))
        have := hinv s hs'
        have hw : Q.map (s ≫ φ.f) = Q.map (g ≫ φ.s) := by
          simp only [Q.map_comp]
          rw [← cancel_epi (Q.map s)] at h
          simpa only [Category.assoc, IsIso.hom_inv_id_assoc,
            IsIso.inv_hom_id, Category.comp_id] using h =≫ Q.map φ.s
        obtain ⟨N, t, ht, hfg⟩ := heq _ _ hw
        exact ⟨⟨t ≫ s, W.comp_mem _ _ ht hs', t ≫ g⟩,
          by simpa only [Category.assoc] using hfg⟩
      ext := by
        intro X Y Y' f g s hs h
        have := hinv s hs
        obtain ⟨M, t, ht, hfg⟩ := heq f g (by
          apply (cancel_mono (Q.map s)).1
          simpa only [← Q.map_comp] using congrArg Q.map h)
        exact ⟨M, t, ht, hfg⟩ }
  let L := Localization.Construction.lift Q hinv
  have hmap {X Y : A} (f : X ⟶ Y) : L.map (W.Q.map f) = Q.map f :=
    by simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
      Functor.congr_hom (Localization.Construction.fac Q hinv) f
  have : L.Full := by
    apply L.full_of_comp_essSurj W.Q
    intro X Y f
    obtain ⟨M, s, g, hs, h⟩ := hroof X Y f
    have := Localization.inverts W.Q W s hs
    exact ⟨inv (W.Q.map s) ≫ W.Q.map g, by
      simpa only [L.map_comp, L.map_inv, hmap] using h.symm⟩
  have hfaith : L.op.Faithful := by
    apply Functor.faithful_of_comp_of_hasLeftCalculusOfFractions W.Q.op W.op L.op
    intro X Y f g h
    apply Quiver.Hom.unop_inj
    change W.Q.map f.unop = W.Q.map g.unop
    apply (MorphismProperty.map_eq_iff_precomp W.Q W _ _).2
    obtain ⟨M, s, hs, hfg⟩ := heq f.unop g.unop (by
      have hh := congrArg Quiver.Hom.unop h
      change L.map (W.Q.map f.unop) = L.map (W.Q.map g.unop) at hh
      simpa only [hmap] using hh)
    exact ⟨M, s, hs, hfg⟩
  have : L.Faithful := ⟨fun h ↦ Quiver.Hom.op_inj (L.op.map_injective
    (show L.op.map _ = L.op.map _ from congrArg Quiver.Hom.op h))⟩
  have : L.EssSurj := by
    constructor
    intro X
    obtain ⟨Y, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage Q X
    exact ⟨W.Q.obj Y, ⟨e⟩⟩
  exact ⟨hinv, { }⟩

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem restrict_homotopy
    {K L A B : CochainComplex (ModuleCat.{u} R) ℤ}
    (a : A ⟶ K) (b : B ⟶ L) [Mono b]
    {f g : K ⟶ L} (h : Homotopy f g)
    (f' g' : A ⟶ B) (hf : f' ≫ b = a ≫ f) (hg : g' ≫ b = a ≫ g)
    (hlift : ∀ n m : ℤ, ∃ l : A.X n ⟶ B.X m,
      l ≫ b.f m = a.f n ≫ h.hom n m) :
    ∃ h' : Homotopy f' g', ∀ n m : ℤ,
      a.f n ≫ h.hom n m = h'.hom n m ≫ b.f m := by
  classical
  choose l hl using hlift
  have hf' (n : ℤ) : f'.f n ≫ b.f n = a.f n ≫ f.f n :=
    congrArg (fun q ↦ q.f n) hf
  have hg' (n : ℤ) : g'.f n ≫ b.f n = a.f n ≫ g.f n :=
    congrArg (fun q ↦ q.f n) hg
  refine ⟨{ hom := l, zero := ?_, comm := ?_ }, fun n m ↦ (hl n m).symm⟩
  · intro n m hnm
    apply (cancel_mono (b.f m)).1
    simp only [hl, h.zero n m hnm, comp_zero, zero_comp]
  · intro n
    apply (cancel_mono (b.f n)).1
    change f'.f n ≫ b.f n =
      ((A.d n _ ≫ l _ n + l n _ ≫ B.d _ n) + g'.f n) ≫ b.f n
    simp only [Preadditive.add_comp, Category.assoc, hl]
    rw [← b.comm, ← Category.assoc (l n _), hl, Category.assoc, ← a.comm_assoc]
    rw [hf', hg', h.comm]
    simp only [Preadditive.comp_add, dNext, prevD]
    rfl

private abbrev BComplex := ObjectProperty.FullSubcategory
  (fun K : CochainComplex (ModuleCat.{u} R) ℤ ↦
    ∃ (m n : ℤ), ∀ r : ℤ, r < m ∨ n < r → IsZero (K.X r))

private def bHomotopyRel : HomRel (BComplex R) :=
  fun {_ _} f g ↦ Nonempty (Homotopy f.hom g.hom)

private noncomputable def bQ : BComplex R ⥤ Bounded (ModuleCat.{u} R) where
  obj K := ⟨Q.obj K.obj, by
    obtain ⟨m, n, h⟩ := K.property
    have : K.obj.IsStrictlyGE m := (K.obj.isStrictlyGE_iff m).2
      (fun r hr ↦ h r (Or.inl hr))
    have : K.obj.IsStrictlyLE n := (K.obj.isStrictlyLE_iff n).2
      (fun r hr ↦ h r (Or.inr hr))
    exact ⟨⟨m, inferInstance⟩, ⟨n, inferInstance⟩⟩⟩
  map f := ObjectProperty.homMk (Q.map f.hom)
  map_id K := by ext; exact Q.map_id K.obj
  map_comp f g := by ext; exact Q.map_comp f.hom g.hom

private noncomputable def bQh :
    CategoryTheory.Quotient (bHomotopyRel R) ⥤ Bounded (ModuleCat.{u} R) :=
  CategoryTheory.Quotient.lift _ (bQ R) (by
    rintro K L f g ⟨h⟩
    apply ObjectProperty.hom_ext
    exact Q_map_eq_of_homotopy _ h)

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem common_bounds (Ks : List (BComplex R)) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ K ∈ Ks, K.obj.IsStrictlyGE a ∧ K.obj.IsStrictlyLE b := by
  induction Ks with
  | nil => exact ⟨0, 0, le_rfl, by simp⟩
  | cons K Ks ih =>
    obtain ⟨a, b, hab, hKs⟩ := ih
    obtain ⟨m, n, hK⟩ := K.property
    refine ⟨min a m, max b n, by omega, ?_⟩
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact ⟨(L.obj.isStrictlyGE_iff _).2 (fun r hr ↦ hK r (Or.inl (by omega))),
        (L.obj.isStrictlyLE_iff _).2 (fun r hr ↦ hK r (Or.inr (by omega)))⟩
    · obtain ⟨ha, hb⟩ := hKs L hL
      exact ⟨L.obj.isStrictlyGE_of_ge _ a (by omega),
        L.obj.isStrictlyLE_of_le b _ (by omega)⟩

private theorem bQh_localization :
    (bQh R).IsLocalization ((MorphismProperty.isomorphisms _).inverseImage (bQh R)) := by
  let W := (MorphismProperty.isomorphisms _).inverseImage (bQh R)
  have hsurj : (bQh R).EssSurj := by
    constructor
    intro C
    obtain ⟨a, b, K, hab, ha, hb, ⟨e⟩⟩ := (boundedDerivedRoofs R).2.1 C
    refine ⟨⟨⟨K, a, b, fun r hr ↦ ?_⟩⟩, ⟨?_⟩⟩
    · rcases hr with hr | hr
      · exact K.isZero_of_isStrictlyGE a r hr
      · exact K.isZero_of_isStrictlyLE b r hr
    · exact ObjectProperty.isoMk _ e.symm
  apply localization_of_roofs (bQh R) W (fun _ _ f hf ↦ hf)
  · intro X Y f
    obtain ⟨a, b, hab, h⟩ := common_bounds R [X.as, Y.as]
    obtain ⟨haX, hbX⟩ := h X.as (by simp)
    obtain ⟨haY, hbY⟩ := h Y.as (by simp)
    obtain ⟨M, haM, hbM, s, hs, g, hg⟩ :=
      (boundedDerivedRoofs R).2.2.1 _ _ a b X.as.obj Y.as.obj haX hbX haY hbY hab
        (Iso.refl _) (Iso.refl _) f.hom
    let M' : BComplex R := ⟨M, a, b, fun r hr ↦ hr.elim
      (fun hr ↦ M.isZero_of_isStrictlyGE a r hr)
      (fun hr ↦ M.isZero_of_isStrictlyLE b r hr)⟩
    let s' : M' ⟶ X.as := ObjectProperty.homMk s
    let g' : M' ⟶ Y.as := ObjectProperty.homMk g
    refine ⟨⟨M'⟩, (CategoryTheory.Quotient.functor _).map s',
      (CategoryTheory.Quotient.functor _).map g', ?_, ?_⟩
    · apply (ObjectProperty.isIso_hom_iff _).1
      change IsIso (Q.map s)
      infer_instance
    · apply ObjectProperty.hom_ext
      rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.hom_inv]
      change f.hom = inv (Q.map s) ≫ Q.map g
      simpa only [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id] using hg
  · intro X Y f g hfg
    obtain ⟨f, rfl⟩ := (CategoryTheory.Quotient.functor (bHomotopyRel R)).map_surjective f
    obtain ⟨g, rfl⟩ := (CategoryTheory.Quotient.functor (bHomotopyRel R)).map_surjective g
    have hfg' : Q.map f.hom = Q.map g.hom := congrArg (fun t ↦ t.hom) hfg
    obtain ⟨a, b, hab, h⟩ := common_bounds R [X.as, Y.as]
    obtain ⟨haX, hbX⟩ := h X.as (by simp)
    obtain ⟨haY, hbY⟩ := h Y.as (by simp)
    obtain ⟨P, v₁, v₂, hP, hv₁, hv₂, ⟨hs⟩, ⟨hg⟩⟩ :=
      (boundedDerivedRoofs R).2.2.2 X.as.obj Y.as.obj X.as.obj X.as.obj
        (𝟙 _) f.hom (𝟙 _) g.hom
        ⟨a, b, hab, haX, hbX, haY, hbY, haX, hbX, haX, hbX⟩ (by simpa using hfg')
    obtain ⟨c, d, hcd, hc, hd⟩ := hP
    let P' : BComplex R := ⟨P, c, d, fun r hr ↦ hr.elim
      (fun hr ↦ P.isZero_of_isStrictlyGE c r hr)
      (fun hr ↦ P.isZero_of_isStrictlyLE d r hr)⟩
    let v₁' : P' ⟶ X.as := ObjectProperty.homMk v₁
    let v₂' : P' ⟶ X.as := ObjectProperty.homMk v₂
    let q := CategoryTheory.Quotient.functor (bHomotopyRel R)
    have hv : q.map v₁' = q.map v₂' := by
      apply CategoryTheory.Quotient.sound
      change Nonempty (Homotopy v₁ v₂)
      exact ⟨by simpa only [Category.comp_id] using hs⟩
    refine ⟨⟨P'⟩, q.map v₁', ?_, ?_⟩
    · apply (ObjectProperty.isIso_hom_iff _).1
      change IsIso (Q.map v₁)
      infer_instance
    · calc
        q.map v₁' ≫ q.map f = q.map v₂' ≫ q.map g := by
          rw [← q.map_comp, ← q.map_comp]
          exact CategoryTheory.Quotient.sound _ ⟨hg⟩
        _ = q.map v₁' ≫ q.map g := by rw [hv]

private theorem localization_comparison_data :
    ∃ (omega : (finiteFilteredModuleQuasiIso R).Localization ⥤
        DerivedCategory (ModuleCat.{u} R))
      (Fω : FiniteFilteredModuleHomotopy R ⥤ DerivedCategory (ModuleCat.{u} R))
      (_hω : Localization.Lifting (finiteFilteredModuleQuasiIso R).Q
        (finiteFilteredModuleQuasiIso R) Fω omega)
      (hωobj : ∀ K : FiniteFilteredModuleHomotopy R,
        Fω.obj K = HomologicalComplexUpToQuasiIso.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj K.as.obj.obj)),
      (∀ (K L : FiniteFilteredModuleHomotopy R) (f : K.as ⟶ L.as),
        Fω.map ((finiteFilteredModuleHomotopyQuotient R).map f) =
          eqToHom (hωobj ((finiteFilteredModuleHomotopyQuotient R).obj K.as)) ≫
            HomologicalComplexUpToQuasiIso.Qh.map
              ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map f.hom.hom) ≫
            eqToHom (hωobj ((finiteFilteredModuleHomotopyQuotient R).obj L.as)).symm) ∧
      ∃ (gr : ℤ → (finiteFilteredModuleQuasiIso R).Localization ⥤
          DerivedCategory (ModuleCat.{u} R))
        (Fgr : ℤ → FiniteFilteredModuleHomotopy R ⥤ DerivedCategory (ModuleCat.{u} R))
        (_hgr : ∀ i : ℤ, Localization.Lifting (finiteFilteredModuleQuasiIso R).Q
          (finiteFilteredModuleQuasiIso R) (Fgr i) (gr i))
        (hgro : ∀ (i : ℤ) (K : FiniteFilteredModuleHomotopy R),
          (Fgr i).obj K = HomologicalComplexUpToQuasiIso.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
              (K.as.obj.filtration.gradedPiece i))),
        ∀ (i : ℤ) (K L : FiniteFilteredModuleHomotopy R) (f : K.as ⟶ L.as),
          (Fgr i).map ((finiteFilteredModuleHomotopyQuotient R).map f) =
            eqToHom (hgro i ((finiteFilteredModuleHomotopyQuotient R).obj K.as)) ≫
              HomologicalComplexUpToQuasiIso.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                  (FilteredObject.gradedMapSteps f.hom i)) ≫
              eqToHom (hgro i ((finiteFilteredModuleHomotopyQuotient R).obj L.as)).symm := by
  classical
  have data := CochainComplex.filteredTensor_localization (R := R)
  obtain ⟨E, data⟩ := data
  obtain ⟨eE, data⟩ := data
  obtain ⟨F, data⟩ := data
  obtain ⟨B, data⟩ := data
  obtain ⟨hB, data⟩ := data
  obtain ⟨hconv, data⟩ := data
  obtain ⟨conv, data⟩ := data
  obtain ⟨hconv₁, data⟩ := data
  obtain ⟨hconv₂, data⟩ := data
  obtain ⟨hrep, data⟩ := data
  obtain ⟨m, data⟩ := data
  obtain ⟨hm, data⟩ := data
  obtain ⟨hid, data⟩ := data
  obtain ⟨hcomp, data⟩ := data
  obtain ⟨hmap, data⟩ := data
  obtain ⟨star, data⟩ := data
  obtain ⟨τ, data⟩ := data
  obtain ⟨hτ, data⟩ := data
  obtain ⟨omega, data⟩ := data
  obtain ⟨Fω, data⟩ := data
  obtain ⟨hω, data⟩ := data
  obtain ⟨hωobj, data⟩ := data
  obtain ⟨hωmap, data⟩ := data
  obtain ⟨gr, data⟩ := data
  obtain ⟨Fgr, data⟩ := data
  obtain ⟨hgr, data⟩ := data
  obtain ⟨hgro, data⟩ := data
  obtain ⟨hgrmap, data⟩ := data
  clear E eE F B hB hconv conv hconv₁ hconv₂ hrep m hm hid hcomp hmap star τ hτ data
  exact ⟨omega, Fω, hω, hωobj, hωmap, gr, Fgr, hgr, hgro, hgrmap⟩

set_option backward.defeqAttrib.useBackward true in
private theorem localization_comparisons :
    ∃ (omega : (finiteFilteredModuleQuasiIso R).Localization ⥤
        DerivedCategory (ModuleCat.{u} R))
      (gr : ℤ → (finiteFilteredModuleQuasiIso R).Localization ⥤
        DerivedCategory (ModuleCat.{u} R))
      (eForget : ∀ P : FiniteFilteredModuleComplex R,
        omega.obj ((finiteFilteredModuleHomotopyQuotient R ⋙
          (finiteFilteredModuleQuasiIso R).Q).obj P) ≅ Q.obj P.obj.obj)
      (eGrade : ∀ i (P : FiniteFilteredModuleComplex R),
        (gr i).obj ((finiteFilteredModuleHomotopyQuotient R ⋙
          (finiteFilteredModuleQuasiIso R).Q).obj P) ≅
            Q.obj (P.obj.filtration.gradedPiece i)),
      (∀ (P P' : FiniteFilteredModuleComplex R) (f : P ⟶ P'),
        omega.map ((finiteFilteredModuleHomotopyQuotient R ⋙
          (finiteFilteredModuleQuasiIso R).Q).map f) ≫ (eForget P').hom =
        (eForget P).hom ≫ Q.map f.hom.hom) ∧
      (∀ i (P P' : FiniteFilteredModuleComplex R) (f : P ⟶ P'),
        (gr i).map ((finiteFilteredModuleHomotopyQuotient R ⋙
          (finiteFilteredModuleQuasiIso R).Q).map f) ≫ (eGrade i P').hom =
        (eGrade i P).hom ≫ Q.map (FilteredObject.gradedMapSteps f.hom i)) := by
  classical
  obtain ⟨omega, Fω, hω, hωobj, hωmap, gr, Fgr, hgr, hgro, hgrmap⟩ :=
    localization_comparison_data R
  let eForget := fun P : FiniteFilteredModuleComplex R ↦
    (Localization.Lifting.iso (finiteFilteredModuleQuasiIso R).Q
      (finiteFilteredModuleQuasiIso R) Fω omega).app
        ((finiteFilteredModuleHomotopyQuotient R).obj P) ≪≫
      eqToIso (hωobj ((finiteFilteredModuleHomotopyQuotient R).obj P)) ≪≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app P.obj.obj
  let eGrade := fun (i : ℤ) (P : FiniteFilteredModuleComplex R) ↦
    (Localization.Lifting.iso (finiteFilteredModuleQuasiIso R).Q
      (finiteFilteredModuleQuasiIso R) (Fgr i) (gr i)).app
        ((finiteFilteredModuleHomotopyQuotient R).obj P) ≪≫
      eqToIso (hgro i ((finiteFilteredModuleHomotopyQuotient R).obj P)) ≪≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app
        (P.obj.filtration.gradedPiece i)
  refine ⟨omega, gr, eForget, eGrade, ?_, ?_⟩
  · intro P P' f
    dsimp only [eForget, Iso.trans_hom, Iso.app_hom, eqToIso.hom]
    erw [← Category.assoc, (Localization.Lifting.iso
      (finiteFilteredModuleQuasiIso R).Q (finiteFilteredModuleQuasiIso R)
      Fω omega).hom.naturality, hωmap]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    erw [DerivedCategory.quotientCompQhIso_hom_naturality]
    rfl
  · intro i P P' f
    dsimp only [eGrade, Iso.trans_hom, Iso.app_hom, eqToIso.hom]
    erw [← Category.assoc, (Localization.Lifting.iso
      (finiteFilteredModuleQuasiIso R).Q (finiteFilteredModuleQuasiIso R)
      (Fgr i) (gr i)).hom.naturality, hgrmap]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    erw [DerivedCategory.quotientCompQhIso_hom_naturality]
    rfl

set_option linter.unusedVariables false in
/-- Canonical truncation filtration on bounded derived modules.

Source: Stacks Project, `more-algebra.tex`, Tag 0H7Z; `homology.tex`, Tag 0118;
Derived Categories, Tags 05RW, 05S2 and 05S6
(blueprint: lem-kun-derived-canonical-filtration).

Proof steps. (1) Use `DerivedCategory.boundedDerivedRoofs` to represent bounded
objects and morphisms by bounded complexes and bounded roofs. (2) Apply
`CochainComplex.exists_canonicalTruncationFiltration`; its good truncations form a
finite filtered complex, its two-term graded quotient maps quasi-isomorphically to
shifted cohomology, and its maps and homotopies are filtration preserving.
(3) Use bounded roofs and common refinements to identify the bounded homotopy
category localization with the bounded derived category. Descend the canonical
filtration by this universal property; obtain forgetful and graded functors from
`CochainComplex.filteredTensor_localization`.
(4) Forgetting the filtration gives the original derived object and morphism, while
the graded comparison gives `H⁻ⁱ(C)[i]`; naturality of the representative maps
identifies every derived morphism with `u` and `H⁻ⁱ(u)[i]`.
(5) For every bounded representative and every identification `eC : C ≅ Q(K)`,
provide `rep C K hK eC : T(C) ≅ Q_W q(K,F)`. Its chain-map equation is the
representative formula for `T`; its roof equation says the conjugate of `T(u)`
is `Q_W(q(s))⁻¹ ≫ Q_W(q(g))` for every bounded roof representing `u`.
The common-refinement clause of `DerivedCategory.boundedDerivedRoofs` and the
localization universal property make this independent of roofs and representatives.
In particular, applying the roof equation to an identity
morphism determines the transition `rep_K⁻¹ ≫ rep_L` between any two representatives.
(6) The natural representative identifications `eForget` and `eGrade` specify the
forgetful and graded functors on all finite filtered complexes and maps. The two
normalization equations tie `rep` to `eOmega` via `eC` and to `eGr` via the specified
quotient `pi`, the canonical homology comparison, and the single-complex shift
isomorphism. Thus the representative transitions preserve both comparisons.
No termwise functorial choice of a bounded representative is made.
-/
theorem exists_derivedCanonicalFiltration :
    ∃ (F : ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
        DecreasingFiltration K)
      (pi : ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
        (F K).gradedPiece i ⟶
          (CochainComplex.singleFunctor (ModuleCat.{u} R) (-i)).obj
            (K.homology (-i))),
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
        (F K).step i = Subobject.mk (K.ιTruncLE (-i))) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ),
        (∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r)) →
          ∃ (a b : ℤ), a < b ∧ (F K).step a = ⊤ ∧ (F K).step b = ⊥) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (i : ℤ),
        ∃ (M : CochainComplex (ModuleCat.{u} R) ℤ)
          (e : (F K).gradedPiece i ≅ M)
          (e₀ : M.X (-i - 1) ≅ cokernel (kernel.ι (K.d (-i - 1) (-i))))
          (e₁ : M.X (-i) ≅ K.cycles (-i)),
          (∀ (r : ℤ), r ≠ -i - 1 → r ≠ -i → IsZero (M.X r)) ∧
          Mono (M.d (-i - 1) (-i)) ∧
          cokernel.π (kernel.ι (K.d (-i - 1) (-i))) ≫ e₀.inv ≫
              M.d (-i - 1) (-i) ≫ e₁.hom ≫ K.iCycles (-i) =
            K.d (-i - 1) (-i) ∧
          (pi K i).f (-i) ≫
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-i)
                (K.homology (-i))).hom =
            e.hom.f (-i) ≫ e₁.hom ≫ K.homologyπ (-i) ∧
          QuasiIso (pi K i)) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f : K ⟶ L),
        ∃ (φ : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
          φ.hom = f ∧
          ∀ (i : ℤ), FilteredObject.gradedMapSteps φ i ≫ pi L i =
            pi K i ≫
              (CochainComplex.singleFunctor (ModuleCat.{u} R) (-i)).map
                (HomologicalComplex.homologyMap f (-i))) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f g : K ⟶ L) (h : Homotopy f g),
        ∃ (hf : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
          hf.hom = f ∧
          ∃ (hg : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
            hg.hom = g ∧
            ∀ (i : ℤ),
              ∃ (hf_i hg_i :
                  ((F K).step i : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
                    ((F L).step i : CochainComplex (ModuleCat.{u} R) ℤ))
                (h_i : Homotopy hf_i hg_i),
                hf_i ≫ ((F L).step i).arrow =
                    ((F K).step i).arrow ≫ f ∧
                  hg_i ≫ ((F L).step i).arrow =
                    ((F K).step i).arrow ≫ g ∧
                  ∀ (n m : ℤ),
                    ((F K).step i).arrow.f n ≫ h.hom n m =
                      h_i.hom n m ≫ ((F L).step i).arrow.f m) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f : K ⟶ L), (∀ (r : ℤ), IsIso (K.homologyMap f r)) →
          ∀ (i : ℤ), ∃ (φ : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
            φ.hom = f ∧ QuasiIso (FilteredObject.gradedMapSteps φ i)) ∧
      ∃ (T : DerivedCategory.Bounded (ModuleCat.{u} R) ⥤
        (finiteFilteredModuleQuasiIso R).Localization)
        (omega : (finiteFilteredModuleQuasiIso R).Localization ⥤
          DerivedCategory (ModuleCat.{u} R))
        (gr : ℤ → (finiteFilteredModuleQuasiIso R).Localization ⥤
          DerivedCategory (ModuleCat.{u} R))
        (eOmega : T ⋙ omega ≅ DerivedCategory.Bounded.ι)
        (eGr : ∀ i : ℤ,
          T ⋙ gr i ≅
            DerivedCategory.Bounded.ι ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-i) ⋙
              DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
              shiftFunctor (DerivedCategory (ModuleCat.{u} R)) i)
        (eForget : ∀ P : FiniteFilteredModuleComplex R,
          omega.obj ((finiteFilteredModuleHomotopyQuotient R ⋙
            (finiteFilteredModuleQuasiIso R).Q).obj P) ≅
              DerivedCategory.Q.obj P.obj.obj)
        (eGrade : ∀ (i : ℤ) (P : FiniteFilteredModuleComplex R),
          (gr i).obj ((finiteFilteredModuleHomotopyQuotient R ⋙
            (finiteFilteredModuleQuasiIso R).Q).obj P) ≅
              DerivedCategory.Q.obj (P.obj.filtration.gradedPiece i))
        (hfinite : ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ),
          (∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r)) →
            (F K).IsFinite)
        (rep : ∀ (C : DerivedCategory.Bounded (ModuleCat.{u} R))
          (K : CochainComplex (ModuleCat.{u} R) ℤ)
          (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
          (eC : C.1 ≅ DerivedCategory.Q.obj K),
          T.obj C ≅ (finiteFilteredModuleHomotopyQuotient R ⋙
            (finiteFilteredModuleQuasiIso R).Q).obj ⟨⟨K, F K⟩, hfinite K hK⟩),
        (∀ (P P' : FiniteFilteredModuleComplex R) (f : P ⟶ P'),
          omega.map ((finiteFilteredModuleHomotopyQuotient R ⋙
              (finiteFilteredModuleQuasiIso R).Q).map f) ≫ (eForget P').hom =
            (eForget P).hom ≫ DerivedCategory.Q.map f.hom.hom) ∧
        (∀ (i : ℤ) (P P' : FiniteFilteredModuleComplex R) (f : P ⟶ P'),
          (gr i).map ((finiteFilteredModuleHomotopyQuotient R ⋙
              (finiteFilteredModuleQuasiIso R).Q).map f) ≫ (eGrade i P').hom =
            (eGrade i P).hom ≫
              DerivedCategory.Q.map (FilteredObject.gradedMapSteps f.hom i)) ∧
        (∀ (C : DerivedCategory.Bounded (ModuleCat.{u} R)),
          ∃ (a b : ℤ) (K : CochainComplex (ModuleCat.{u} R) ℤ),
            a ≤ b ∧ K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧
              Nonempty (C.1 ≅ DerivedCategory.Q.obj K)) ∧
        (∀ (C : DerivedCategory.Bounded (ModuleCat.{u} R))
          (K : CochainComplex (ModuleCat.{u} R) ℤ)
          (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
          (eC : C.1 ≅ DerivedCategory.Q.obj K),
          eOmega.hom.app C ≫ eC.hom =
            omega.map (rep C K hK eC).hom ≫
              (eForget ⟨⟨K, F K⟩, hfinite K hK⟩).hom) ∧
        (∀ (i : ℤ) (C : DerivedCategory.Bounded (ModuleCat.{u} R))
          (K : CochainComplex (ModuleCat.{u} R) ℤ)
          (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
          (eC : C.1 ≅ DerivedCategory.Q.obj K),
          (eGr i).hom.app C ≫
              (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
                shiftFunctor (DerivedCategory (ModuleCat.{u} R)) i).map
                ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-i)).map eC.hom ≫
                  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (-i)).hom.app K) =
            (gr i).map (rep C K hK eC).hom ≫
              (eGrade i ⟨⟨K, F K⟩, hfinite K hK⟩).hom ≫
              DerivedCategory.Q.map (pi K i) ≫
              ((DerivedCategory.singleFunctors (ModuleCat.{u} R)).shiftIso
                i (-i) 0 (add_neg_cancel i)).inv.app (K.homology (-i))) ∧
        (∀ (C C' : DerivedCategory.Bounded (ModuleCat.{u} R))
          (K L : CochainComplex (ModuleCat.{u} R) ℤ)
          (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
          (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
          (eC : C.1 ≅ DerivedCategory.Q.obj K)
          (eC' : C'.1 ≅ DerivedCategory.Q.obj L)
          (f : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
          T.map (ObjectProperty.homMk
              (eC.hom ≫ DerivedCategory.Q.map f.hom ≫ eC'.inv)) ≫
              (rep C' L hL eC').hom =
            (rep C K hK eC).hom ≫
              (finiteFilteredModuleHomotopyQuotient R ⋙
                (finiteFilteredModuleQuasiIso R).Q).map
                (ObjectProperty.homMk f :
                  (⟨⟨K, F K⟩, hfinite K hK⟩ : FiniteFilteredModuleComplex R) ⟶
                    ⟨⟨L, F L⟩, hfinite L hL⟩)) ∧
        (∀ (C C' : DerivedCategory.Bounded (ModuleCat.{u} R))
          (K L M : CochainComplex (ModuleCat.{u} R) ℤ)
          (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
          (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
          (hM : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (M.X r))
          (eC : C.1 ≅ DerivedCategory.Q.obj K)
          (eC' : C'.1 ≅ DerivedCategory.Q.obj L)
          (s : FilteredObject.Hom ⟨M, F M⟩ ⟨K, F K⟩)
          (g : FilteredObject.Hom ⟨M, F M⟩ ⟨L, F L⟩)
          (hs : QuasiIso s.hom) (f : C ⟶ C'),
          f.hom = eC.hom ≫ inv (DerivedCategory.Q.map s.hom) ≫
            DerivedCategory.Q.map g.hom ≫ eC'.inv →
          ∃ (_hs' : IsIso ((finiteFilteredModuleHomotopyQuotient R ⋙
            (finiteFilteredModuleQuasiIso R).Q).map
              (ObjectProperty.homMk s :
                (⟨⟨M, F M⟩, hfinite M hM⟩ : FiniteFilteredModuleComplex R) ⟶
                  ⟨⟨K, F K⟩, hfinite K hK⟩))),
          (rep C K hK eC).inv ≫ T.map f ≫ (rep C' L hL eC').hom =
            inv ((finiteFilteredModuleHomotopyQuotient R ⋙
              (finiteFilteredModuleQuasiIso R).Q).map
                (ObjectProperty.homMk s :
                  (⟨⟨M, F M⟩, hfinite M hM⟩ : FiniteFilteredModuleComplex R) ⟶
                    ⟨⟨K, F K⟩, hfinite K hK⟩)) ≫
              (finiteFilteredModuleHomotopyQuotient R ⋙
                (finiteFilteredModuleQuasiIso R).Q).map
                (ObjectProperty.homMk g :
                  (⟨⟨M, F M⟩, hfinite M hM⟩ : FiniteFilteredModuleComplex R) ⟶
                    ⟨⟨L, F L⟩, hfinite L hL⟩)) ∧
        (∀ (C C' : DerivedCategory.Bounded (ModuleCat.{u} R)) (f : C ⟶ C'),
          eOmega.hom.app C ≫ DerivedCategory.Bounded.ι.map f =
            (T ⋙ omega).map f ≫ eOmega.hom.app C') ∧
        (∀ (i : ℤ) (C C' : DerivedCategory.Bounded (ModuleCat.{u} R))
          (f : C ⟶ C'),
          (eGr i).hom.app C ≫
              (DerivedCategory.Bounded.ι ⋙
                DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-i) ⋙
                DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
                shiftFunctor (DerivedCategory (ModuleCat.{u} R)) i).map f =
            (T ⋙ gr i).map f ≫ (eGr i).hom.app C') := by
  classical
  obtain ⟨F, pi, hstep, hfinite', hpiece, hmap, hhom, hqi⟩ :=
    CochainComplex.exists_canonicalTruncationFiltration (R := R)
  have hfinite (K : CochainComplex (ModuleCat.{u} R) ℤ)
      (hK : ∃ m n : ℤ, ∀ r : ℤ, r < m ∨ n < r → IsZero (K.X r)) :
      (F K).IsFinite := by
    obtain ⟨a, b, hab, ha, hb⟩ := hfinite' K hK
    exact ⟨a, b, ha, hb⟩
  have hhom' : ∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
      (hK : ∃ m n : ℤ, ∀ r : ℤ, r < m ∨ n < r → IsZero (K.X r))
      (hL : ∃ m n : ℤ, ∀ r : ℤ, r < m ∨ n < r → IsZero (L.X r))
      (f g : K ⟶ L) (h : Homotopy f g),
      ∃ (hf : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
        hf.hom = f ∧
        ∃ (hg : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
          hg.hom = g ∧ ∀ i : ℤ,
          ∃ (fi gi : ((F K).step i : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
              ((F L).step i : CochainComplex (ModuleCat.{u} R) ℤ))
            (hi : Homotopy fi gi),
            fi ≫ ((F L).step i).arrow = ((F K).step i).arrow ≫ f ∧
            gi ≫ ((F L).step i).arrow = ((F K).step i).arrow ≫ g ∧
            ∀ n m : ℤ, ((F K).step i).arrow.f n ≫ h.hom n m =
              hi.hom n m ≫ ((F L).step i).arrow.f m := by
    intro K L hK hL f g h
    obtain ⟨hf, hhf, hg, hhg, hh⟩ := hhom K L hK hL f g h
    refine ⟨hf, hhf, hg, hhg, ?_⟩
    intro i
    obtain ⟨fi, hfi⟩ := hf.preserves i
    obtain ⟨gi, hgi⟩ := hg.preserves i
    rw [hhf] at hfi
    rw [hhg] at hgi
    obtain ⟨hi, hhi⟩ := restrict_homotopy R _ _ h fi gi hfi hgi (hh i)
    exact ⟨fi, gi, hi, hfi, hgi, hhi⟩
  refine ⟨F, pi, hstep, hfinite', hpiece, hmap, hhom', hqi, ?_⟩
  let CF : BComplex R ⥤ FiniteFilteredModuleComplex R :=
    { obj := fun K ↦ ⟨⟨K.obj, F K.obj⟩, hfinite K.obj K.property⟩
      map := fun {K L} f ↦ ObjectProperty.homMk
        (hmap K.obj L.obj K.property L.property f.hom).choose
      map_id := by
        intro K
        apply ObjectProperty.hom_ext
        apply filtered_ext
        exact (hmap K.obj K.obj K.property K.property (𝟙 K.obj)).choose_spec.1
      map_comp := by
        intro K L M f g
        apply ObjectProperty.hom_ext
        apply filtered_ext
        change (hmap K.obj M.obj K.property M.property (f.hom ≫ g.hom)).choose.hom =
          (hmap K.obj L.obj K.property L.property f.hom).choose.hom ≫
            (hmap L.obj M.obj L.property M.property g.hom).choose.hom
        rw [(hmap K.obj M.obj K.property M.property (f.hom ≫ g.hom)).choose_spec.1,
          (hmap K.obj L.obj K.property L.property f.hom).choose_spec.1,
          (hmap L.obj M.obj L.property M.property g.hom).choose_spec.1] }
  have CFmap {K L : BComplex R} (f : K ⟶ L) : (CF.map f).hom.hom = f.hom :=
    (hmap K.obj L.obj K.property L.property f.hom).choose_spec.1
  let qf := finiteFilteredModuleHomotopyQuotient R
  let Qf := qf ⋙ (finiteFilteredModuleQuasiIso R).Q
  let FH : CategoryTheory.Quotient (bHomotopyRel R) ⥤
      (finiteFilteredModuleQuasiIso R).Localization :=
    CategoryTheory.Quotient.lift _ (CF ⋙ Qf) (by
      rintro K L f g ⟨h⟩
      apply congrArg (finiteFilteredModuleQuasiIso R).Q.map
      apply CategoryTheory.Quotient.sound
      obtain ⟨hf, hhf, hg, hhg, hh⟩ := hhom K.obj L.obj K.property L.property
        f.hom g.hom h
      dsimp only [finiteFilteredModuleHomotopyRel]
      rw [CFmap, CFmap]
      exact ⟨h, hh⟩)
  have := bQh_localization R
  let Wb := (MorphismProperty.isomorphisms _).inverseImage (bQh R)
  have hinv : Wb.IsInvertedBy FH := by
    intro X Y f hf
    obtain ⟨f, rfl⟩ := (CategoryTheory.Quotient.functor (bHomotopyRel R)).map_surjective f
    have : IsIso ((bQh R).map
        ((CategoryTheory.Quotient.functor _).map f)) := hf
    have hi : IsIso (Q.map f.hom) := by
      exact (inferInstance : IsIso ((bQh R).map
        ((CategoryTheory.Quotient.functor _).map f)).hom)
    have hs : QuasiIso f.hom := (isIso_Q_map_iff_quasiIso _ f.hom).1 hi
    apply Localization.inverts (finiteFilteredModuleQuasiIso R).Q
      (finiteFilteredModuleQuasiIso R)
    refine ⟨CF.map f, rfl, ?_⟩
    intro i
    obtain ⟨φ, hφ, hφqi⟩ := hqi X.as.obj Y.as.obj X.as.property Y.as.property
      f.hom (fun r ↦ by infer_instance) i
    have he : φ = (CF.map f).hom := by
      apply filtered_ext
      rw [hφ, CFmap]
    simpa only [he] using hφqi
  let T := Localization.lift FH hinv (bQh R)
  let eT : bQh R ⋙ T ≅ FH := Localization.fac FH hinv (bQh R)
  obtain ⟨omega, gr, eForget, eGrade, hForget, hGrade⟩ := localization_comparisons R
  let q := CategoryTheory.Quotient.functor (bHomotopyRel R)
  let eωH : FH ⋙ omega ≅ bQh R ⋙ Bounded.ι :=
    CategoryTheory.Quotient.natIsoLift _ (NatIso.ofComponents
      (fun K ↦ eForget (CF.obj K)) (by
        intro K L f
        change omega.map (Qf.map (CF.map f)) ≫ (eForget (CF.obj L)).hom = _
        have hh := hForget _ _ (CF.map f)
        rw [CFmap] at hh
        exact hh))
  let liftTω : Localization.Lifting (bQh R) Wb (FH ⋙ omega) (T ⋙ omega) :=
    ⟨Functor.isoWhiskerRight eT omega⟩
  let eOmega : T ⋙ omega ≅ Bounded.ι :=
    Localization.liftNatIso (bQh R) Wb (FH ⋙ omega) (bQh R ⋙ Bounded.ι)
      (T ⋙ omega) Bounded.ι (h₁ := liftTω)
      (h₂ := ⟨Iso.refl _⟩) eωH
  let S := fun i : ℤ ↦ singleFunctor (ModuleCat.{u} R) 0 ⋙
    shiftFunctor (DerivedCategory (ModuleCat.{u} R)) i
  let H := fun i : ℤ ↦ Bounded.ι ⋙ homologyFunctor (ModuleCat.{u} R) (-i) ⋙ S i
  let ei := fun i : ℤ ↦ (singleFunctors (ModuleCat.{u} R)).shiftIso
    i (-i) 0 (add_neg_cancel i)
  have hpi (K : BComplex R) (i : ℤ) : QuasiIso (pi K.obj i) := by
    obtain ⟨M, e, e₀, e₁, h₀, hmono, hd, hπ, hq⟩ := hpiece K.obj K.property i
    exact hq
  let ec := fun (i : ℤ) (K : BComplex R) ↦
    eGrade i (CF.obj K) ≪≫ @asIso _ _ _ _ (Q.map (pi K.obj i))
      (by have := hpi K i; infer_instance) ≪≫ (ei i).symm.app (K.obj.homology (-i)) ≪≫
      (S i).mapIso ((homologyFunctorFactors (ModuleCat.{u} R) (-i)).symm.app K.obj)
  have hec (i : ℤ) (K L : BComplex R) (f : K ⟶ L) :
      (gr i).map (Qf.map (CF.map f)) ≫ (ec i L).hom =
        (ec i K).hom ≫ (H i).map ((bQ R).map f) := by
    have hp := (hmap K.obj L.obj K.property L.property f.hom).choose_spec.2 i
    have hφ : (hmap K.obj L.obj K.property L.property f.hom).choose =
        (CF.map f).hom := rfl
    rw [hφ] at hp
    have hfac := (homologyFunctorFactors (ModuleCat.{u} R) (-i)).inv.naturality f.hom
    have hsingle := (singleFunctorIsoCompQ (ModuleCat.{u} R) (-i)).hom.naturality
      (HomologicalComplex.homologyMap f.hom (-i))
    simp only [singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp, Category.comp_id, Functor.comp_map] at hsingle
    have h₂ : Q.map (FilteredObject.gradedMapSteps (CF.map f).hom i) ≫
        Q.map (pi L.obj i) = Q.map (pi K.obj i) ≫
          (singleFunctor (ModuleCat.{u} R) (-i)).map
            (HomologicalComplex.homologyMap f.hom (-i)) := by
      rw [← Q.map_comp, hp, Q.map_comp, ← hsingle]
    have h₃ := (ei i).inv.naturality (HomologicalComplex.homologyMap f.hom (-i))
    change HomologicalComplex.homologyMap f.hom (-i) ≫
        (homologyFunctorFactors (ModuleCat.{u} R) (-i)).inv.app L.obj =
      (homologyFunctorFactors (ModuleCat.{u} R) (-i)).inv.app K.obj ≫
        (homologyFunctor (ModuleCat.{u} R) (-i)).map (Q.map f.hom) at hfac
    have h₄ : (S i).map (HomologicalComplex.homologyMap f.hom (-i)) ≫
        (S i).map ((homologyFunctorFactors (ModuleCat.{u} R) (-i)).inv.app L.obj) =
      (S i).map ((homologyFunctorFactors (ModuleCat.{u} R) (-i)).inv.app K.obj) ≫
        (H i).map ((bQ R).map f) := by
      rw [← (S i).map_comp, hfac, (S i).map_comp]
      rfl
    have hh := paste_squares (paste_squares (paste_squares
      (hGrade i _ _ (CF.map f)) h₂) h₃) h₄
    simpa only [ec, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Iso.app_hom, asIso_hom, Category.assoc] using hh
  let egrH := fun i : ℤ ↦ CategoryTheory.Quotient.natIsoLift (bHomotopyRel R)
    (F := FH ⋙ gr i) (G := bQh R ⋙ H i)
    (NatIso.ofComponents (ec i) (fun {K L} f ↦ hec i K L f))
  let liftTgr : ∀ i : ℤ, Localization.Lifting (bQh R) Wb (FH ⋙ gr i) (T ⋙ gr i) :=
    fun i ↦ ⟨Functor.isoWhiskerRight eT (gr i)⟩
  let eGr := fun i : ℤ ↦
    Localization.liftNatIso (bQh R) Wb (FH ⋙ gr i) (bQh R ⋙ H i)
      (T ⋙ gr i) (H i) (h₁ := liftTgr i) (h₂ := ⟨Iso.refl _⟩) (egrH i)
  let rep := fun (C : Bounded (ModuleCat.{u} R))
      (K : CochainComplex (ModuleCat.{u} R) ℤ)
      (hK : ∃ m n : ℤ, ∀ r : ℤ, r < m ∨ n < r → IsZero (K.X r))
      (eC : C.obj ≅ Q.obj K) ↦
    T.mapIso (ObjectProperty.isoMk _ eC : C ≅ (bQ R).obj ⟨K, hK⟩) ≪≫
      eT.app (q.obj ⟨K, hK⟩)
  have rep_map (C C' : Bounded (ModuleCat.{u} R)) (K L : BComplex R)
      (eC : C.obj ≅ Q.obj K.obj) (eC' : C'.obj ≅ Q.obj L.obj) (f : K ⟶ L) :
      T.map (ObjectProperty.homMk (eC.hom ≫ Q.map f.hom ≫ eC'.inv)) ≫
          (rep C' L.obj L.property eC').hom =
        (rep C K.obj K.property eC).hom ≫ Qf.map (CF.map f) := by
    let e : C ≅ (bQ R).obj K := ObjectProperty.isoMk _ eC
    let e' : C' ≅ (bQ R).obj L := ObjectProperty.isoMk _ eC'
    change T.map (e.hom ≫ (bQ R).map f ≫ e'.inv) ≫
        (T.map e'.hom ≫ (eT.app (q.obj L)).hom) =
      (T.map e.hom ≫ (eT.app (q.obj K)).hom) ≫ Qf.map (CF.map f)
    rw [T.map_comp, T.map_comp]
    simp only [Category.assoc]
    rw [← T.map_comp_assoc e'.inv e'.hom, e'.inv_hom_id,
      T.map_id, Category.id_comp]
    have hh := eT.hom.naturality (q.map f)
    exact congrArg (fun t ↦ T.map e.hom ≫ t) hh
  refine ⟨T, omega, gr, eOmega, eGr, eForget, eGrade, hfinite, rep,
    hForget, hGrade, (boundedDerivedRoofs R).2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C K hK eC
    have he : eOmega.hom.app ((bQ R).obj ⟨K, hK⟩) =
        omega.map (eT.app (q.obj ⟨K, hK⟩)).hom ≫
          (eForget (CF.obj ⟨K, hK⟩)).hom := by
      change (Localization.liftNatTrans (bQh R) Wb _ _ _ _ _).app
        ((bQh R).obj (q.obj ⟨K, hK⟩)) = _
      rw [Localization.liftNatTrans_app]
      dsimp only [Localization.Lifting.iso, liftTω, Functor.isoWhiskerRight_hom,
        Functor.whiskerRight_app, eωH, CategoryTheory.Quotient.natIsoLift_hom,
        CategoryTheory.Quotient.natTransLift_app]
      simp only [Iso.refl_inv, NatTrans.id_app, Category.comp_id]
      rfl
    have hh := eOmega.hom.naturality (ObjectProperty.homMk eC.hom :
      C ⟶ (bQ R).obj ⟨K, hK⟩)
    change _ = eOmega.hom.app C ≫ eC.hom at hh
    rw [← hh, he]
    simp only [rep, Iso.trans_hom, Functor.mapIso_hom, omega.map_comp, Category.assoc]
    rfl
  · intro i C K hK eC
    have he : (eGr i).hom.app ((bQ R).obj ⟨K, hK⟩) =
        (gr i).map (eT.app (q.obj ⟨K, hK⟩)).hom ≫ (ec i ⟨K, hK⟩).hom := by
      change (Localization.liftNatTrans (bQh R) Wb _ _ _ _ _).app
        ((bQh R).obj (q.obj ⟨K, hK⟩)) = _
      rw [Localization.liftNatTrans_app]
      dsimp only [Localization.Lifting.iso, liftTgr, Functor.isoWhiskerRight_hom,
        Functor.whiskerRight_app, egrH, CategoryTheory.Quotient.natIsoLift_hom,
        CategoryTheory.Quotient.natTransLift_app]
      simp only [Iso.refl_inv, NatTrans.id_app, Category.comp_id]
      rfl
    let e : C ≅ (bQ R).obj ⟨K, hK⟩ := ObjectProperty.isoMk _ eC
    have hh := (eGr i).hom.naturality e.hom
    change (T ⋙ gr i).map e.hom ≫ (eGr i).hom.app ((bQ R).obj ⟨K, hK⟩) =
      (eGr i).hom.app C ≫ (S i).map
        ((homologyFunctor (ModuleCat.{u} R) (-i)).map eC.hom) at hh
    change (eGr i).hom.app C ≫ (S i).map
      ((homologyFunctor (ModuleCat.{u} R) (-i)).map eC.hom ≫
        (homologyFunctorFactors (ModuleCat.{u} R) (-i)).hom.app K) = _
    rw [(S i).map_comp, ← Category.assoc, ← hh, he]
    simp only [ec, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
      Category.assoc]
    erw [← (S i).map_comp, Iso.inv_hom_id_app, (S i).map_id, Category.comp_id]
    simp only [rep, Iso.trans_hom, Functor.mapIso_hom, (gr i).map_comp, Category.assoc]
    rfl
  · intro C C' K L hK hL eC eC' f
    let f' : (⟨K, hK⟩ : BComplex R) ⟶ ⟨L, hL⟩ := ObjectProperty.homMk f.hom
    have he : (CF.map f').hom = f := filtered_ext R (CFmap f')
    have hh := rep_map C C' ⟨K, hK⟩ ⟨L, hL⟩ eC eC' f'
    change T.map (ObjectProperty.homMk (eC.hom ≫ Q.map f.hom ≫ eC'.inv)) ≫
      (rep C' L hL eC').hom = (rep C K hK eC).hom ≫ Qf.map (CF.map f') at hh
    have he' : CF.map f' = ObjectProperty.homMk f := ObjectProperty.hom_ext _ he
    rw [he'] at hh
    exact hh
  · intro C C' K L M hK hL hM eC eC' s g hs f hf
    let MK : BComplex R := ⟨M, hM⟩
    let KK : BComplex R := ⟨K, hK⟩
    let LL : BComplex R := ⟨L, hL⟩
    let s' : MK ⟶ KK := ObjectProperty.homMk s.hom
    let g' : MK ⟶ LL := ObjectProperty.homMk g.hom
    have hcs : CF.map s' = ObjectProperty.homMk s := by
      apply ObjectProperty.hom_ext
      apply filtered_ext
      exact CFmap s'
    have hcg : CF.map g' = ObjectProperty.homMk g := by
      apply ObjectProperty.hom_ext
      apply filtered_ext
      exact CFmap g'
    let CM := (bQ R).obj MK
    let sd : CM ⟶ C := ObjectProperty.homMk (Q.map s.hom ≫ eC.inv)
    let gd : CM ⟶ C' := ObjectProperty.homMk (Q.map g.hom ≫ eC'.inv)
    have hsf : sd ≫ f = gd := by
      apply ObjectProperty.hom_ext
      change (Q.map s.hom ≫ eC.inv) ≫ f.hom = Q.map g.hom ≫ eC'.inv
      rw [hf]
      simp only [Category.assoc, eC.inv_hom_id_assoc, IsIso.hom_inv_id_assoc]
    have hsmap := rep_map CM C MK KK (Iso.refl _) eC s'
    have hgmap := rep_map CM C' MK LL (Iso.refl _) eC' g'
    simp only [Iso.refl_hom, Category.id_comp] at hsmap hgmap
    change T.map sd ≫ (rep C K hK eC).hom =
      (rep CM M hM (Iso.refl _)).hom ≫ Qf.map (CF.map s') at hsmap
    change T.map gd ≫ (rep C' L hL eC').hom =
      (rep CM M hM (Iso.refl _)).hom ≫ Qf.map (CF.map g') at hgmap
    rw [hcs] at hsmap
    rw [hcg] at hgmap
    have hsd : IsIso sd := by
      apply (ObjectProperty.isIso_hom_iff _).1
      change IsIso (Q.map s.hom ≫ eC.inv)
      infer_instance
    have hiso : IsIso (Qf.map (ObjectProperty.homMk s : CF.obj MK ⟶ CF.obj KK)) := by
      have hh : Qf.map (ObjectProperty.homMk s : CF.obj MK ⟶ CF.obj KK) =
          (rep CM M hM (Iso.refl _)).inv ≫ T.map sd ≫ (rep C K hK eC).hom := by
        erw [hsmap, Iso.inv_hom_id_assoc]
      rw [hh]
      infer_instance
    refine ⟨hiso, ?_⟩
    apply (cancel_epi (Qf.map (ObjectProperty.homMk s : CF.obj MK ⟶ CF.obj KK))).1
    have hsmap' : Qf.map (ObjectProperty.homMk s : CF.obj MK ⟶ CF.obj KK) ≫
        (rep C K hK eC).inv =
      (rep CM M hM (Iso.refl _)).inv ≫ T.map sd := by
      rw [← cancel_mono (rep C K hK eC).hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hsmap, Iso.inv_hom_id_assoc]
    rw [← Category.assoc _ (rep C K hK eC).inv, hsmap']
    simp only [Category.assoc]
    rw [← T.map_comp_assoc, hsf, hgmap, Iso.inv_hom_id_assoc]
    change Qf.map (ObjectProperty.homMk g : CF.obj MK ⟶ CF.obj LL) =
      Qf.map (ObjectProperty.homMk s : CF.obj MK ⟶ CF.obj KK) ≫
        inv (Qf.map (ObjectProperty.homMk s : CF.obj MK ⟶ CF.obj KK)) ≫
          Qf.map (ObjectProperty.homMk g : CF.obj MK ⟶ CF.obj LL)
    rw [IsIso.hom_inv_id_assoc]
  · intro C C' f
    exact (eOmega.hom.naturality f).symm
  · intro i C C' f
    exact ((eGr i).hom.naturality f).symm


end DerivedCategory
