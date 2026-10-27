module

public import Sheaf.CategoryTheory.ScalarLocalizationDerivedHom
public import Sheaf.CategoryTheory.ScalarLocalization
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Raw localization embedding of a bounded Hom-continuous full subcategory

Source: Bhatt–Scholze, The pro-étale topology for schemes, Proposition 6.8.14(2),
pp. 61–62, full faithfulness via Lemma 6.8.12
(blueprint: lem-per-bounded-hom-localization-embedding).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w x y vD vT

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace CategoryTheory

/-- The raw-functor clause, with unchanged objects, normalized on every fraction.
The equalities of objects only insert transports into the Hom formulas. The source
is the existing tensor-Hom category, with no idempotent completion.

Source: Bhatt–Scholze, Proposition 6.8.14(2), full-faithfulness assembly
(blueprint: lem-per-bounded-hom-localization-embedding). -/
def RawScalarLocalizationEmbedding (A : Type v) [CommRing A] (t : A)
    {D : Type x} [Category.{vD} D] [Preadditive D] [Linear A D]
    {T : Type y} [Category.{vT} T] [Preadditive T] [Linear (Localization.Away t) T]
    (F : D ⥤ T) (P : ObjectProperty D) : Prop :=
  ∃ (J : ScalarLocalization A P.FullSubcategory t ⥤ T)
    (hobj : ∀ K : P.FullSubcategory, J.obj ⟨K⟩ = F.obj K.obj),
    J.Additive ∧ J.Linear (Localization.Away t) ∧ J.Full ∧ J.Faithful ∧
    (∀ (K L : P.FullSubcategory) (f : K ⟶ L) (n : ℕ),
      eqToHom (hobj K).symm ≫
        J.map (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) ⊗ₜ[A] f) ≫
          eqToHom (hobj L) =
        (IsLocalization.Away.invSelf t : Localization.Away t) ^ n • F.map f.hom) ∧
    (∀ (K L : P.FullSubcategory)
      (z : (ScalarLocalization.localization A P.FullSubcategory t).obj K ⟶
        (ScalarLocalization.localization A P.FullSubcategory t).obj L),
      ∃ (f : K ⟶ L) (n : ℕ),
        z = ((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) ⊗ₜ[A] f) ∧
    (∀ K : P.FullSubcategory,
      eqToHom (hobj K).symm ≫
        J.map ((ScalarLocalization.localization A P.FullSubcategory t).map (𝟙 K)) ≫
          eqToHom (hobj K) = 𝟙 (F.obj K.obj)) ∧
    (∀ (K L M : P.FullSubcategory) (f : K ⟶ L) (g : L ⟶ M) (n m : ℕ),
      eqToHom (hobj K).symm ≫
        J.map ((((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) ⊗ₜ[A] f) ≫
          (((IsLocalization.Away.invSelf t : Localization.Away t) ^ m) ⊗ₜ[A] g)) ≫
            eqToHom (hobj M) =
        (IsLocalization.Away.invSelf t : Localization.Away t) ^ (m + n) •
          F.map (f.hom ≫ g.hom) ∧
      (IsLocalization.Away.invSelf t : Localization.Away t) ^ (m + n) •
          F.map (f.hom ≫ g.hom) =
        ((IsLocalization.Away.invSelf t : Localization.Away t) ^ n • F.map f.hom) ≫
          ((IsLocalization.Away.invSelf t : Localization.Away t) ^ m • F.map g.hom))

private def postcompLinearEquiv (S : Type v) [CommRing S]
    {D : Type x} [Category.{vD} D] [Preadditive D] [Linear S D]
    (K : D) {L M : D} (e : L ≅ M) : (K ⟶ L) ≃ₗ[S] (K ⟶ M) where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := by simp [Category.assoc]
  right_inv f := by simp [Category.assoc]
  map_add' f g := by simp only [Preadditive.add_comp]
  map_smul' a f := by simp only [Linear.smul_comp, RingHom.id_apply]

private theorem inversePower_eq_mk (A : Type v) [CommRing A] (t : A) (n : ℕ) :
    (IsLocalization.Away.invSelf t : Localization.Away t) ^ n =
      Localization.mk 1 (⟨t ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers t) := by
  rw [Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  rw [map_pow, ← mul_pow, mul_comm (IsLocalization.Away.invSelf t),
    IsLocalization.Away.mul_invSelf, one_pow, map_one]

private theorem tensor_is_fraction (A : Type v) [CommRing A] (t : A)
    (M : Type vD) [AddCommGroup M] [Module A M]
    (z : Localization.Away t ⊗[A] M) :
    ∃ (f : M) (n : ℕ),
      z = ((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) ⊗ₜ[A] f := by
  obtain ⟨x, rfl⟩ := (LocalizedModule.equivTensorProduct (Submonoid.powers t) M).surjective z
  induction x using LocalizedModule.induction_on with
  | _ f s =>
    obtain ⟨n, hn⟩ := s.property
    have hs : s = ⟨t ^ n, ⟨n, rfl⟩⟩ := Subtype.ext hn.symm
    subst s
    exact ⟨f, n, by rw [LocalizedModule.equivTensorProduct_apply_mk,
      inversePower_eq_mk]⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorHomEquivalences (A : Type v) [CommRing A] (t : A)
    {D : Type x} [Category.{vD} D] [Preadditive D] [Linear A D] [HasShift D ℤ]
    {T : Type y} [Category.{vD} T] [Preadditive T]
    [Linear (Localization.Away t) T] [HasShift T ℤ]
    (F : D ⥤ T) [F.CommShift ℤ] (P : ObjectProperty D)
    (h : scalarLocalizationHomComparison A t F P P) :
    ∃ e : ∀ K L : P.FullSubcategory,
      (Localization.Away t ⊗[A] (K ⟶ L)) ≃ₗ[Localization.Away t]
        (F.obj K.obj ⟶ F.obj L.obj),
      ∀ (K L : P.FullSubcategory) (a : Localization.Away t) (f : K ⟶ L),
        e K L (a ⊗ₜ[A] f) = a • F.map f.hom := by
  obtain ⟨e, he, _⟩ := h
  let g (K L : P.FullSubcategory) :
      (K ⟶ L) ≃ₗ[A] (K.obj ⟶ L.obj⟦(0 : ℤ)⟧) :=
    (InducedCategory.homLinearEquiv (R := A)).trans
      (postcompLinearEquiv A K.obj ((shiftFunctorZero D ℤ).app L.obj).symm)
  let E (K L : P.FullSubcategory) :
      (Localization.Away t ⊗[A] (K ⟶ L)) ≃ₗ[Localization.Away t]
        (F.obj K.obj ⟶ F.obj L.obj) := by
    let : Module (Localization.Away t)
        (LocalizedModule.Away t (K.obj ⟶ L.obj⟦(0 : ℤ)⟧)) :=
      LocalizedModule.moduleOfIsLocalization
        (S := Submonoid.powers t) (T := Localization.Away t)
    exact ((g K L).baseChange A (Localization.Away t) _ _).trans
      ((IsLocalizedModule.isBaseChange (Submonoid.powers t) (Localization.Away t)
        (LocalizedModule.mkLinearMap (Submonoid.powers t)
          (K.obj ⟶ L.obj⟦(0 : ℤ)⟧))).equiv.trans
        ((e K.obj K.property L.obj L.property 0).trans
          (postcompLinearEquiv (Localization.Away t) (F.obj K.obj)
            ((shiftFunctorZero T ℤ).app (F.obj L.obj)))))
  refine ⟨E, ?_⟩
  intro K L a f
  have h₁ : E K L (1 ⊗ₜ[A] f) = F.map f.hom := by
    let : Module (Localization.Away t)
        (LocalizedModule.Away t (K.obj ⟶ L.obj⟦(0 : ℤ)⟧)) :=
      LocalizedModule.moduleOfIsLocalization
        (S := Submonoid.powers t) (T := Localization.Away t)
    let b := IsLocalizedModule.isBaseChange (Submonoid.powers t) (Localization.Away t)
      (LocalizedModule.mkLinearMap (Submonoid.powers t) (K.obj ⟶ L.obj⟦(0 : ℤ)⟧))
    have hb := b.equiv_symm_apply (g K L f)
    simp only [E, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
    rw [← hb, LinearEquiv.apply_symm_apply]
    change e K.obj K.property L.obj L.property 0
      (LocalizedModule.mk (g K L f) 1) ≫ (shiftFunctorZero T ℤ).hom.app _ = _
    have hn := he K.obj K.property L.obj L.property 0 (g K L f) 0
    simp only [pow_zero, one_smul] at hn
    change e K.obj K.property L.obj L.property 0
      (LocalizedModule.mk (g K L f) 1) = _ at hn
    rw [hn, F.commShiftIso_zero, Functor.CommShift.isoZero_hom_app]
    change (F.map (f.hom ≫ (shiftFunctorZero D ℤ).inv.app L.obj) ≫
      F.map ((shiftFunctorZero D ℤ).hom.app L.obj) ≫
        (shiftFunctorZero T ℤ).inv.app (F.obj L.obj)) ≫
          (shiftFunctorZero T ℤ).hom.app (F.obj L.obj) = F.map f.hom
    simp only [Category.assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.id_obj]
    rw [Category.comp_id, ← F.map_comp, Category.assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.id_obj]
    rw [Category.comp_id]
  have ha : a ⊗ₜ[A] f = a • ((1 : Localization.Away t) ⊗ₜ[A] f) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [ha, map_smul, h₁]

private theorem rawEmbedding_of_tensorHom (A : Type v) [CommRing A] (t : A)
    {D : Type x} [Category.{vD} D] [Preadditive D] [Linear A D]
    {T : Type y} [Category.{vT} T] [Preadditive T] [Linear (Localization.Away t) T]
    (F : D ⥤ T) (P : ObjectProperty D)
    (e : ∀ K L : P.FullSubcategory,
      (Localization.Away t ⊗[A] (K ⟶ L)) ≃ₗ[Localization.Away t]
        (F.obj K.obj ⟶ F.obj L.obj))
    (he : ∀ (K L : P.FullSubcategory) (a : Localization.Away t) (f : K ⟶ L),
      e K L (a ⊗ₜ[A] f) = a • F.map f.hom) :
    RawScalarLocalizationEmbedding A t F P := by
  let G : ScalarLocalization A P.FullSubcategory t ⥤ T :=
    { obj K := F.obj K.obj.obj
      map {K L} f := e K.obj L.obj f
      map_id K := by
        change e K.obj K.obj (1 ⊗ₜ[A] 𝟙 K.obj) = 𝟙 _
        rw [he, ObjectProperty.FullSubcategory.id_hom, F.map_id, one_smul]
      map_comp {K L M} f g := by
        change e K.obj M.obj (ScalarLocalization.composition A P.FullSubcategory t
          K.obj L.obj M.obj g f) = e K.obj L.obj f ≫ e L.obj M.obj g
        induction g using TensorProduct.induction_on with
        | zero => simp
        | tmul b g =>
          induction f using TensorProduct.induction_on with
          | zero => simp
          | tmul a f =>
            rw [ScalarLocalization.composition_tmul, he, he, he,
              ObjectProperty.FullSubcategory.comp_hom, F.map_comp,
              Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm b a]
          | add f f' hf hf' => simp [map_add, hf, hf', Preadditive.add_comp]
        | add g g' hg hg' => simp [map_add, hg, hg', Preadditive.comp_add] }
  have : G.Additive := ⟨fun {K L} {f g} ↦ (e K.obj L.obj).map_add f g⟩
  have : G.Linear (Localization.Away t) :=
    ⟨fun {K L} f a ↦ (e K.obj L.obj).map_smul a f⟩
  have : G.Full := ⟨fun {K L} ↦ (e K.obj L.obj).surjective⟩
  have : G.Faithful := ⟨fun {K L} ↦ (e K.obj L.obj).injective⟩
  refine ⟨G, fun _ ↦ rfl, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ?_, ?_, ?_⟩
  · intro K L f n
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact he K L _ f
  · intro K L z
    exact tensor_is_fraction A t (K ⟶ L) z
  · intro K
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
      Functor.map_id]
    exact G.map_id _
  · intro K L M f g n m
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    constructor
    · change e K M (ScalarLocalization.composition A P.FullSubcategory t K L M
        (_ ⊗ₜ[A] g) (_ ⊗ₜ[A] f)) = _
      rw [ScalarLocalization.composition_tmul, he, ← pow_add,
        ObjectProperty.FullSubcategory.comp_hom]
    · rw [F.map_comp, Linear.smul_comp, Linear.comp_smul, smul_smul,
        ← pow_add, Nat.add_comm n m]

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- The actual exact scalar extension embeds the raw scalar localization of a full,
shift-stable, bounded-below Hom-continuous subcategory into the ambient derived category.
The first conjunct supplies localized shifted Hom equivalences with the fraction formula,
pre/postcomposition naturality and simultaneous integer-shift compatibility. The second
conjunct supplies the fully faithful localized-linear functor with the same degree-zero
fraction formula, identity and composition laws on every localized arrow.

Source: Bhatt–Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61–62
(blueprint: lem-per-bounded-hom-localization-embedding).

Proof:
1. Apply lem-weil-pbc-scalar-localization-derived-hom with the given site, coefficient
map, scalar and exact extension functor. The source continuity and target lower-bound
hypotheses are precisely hcontinuous and hbounded. Its derived construction fixes all
shift comparisons, giving the fraction-normalized equivalences in every integer degree.
2. Identify the raw tensor Hom with the localized module: send h tensor a/t^n to
ah/t^n, and h/t^n to h tensor t^(-n). Tensor balancing gives the first map. The fraction
relation t^k(t^m h - t^n h') = 0 gives equality of the second map's values after
multiplication by t^(-(k+n+m)). These maps are inverse; finite sums admit a common
power denominator. Use def-weil-module-base-change and def-weil-pbc-module-localization-away.
3. The comparison's naturality and simultaneous-shift equations give precomposition
by integral a, postcomposition by integral b and simultaneous shifts by any r.
Shift stability keeps the shifted objects in the full subcategory. Each equation
sends f/t^n to t^(-n) F(f), using the specified shift comparison in degree q.
4. Set J(QK) = FK and take its Hom map from the degree-zero comparison and step 2.
Functoriality and bilinearity give J(1/1) = 1 and
J((g/t^m) composed with (f/t^n)) = t^(-(m+n)) F(gf)
= (t^(-m) F(g)) composed with (t^(-n) F(f)). Step 2 covers every arrow.
The Hom maps are localized-linear bijections, so J is linear, full and faithful.
No essential-surjectivity assertion is used. -/
theorem boundedHomLocalizationEmbedding (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A)
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))))]
    (E : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))))
    (hE : ∀ M, E.obj M =
      SheafOfModules.changeOfRings (ringedLocalizationRingUnit R (a t)) M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hE M) ≫
      SheafOfModules.changeOfRingsHom (ringedLocalizationRingUnit R (a t)) M f ≫
        eqToHom (hE N).symm)
    [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (P : ObjectProperty (DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))))
    (hshift : ∀ (K : DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))),
      P K → ∀ r : ℤ, P (K⟦r⟧))
    (hbounded : ∀ K, P K → ∃ b : ℤ, K.IsGE b)
    (hcontinuous : ∀ K, P K → DerivedCategory.CountableBoundedBelowHomContinuous K) :
    (fun [_iA : Linear A (DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))]
      [_iT : Linear (Localization.Away t) (DerivedCategory
        (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRing R (a t)))))] ↦
      scalarLocalizationHomComparison A t E.mapDerivedCategory P P ∧
        RawScalarLocalizationEmbedding A t E.mapDerivedCategory P)
      (_iA := scalarLocalizationDerivedLinear A R a)
      (_iT := scalarLocalizationDerivedLinear (Localization.Away t)
        (ringedLocalizationRing R (a t)) (scalarLocalizationCoefficientMap A R a t)) := by
  classical
  let : Linear A (DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :=
    scalarLocalizationDerivedLinear A R a
  let : Linear (Localization.Away t) (DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))))) :=
    scalarLocalizationDerivedLinear (Localization.Away t)
      (ringedLocalizationRing R (a t)) (scalarLocalizationCoefficientMap A R a t)
  change scalarLocalizationHomComparison A t E.mapDerivedCategory P P ∧
    RawScalarLocalizationEmbedding A t E.mapDerivedCategory P
  have hc : scalarLocalizationHomComparison A t E.mapDerivedCategory P P := by
    obtain ⟨e, hn, hnat, hid, hcomp, hs⟩ :=
      scalarLocalization_derivedHom A R a t E hE hmap
    refine ⟨fun K hK L hL q ↦ e K (hcontinuous K hK) L (hbounded L hL) q,
      ?_, ?_, ?_, ?_, ?_⟩
    · intros; apply hn
    · intros; apply hnat
    · intros; apply hid
    · intros; apply hcomp
    · intro K hK L hL p q hKq hLq f n
      exact hs K (hcontinuous K hK) L (hbounded L hL) p q
        (hcontinuous _ (hshift K hK q)) (hbounded _ (hshift L hL q)) f n
  refine ⟨hc, ?_⟩
  obtain ⟨e, he⟩ := tensorHomEquivalences A t E.mapDerivedCategory P hc
  exact rawEmbedding_of_tensorHom A t E.mapDerivedCategory P e he

end CategoryTheory
