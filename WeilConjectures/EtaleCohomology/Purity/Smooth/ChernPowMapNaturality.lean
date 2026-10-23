/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.HyperplaneClass

/-!
# Naturality of the map of the projective bundle formula

The component `chernPowMap q h a : Λ_S(-a)[-2a] ⟶ Rq_* Λ_P` of the map of the projective bundle
formula is the adjoint of a morphism `chernPowAdj q h a : Lq^* (Λ_S(-a)[-2a]) ⟶ Λ_P`. For a
morphism `f : X ⟶ Y` over `S`, its formation commutes with pullback along `f`
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_chernPowAdj`), hence

`chernPowMap (f ≫ q) (f^* h) a = chernPowMap q h a ≫ Rq_* (Λ_Y ⟶ Rf_* Λ_X)`

(`AlgebraicGeometry.Etale.chernPowMap_comp`). In particular the projective space formula is
invariant under isomorphisms over `S` (`AlgebraicGeometry.Etale.projectiveFormula_of_equiv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] {F : C ⥤ D} {G : D ⥤ C}
  {F' : D ⥤ E} {G' : E ⥤ D} {F'' : C ⥤ E} {G'' : E ⥤ C}

/-- Transposition along adjunctions `F ⊣ G`, `F' ⊣ G'` and `F'' ⊣ G''` with `F'' ≅ F ⋙ F'`:
the transpose of `F'' A ≅ F' F A ⟶ F' B ⟶ Z` is the transpose `A ⟶ G B` of `F A ⟶ B` followed
by `G` of the transpose `B ⟶ G' Z` of `F' B ⟶ Z` and the conjugate isomorphism
`G G' Z ≅ G'' Z`. -/
lemma homEquiv_conjugateIsoEquiv (adj : F ⊣ G) (adj' : F' ⊣ G') (adj'' : F'' ⊣ G'')
    (φ : F'' ≅ F ⋙ F') {A : C} {B : D} {Z : E} (x : F.obj A ⟶ B) (y : F'.obj B ⟶ Z) :
    adj''.homEquiv A Z (φ.hom.app A ≫ F'.map x ≫ y) =
      adj.homEquiv A B x ≫ G.map (adj'.homEquiv B Z y) ≫
        (conjugateIsoEquiv (adj.comp adj') adj'' φ).hom.app Z := by
  have hu := unit_conjugateEquiv (adj.comp adj') adj'' φ.hom A
  have hn := (conjugateIsoEquiv (adj.comp adj') adj'' φ).hom.naturality (F'.map x ≫ y)
  have hx := adj'.unit.naturality x
  rw [comp_unit_app] at hu
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at hn hx
  rw [homEquiv_unit, homEquiv_unit, homEquiv_unit, Functor.map_comp, Functor.map_comp,
    Functor.map_comp, ← Functor.map_comp_assoc G x, hx, Functor.map_comp, Category.assoc,
    ← Functor.map_comp_assoc G' (F'.map x), reassoc_of% hn]
  simp only [Category.assoc]
  rw [← reassoc_of% hu, Functor.map_comp]
  rfl

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

open Scheme

namespace Etale

open ProjectiveSpace

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasKummerClass Λ]

section Unit

variable {X Y : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

omit [Finite Λ] in
/-- The unit class `Λ_Y ≅ Λ_Y(0)[0]` is compatible with pullback. -/
@[reassoc]
lemma leftDerivedUpperStar_map_tateObjectShiftZeroIso'_hom (f : X ⟶ Y) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (tateObjectShiftZeroIso' (Λ := Λ) (X := Y)).hom ≫
        (leftDerivedUpperStarTateShiftIso Λ f 0).hom =
      (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
        (tateObjectShiftZeroIso' (Λ := Λ) (X := X)).hom := by
  rw [← cancel_epi (leftDerivedUpperStarConstantComplexIso Λ f).inv, Iso.inv_hom_id_assoc]
  simp only [tateObjectShiftZeroIso', Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    leftDerivedUpperStarTateShiftIso, Functor.mapIso_hom]
  exact leftDerivedUpperStarConstantComplexIso_inv_comp_map_twistObjectZeroIso_inv Λ f (by simp)

omit [Finite Λ] in
/-- The isomorphism `Λ_X(m + -m)[2(m + -m)] ≅ Λ_X` is the unit class `Λ_X(0)[0] ≅ Λ_X` up to the
equation `m + -m = 0`. -/
lemma tateObjectShiftAddNegIso_eq (m : ℤ) :
    tateObjectShiftAddNegIso (Λ := Λ) (X := X) m =
      eqToIso (by rw [add_neg_cancel]) ≪≫ (tateObjectShiftZeroIso' (Λ := Λ) (X := X)).symm := by
  have key (k : ℤ) (hk : k = 0) (h₁ : 2 * k = 0)
      (h₂ : (shiftFunctor (_root_.DerivedCategory
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) 0).obj (tateObject Λ X k) =
          HasTateTwist.twistObject X 0)
      (h₃ : (tateObject Λ X k)⟦2 * k⟧ = (tateObject Λ X 0)⟦2 * (0 : ℤ)⟧) :
      (shiftFunctorZero' _ (2 * k) h₁).app _ ≪≫ eqToIso h₂ ≪≫
          HasTateTwist.twistObjectZeroIso X =
        eqToIso h₃ ≪≫ (tateObjectShiftZeroIso' (Λ := Λ) (X := X)).symm := by
    subst hk
    ext
    simp [tateObjectShiftZeroIso', tateObject]
  exact key _ (add_neg_cancel m) _ _ _

omit [Finite Λ] in
/-- The isomorphism `Λ(m + -m)[2(m + -m)] ≅ Λ` is compatible with pullback. -/
lemma leftDerivedUpperStar_map_tateObjectShiftAddNegIso_hom (f : X ⟶ Y) (m : ℤ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (tateObjectShiftAddNegIso (Λ := Λ) (X := Y) m).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ f).hom =
      (leftDerivedUpperStarTateShiftIso Λ f (m + -m)).hom ≫
        (tateObjectShiftAddNegIso (Λ := Λ) (X := X) m).hom := by
  rw [tateObjectShiftAddNegIso_eq, tateObjectShiftAddNegIso_eq]
  simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (leftDerivedUpperStar_map_eqToHom_tateObjectShift f (add_neg_cancel m)
    (by rw [add_neg_cancel]) (by rw [add_neg_cancel]))]
  congr 1
  rw [← cancel_mono (tateObjectShiftZeroIso' (Λ := Λ) (X := X)).hom, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← leftDerivedUpperStar_map_tateObjectShiftZeroIso'_hom, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

omit [Finite Λ] in
/-- Pullback of the inverse of the left unitor of the derived tensor product. -/
@[reassoc]
lemma leftDerivedUpperStar_map_derivedTensorLeftUnitor_inv (f : X ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) Y K).inv ≫
        (leftDerivedUpperStarTensorIso _ f _ K).hom =
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X _).inv ≫
        derivedTensorHom _ (leftDerivedUpperStarConstantComplexIso Λ f).inv (𝟙 _) := by
  have h : (leftDerivedUpperStarTensorIso _ f _ K).hom ≫
      derivedTensorHom _ (leftDerivedUpperStarConstantComplexIso Λ f).hom (𝟙 _) ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X _).hom =
      (L((f)^*[ModuleCat.{u + 1} Λ])).map (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) Y K).hom := by
    rw [leftDerivedUpperStar_map_derivedTensorLeftUnitor_hom, derivedTensorHom,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  calc _ = (L((f)^*[ModuleCat.{u + 1} Λ])).map
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) Y K).inv ≫
        ((leftDerivedUpperStarTensorIso _ f _ K).hom ≫
          derivedTensorHom _ (leftDerivedUpperStarConstantComplexIso Λ f).hom (𝟙 _) ≫
            (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X _).hom) ≫
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X _).inv ≫
            derivedTensorHom _ (leftDerivedUpperStarConstantComplexIso Λ f).inv (𝟙 _) := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, derivedTensorHom_comp, Iso.hom_inv_id,
          Category.comp_id, derivedTensorHom_id]
    _ = _ := by
        rw [h, ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
          Category.id_comp]

/-- **Cup product with a class and the unit class commute with pullback**: for
`x ∈ H^{2m}(Y, Λ(m))`, the map `Λ(-m)[-2m] ≅ Λ ⊗ Λ(-m)[-2m] ⟶ Λ(m)[2m] ⊗ Λ(-m)[-2m] ≅ Λ`
(cup product with `x`) pulls back along `f` to the corresponding map for `f^* x`. -/
lemma leftDerivedUpperStar_map_cupTateShift (f : X ⟶ Y) (m : ℤ)
    (x : constantComplex Λ Y ⟶ (tateObject Λ Y m)⟦2 * m⟧) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) Y _).inv ≫
          ((derivedTensor (ModuleCat.{u + 1} Λ) Y).map x).app _ ≫
          (shiftTateObjectAddIso Λ Y m (-m)).hom ≫
          (tateObjectShiftAddNegIso m).hom) ≫
        (leftDerivedUpperStarConstantComplexIso Λ f).hom =
      (leftDerivedUpperStarTateShiftIso Λ f (-m)).hom ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X _).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
          ((leftDerivedUpperStarConstantComplexIso Λ f).inv ≫
            (L((f)^*[ModuleCat.{u + 1} Λ])).map x ≫
            (leftDerivedUpperStarTateShiftIso Λ f m).hom)).app _ ≫
        (shiftTateObjectAddIso Λ X m (-m)).hom ≫
        (tateObjectShiftAddNegIso m).hom := by
  have hx (Z : Scheme.{u})
      {K K₁ M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (y : K ⟶ K₁) :
      ((derivedTensor (ModuleCat.{u + 1} Λ) Z).map y).app M = derivedTensorHom _ y (𝟙 M) := by
    simp [derivedTensorHom]
  have hy (Z : Scheme.{u})
      {K M M₁ : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (g : M ⟶ M₁) :
      ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj K).map g = derivedTensorHom _ (𝟙 K) g := by
    simp [derivedTensorHom]
  have hλ := (derivedTensorLeftUnitorNatIso (ModuleCat.{u + 1} Λ) X).inv.naturality
    (leftDerivedUpperStarTateShiftIso Λ f (-m)).hom
  simp only [derivedTensorLeftUnitorNatIso, NatIso.ofComponents_inv_app, Functor.id_map] at hλ
  simp only [Functor.map_comp, Category.assoc,
    leftDerivedUpperStar_map_tateObjectShiftAddNegIso_hom]
  rw [reassoc_of% (leftDerivedUpperStar_map_shiftTateObjectAddIso Λ f m (-m))]
  simp only [hx]
  rw [leftDerivedUpperStarTensorIso_hom_naturality_assoc,
    leftDerivedUpperStar_map_derivedTensorLeftUnitor_inv_assoc, reassoc_of% hλ]
  simp only [hy, derivedTensorHom_comp_assoc, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Category.assoc]

end Unit

section Adjoint

variable {S P : Scheme.{u}} [HasInvertibleExponent Λ S] [HasInvertibleExponent Λ P]

/-- The adjoint `Lq^*(Λ_S(-a)[-2a]) ⟶ Λ_P` of the component `chernPowMap q h a` of the map of the
projective bundle formula: `Lq^*(Λ_S(-a)[-2a]) ≅ Λ ⊗ Λ(-a)[-2a] ⟶ Λ(a)[2a] ⊗ Λ(-a)[-2a] ≅ Λ`,
the middle map being `hᵃ ⊗ 1`. -/
noncomputable def chernPowAdj (q : P ⟶ S)
    (h : constantComplex Λ P ⟶ (tateObject Λ P 1)⟦2 * (1 : ℤ)⟧) (a : ℕ) :
    (L((q)^*[ModuleCat.{u + 1} Λ])).obj ((tateObject Λ S (-(a : ℤ)))⟦2 * (-(a : ℤ))⟧) ⟶
      constantComplex Λ P :=
  (leftDerivedUpperStarTateShiftIso Λ q (-(a : ℤ))).hom ≫
    (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) P _).inv ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) P).map (chernPow h a)).app _ ≫
    (shiftTateObjectAddIso Λ P a (-(a : ℤ))).hom ≫
    (tateObjectShiftAddNegIso (a : ℤ)).hom

lemma chernPowMap_eq_homEquiv (q : P ⟶ S)
    (h : constantComplex Λ P ⟶ (tateObject Λ P 1)⟦2 * (1 : ℤ)⟧) (a : ℕ) :
    chernPowMap q h a =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).homEquiv _ _
        (chernPowAdj q h a) :=
  rfl

end Adjoint

section Naturality

variable {X Y S : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]
  [HasInvertibleExponent Λ S]

/-- The composite of derived direct images `Rq_* ∘ Rf_* ≅ R(f ≫ q)_*`, conjugate to
`L(f ≫ q)^* ≅ Lf^* ∘ Lq^*`. -/
noncomputable def rightDerivedLowerStarCompIso (f : X ⟶ Y) (q : Y ⟶ S) (c : X ⟶ S)
    (hc : c = f ≫ q) :
    R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ R((q)_*[ModuleCat.{u + 1} Λ]) ≅
      R((c)_*[ModuleCat.{u + 1} Λ]) :=
  conjugateIsoEquiv ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f q c hc)

/-- **The adjoint of the projective bundle map commutes with pullback**: for `f : X ⟶ Y` and
`q : Y ⟶ S`, `Lf^*` of `chernPowAdj q h a` is `chernPowAdj (f ≫ q) (f^* h) a`, through
`L(f ≫ q)^* ≅ Lf^* Lq^*` and `Lf^* Λ_Y ≅ Λ_X`. -/
theorem leftDerivedUpperStar_map_chernPowAdj (f : X ⟶ Y) (q : Y ⟶ S) (c : X ⟶ S)
    (hc : c = f ≫ q) (h : constantComplex Λ Y ⟶ (tateObject Λ Y 1)⟦2 * (1 : ℤ)⟧) (a : ℕ) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f q c hc).hom.app _ ≫
        (L((f)^*[ModuleCat.{u + 1} Λ])).map (chernPowAdj q h a) ≫
        (leftDerivedUpperStarConstantComplexIso Λ f).hom =
      chernPowAdj c (VectorBundle.classRestriction Λ (r := 1) f h) a := by
  have ih := classRestriction_chernPow f h a
  rw [chernPowAdj, chernPowAdj, ← ih, VectorBundle.classRestriction,
    leftDerivedUpperStarTateShiftIso_comp Λ f q c hc,
    Functor.map_comp (L((f)^*[ModuleCat.{u + 1} Λ])) (leftDerivedUpperStarTateShiftIso Λ q _).hom,
    Category.assoc, leftDerivedUpperStar_map_cupTateShift]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]

/-- **Naturality of the projective bundle map**: for `f : X ⟶ Y` and `q : Y ⟶ S`,

`chernPowMap (f ≫ q) (f^* h) a = chernPowMap q h a ≫ Rq_*(Λ_Y ⟶ Rf_* Λ_X)`

through `Rq_* Rf_* ≅ R(f ≫ q)_*`. -/
theorem chernPowMap_comp (f : X ⟶ Y) (q : Y ⟶ S) (c : X ⟶ S) (hc : c = f ≫ q)
    (h : constantComplex Λ Y ⟶ (tateObject Λ Y 1)⟦2 * (1 : ℤ)⟧) (a : ℕ) :
    chernPowMap c (VectorBundle.classRestriction Λ (r := 1) f h) a =
      chernPowMap q h a ≫ (R((q)_*[ModuleCat.{u + 1} Λ])).map (constantComplexUnit Λ f) ≫
        (rightDerivedLowerStarCompIso f q c hc).hom.app (constantComplex Λ X) := by
  rw [chernPowMap_eq_homEquiv, chernPowMap_eq_homEquiv,
    ← leftDerivedUpperStar_map_chernPowAdj f q c hc h a,
    Adjunction.homEquiv_conjugateIsoEquiv,
    Adjunction.homEquiv_unit (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)]
  rfl

/-- Naturality of the map of the projective bundle formula
(`AlgebraicGeometry.Etale.chernPowMap_comp`). -/
theorem projectiveFormulaMap_comp (f : X ⟶ Y) (q : Y ⟶ S) (c : X ⟶ S) (hc : c = f ≫ q)
    (h : constantComplex Λ Y ⟶ (tateObject Λ Y 1)⟦2 * (1 : ℤ)⟧) (r : ℕ) :
    projectiveFormulaMap c (VectorBundle.classRestriction Λ (r := 1) f h) r =
      projectiveFormulaMap q h r ≫ (R((q)_*[ModuleCat.{u + 1} Λ])).map (constantComplexUnit Λ f) ≫
        (rightDerivedLowerStarCompIso f q c hc).hom.app (constantComplex Λ X) := by
  refine biproduct.hom_ext' _ _ fun a ↦ ?_
  simp only [projectiveFormulaMap, biproduct.ι_desc, biproduct.ι_desc_assoc]
  exact chernPowMap_comp f q c hc h a

/-- For an isomorphism `f`, the unit `Λ_Y ⟶ Rf_* Λ_X` is an isomorphism. -/
theorem isIso_constantComplexUnit_of_isIso (f : X ⟶ Y) [IsIso f] :
    IsIso (constantComplexUnit Λ f) := by
  have hid : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 Y)).unit.app
      (constantComplex Λ Y)) := by
    obtain ⟨e⟩ := nonempty_leftDerivedUpperStar_id_iso Λ Y (𝟙 Y) rfl
    have : (L((𝟙 Y)^*[ModuleCat.{u + 1} Λ])).Full := Functor.Full.of_iso e.symm
    have : (L((𝟙 Y)^*[ModuleCat.{u + 1} Λ])).Faithful := Functor.Faithful.of_iso e.symm
    infer_instance
  have := isIso_unit_app_comp_of_isIso Λ f (𝟙 Y) _ hid
  rw [Category.comp_id] at this
  rw [constantComplexUnit]
  infer_instance

/-- The projective bundle formula is invariant under isomorphisms over the base. -/
theorem isIso_projectiveFormulaMap_comp_iff (f : X ⟶ Y) [IsIso f] (q : Y ⟶ S) (c : X ⟶ S)
    (hc : c = f ≫ q) (h : constantComplex Λ Y ⟶ (tateObject Λ Y 1)⟦2 * (1 : ℤ)⟧) (r : ℕ) :
    IsIso (projectiveFormulaMap c (VectorBundle.classRestriction Λ (r := 1) f h) r) ↔
      IsIso (projectiveFormulaMap q h r) := by
  have := isIso_constantComplexUnit_of_isIso (Λ := Λ) f
  rw [projectiveFormulaMap_comp f q c hc h r]
  exact isIso_comp_right_iff _ _

end Naturality

variable {S : Scheme.{u}} [HasInvertibleExponent Λ S]

variable [HasKummerClass.IsNormalized Λ] {k : Type u} [Field k] (aS : S ⟶ Spec (.of k))
  [IsSeparated aS] [LocallyOfFiniteType aS]

include aS in
/-- *Invariance under renaming the coordinates* of the projective-space formula: an equivalence
`e : n ≃ n'` induces an isomorphism `ℙ(Option n; S) ≅ ℙ(Option n'; S)` over `S` along which the
first Chern class of the hyperplane class restricts to that of the hyperplane class
(`AlgebraicGeometry.Etale.classRestriction_reindex_hyperplaneChernClass`), and the projective
bundle map is natural (`AlgebraicGeometry.Etale.isIso_projectiveFormulaMap_comp_iff`). -/
lemma projectiveFormula_of_equiv {n n' : Type u} [Fintype n] [Fintype n'] (e : n ≃ n')
    (h : ProjectiveFormula Λ S n) : ProjectiveFormula Λ S n' := by
  intro γ hγ
  have : IsIso (reindexHom S (Equiv.optionCongr e)) :=
    (reindexIso S (Equiv.optionCongr e)).isIso_hom
  rw [eq_hyperplaneClass aS hγ, ← Fintype.card_congr e,
    ← isIso_projectiveFormulaMap_comp_iff (reindexHom S (Equiv.optionCongr e))
      (ℙ(Option n'; S) ↘ S) (ℙ(Option n; S) ↘ S) (reindexHom_over S _).symm,
    classRestriction_reindex_hyperplaneChernClass aS e]
  exact h _ (isHyperplaneClass_hyperplaneClass aS)

end Etale

end AlgebraicGeometry
