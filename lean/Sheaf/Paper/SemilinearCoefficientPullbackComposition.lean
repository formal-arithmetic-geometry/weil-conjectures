/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z8
-/
module

public import Sheaf.Paper.SemilinearGeometryDerived
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Composition of normalized coefficient pullback squares

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03CZ and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits

section Mates

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type*}
  [Category X₀] [Category X₁] [Category X₂]
  [Category Y₀] [Category Y₁] [Category Y₂]
  {Lh : X₁ ⥤ X₀} {Lk : X₂ ⥤ X₁} {Lc : X₂ ⥤ X₀}
  {Rh : X₀ ⥤ X₁} {Rk : X₁ ⥤ X₂} {Rc : X₀ ⥤ X₂}
  {lh : Y₁ ⥤ Y₀} {lk : Y₂ ⥤ Y₁} {lc : Y₂ ⥤ Y₀}
  {rh : Y₀ ⥤ Y₁} {rk : Y₁ ⥤ Y₂} {rc : Y₀ ⥤ Y₂}
  (ah : Lh ⊣ Rh) (ak : Lk ⊣ Rk) (ac : Lc ⊣ Rc)
  (bh : lh ⊣ rh) (bk : lk ⊣ rk) (bc : lc ⊣ rc)
  (F₀ : X₀ ⥤ Y₀) (F₁ : X₁ ⥤ Y₁) (F₂ : X₂ ⥤ Y₂)
  (a : Lk ⋙ Lh ≅ Lc) (b : lk ⋙ lh ≅ lc)
  (d : Rh ⋙ Rk ≅ Rc) (e : rh ⋙ rk ≅ rc)
  (ch : Lh ⋙ F₀ ≅ F₁ ⋙ lh) (ck : Lk ⋙ F₁ ≅ F₂ ⋙ lk)
  (cc : Lc ⋙ F₀ ≅ F₂ ⋙ lc)
  (sh : Rh ⋙ F₁ ≅ F₀ ⋙ rh) (sk : Rk ⋙ F₂ ≅ F₁ ⋙ rk)
  (sc : Rc ⋙ F₂ ≅ F₀ ⋙ rc)

private theorem mate_composition
    (ha : ∀ P Q (f : Lc.obj P ⟶ Q),
      ak.homEquiv _ _ (ah.homEquiv _ _ (a.hom.app P ≫ f)) =
        ac.homEquiv _ _ f ≫ d.inv.app Q)
    (hb : ∀ P Q (f : lc.obj P ⟶ Q),
      bk.homEquiv _ _ (bh.homEquiv _ _ (b.hom.app P ≫ f)) =
        bc.homEquiv _ _ f ≫ e.inv.app Q)
    (hh : ∀ P, bh.homEquiv _ _ (ch.inv.app P) =
      F₁.map (ah.unit.app P) ≫ sh.hom.app (Lh.obj P))
    (hk : ∀ P, bk.homEquiv _ _ (ck.inv.app P) =
      F₂.map (ak.unit.app P) ≫ sk.hom.app (Lk.obj P))
    (hc : ∀ P, bc.homEquiv _ _ (cc.inv.app P) =
      F₂.map (ac.unit.app P) ≫ sc.hom.app (Lc.obj P))
    (hs : ∀ Q, F₂.map (d.hom.app Q) ≫ sc.hom.app Q =
      sk.hom.app (Rh.obj Q) ≫ rk.map (sh.hom.app Q) ≫ e.hom.app (F₀.obj Q))
    (P : X₂) :
    F₀.map (a.hom.app P) ≫ cc.hom.app P =
      ch.hom.app (Lk.obj P) ≫ lh.map (ck.hom.app P) ≫ b.hom.app (F₂.obj P) := by
  dsimp only [Functor.comp_obj] at hh hk hc
  have hi : b.hom.app (F₂.obj P) ≫ cc.inv.app P =
      lh.map (ck.inv.app P) ≫ ch.inv.app (Lk.obj P) ≫ F₀.map (a.hom.app P) := by
    apply (bh.homEquiv _ _).injective
    apply (bk.homEquiv _ _).injective
    rw [hb]
    dsimp only [Functor.comp_obj]
    rw [hc]
    rw [bh.homEquiv_naturality_left, bh.homEquiv_naturality_right]
    rw [hh, bk.homEquiv_naturality_right, hk]
    simp only [Functor.map_comp, Category.assoc]
    have hη := sk.hom.naturality (ah.unit.app (Lk.obj P))
    have hα := sh.hom.naturality (a.hom.app P)
    have hβ := sk.hom.naturality (Rh.map (a.hom.app P))
    dsimp only [Functor.comp_map, Functor.comp_obj] at hη hα hβ
    rw [← reassoc_of% hη, ← rk.map_comp, ← hα]
    simp only [Functor.map_comp]
    rw [← reassoc_of% hβ]
    simp only [← Functor.map_comp_assoc]
    have hu := ha P (Lc.obj P) (𝟙 _)
    simp only [Adjunction.homEquiv_apply, Category.comp_id, CategoryTheory.Functor.map_id,
      Functor.map_comp, Category.assoc] at hu
    erw [Category.id_comp] at hu
    rw [hu]
    simp only [Functor.map_comp, Category.assoc]
    apply congrArg (F₂.map (ac.unit.app P) ≫ ·)
    apply (cancel_mono (e.hom.app (F₀.obj (Lc.obj P)))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← hs]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  apply (cancel_mono (cc.inv.app P)).mp
  apply (cancel_epi (ch.inv.app (Lk.obj P))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app]
  rw [hi, ← lh.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [lh.map_id]
  simp only [Category.id_comp, Category.comp_id, Iso.inv_hom_id_app_assoc]

end Mates

section Localization

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategoryFactors

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type*}
  [Category X₀] [Category X₁] [Category X₂]
  [Category Y₀] [Category Y₁] [Category Y₂]
  [Abelian X₀] [Abelian X₁] [Abelian X₂]
  [Abelian Y₀] [Abelian Y₁] [Abelian Y₂]
  [HasDerivedCategory X₀] [HasDerivedCategory X₁] [HasDerivedCategory X₂]
  [HasDerivedCategory Y₀] [HasDerivedCategory Y₁] [HasDerivedCategory Y₂]

private theorem square_fac {R : X₀ ⥤ X₁} {S : Y₀ ⥤ Y₁}
    {F : X₀ ⥤ Y₀} {G : X₁ ⥤ Y₁}
    [R.Additive] [S.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : R ⋙ G ≅ F ⋙ S) (P : CochainComplex X₀ ℤ) :
    (Functor.mapDerivedCategorySquareIso a).hom.app (DerivedCategory.Q.obj P) ≫
        S.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        S.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app P) := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso R G).hom.app
    (DerivedCategory.Q.obj P))).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]

private theorem composition_fac {R : X₀ ⥤ X₁} {S : X₁ ⥤ X₂} {T : X₀ ⥤ X₂}
    [R.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (a : R ⋙ S ≅ T) (P : CochainComplex X₀ ℤ) :
    ((Functor.mapDerivedCategoryCompIso R S).symm ≪≫
        Functor.mapDerivedCategoryNatIso a).hom.app (DerivedCategory.Q.obj P) ≫
        T.mapDerivedCategoryFactors.hom.app P =
      S.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app P) ≫
        S.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app P) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso R S).hom.app
    (DerivedCategory.Q.obj P))).mp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [Functor.mapDerivedCategoryNatIso_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]

variable (Rh : X₀ ⥤ X₁) (Rk : X₁ ⥤ X₂) (Rc : X₀ ⥤ X₂)
  (rh : Y₀ ⥤ Y₁) (rk : Y₁ ⥤ Y₂) (rc : Y₀ ⥤ Y₂)
  (F₀ : X₀ ⥤ Y₀) (F₁ : X₁ ⥤ Y₁) (F₂ : X₂ ⥤ Y₂)
  [Rh.Additive] [Rk.Additive] [Rc.Additive]
  [rh.Additive] [rk.Additive] [rc.Additive]
  [F₀.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits Rh] [PreservesFiniteColimits Rh]
  [PreservesFiniteLimits Rk] [PreservesFiniteColimits Rk]
  [PreservesFiniteLimits Rc] [PreservesFiniteColimits Rc]
  [PreservesFiniteLimits rh] [PreservesFiniteColimits rh]
  [PreservesFiniteLimits rk] [PreservesFiniteColimits rk]
  [PreservesFiniteLimits rc] [PreservesFiniteColimits rc]
  [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]

private theorem localized_composition
    (d : Rh ⋙ Rk ≅ Rc) (e : rh ⋙ rk ≅ rc)
    (sh : Rh ⋙ F₁ ≅ F₀ ⋙ rh) (sk : Rk ⋙ F₂ ≅ F₁ ⋙ rk)
    (sc : Rc ⋙ F₂ ≅ F₀ ⋙ rc)
    (hs : ∀ Q, F₂.map (d.hom.app Q) ≫ sc.hom.app Q =
      sk.hom.app (Rh.obj Q) ≫ rk.map (sh.hom.app Q) ≫ e.hom.app (F₀.obj Q))
    (P : DerivedCategory X₀) :
    F₂.mapDerivedCategory.map
        (((Functor.mapDerivedCategoryCompIso Rh Rk).symm ≪≫
          Functor.mapDerivedCategoryNatIso d).hom.app P) ≫
        (Functor.mapDerivedCategorySquareIso sc).hom.app P =
      (Functor.mapDerivedCategorySquareIso sk).hom.app (Rh.mapDerivedCategory.obj P) ≫
        rk.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso sh).hom.app P) ≫
        ((Functor.mapDerivedCategoryCompIso rh rk).symm ≪≫
          Functor.mapDerivedCategoryNatIso e).hom.app (F₀.mapDerivedCategory.obj P) := by
  let dD := (Functor.mapDerivedCategoryCompIso Rh Rk).symm ≪≫
    Functor.mapDerivedCategoryNatIso d
  let eD := (Functor.mapDerivedCategoryCompIso rh rk).symm ≪≫
    Functor.mapDerivedCategoryNatIso e
  have heq : Functor.whiskerRight dD.hom F₂.mapDerivedCategory ≫
        (Functor.mapDerivedCategorySquareIso sc).hom =
      Functor.whiskerLeft Rh.mapDerivedCategory (Functor.mapDerivedCategorySquareIso sk).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategorySquareIso sh).hom rk.mapDerivedCategory ≫
        Functor.whiskerLeft F₀.mapDerivedCategory eD.hom := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso X₀ (.up ℤ))
    intro Q
    let Q₀ := (F₀.mapHomologicalComplex (.up ℤ)).obj Q
    let Qh := (Rh.mapHomologicalComplex (.up ℤ)).obj Q
    apply (cancel_mono (rc.mapDerivedCategory.map (F₀.mapDerivedCategoryFactors.hom.app Q) ≫
      rc.mapDerivedCategoryFactors.hom.app Q₀)).mp
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc]
    rw [square_fac sc Q]
    have hn := eD.hom.naturality (F₀.mapDerivedCategoryFactors.hom.app Q)
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn, composition_fac e Q₀]
    rw [← rk.mapDerivedCategory.map_comp_assoc,
      ← rk.mapDerivedCategory.map_comp_assoc]
    simp only [Category.assoc]
    erw [square_fac sh Q]
    simp only [Functor.map_comp, Category.assoc]
    have hsk := (Functor.mapDerivedCategorySquareIso sk).hom.naturality
      (Rh.mapDerivedCategoryFactors.hom.app Q)
    dsimp only [Functor.comp_map] at hsk
    rw [← reassoc_of% hsk]
    have hr := rk.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex sh.hom (.up ℤ)).app Q)
    dsimp only [Functor.comp_map] at hr
    erw [reassoc_of% hr]
    erw [reassoc_of% (square_fac sk Qh)]
    rw [← F₂.mapDerivedCategory.map_comp_assoc, composition_fac d Q]
    simp only [Functor.map_comp, Category.assoc]
    have hd := F₂.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app Q)
    dsimp only [Functor.comp_map] at hd
    rw [reassoc_of% hd]
    simp only [← Functor.map_comp]
    congr 3
    apply congrArg DerivedCategory.Q.map
    ext n
    exact hs (Q.X n)
  exact congr_app heq P

end Localization

namespace WeilConjectures.SemilinearSections

attribute [local irreducible] hasDerived HasDerivedCategory.standard
  Functor.mapDerivedCategory systemRing ringPresheaf rings
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  (A : Data.{c, v, r} J B τ)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)

private abbrev ordinaryComposition {s m n : ℕ} (h : n ≤ m) (k : m ≤ s) :=
  (restrictionComposition_existsUnique.{c, v, max c v r} J B τ h k).exists.choose

private theorem ordinaryComposition_underlying {s m n : ℕ} (h : n ≤ m) (k : m ≤ s)
    (M : Mod.{c, v, max c v r} J (B n)) :
    (underlying.{c, v, r} J (B s)).map
      ((ordinaryComposition.{c, v, r} J B τ h k).hom.app M) = 𝟙 _ := by
  ext U x
  exact congrFun (eq_of_heq
    ((restrictionComposition_existsUnique.{c, v, max c v r} J B τ h k).exists.choose_spec
      M U)) x

private theorem ordinary_restriction_composition
    (G : Geometry.{c, v, r} J B τ A J' uInv uPush adjSet)
    {s m n : ℕ} (h : n ≤ m) (k : m ≤ s)
    (M : Mod.{c, v, max c v r} J (B n)) :
    (G.inverseImage s).modules.map ((ordinaryComposition.{c, v, r} J B τ h k).hom.app M) ≫
        (G.restrictionPullback (h.trans k)).hom.app M =
      (G.restrictionPullback k).hom.app ((res (coefficientMap.{c, v, max c v r} J B τ h)).obj M) ≫
        (res (coefficientMap.{c, v, max c v r} J' G.coefficients G.coefficientTransition k)).map
          ((G.restrictionPullback h).hom.app M) ≫
        (ordinaryComposition.{c, v, r} J' G.coefficients G.coefficientTransition h k).hom.app
          ((G.inverseImage n).modules.obj M) := by
  apply (underlying.{c, v, r} J' (G.coefficients s)).map_injective
  apply (cancel_mono ((G.inverseImage n).moduleUnderlying.hom.app M)).mp
  simp only [Functor.map_comp, Category.assoc]
  erw [G.restrictionPullback_underlying (h.trans k) M]
  have he := ordinaryComposition_underlying.{c, v, r} J' G.coefficients G.coefficientTransition h k
    ((G.inverseImage n).modules.obj M)
  erw [he, Category.id_comp]
  change _ =
    (underlying.{c, v, r} J' (G.coefficients s)).map
      ((G.restrictionPullback k).hom.app ((res (coefficientMap.{c, v, max c v r} J B τ h)).obj M)) ≫
    (underlying.{c, v, r} J' (G.coefficients m)).map
      ((G.restrictionPullback h).hom.app M) ≫
    (G.inverseImage n).moduleUnderlying.hom.app M
  erw [G.restrictionPullback_underlying h M,
    G.restrictionPullback_underlying k ((res
      (coefficientMap.{c, v, max c v r} J B τ h)).obj M)]
  have hn := (G.inverseImage s).moduleUnderlying.hom.naturality
    ((ordinaryComposition.{c, v, r} J B τ h k).hom.app M)
  dsimp only [Functor.comp_map] at hn
  erw [hn, ordinaryComposition_underlying.{c, v, r} J B τ h k M,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- The left-adjoint coefficient squares compose with the actual scalar associators.
Source: blueprint `sk-lem-sp-tower-bound-operations.proof.md` (2), transposes of
units and counits; Zheng Construction 4.1 and Lemma 4.10; Stacks 03CZ and 07A4.
(blueprint: lem-sp-semilinear-coefficient-pullback-composition).

Proof: first compose the ordinary restrictionPullback squares. After forgetting module
structure their components are the identities on the same inverse-image sheaf, by
restrictionPullback_underlying; faithfulness gives equality with the direct restriction
square, including the section identity restrictionComposition on each side. Exact
termwise localization preserves this equality and its associators. Transpose this
localized equation through the two scalar adjunctions. Use
coefficientPullback_transpose for each coefficient square and
scalarComposition_transpose for each scalar associator. Naturality moves the units
through the restriction comparisons, and the adjunction triangle identities cancel
them. The resulting equality is the inverse of the displayed invertible square;
cancelling its invertible factors gives the displayed hom equation. This step uses
only coefficient pullback and scalar extension, not any geometric direct-image mate,
open operation, or strict-tower coordinate choice. Equal indices and nonflat quotient
maps are allowed, since the argument transposes actual derived adjunctions. -/
theorem Geometry.coefficientPullback_composition
    (G : Geometry.{c, v, r} J B τ A J' uInv uPush adjSet)
    {s m n : ℕ} (h : n ≤ m) (k : m ≤ s)
    (P : D.{c, v, max c v r} J (B s)) :
    (derivedExact.{c, v, max c v r, c, v} J J' (B n)
        (G.coefficients n) (G.inverseImage n).modules).map
          ((A.scalarComposition h k).hom.app P) ≫
        (G.coefficientPullback (h.trans k)).hom.app P =
      (G.coefficientPullback h).hom.app ((A.scalar k).T.obj P) ≫
        (G.target.scalar h).T.map ((G.coefficientPullback k).hom.app P) ≫
        (G.target.scalarComposition h k).hom.app
          ((derivedExact.{c, v, max c v r, c, v} J J' (B s)
            (G.coefficients s) (G.inverseImage s).modules).obj P) := by
  exact mate_composition
    (A.scalar h).adjunction (A.scalar k).adjunction (A.scalar (h.trans k)).adjunction
    (G.target.scalar h).adjunction (G.target.scalar k).adjunction
    (G.target.scalar (h.trans k)).adjunction
    (derivedExact.{c, v, max c v r, c, v} J J' (B n)
      (G.coefficients n) (G.inverseImage n).modules)
    (derivedExact.{c, v, max c v r, c, v} J J' (B m)
      (G.coefficients m) (G.inverseImage m).modules)
    (derivedExact.{c, v, max c v r, c, v} J J' (B s)
      (G.coefficients s) (G.inverseImage s).modules)
    (A.scalarComposition h k) (G.target.scalarComposition h k)
    (restrictionComposition.{c, v, max c v r} J B τ h k)
    (restrictionComposition.{c, v, max c v r} J' G.coefficients
      G.coefficientTransition h k)
    (G.coefficientPullback h) (G.coefficientPullback k)
    (G.coefficientPullback (h.trans k))
    (Functor.mapDerivedCategorySquareIso (G.restrictionPullback h))
    (Functor.mapDerivedCategorySquareIso (G.restrictionPullback k))
    (Functor.mapDerivedCategorySquareIso (G.restrictionPullback (h.trans k)))
    (A.scalarComposition_transpose h k) (G.target.scalarComposition_transpose h k)
    (G.coefficientPullback_transpose h) (G.coefficientPullback_transpose k)
    (G.coefficientPullback_transpose (h.trans k))
    (localized_composition
      (res (coefficientMap.{c, v, max c v r} J B τ h))
      (res (coefficientMap.{c, v, max c v r} J B τ k))
      (res (coefficientMap.{c, v, max c v r} J B τ (h.trans k)))
      (res (coefficientMap.{c, v, max c v r} J' G.coefficients G.coefficientTransition h))
      (res (coefficientMap.{c, v, max c v r} J' G.coefficients G.coefficientTransition k))
      (res (coefficientMap.{c, v, max c v r} J' G.coefficients
        G.coefficientTransition (h.trans k)))
      (G.inverseImage n).modules (G.inverseImage m).modules (G.inverseImage s).modules
      (ordinaryComposition.{c, v, r} J B τ h k)
      (ordinaryComposition.{c, v, r} J' G.coefficients G.coefficientTransition h k)
      (G.restrictionPullback h) (G.restrictionPullback k)
      (G.restrictionPullback (h.trans k))
      (ordinary_restriction_composition.{c, v, r} J B τ A J' uInv uPush adjSet G h k)) P

end WeilConjectures.SemilinearSections
