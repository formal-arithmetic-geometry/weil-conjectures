/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCharacteristic
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite
public import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
public import Sheaf.SecSmoothPurity.DirectImageScalarExchange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.SixFunctors.ScalarSixPullback

/-!
# Absolute Frobenius and finite coefficient change

Source: main-20261015 blueprint, six-functors-basics,
`sk-prop-sf-rf-shriek-preservation/lem-trf-absolute-frobenius-site.proof.md`, final
paragraph; Stacks Tag 0F6W (blueprint: lem-trf-absolute-frobenius-coefficient-naturality).

The scalar extension is the left adjoint of exact derived restriction, hence the ordinary
uncompleted derived tensor product. Its pullback comparison is the scalar-adjunction mate
of the section-normalized restriction comparison. This specifies the transported comparison
without choosing an arbitrary natural isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Exact derived descent of the relative-Frobenius-normalized module trivialization.
The dependency fixes the site isomorphism by its two projections, then fixes its module
mate by the section-unit equation; the choice therefore takes a uniquely specified map.
Source: Stacks 0F6W; final paragraph of lem-trf-absolute-frobenius-site.proof.md
(blueprint: lem-trf-absolute-frobenius-coefficient-naturality). -/
def coefficientFrobeniusTrivialization (p : ℕ) (hp : p.Prime)
    (X : Scheme.{u}) (hX : X.IsCharacteristic p)
    (A : Type u) [CommRing A] [Finite A] (b : ℕ) :
    proEtaleConstantRingDerivedPullback A (X.iterateFrobenius hp (hX.2 ⊤) b) ≅
      𝟭 (proEtaleDerivedCategory X A) :=
  proEtaleFrobeniusDerivedIso A
    ((absoluteFrobenius_proEtale_trivialization_pullback p hp A).choose_spec.2.choose_spec.2.choose
      X hX b)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarMate_trivialization
    {C D : Type*} [Category C] [Category D]
    {T : C ⥤ D} {R : D ⥤ C} (adj : T ⊣ R)
    {P : C ⥤ C} {Q : D ⥤ D} (s : P ≅ 𝟭 C) (t : Q ≅ 𝟭 D)
    (β : R ⋙ P ⟶ Q ⋙ R)
    (hβ : ∀ N, β.app N ≫ R.map (t.hom.app N) = s.hom.app (R.obj N))
    (K : C) :
    ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ β)).app K ≫
      t.hom.app (T.obj K) = T.map (s.hom.app K) := by
  simp only [mateEquiv_symm_apply, TwoSquare.mk, TwoSquare.natTrans,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Category.id_comp, Functor.comp_map, Functor.comp_obj,
    T.map_id, Functor.id_obj, Category.assoc]
  rw [← adj.counit_naturality (t.hom.app (T.obj K))]
  calc
    _ = T.map (P.map (adj.unit.app K) ≫ β.app (T.obj K) ≫
        R.map (t.hom.app (T.obj K))) ≫ adj.counit.app (T.obj K) := by
      simp only [T.map_comp, Functor.id_obj, Category.assoc]
    _ = T.map (P.map (adj.unit.app K) ≫ s.hom.app (R.obj (T.obj K))) ≫
        adj.counit.app (T.obj K) := by rw [hβ]
    _ = T.map (s.hom.app K ≫ adj.unit.app K) ≫ adj.counit.app (T.obj K) := by
      exact congrArg (fun z ↦ T.map z ≫ adj.counit.app (T.obj K))
        (s.hom.naturality (adj.unit.app K))
    _ = T.map (s.hom.app K) := by
      simp only [T.map_comp, Category.assoc]
      erw [adj.left_triangle_components]
      exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem moduleRestriction_trivialization
    {X : Scheme.{u}} (f : X ⟶ X)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (r : 𝟭 X.ProEt ≅ proEtaleBaseChange f)
    (s : proEtaleConstantRingPullback A f ≅ 𝟭 _)
    (t : proEtaleConstantRingPullback B f ≅ 𝟭 _)
    (hs : ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A))
      (V : X.ProEt) (m : M.val.obj (Opposite.op V)),
      ((proEtaleConstantRingAdjunction A f).unit.app M ≫
        (proEtaleConstantRingPushforward A f).map (s.hom.app M)).val.app
          (Opposite.op V) m = M.val.map (r.inv.app V).op m)
    (ht : ∀ (M : proEtaleRingModules X (proEtaleConstantRing X B))
      (V : X.ProEt) (m : M.val.obj (Opposite.op V)),
      ((proEtaleConstantRingAdjunction B f).unit.app M ≫
        (proEtaleConstantRingPushforward B f).map (t.hom.app M)).val.app
          (Opposite.op V) m = M.val.map (r.inv.app V).op m)
    (M : proEtaleRingModules X (proEtaleConstantRing X B)) :
    (proEtaleRingRestrictionPullbackInv f
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRingMap φ) (proEtaleConstantRingMap φ)
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
      (proEtaleConstantInverseImageMap_naturality f
        (CommRingCat.ofHom (RingHom.ulift φ))).symm).app M ≫
      (proEtaleRingRestrictScalars (proEtaleConstantRingMap φ)).map (t.hom.app M) =
        s.hom.app ((proEtaleRingRestrictScalars (proEtaleConstantRingMap φ)).obj M) := by
  let R := proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := X) φ)
  let adjA := proEtaleConstantRingAdjunction A f
  let adjB := proEtaleConstantRingAdjunction B f
  let d := proEtaleRingRestrictionDirectImage f
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap φ) (proEtaleConstantRingMap φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm
  have happ : (proEtaleRingRestrictionPullbackInv f
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B)
      (proEtaleConstantRingMap φ) (proEtaleConstantRingMap φ)
      (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
      (proEtaleConstantInverseImageMap_naturality f
        (CommRingCat.ofHom (RingHom.ulift φ))).symm).app M =
      (adjA.homEquiv _ _).symm (R.map (adjB.unit.app M) ≫ d.hom.app _) := by
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rfl
  apply (adjA.homEquiv _ _).injective
  rw [happ, Adjunction.homEquiv_naturality_right]
  dsimp only [Functor.comp_obj, Functor.id_obj] at *
  erw [Equiv.apply_symm_apply]
  change (R.map (adjB.unit.app M) ≫ d.hom.app _) ≫
    (proEtaleConstantRingPushforward A f).map (R.map (t.hom.app M)) = _
  rw [Category.assoc]
  have hn := d.hom.naturality (t.hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [← hn]
  change R.map (adjB.unit.app M) ≫ R.map
    ((proEtaleConstantRingPushforward B f).map (t.hom.app M)) ≫ d.hom.app M = _
  rw [← Category.assoc, ← R.map_comp, Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext m
  have hd := (proEtaleRingRestrictionDirectImage_existsUnique f
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap φ) (proEtaleConstantRingMap φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm).choose_spec.1 M V
  change (d.hom.app M).val.app V
    (((adjB.unit.app M ≫ (proEtaleConstantRingPushforward B f).map
      (t.hom.app M)).val.app V) m) = _
  dsimp only [d, proEtaleRingRestrictionDirectImage]
  erw [hd]
  exact (ht M V.unop m).trans (hs (R.obj M) V.unop m).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem frobeniusSiteIso_eq (p : ℕ) (hp : p.Prime)
    (X : Scheme.{u}) (hX : X.IsCharacteristic p) (b : ℕ)
    (r s : 𝟭 X.ProEt ≅ proEtaleBaseChange (X.iterateFrobenius hp (hX.2 ⊤) b))
    (hr : ∀ V : X.ProEt, ∃ hV : (p : Γ(V.left, ⊤)) = 0,
      (r.hom.app V).left ≫ pullback.fst V.hom
        (X.iterateFrobenius hp (hX.2 ⊤) b) = V.left.iterateFrobenius hp hV b)
    (hs : ∀ V : X.ProEt, ∃ hV : (p : Γ(V.left, ⊤)) = 0,
      (s.hom.app V).left ≫ pullback.fst V.hom
        (X.iterateFrobenius hp (hX.2 ⊤) b) = V.left.iterateFrobenius hp hV b) :
    r = s := by
  apply Iso.ext
  apply NatTrans.ext
  funext V
  obtain ⟨hV, hrV⟩ := hr V
  obtain ⟨hV', hsV⟩ := hs V
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · exact hrV.trans hsV.symm
  · exact (r.hom.app V).w.trans (s.hom.app V).w.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical absolute-Frobenius trivialization commutes with every finite unital
coefficient change on the ordinary unbounded derived category, at every nonnegative iterate.

Source: main-20261015 blueprint, final paragraph of
lem-trf-absolute-frobenius-site.proof.md; geometric input Stacks 0F6W
(blueprint: lem-trf-absolute-frobenius-coefficient-naturality).

Proof:
1. The site isomorphisms selected for A and B coincide. Their first projections are
   the same b-fold Frobenius, and their second projections are the structure maps.
   The universal property of the fibre product proves equality, including b=0.
2. Let R be restriction along the constant-ring map. The ordinary comparison
   P_A R → R P_B is the mate of the identity-on-sections direct-image comparison.
   Take adjuncts of its composite with R(tau_B) and of tau_A R. Naturality of the
   direct-image comparison reduces their equality to the two section-unit
   normalizations. Step 1 identifies the site maps in those normalizations.
3. All functors in this restriction square are exact. Apply the existing
   mapDerivedCategorySquareIso_hom_app_id lemma to descend its compatibility to
   the ordinary unbounded derived categories, with their identity comparisons.
4. Scalar extension is left adjoint to exact restriction. Its inverse pullback
   comparison is the mate of the restriction square. Expand that mate, use its
   compatibility from Step 3 and naturality of the trivializations, and cancel
   the unit and counit by the triangle identity. Invert the pullback comparison
   to obtain the displayed equation. This proves every iterate directly and
   requires no flatness or finite Tor-amplitude assumption. -/
theorem absoluteFrobenius_coefficient_naturality (p : ℕ) (hp : p.Prime)
    (X : Scheme.{u}) (hX : X.IsCharacteristic p)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (b : ℕ) (K : proEtaleDerivedCategory X A) :
    (AlgebraicGeometry.ProEtale.directImageScalarPullbackIso φ
      (X.iterateFrobenius hp (hX.2 ⊤) b)).hom.app K ≫
        (AlgebraicGeometry.ProEtale.directImageScalarExtension φ X).map
          ((coefficientFrobeniusTrivialization p hp X hX A b).hom.app K) =
      (coefficientFrobeniusTrivialization p hp X hX B b).hom.app
        ((AlgebraicGeometry.ProEtale.directImageScalarExtension φ X).obj K) := by
  classical
  let f := X.iterateFrobenius hp (hX.2 ⊤) b
  let dA := absoluteFrobenius_proEtale_trivialization_pullback p hp A
  let dB := absoluteFrobenius_proEtale_trivialization_pullback p hp B
  let s := dA.choose_spec.2.choose_spec.2.choose X hX b
  let t := dB.choose_spec.2.choose_spec.2.choose X hX b
  have hr : dA.choose X hX b = dB.choose X hX b :=
    frobeniusSiteIso_eq p hp X hX b _ _
      (dA.choose_spec.1 X hX b) (dB.choose_spec.1 X hX b)
  let a := proEtaleConstantRingMap (T := X) φ
  let R := proEtaleRingRestrictScalars a
  let comm := (proEtaleConstantInverseImageMap_naturality f
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ))).symm
  let β := proEtaleRingRestrictionPullbackInv f
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B) a a
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B) comm
  have : IsIso β := proEtaleRingRestrictionPullbackInv_isIso f
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B) a a
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B) comm
  have hβ (M : proEtaleRingModules X (proEtaleConstantRing X B)) :
      β.app M ≫ R.map (t.hom.app M) = s.hom.app (R.obj M) := by
    apply moduleRestriction_trivialization f φ (dA.choose X hX b) s t
    · exact dA.choose_spec.2.choose_spec.2.choose_spec.1 X hX b
    · intro M V m
      rw [hr]
      exact dB.choose_spec.2.choose_spec.2.choose_spec.1 X hX b M V m
  have hD := Functor.mapDerivedCategorySquareIso_hom_app_id
    (asIso β) t s hβ
  let δ := proEtaleRingRestrictionDerivedPullback f
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B) a a
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B) comm
  have hδ (N : proEtaleDerivedCategory X B) :
      δ.inv.app N ≫ R.mapDerivedCategory.map
        ((coefficientFrobeniusTrivialization p hp X hX B b).hom.app N) =
      (coefficientFrobeniusTrivialization p hp X hX A b).hom.app
        (R.mapDerivedCategory.obj N) := by
    simpa only [δ, proEtaleRingRestrictionDerivedPullback,
      Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
      ← Functor.mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq, Category.assoc,
      coefficientFrobeniusTrivialization, proEtaleFrobeniusDerivedIso, s, t, dA, dB]
      using hD N
  have hmate := scalarMate_trivialization
    (proEtaleRingDerivedExtensionAdjunction a)
    (coefficientFrobeniusTrivialization p hp X hX A b)
    (coefficientFrobeniusTrivialization p hp X hX B b) δ.inv hδ K
  apply (cancel_epi
    ((AlgebraicGeometry.ProEtale.directImageScalarPullbackIso φ f).inv.app K)).1
  rw [Iso.inv_hom_id_app_assoc]
  exact hmate.symm

end AlgebraicGeometry.Scheme
