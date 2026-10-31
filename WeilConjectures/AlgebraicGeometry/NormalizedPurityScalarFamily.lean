/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalScalarComparisonData
import WeilConjectures.AlgebraicGeometry.RationalScalarComparisonIdentification
import all WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.CompactSupportNormalizedScalarIsomorphisms

/-! # The uniquely normalized rational purity scalar family

Source: current blueprint, sec-smooth-purity/sk-thm-purity-transport,
composition-coherence transport; DAG proof Steps 1--8
(blueprint: lem-pur-normalized-rational-purity-family).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 128
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
namespace WeilConjectures.IteratedPurityScalarPasting
open AdicPurityScalarNaturality RationalScalarComparisonIdentification
attribute [local irreducible] H G T Q alpha unit
  SourceLocalizationNormalization

private theorem shift_structure_unique
    {B A V : Type*} [Category* B] [Category* A] [Category* V]
    [HasShift B ℤ] [HasShift A ℤ] [HasShift V ℤ]
    (L : B ⥤ A) (F : A ⥤ V) (J : B ⥤ V)
    (sL : L.CommShift ℤ) (sJ : J.CommShift ℤ)
    (s t : F.CommShift ℤ) (e : J ≅ L ⋙ F)
    (hL : ∀ K : A, ∃ P : B, L.obj P = K)
    (hs : @NatTrans.CommShift _ _ _ _ _ _ e.hom ℤ _ _ _ sJ
      (@Functor.CommShift.comp _ _ _ _ _ _ L F ℤ _ _ _ _ sL s))
    (ht : @NatTrans.CommShift _ _ _ _ _ _ e.hom ℤ _ _ _ sJ
      (@Functor.CommShift.comp _ _ _ _ _ _ L F ℤ _ _ _ _ sL t)) : s = t := by
  have he : s.commShiftIso = t.commShiftIso := by
    funext n
    apply Iso.ext
    ext K
    obtain ⟨P, rfl⟩ := hL K
    have hh := (congr_app (hs.shift_comm n) P).symm.trans
      (congr_app (ht.shift_comm n) P)
    simp only [NatTrans.comp_app, whiskerLeft_app,
      Functor.commShiftIso_comp_hom_app] at hh
    exact (cancel_epi _).1 ((cancel_epi _).1 hh)
  cases s
  cases t
  cases he
  rfl

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)

private theorem rational_representative (W : Scheme.{u})
    [W.Over (Spec (.of D.k))] (E : AdicPurityScalarNaturality.Field D C)
    (K : RCat D C E W) : ∃ L : Cat D C E W, (Q D C E W).obj L = K := by
  let : ∀ x : W, Invertible (C.l : W.residueField x) :=
    sfCompactSupportScalarResidueUnit C.l D.k
      (PurCompactSupport.coefficientPrimeUnit C.l D C.different) W
  have h := (integral_residue_tor D C.l C.different E.val W).2
  refine ⟨⟨K.obj.obj, h ▸ K.obj.property⟩, ?_⟩
  unfold Q
  cases K
  rfl

section Single
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]
  (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
  (I : Data D C f d S)

/-- A bundling of the existing normalized rational comparison data. The localization
is fixed on all good representatives; gamma is literally the localization of I.gamma;
a is fixed componentwise to the canonical sourceScalar. This adds no new choices of
purity, scalar maps or source coordinates to the recorded comparison-identification node.
Source: purity transport, rationalization of the simultaneous integral family
(blueprint: lem-pur-normalized-rational-purity-family). -/
structure Family where
  shift : ∀ E : AdicPurityScalarNaturality.Field D C, (H D C f d E).CommShift ℤ
  localization : ∀ E : AdicPurityScalarNaturality.Field D C,
    source D C f d E ⋙ Q D C E X ≅ Q D C E Y ⋙ H D C f d E
  localization_normalization : ∀ E : AdicPurityScalarNaturality.Field D C,
    SourceLocalizationNormalization D C f d E (localization E)
  localization_shift : ∀ E : AdicPurityScalarNaturality.Field D C,
    ShiftCompatibility (source D C f d E ⋙ Q D C E X) (Q D C E Y ⋙ H D C f d E)
      (composeShift _ _ (sourceShift D C f d E) (qXShift D C f S E))
      (composeShift _ _ (qYShift D C f S E) (shift E)) (localization E)
  gamma : ∀ E : AdicPurityScalarNaturality.Field D C, H D C f d E ≅ G D C f S E
  gamma_localization : ∀ (E : AdicPurityScalarNaturality.Field D C) (K : Cat D C E Y),
    (localization E).hom.app K ≫ (gamma E).hom.app ((Q D C E Y).obj K) =
      (Q D C E X).map ((I.gamma E).hom.app K) ≫
        (gLocalization D C f S E).hom.app K
  a : ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
    H D C f d E ⋙ T D C E F h X ≅ T D C E F h Y ⋙ H D C f d F
  a_normalization : ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
    (K : RCat D C E Y), HEq ((a E F h).app K)
      (RationalSmoothPurityCanonical.sourceScalar C.l E.val F.val
        (IntermediateField.inclusion h) f d K)

private theorem localization_unique (V W : Family D C f d S I)
    (E : AdicPurityScalarNaturality.Field D C) : V.localization E = W.localization E := by
  apply Iso.ext
  ext K
  let L := integralOperationsGoodLocalization C.l E.val X
  let Wq := (HomologicalComplex.quasiIso (integralTowerModules C.l E.val X) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex C.l E.val X).ι
  have : L.IsLocalization Wq := integralOperationsGoodLocalization_isLocalization C.l E.val X
  have := Localization.essSurj L Wq
  let P := L.objPreimage ((integralDerivedPullback C.l E.val f).obj K.obj)
  let eP := L.objObjPreimageIso ((integralDerivedPullback C.l E.val f).obj K.obj)
  have hnV := (V.localization_normalization E)
  have hnW := (W.localization_normalization E)
  unfold SourceLocalizationNormalization at hnV hnW
  apply (Iso.cancel_iso_hom_right _ _ (sourceObjectIdentification D C f d E K)).1
  rw [hnV.2 K P.obj P.property hnV.1 eP, hnW.2 K P.obj P.property hnV.1 eP]

private theorem gamma_unique (V W : Family D C f d S I)
    (E : AdicPurityScalarNaturality.Field D C) : V.gamma E = W.gamma E := by
  apply Iso.ext
  ext K
  obtain ⟨L, rfl⟩ := rational_representative D C Y E K
  apply (Iso.cancel_iso_hom_left ((V.localization E).app L) _ _).1
  change (V.localization E).hom.app L ≫ _ = (V.localization E).hom.app L ≫ _
  rw [V.gamma_localization, localization_unique D C f d S I V W E]
  exact (W.gamma_localization E L).symm

private theorem scalar_unique (V W : Family D C f d S I)
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) : V.a E F h = W.a E F h := by
  apply Iso.ext
  ext K
  exact congrArg Iso.hom (eq_of_heq
    ((V.a_normalization E F h K).trans (W.a_normalization E F h K).symm))

private theorem family_ext (V W : Family D C f d S I)
    (hs : V.shift = W.shift) (hl : V.localization = W.localization)
    (hg : V.gamma = W.gamma) (ha : V.a = W.a) : V = W := by
  cases V
  cases W
  dsimp only at hs hl hg ha
  cases hs
  cases hl
  cases hg
  cases ha
  rfl

/-- The normalized rational family is uniquely determined by the integral family.
Source: purity transport, rationalization and normalized source identifications
(blueprint: lem-pur-normalized-rational-purity-family).
Proof: take shift, localization, eta and a from the recorded
rationalScalarComparisonIdentification. Its normalization, shift and eta equations
are exactly the fields above. Every good resolution of an integral pullback has
the prescribed source comparison. Resolving localization is essentially surjective
and natural transformations out of it are determined on good representatives,
so the localization is unique. The displayed gamma equation then determines gamma
on every rational object, since each has an integral representative and the source
localization is invertible. The a normalization fixes every component, so it fixes
a as a natural isomorphism. Finally the localization shift equation determines the
source shift on all rational objects, since the integral shifts and localization
shifts are fixed. Structure extensionality and proof irrelevance give uniqueness. -/
theorem family_existsUnique : ∃! _V : Family D C f d S I, True := by
  obtain ⟨s, _, loc, hn, hs, _, sloc, _, _, _, _, _, gam, _, hg, a,
    _, _, ha, _⟩ := rationalScalarComparisonIdentification D C f d S I
  let V : Family D C f d S I := ⟨s, loc, hn, hs, gam, hg, a, ha⟩
  refine ⟨V, trivial, ?_⟩
  intro W _
  have hl : W.localization = V.localization := funext (localization_unique D C f d S I W V)
  have hg : W.gamma = V.gamma := funext (gamma_unique D C f d S I W V)
  have ha' : W.a = V.a := by
    funext E F h
    exact scalar_unique D C f d S I W V E F h
  have hs' : W.shift = V.shift := by
    funext E
    have hw := W.localization_shift E
    have hv := V.localization_shift E
    rw [hl] at hw
    exact shift_structure_unique (Q D C E Y) (H D C f d E)
      (source D C f d E ⋙ Q D C E X) (qYShift D C f S E)
      (composeShift _ _ (sourceShift D C f d E) (qXShift D C f S E))
      (W.shift E) (V.shift E) (V.localization E)
      (rational_representative D C Y E) hw hv
  exact family_ext D C f d S I W V hs' hl hg ha'

/-- The unique normalized family, rather than an arbitrary endpoint isomorphism.
Source: purity transport, gamma and a
(blueprint: lem-pur-normalized-rational-purity-family). -/
@[irreducible] def family : Family D C f d S I := (family_existsUnique D C f d S I).exists.choose

end Single

end WeilConjectures.IteratedPurityScalarPasting
