/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.Paper.PadicIntegersInvertEll
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation

/-!
# Inverse image of the three coefficient comparisons

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-prop-sfb-qlbar-colimit-x-pullback.md`, clauses 1--3
(blueprint: det-prop-sfb-qlbar-colimit-x-pullback).

The integral comparison is normalized by the same adjunction mate as its dependency.
Localization is stated for any module-colimit representatives with their localization
ring structures. The algebraic-closure clause uses the published finite-subextension cocone.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma scalar_legs_ext {C : Type*} [Category C] [Preadditive C]
    {A B : C} (l : ℕ) (t : End B) (ht : (l • 𝟙 B) ≫ t = 𝟙 B)
    (a b : ℕ → (A ⟶ B))
    (ha : ∀ n, l • a (n + 1) = a n) (hb : ∀ n, l • b (n + 1) = b n)
    (h0 : a 0 = b 0) (n : ℕ) : a n = b n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    have h : a (n + 1) ≫ (l • 𝟙 B) = b (n + 1) ≫ (l • 𝟙 B) := by
      simpa only [Preadditive.comp_nsmul, Category.comp_id, ha, hb] using ih
    have := congrArg (fun k ↦ k ≫ t) h
    simpa only [Category.assoc, ht, Category.comp_id] using this

private lemma scalar_cocone_recurrence {C : Type*} [Category C] [Preadditive C]
    (l : ℕ) (A : C) (c : Cocone (Functor.ofSequence (fun _ ↦ l • 𝟙 A))) (n : ℕ) :
    l • c.ι.app (n + 1) = c.ι.app n := by
  have h := c.w (homOfLE (Nat.le_succ n))
  rw [Functor.ofSequence_map_homOfLE_succ] at h
  change (l • 𝟙 A) ≫ c.ι.app (n + 1) = c.ι.app n at h
  simpa only [Preadditive.nsmul_comp, Category.id_comp] using h

private lemma scalar_pullback_legs {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {A B : C} {A' B' : D} (l : ℕ) (t : End B') (ht : (l • 𝟙 B') ≫ t = 𝟙 B')
    (a : ℕ → (A ⟶ B)) (b : ℕ → (A' ⟶ B'))
    (d : F.obj B ⟶ B') (s : F.obj A ⟶ A')
    (ha : ∀ n, l • a (n + 1) = a n) (hb : ∀ n, l • b (n + 1) = b n)
    (h0 : F.map (a 0) ≫ d = s ≫ b 0) (n : ℕ) :
    F.map (a n) ≫ d = s ≫ b n := by
  apply scalar_legs_ext l t ht _ _ ?_ ?_ h0 n
  · intro n
    rw [← Preadditive.nsmul_comp, ← F.map_nsmul, ha]
  · intro n
    rw [← Preadditive.comp_nsmul, hb]

private theorem ringComparisonNaturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (e : F ⋙ G ≅ H) [NatTrans.IsMonoidal e.hom] (A B : Mon C) (a : A.X ⟶ B.X) :
    G.map (F.map a) ≫
        (((Functor.mapMonCompIso (F := F) (G := G)).symm.app B ≪≫
          (Functor.mapMonNatIso e).app B).hom).hom =
      (e.app A.X).hom ≫ H.map a := by
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Mon.comp_hom',
    Functor.mapMonCompIso_inv_app_hom, Functor.mapMonNatIso_hom_app_hom]
  change G.map (F.map a) ≫ (𝟙 _ ≫ e.hom.app B.X) = _
  rw [Category.id_comp]
  exact e.hom.naturality a


private theorem ringIsoComposite
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] {A B : Mon C} {A' B' : Mon D}
    (e : A ≅ B) (d : F.mapMon.obj B ≅ B') (e' : A' ≅ B') :
    (F.mapMon.mapIso e ≪≫ d ≪≫ e'.symm).hom.hom ≫ e'.hom.hom =
      F.map e.hom.hom ≫ d.hom.hom := by
  change (F.map e.hom.hom ≫ d.hom.hom ≫ e'.inv.hom) ≫ e'.hom.hom = _
  rw [Category.assoc, Category.assoc, ← Mon.comp_hom', e'.inv_hom_id]
  rw [Mon.id_hom', Category.comp_id]

/-- The canonical comparison between a constant commutative ring sheaf, regarded as
an abelian sheaf, and the constant abelian sheaf of its additive group.
Source: blueprint pullback clause 1, canonical finite constant-sheaf identifications
(blueprint: det-prop-sfb-qlbar-colimit-x-pullback). -/
def sfbConstantRingAbIso (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A)) ≅
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of A) :=
  letI : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  letI : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
    ((constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app A) ≪≫
    (constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).app ((forget₂ CommRingCat RingCat).obj A)

/-- The canonical finite constant coefficient comparison, with the ring-sheaf encoding
transported to abelian sheaves by the canonical constant/forgetful comparison.
Source: blueprint pullback clause 1, the constant-sheaf identifications
(blueprint: det-prop-sfb-qlbar-colimit-x-pullback). -/
def sfbFiniteCoefficientPullbackIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (f)^*[Ab.{u + 1}].obj
        ((sheafCompose (Scheme.ProEt.topology Y) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (integralCoefficientSheaf l E Y n)) ≅
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (integralCoefficientSheaf l E X n) :=
  (f)^*[Ab.{u + 1}].mapIso
    (sfbConstantRingAbIso Y
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ≪≫
    (constantSheafCompUpperStarIso Ab.{u + 1} f).app
      (AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) ≪≫
    (sfbConstantRingAbIso X
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).symm

/-- The normalization of the integral comparison from the integral-limit dependency:
its adjunction mate is reduction on every profinite test object, using the natural
finite-label representation. This predicate introduces no new coefficient object.
Source: blueprint integral-limit clause 3 and pullback proof Steps 2--3
(blueprint: det-prop-sfb-qlbar-colimit-x-pullback). -/
def SfbIntegralComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (e : (coefficientRing X (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E X) :
    Prop :=
  IsMonHom e.hom ∧ IsMonHom e.inv ∧
    ∃ (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
      (c : Cone (sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite))
      (j : sfbIntegralProfinite l E ≅ c.pt),
      (∀ (n : ℕ) (x : Padic.coefficientExtensionIntegers l E),
        (j.hom ≫ c.π.app (op n)) x =
          Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x) ∧
      Nonempty (IsLimit c) ∧
      ∀ (S : Profinite.{u}) (g : S ⟶ sfbIntegralProfinite l E) (n : ℕ),
        (sfbIntegralFiniteRepresentation l E X a n).hom.app
            (op ((profiniteToProEtOf X).obj S))
          (((limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app
              (op ((profiniteToProEtOf X).obj S)))
            ((e.hom.hom.app (op ((profiniteToProEtOf X).obj S)))
              (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
                (op S) (ULift.up g.hom.hom)))) =
          ULift.up ((profiniteToProEtOf X).map (g ≫ j.hom ≫ c.π.app (op n)))

/-- The canonical integral comparisons commute with inverse image. The displayed
projection equations specify the usual limit comparison, and the mapped limit cone is
limiting: preservation is asserted only for this particular positive quotient tower.

Source: blueprint pullback clause 1 (blueprint: det-prop-sfb-qlbar-colimit-x-pullback).
Proof: use adjunction and Yoneda to identify inverse images of represented sheaves,
naturally in their representing schemes. Associativity of fibre products identifies
Y[S] times_Y X with X[S]. The mate definition of upperStarFromPointComp sends the
universal element to that same universal element, so the normalized integral comparison
and every reduction commute with alpha. Equality after every finite projection gives the
comparison square by the limit universal property. The comparison is invertible because
the other three arrows are. Its ring compatibility follows from the componentwise ring
operations; transporting the limiting cone along it proves preservation of this limit.
Use det-pe-topos-functoriality-site, det-pe-topos-functoriality-inverse-image,
lem-galois-yoneda-hom-bijection, sk-def-sfb-pullback-from-point,
sk-def-sfb-pullback-from-point-comp and det-prop-sfb-qlbar-colimit-x-integral-limit. -/
theorem sfb_integral_comparison_pullback (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ (eX : (coefficientRing X (sfbCondensedIntegers l (ULift.{u} E.1))).X ≅
          sfbCompletedIntegersAb l (ULift.{u} E.1) X)
      (eY : (coefficientRing Y (sfbCondensedIntegers l (ULift.{u} E.1))).X ≅
          sfbCompletedIntegersAb l (ULift.{u} E.1) Y),
      SfbIntegralComparison l (ULift.{u} E.1) X eX ∧ SfbIntegralComparison l (ULift.{u} E.1) Y eY ∧
      ∃ c : (f)^*[Ab.{u + 1}].obj (sfbCompletedIntegersAb l (ULift.{u} E.1) Y) ≅
          sfbCompletedIntegersAb l (ULift.{u} E.1) X,
        (f)^*[Ab.{u + 1}].mapIso eY ≪≫ c =
          (upperStarFromPointComp f).app (sfbCondensedIntegers l (ULift.{u} E.1)).X ≪≫ eX ∧
        IsMonHom c.hom ∧ IsMonHom c.inv ∧
        (∀ n : ℕ,
          (f)^*[Ab.{u + 1}].map
              ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
                (limit.π (integralCoefficientSheafSystem l (ULift.{u} E.1) Y) (op n))) ≫
              (sfbFiniteCoefficientPullbackIso l (ULift.{u} E.1) f n).hom =
            c.hom ≫ (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              (limit.π (integralCoefficientSheafSystem l (ULift.{u} E.1) X) (op n))) ∧
        Nonempty (IsLimit ((f)^*[Ab.{u + 1}].mapCone
          ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapCone
            (limit.cone (integralCoefficientSheafSystem l (ULift.{u} E.1) Y))))) := by
  sorry

/-- The canonical localization comparisons commute with inverse image, for any choices
of the two module colimits with their localization ring structures. The zeroth-leg
normalizations characterize the localization isomorphisms; the last equation checks
all fraction legs, not only the integral inclusion.

Source: blueprint pullback clause 2 (blueprint: det-prop-sfb-qlbar-colimit-x-pullback).
Proof: naturality of alpha for the integral inclusion identifies phi_Y with phi_X.
Additivity identifies multiplication by ell, and hence its unique inverse on E, under
alpha. Thus every leg ell^(-m) phi commutes with alpha. Module inverse image is extension
of scalars after abelian inverse image; since the coefficient map alpha is invertible,
its underlying abelian sheaf is the ordinary inverse image. The module adjunction
preserves the localization colimit. The universal property gives the comparison on
any chosen colimit, and equality on its legs gives the square. Monoidality of alpha
makes it a square of ring isomorphisms. Use det-prop-sfb-qlbar-colimit-x-invert-ell,
def-sfb-integers-to-subfield, sk-def-sfb-pullback-from-point-comp,
def-sfb-module-upper-star and def-sfb-module-upper-lower-adjunction. -/
theorem sfb_localization_comparison_pullback (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cY : Cocone (padicIntegersEllSequence Y l E)) (hY : IsColimit cY)
    (cX : Cocone (padicIntegersEllSequence X l E)) (hX : IsColimit cX)
    [MonObj cY.pt.X] [IsCommMonObj cY.pt.X]
    [MonObj cX.pt.X] [IsCommMonObj cX.pt.X]
    (rY : IsMonHom (@id
      (condensedRingObj (Profinite.padicIntegersRingObj l E.1) Y ⟶ cY.pt.X)
      (cY.ι.app 0).hom))
    (rX : IsMonHom (@id
      (condensedRingObj (Profinite.padicIntegersRingObj l E.1) X ⟶ cX.pt.X)
      (cX.ι.app 0).hom)) :
    ∃ (eY : Mon.mk cY.pt.X ≅ Mon.mk (padicSubfieldRingObj Y l E))
      (eX : Mon.mk cX.pt.X ≅ Mon.mk (padicSubfieldRingObj X l E))
      (c : (f)^*[Ab.{u + 1}].mapMon.obj (Mon.mk cY.pt.X) ≅ Mon.mk cX.pt.X),
      (cY.ι.app 0).hom ≫ eY.hom.hom = padicIntegersToPadicSubfield Y l E ∧
      (cX.ι.app 0).hom ≫ eX.hom.hom = padicIntegersToPadicSubfield X l E ∧
      (f)^*[Ab.{u + 1}].mapMon.mapIso eY ≪≫
          coefficientPullbackIso f (Mon.mk (Profinite.continuousMapRingObj E.1)) =
        c ≪≫ eX ∧
      ∀ m : ℕ,
        (f)^*[Ab.{u + 1}].map (cY.ι.app m).hom ≫ c.hom.hom =
          ((upperStarFromPointComp f).app (Profinite.padicIntegersRingObj l E.1)).hom ≫
            (cX.ι.app m).hom := by
  obtain ⟨jY, hjY, tY, htY, htY', αY, hαY, hcY, heY, _⟩ :=
    padicIntegers_invertEll Y l E
  obtain ⟨jX, hjX, tX, htX, htX', αX, hαX, hcX, heX, _⟩ :=
    padicIntegers_invertEll X l E
  obtain ⟨eY, heY⟩ := heY cY hY rY
  obtain ⟨eX, heX⟩ := heX cX hX rX
  let d := coefficientPullbackIso f (Mon.mk (Profinite.continuousMapRingObj E.1))
  let c := (f)^*[Ab.{u + 1}].mapMon.mapIso eY ≪≫ d ≪≫ eX.symm
  refine ⟨eY, eX, c, ?_, ?_, ?_, ?_⟩
  · simpa only [heY, hαY, pow_zero, End.one_def, Category.comp_id] using hjY
  · simpa only [heX, hαX, pow_zero, End.one_def, Category.comp_id] using hjX
  · simp only [c, d, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  · intro m
    have heY0 : (cY.ι.app 0).hom ≫ eY.hom.hom =
        padicIntegersToPadicSubfield Y l E := by
      simpa only [heY, hαY, pow_zero, End.one_def, Category.comp_id] using hjY
    have heX0 : (cX.ι.app 0).hom ≫ eX.hom.hom =
        padicIntegersToPadicSubfield X l E := by
      simpa only [heX, hαX, pow_zero, End.one_def, Category.comp_id] using hjX
    have ht := congrArg (fun k ↦ k.hom) htX
    simp only [Mod.comp_hom', Mod.nsmul_hom, Mod.id_hom'] at ht
    have hn : (f)^*[Ab.{u + 1}].map (padicIntegersToPadicSubfield Y l E) ≫
        d.hom.hom =
          ((upperStarFromPointComp f).app (Profinite.padicIntegersRingObj l E.1)).hom ≫
            padicIntegersToPadicSubfield X l E := by
      exact ringComparisonNaturality (upperStarFromPoint Y) (f)^*[Ab.{u + 1}]
        (upperStarFromPoint X) (upperStarFromPointComp f)
        (Mon.mk (Profinite.padicIntegersRingObj l E.1))
        (Mon.mk (Profinite.continuousMapRingObj E.1))
        (padicIntegersRingObjToContinuousMapRingObj l E)
    have hlegs := scalar_pullback_legs (f)^*[Ab.{u + 1}] l tX.hom ht
      (fun n ↦ (cY.ι.app n).hom ≫ eY.hom.hom)
      (fun n ↦ (cX.ι.app n).hom ≫ eX.hom.hom)
      d.hom.hom
      ((upperStarFromPointComp f).app (Profinite.padicIntegersRingObj l E.1)).hom
      (fun n ↦ ?_) (fun n ↦ ?_) ?_ m
    · apply (cancel_mono ((Mon.forget _).map eX.hom)).1
      change _ ≫ eX.hom.hom = _ ≫ eX.hom.hom
      rw [Category.assoc, ringIsoComposite]
      simpa only [Functor.map_comp, Category.assoc] using hlegs
    · have h := congrArg (fun k ↦ k.hom)
        (scalar_cocone_recurrence l (padicIntegersRegularModule Y l E) cY n)
      rw [Mod.nsmul_hom] at h
      simpa only [Preadditive.nsmul_comp] using congrArg (fun k ↦ k ≫ eY.hom.hom) h
    · have h := congrArg (fun k ↦ k.hom)
        (scalar_cocone_recurrence l (padicIntegersRegularModule X l E) cX n)
      rw [Mod.nsmul_hom] at h
      simpa only [Preadditive.nsmul_comp] using congrArg (fun k ↦ k ≫ eX.hom.hom) h
    · simpa only [heY0, heX0] using hn

/-- The finite-subextension colimit is preserved, and its canonical ring comparison is
alpha: the equation on every inclusion leg identifies the two colimit comparisons.

Source: blueprint pullback clause 3 (blueprint: det-prop-sfb-qlbar-colimit-x-pullback).
Proof: finite-subextension-valued sections give the point colimit: a compatible family
of additive maps extends by choosing a field containing the values of a section.
A finite compositum proves independence, additivity and uniqueness. Pulling back by
p_Z^* and then by f^* preserves this colimit by their adjunctions. Naturality of alpha
for every subextension inclusion identifies all diagram maps and every cocone leg;
uniqueness of a colimit map identifies the comparison with alpha. Tensor preserves
colimits separately, so multiplication is checked on each pair of subfield legs after
passing to their finite compositum. The unit is preserved on any leg. Thus the same
comparison is the ring comparison. Use sk-def-sfb-qlbar-condensed,
def-sfb-qlbar-subextension-map, def-sfb-qlbar-subextension-to-qlbar,
def-sfb-qlbar-x-cocone, sk-def-sfb-pullback-from-point-comp,
def-sfb-finite-upper-lower-star-adjunction and sk-def-sfb-sheaf-tensor. -/
theorem sfb_qlbar_comparison_pullback (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty (IsColimit ((f)^*[Ab.{u + 1}].mapCocone (padicAlgClRingObjCocone Y l))) ∧
      ∀ E : PadicAlgCl.FiniteIntermediateField l,
        (f)^*[Ab.{u + 1}].map (padicSubfieldRingObjToPadicAlgCl Y l E) ≫
            (coefficientPullbackIso f (Mon.mk (Profinite.padicAlgClRingObj l))).hom.hom =
          ((upperStarFromPointComp f).app (Profinite.continuousMapRingObj E.1)).hom ≫
            padicSubfieldRingObjToPadicAlgCl X l E := by
  constructor
  · exact ⟨isColimitOfPreserves (f)^*[Ab.{u + 1}]
      (isColimitPadicAlgClRingObjCocone Y l)⟩
  · intro E
    exact ringComparisonNaturality (upperStarFromPoint Y) (f)^*[Ab.{u + 1}]
      (upperStarFromPoint X) (upperStarFromPointComp f)
      (Mon.mk (Profinite.continuousMapRingObj E.1))
      (Mon.mk (Profinite.padicAlgClRingObj l))
      (Profinite.padicSubfieldRingObjToPadicAlgCl l E)

end AlgebraicGeometry.ProEtale
