/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteReductionPullback
public import Sheaf.Paper.PadicIntegersInvertEll
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation

import Mathlib.Algebra.Category.Ring.Limits
import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties

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

private theorem ringPullbackComposite
    {A B C : Type*} [Category A] [Category B] [Category C]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (e : F ⋙ G ≅ H) [NatTrans.IsMonoidal e.hom] (R : Mon A)
    (B' : B) [MonObj B'] (C' : C) [MonObj C']
    (p : F.obj R.X ≅ B') [IsMonHom p.hom]
    (q : H.obj R.X ≅ C') [IsMonHom q.hom] :
    ∃ c : G.obj B' ≅ C',
      G.mapIso p ≪≫ c = e.app R.X ≪≫ q ∧ IsMonHom c.hom ∧ IsMonHom c.inv := by
  let p' : F.mapMon.obj R ≅ Mon.mk B' := Mon.mkIso' p
  let q' : H.mapMon.obj R ≅ Mon.mk C' := Mon.mkIso' q
  let d : G.mapMon.obj (F.mapMon.obj R) ≅ H.mapMon.obj R :=
    (Functor.mapMonCompIso (F := F) (G := G)).symm.app R ≪≫
      (Functor.mapMonNatIso e).app R
  let c := G.mapMon.mapIso p'.symm ≪≫ d ≪≫ q'
  refine ⟨(Mon.forget C).mapIso c, ?_, ?_, ?_⟩
  · apply Iso.ext
    change G.map p.hom ≫ (G.map p.inv ≫ d.hom.hom ≫ q.hom) = _
    rw [← Category.assoc, ← G.map_comp, p.hom_inv_id, G.map_id, Category.id_comp]
    dsimp only [d]
    simp only [Iso.trans_hom, Mon.comp_hom', Iso.app_hom, Iso.symm_hom,
      Functor.mapMonCompIso_inv_app_hom, Functor.mapMonNatIso_hom_app_hom]
    change (𝟙 _ ≫ e.hom.app R.X) ≫ q.hom = _
    rw [Category.id_comp]
  · exact inferInstanceAs (IsMonHom c.hom.hom)
  · exact inferInstanceAs (IsMonHom c.inv.hom)

private def sfbConstantRingAbNatIso (X : Scheme.{u}) :
    constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} ⋙
        sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1}) ≅
      forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1} ⋙
        constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  let : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  let : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  Functor.isoWhiskerRight
    (constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})) ≪≫
    Functor.isoWhiskerLeft (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      (constantCommuteCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} Ab.{u + 1}))

private def sfbConstantRingAbPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1} ⋙
        sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        sheafCompose (Scheme.ProEt.topology Y) (forget₂ RingCat.{u + 1} Ab.{u + 1})) ⋙
        (f)^*[Ab.{u + 1}] ≅
      constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} ⋙
        sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
  Functor.isoWhiskerRight (sfbConstantRingAbNatIso Y) (f)^*[Ab.{u + 1}] ≪≫
    Functor.isoWhiskerLeft
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})
      (constantSheafCompUpperStarIso Ab.{u + 1} f) ≪≫
    (sfbConstantRingAbNatIso X).symm

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

private lemma constantRingAbPullback_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : CommRingCat.{u + 1}) :
    (sfbConstantRingAbPullback f).app A =
      (f)^*[Ab.{u + 1}].mapIso (sfbConstantRingAbIso Y A) ≪≫
        (constantSheafCompUpperStarIso Ab.{u + 1} f).app (AddCommGrpCat.of A) ≪≫
          (sfbConstantRingAbIso X A).symm := by
  rfl

private lemma finiteCoefficientPullback_naturality (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (f)^*[Ab.{u + 1}].map
        ((sheafCompose (Scheme.ProEt.topology Y) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (integralCoefficientSheafTransition l E Y n)) ≫
      (sfbFiniteCoefficientPullbackIso l E f n).hom =
    (sfbFiniteCoefficientPullbackIso l E f (n + 1)).hom ≫
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (integralCoefficientSheafTransition l E X n) := by
  let A := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 2)))
  let B := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let a : A ⟶ B := CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
      ((Padic.coefficientExtensionTransition l E (n + 1)).comp
        (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))
  have h := (sfbConstantRingAbPullback f).hom.naturality a
  change _ ≫ ((sfbConstantRingAbPullback f).app B).hom =
    ((sfbConstantRingAbPullback f).app A).hom ≫ _ at h
  rw [constantRingAbPullback_app, constantRingAbPullback_app] at h
  exact h


private def cone_transport {J C : Type*} [Category J] [Category C]
    {F G : J ⥤ C} (e : F ≅ G) (s : Cone F) (t : Cone G) (ht : IsLimit t)
    (p : s.pt ≅ t.pt) (hp : ∀ j, s.π.app j ≫ (e.app j).hom = p.hom ≫ t.π.app j) :
    IsLimit s := by
  apply (IsLimit.postcomposeHomEquiv e s).toFun
  apply ht.ofIsoLimit
  refine Cone.ext p.symm ?_
  intro j
  dsimp
  change t.π.app j = p.inv ≫ (s.π.app j ≫ (e.app j).hom)
  rw [hp, ← Category.assoc, p.inv_hom_id, Category.id_comp]

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
  obtain ⟨aX, qX, jX, hjX, hqX, _, _, _, eX, heX, _⟩ :=
    sfb_integral_coefficient_limit l (ULift.{u} E.1) X
  obtain ⟨aY, qY, jY, hjY, hqY, _, _, _, eY, heY, _⟩ :=
    sfb_integral_coefficient_limit l (ULift.{u} E.1) Y
  have hX : SfbIntegralComparison l (ULift.{u} E.1) X eX :=
    ⟨heX.1, heX.2.1, aX, qX, jX, hjX, hqX, heX.2.2⟩
  have hY : SfbIntegralComparison l (ULift.{u} E.1) Y eY :=
    ⟨heY.1, heY.2.1, aY, qY, jY, hjY, hqY, heY.2.2⟩
  have : IsMonHom eY.hom := hY.1
  have : IsMonHom eX.hom := hX.1
  obtain ⟨c, hc, hcmon, hcmon'⟩ := ringPullbackComposite
    (upperStarFromPoint Y) (f)^*[Ab.{u + 1}] (upperStarFromPoint X)
    (upperStarFromPointComp f) (sfbCondensedIntegers l (ULift.{u} E.1))
    _ _ eY eX
  have hp : ∀ n : ℕ,
      (f)^*[Ab.{u + 1}].map
          ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (limit.π (integralCoefficientSheafSystem l (ULift.{u} E.1) Y) (op n))) ≫
          (sfbFiniteCoefficientPullbackIso l (ULift.{u} E.1) f n).hom =
        c.hom ≫ (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (limit.π (integralCoefficientSheafSystem l (ULift.{u} E.1) X) (op n)) := by
    intro n
    have hq : jY.hom ≫ qY.π.app (op n) = jX.hom ≫ qX.π.app (op n) := by
      ext x
      exact (hjY n x).trans (hjX n x).symm
    have hr := sfb_finite_reduction_pullback l (ULift.{u} E.1) f n aX aY
      (jX.hom ≫ qX.π.app (op n))
      (eX.hom ≫ (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (limit.π (integralCoefficientSheafSystem l (ULift.{u} E.1) X) (op n)))
      (eY.hom ≫ (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (limit.π (integralCoefficientSheafSystem l (ULift.{u} E.1) Y) (op n)))
      (fun S g ↦ heX.2.2 S g n) (fun S g ↦ by
        rw [← hq]
        exact heY.2.2 S g n)
    have hc' := congrArg Iso.hom hc
    change (f)^*[Ab.{u + 1}].map eY.hom ≫ c.hom =
      ((upperStarFromPointComp f).app (sfbCondensedIntegers l (ULift.{u} E.1)).X).hom ≫
        eX.hom at hc'
    apply (cancel_epi ((f)^*[Ab.{u + 1}].map eY.hom)).1
    rw [← Category.assoc, ← Functor.map_comp, hr, ← Category.assoc, ← hc',
      Category.assoc]
  refine ⟨eX, eY, hX, hY, c, hc, hcmon, hcmon', hp, ?_⟩
  let FY := integralCoefficientSheafSystem l (ULift.{u} E.1) Y ⋙
    sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let FX := integralCoefficientSheafSystem l (ULift.{u} E.1) X ⋙
    sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let h : FY ⋙ (f)^*[Ab.{u + 1}] ⟶ FX :=
    NatTrans.ofOpSequence
      (fun n ↦ (sfbFiniteCoefficientPullbackIso l (ULift.{u} E.1) f n).hom)
      (fun n ↦ by
        simp only [FY, FX, Functor.comp_map, integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ]
        exact finiteCoefficientPullback_naturality l (ULift.{u} E.1) f n)
  let e : FY ⋙ (f)^*[Ab.{u + 1}] ≅ FX :=
    NatIso.ofComponents (fun n ↦ sfbFiniteCoefficientPullbackIso l (ULift.{u} E.1) f n.unop)
      (fun g ↦ h.naturality g)
  have : PreservesLimitsOfShape ℕᵒᵖ
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1}) ⋙
        sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) := by
    change PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (Scheme.ProEt.topology X) RingCat.{u + 1} ⋙
        (Functor.whiskeringRight X.ProEtᵒᵖ RingCat.{u + 1} Ab.{u + 1}).obj
          (forget₂ RingCat.{u + 1} Ab.{u + 1}))
    infer_instance
  have : PreservesLimitsOfShape ℕᵒᵖ
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})) :=
    preservesLimitsOfShape_of_reflects_of_preserves
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1}))
      (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  exact ⟨cone_transport e _ _
    (isLimitOfPreserves
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1}))
      (limit.isLimit (integralCoefficientSheafSystem l (ULift.{u} E.1) X)))
    c (fun n ↦ by
      change (f)^*[Ab.{u + 1}].map
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (limit.π (integralCoefficientSheafSystem l (ULift.{u} E.1) Y) n)) ≫ _ = _
      exact hp n.unop)⟩

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
