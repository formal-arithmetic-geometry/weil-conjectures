/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C9
-/
module

public import Sheaf.Paper.EtaleSystemCofinalData
import Sheaf.Paper.EtaleSystemProjectionEvaluation
import Sheaf.Paper.EtaleSystemProjectionCoherence
import Sheaf.Paper.EtaleCofinalExtensionExistence
import Sheaf.Paper.EtaleCofinalSupportEvaluation

/-! # Geometric realization of cofinal support

Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u a av b bv c cv d dv e ev g gv
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

attribute [local irreducible] WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings

section Pushforward
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {C : Type c} [Category.{cv} C]
    {J : GrothendieckTopology A} {K : GrothendieckTopology B}
    {L : GrothendieckTopology C} {F : A ⥤ B} {G : B ⥤ C}
    [F.IsContinuous J K] [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} {R' : Sheaf L RingCat.{u}}

private theorem pushforwardComp_sections
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj R')
    (χ : S ⟶ ((F ⋙ G).sheafPushforwardContinuous RingCat.{u} J L).obj R')
    (he : φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ = χ) :
    ∃ e : SheafOfModules.pushforward.{u} ψ ⋙ SheafOfModules.pushforward.{u} φ ≅
        SheafOfModules.pushforward.{u} (F := F ⋙ G) χ,
      ∀ (M : SheafOfModules.{u} R') (U : Aᵒᵖ)
        (x : ((SheafOfModules.pushforward.{u} ψ ⋙
          SheafOfModules.pushforward.{u} φ).obj M).val.obj U),
        HEq (((e.hom.app M).val.app U) x) x := by
  refine ⟨SheafOfModules.pushforwardComp φ ψ ≪≫
    SheafOfModules.pushforwardCongr (F := F ⋙ G) (R := R') he, ?_⟩
  intro M U x
  exact heq_of_eq ((SheafOfModules.pushforwardCongr_hom_app_val_app
    (F := F ⋙ G) (R := R') he M U
    (((SheafOfModules.pushforwardComp φ ψ).hom.app M).val.app U x)).trans
      (SheafOfModules.pushforwardComp_hom_app_val_app φ ψ M U x))

end Pushforward

set_option linter.unusedVariables false in
private theorem restrictionComposition_nonempty (W : Scheme.{u}) {l : ℕ}
    (B : Coefficients.{u} l) (r s : ℕ ↪o ℕ) : Nonempty (CofinalComposition W B r s) := by
  let J := WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology
  let : (cofinalSite W s ⋙ cofinalSite W r).IsContinuous J J :=
    Functor.isContinuous_comp _ _ _ J _
  let φr := eqToHom (cofinalRing W B r).symm
  let φs := eqToHom (cofinalRing W (cofinalCoefficients B r) s).symm
  let φrs := eqToHom (cofinalRing W B (s.trans r)).symm
  let H := (cofinalSite W s).sheafPushforwardContinuous RingCat.{u + 1}
    (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
    (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
  have he : φs ≫ H.map φr = φrs := by
    simp only [φr, φs, φrs, eqToHom_map, eqToHom_trans]
  obtain ⟨e, hs⟩ := pushforwardComp_sections
    (F := cofinalSite W s) (G := cofinalSite W r)
    (R' := WeilConjectures.SemilinearSections.ring J (rings W B.rings)) φs φr φrs he
  exact ⟨{ ordinary := e, sections := fun M n U x ↦ hs M (op (n, U.unop)) x }⟩

section Comparison
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
    {E : Type e} [Category.{ev} E] {G : Type g} [Category.{gv} G]
    {Lx : A ⥤ C} {Rx : A ⥤ B} {Sx : B ⥤ C}
    {Ly : D ⥤ G} {Ry : D ⥤ E} {Sy : E ⥤ G}
    {FB : C ⥤ G} {FD : B ⥤ E} {FS : A ⥤ D}
    (Fx : Lx ≅ Rx ⋙ Sx) (Fy : Ly ≅ Ry ⋙ Sy)
    (q : FD ⋙ Sy ≅ Sx ⋙ FB) (κ : Rx ⋙ FD ≅ FS ⋙ Ry)

private def supportComparison : Lx ⋙ FB ≅ FS ⋙ Ly :=
  Functor.isoWhiskerRight Fx FB ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft Rx q.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight κ Sy ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft FS Fy.symm

private theorem supportComparison_normalization (N : A) :
    q.hom.app (Rx.obj N) ≫ FB.map (Fx.inv.app N) ≫
      (supportComparison Fx Fy q κ).hom.app N ≫ Fy.hom.app (FS.obj N) =
    Sy.map (κ.hom.app N) := by
  simp only [supportComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Category.id_comp, Category.assoc, Iso.inv_hom_id_app]
  rw [← FB.map_comp_assoc, Fx.inv_hom_id_app]
  rw [FB.map_id ((Rx ⋙ Sx).obj N)]
  simpa only [Functor.comp_obj, Category.id_comp, Category.comp_id] using
    q.hom_inv_id_app_assoc (Rx.obj N) (Sy.map (κ.hom.app N))

end Comparison

private theorem level_jointly_reflects (W : Scheme.{u})
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    JointlyReflectIsomorphisms (level W B) where
  isIso {M N} h hh := by
    have : IsIso
        ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map h) := by
      apply (NatTrans.isIso_iff_isIso_app _).2
      intro U
      have := hh U.unop.1
      have hs : IsIso (((level W B U.unop.1).map h).hom.app (op U.unop.2)) :=
        inferInstance
      have hb := (ConcreteCategory.isIso_iff_bijective
        (((level W B U.unop.1).map h).hom.app (op U.unop.2))).1 hs
      apply (ConcreteCategory.isIso_iff_bijective _).2
      change Function.Bijective (fun x ↦ h.val.app U x) at hb ⊢
      exact hb
    exact isIso_of_reflects_iso h
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)

private theorem projection_isIso_of_single
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (t : Theory c l) {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings)
    (hi : ∀ n : ℕ, IsIso (compactScalarMap (a.app (op n)).hom c)) : IsIso (t.q a) := by
  suffices ∀ M, IsIso ((t.q a).app M) from
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this
  intro M
  let : ∀ n, (level Y C.rings n).Additive := fun n ↦ (t.evaluationY C n).additive
  let : ∀ n, PreservesFiniteLimits (level Y C.rings n) :=
    fun n ↦ (t.evaluationY C n).limits
  let : ∀ n, PreservesFiniteColimits (level Y C.rings n) :=
    fun n ↦ (t.evaluationY C n).colimits
  apply (Functor.jointlyReflectIsomorphisms_mapDerivedCategory
    (level_jointly_reflects Y C.rings)).isIso_iff _ |>.2
  intro n
  have := hi n
  have he : IsIso
      ((scalarExtension (a.app (op n)).hom Y).map
          ((t.supportEvaluation B n).iso.inv.app M) ≫
        (t.scalarEvaluationY a n).iso.inv.app ((t.support B).F.obj M) ≫
        (t.evaluationY C n).E.map ((t.q a).app M) ≫
        (t.supportEvaluation C n).iso.hom.app ((t.scalarX a).model.T.obj M) ≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (C.rings.obj (op n))) c).map
            ((t.scalarEvaluationX a n).iso.hom.app M)) := by
    rw [etaleSystemProjection_evaluation c l t B C a n M]
    infer_instance
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using he

attribute [local irreducible] CofinalRepeatSupport.kappa

/-- The geometric cofinal-extension presentation, before taking a support right mate.
Source: Zheng, Construction 4.1, printed p. 21, and the paragraph preceding Lemma 4.10,
printed p. 23; finite-block form of the coefficient construction
(blueprint: lem-pur-etale-cofinal-support-realization).

Proof: let t(m) be the least i with m ≤ r(i). It is monotone, onto, and its fibers
are nonempty finite intervals: t(r(i))=i and t(m)=i implies m≤r(i). Apply the block
repetition theorem on each small etale site to obtain the exact repetition functors,
their endpoint adjunctions, and preservation of K-injective complexes. Normalize the
ordinary proper comparison on sections, and the open comparison by the extension by
zero adjunction. Their derived composite is exactly CofinalRepeatSupport.kappa.
Transport the selected ordinary extension through strictSystemSequenceEquivalence.
It has at m the tensor C_m ⊗_{C_{r(t(m))}} N_{t(m)}, with transitions given by the
original system transition followed by the tensor associator. Its unit has component
x↦1⊗x at a selected index. The ordinary selected-extension theorem proves its
adjunction to the actual sectionwise cofinalRestriction, not just to an isomorphic
unrecorded restriction. Derive this adjunction using flat-term K-flat representatives
on the sequence site. Evaluation is an exact ringed-topos inverse image and takes
these representatives to level K-flat representatives. The normalized derived-mate
comparison therefore supplies the recorded level isomorphism and its representative
normalization. Transport through a flat-term K-flat resolution also proves computation
on every K-flat representative, by the acyclic K-flat cone criterion.
The ordinary extension is repetition followed by change of coefficients for the actual
map D_m=C_{r(t(m))}→C_m. Identify those left adjoints by equality of their units. On
simultaneously level K-flat representatives both compute the same ordinary strict
complex, including transitions; universal left-derived uniqueness supplies the
factorization and exactly its displayed counit normalization.
Use etaleSystemCoefficientProjection for the fixed compactification. Its q for D→C
is invertible. Define h by the X factorization, the inverse of q on repeated systems,
the derived repetition comparison kappa, and the inverse Y factorization. Cancellation
of these four factors proves the support normalization. Evaluate the same word at m.
The normalized cochain comparisons identify repetition with evaluation at t(m), and
coefficient projection evaluation is compactScalarMap for C_{r(t(m))}→C_m. Cancel the
ordinary/derived factorization isomorphisms to obtain precisely CofinalSupport.evaluation.
Choose the ordinary restriction compositors to be identity on selected sections and
localize them. These constructions give every field of CofinalSupport. No right adjoint
to compact support, counit formula for such a right adjoint, or subsequence coherence
is used in this construction. -/
theorem etaleCofinalSupport_realization
    (k : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (hl : l.Prime) (hlp : l ≠ k.p)
    (X Y : Over (Spec (CommRingCat.of k.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) :
    ∃ t : CofinalSupport c l,
      (∀ (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings),
        IsIso (t.projection.q a)) ∧
      (∀ (B C D : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings),
        t.projection.q (a ≫ b) = t.projection.path a b) := by
  classical
  obtain ⟨_, _, _, _, _, _, _, hsingle, _⟩ :=
    etaleSystemCoefficientProjection k l hl hlp X Y f c
  obtain ⟨T, hgeom⟩ := etaleCofinalBlockFactorization c l
  have hi (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings) : IsIso (T.q a) := by
    apply projection_isIso_of_single T a
    intro n
    exact (hsingle _ _ (B.finite n) (C.finite n) (B.torsion n) (C.torsion n)
      (a.app (op n))).1
  have he := etaleSystemProjection_evaluation c l T
  obtain ⟨hc, -⟩ := etaleSystemProjection_coherence c l T
  let Lx : ∀ (B : Coefficients.{u} l) (r : ℕ ↪o ℕ), CofinalExtension X.left B r :=
    fun B r ↦ Classical.choice (etaleCofinalExtension_nonempty X.left B r)
  let Ly : ∀ (B : Coefficients.{u} l) (r : ℕ ↪o ℕ), CofinalExtension Y.left B r :=
    fun B r ↦ Classical.choice (etaleCofinalExtension_nonempty Y.left B r)
  choose R Fx Fy hdata using fun B r ↦ hgeom B r (Lx B r) (Ly B r)
  let data := fun B r ↦ Classical.choice (hdata B r)
  let h : ∀ (B : Coefficients.{u} l) (r : ℕ ↪o ℕ),
      (Lx B r).model.derived ⋙ (T.support B).F ≅
        (T.support (cofinalCoefficients B r)).F ⋙ (Ly B r).model.derived := fun B r ↦ by
    have := hi (cofinalRepeated B r) B (cofinalCoefficient B r)
    exact supportComparison (Fx B r).derived (Fy B r).derived
      (asIso (T.q (cofinalCoefficient B r))) (R B r).kappa
  have hn (B : Coefficients.{u} l) (r : ℕ ↪o ℕ)
      (N : Derived X.left (cofinalCoefficients B r).rings) :
      (T.q (cofinalCoefficient B r)).app ((R B r).x.R.mapDerivedCategory.obj N) ≫
        (T.support B).F.map ((Fx B r).derived.inv.app N) ≫ (h B r).hom.app N ≫
        (Fy B r).derived.hom.app ((T.support (cofinalCoefficients B r)).F.obj N) =
      (T.scalarY (cofinalCoefficient B r)).model.T.map ((R B r).kappa.hom.app N) := by
    have := hi (cofinalRepeated B r) B (cofinalCoefficient B r)
    exact supportComparison_normalization (Fx B r).derived (Fy B r).derived
      (asIso (T.q (cofinalCoefficient B r))) (R B r).kappa N
  refine ⟨{ projection := T
            extensionX := Lx
            extensionY := Ly
            compositionX := fun B r s ↦
              Classical.choice (restrictionComposition_nonempty X.left B r s)
            compositionY := fun B r s ↦
              Classical.choice (restrictionComposition_nonempty Y.left B r s)
            repetition := R
            factorX := Fx
            factorY := Fy
            h := h
            normalization := hn
            evaluation := ?_ }, hi, hc⟩
  intro B r
  have := hi (cofinalRepeated B r) B (cofinalCoefficient B r)
  exact etaleCofinalSupport_evaluation T B r (Lx B r) (Ly B r) (R B r) (Fx B r) (Fy B r) (data B r)
    (he (cofinalRepeated B r) B (cofinalCoefficient B r)) (h B r) (hn B r)

end AlgebraicGeometry.Etale.SystemProjection
