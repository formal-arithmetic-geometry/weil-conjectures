/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.CategoryTheory.SystemScalarCoherence
public import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
import Sheaf.CategoryTheory.RingedCompleteTriangulated
import all Sheaf.CategoryTheory.UnitPowerCompleteness
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeCoordinates
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeTensor
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.CategoryTheory.FlatScalarKoszulTowerComparison
import Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport
import Sheaf.Paper.FlatRingedIdealCompleteEquivalence
import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.CategoryTheory.RingedCechKoszulHomLimitComparison
import Sheaf.CategoryTheory.RingedCechCompletionUnitIdempotence
import Sheaf.Paper.ExtendedCechCompletionModel

/-! # Finite-free scalar extension and Koszul completion

Source: Stacks Project, algebraization.tex, Tags 099B and 0A0E; the finite-free
scalar-extension argument extracted from blueprint `prop-weil-pbc-scalar-extension`,
steps 6--7 (blueprint: lem-weil-pbc-finite-free-completion-transport).

The four statements give existence and uniqueness of the unit-normalized comparison,
preservation of local completeness, integer-shift compatibility, the actual tensor-unit
normalization, and balanced tensor composition. Binary composition iterates to any finite
tower. No basis is part of the comparison data.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
variable [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
  (derivedChangeRingIndependentCoefficients J R))]
variable [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
  (derivedChangeRingIndependentCoefficients J S))]

private theorem completion_unit_properties
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients J O))]
    (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (D : RingedKoszulLimitPresentation O r b) :
    (∀ (X Y : ringedSiteDerived O) (f : X ⟶ Y),
      f ≫ D.unit Y = D.unit X ≫ D.completion.map f) ∧
    (∀ X, IsIso (D.completion.map (D.unit X))) ∧
    (∀ X, IsIso (D.unit (D.completion.obj X))) := by
  obtain ⟨θ, hθ⟩ := exists_ringed_cech_koszul_hom_limit_comparison O r b D
  let L := ringedCechCompletionFunctor O (ringedExtendedCech O r b).1
  let η := ringedCechCompletionUnit O (ringedExtendedCech O r b).1
    (ringedExtendedCech O r b).2
  have hn (X Y : ringedSiteDerived O) (f : X ⟶ Y) :
      f ≫ η Y = η X ≫ L.map f :=
    (completion_unit_natural O _ _ X Y f).symm
  have hnat (X Y : ringedSiteDerived O) (f : X ⟶ Y) :
      f ≫ D.unit Y = D.unit X ≫ D.completion.map f := by
    rw [← hθ X, ← hθ Y, Category.assoc, ← θ.hom.naturality,
      ← Category.assoc, hn, Category.assoc]
  refine ⟨hnat, ?_, ?_⟩
  · intro X
    have : IsIso (L.map (η X)) :=
      (ringed_cech_completion_unit_idempotence O r b X).1
    have : IsIso (L.map (D.unit X)) := by
      rw [← hθ X, L.map_comp]
      infer_instance
    have hi : IsIso (θ.hom.app X ≫ D.completion.map (D.unit X)) := by
      rw [← θ.hom.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left (θ.hom.app X) _
  · intro X
    have : IsIso (η (L.obj X)) :=
      (ringed_cech_completion_unit_idempotence O r b X).2
    have hi : IsIso (θ.hom.app X ≫ η (D.completion.obj X)) := by
      rw [hn]
      infer_instance
    have : IsIso (η (D.completion.obj X)) :=
      IsIso.of_isIso_comp_left (θ.hom.app X) _
    rw [← hθ]
    infer_instance

private theorem unit_cancel
    {V : Type*} [Category V] (L : V ⥤ V) (η : ∀ X, X ⟶ L.obj X)
    (hn : ∀ {X Y} (f : X ⟶ Y), f ≫ η Y = η X ≫ L.map f)
    (hi : ∀ X, IsIso (L.map (η X)))
    {X Y : V} [IsIso (η Y)] {f g : L.obj X ⟶ Y}
    (h : η X ≫ f = η X ≫ g) : f = g := by
  have := hi X
  have hm : L.map f = L.map g := by
    apply (cancel_epi (L.map (η X))).mp
    simpa only [L.map_comp] using congrArg L.map h
  apply (cancel_mono (η Y)).mp
  rw [hn, hn, hm]

private theorem transport_cancel
    {V W : Type*} [Category V] [Category W]
    (F : V ⥤ W) (L : V ⥤ V) (K : W ⥤ W)
    (η : ∀ X, X ⟶ L.obj X) (ε : ∀ X, X ⟶ K.obj X)
    (hn : ∀ {X Y} (f : X ⟶ Y), f ≫ ε Y = ε X ≫ K.map f)
    (hi : ∀ X, IsIso (K.map (ε X)))
    (κ : L ⋙ F ≅ F ⋙ K)
    (hκ : ∀ X, F.map (η X) ≫ κ.hom.app X = ε (F.obj X))
    {X : V} {Y : W} [IsIso (ε Y)] {f g : F.obj (L.obj X) ⟶ Y}
    (h : F.map (η X) ≫ f = F.map (η X) ≫ g) : f = g := by
  have he : ε (F.obj X) ≫ (κ.inv.app X ≫ f) =
      ε (F.obj X) ≫ (κ.inv.app X ≫ g) := by
    rw [← hκ X]
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using h
  have hh := unit_cancel K ε hn hi he
  exact (cancel_epi (κ.inv.app X)).mp hh

private theorem principal_reflector
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients J O))]
    (t : (O.obj ⋙ forget CommRingCat).sections)
    (D : RingedKoszulLimitPresentation O 1 (fun _ ↦ t)) :
    (∀ X, IsLocallyDerivedRingedIdealComplete O
      (image (ringedKoszulScalar O t)) (image.ι (ringedKoszulScalar O t))
        (D.completion.obj X)) ∧
    (∀ X Y, IsLocallyDerivedRingedIdealComplete O
      (image (ringedKoszulScalar O t)) (image.ι (ringedKoszulScalar O t)) Y →
      Function.Bijective (fun f : D.completion.obj X ⟶ Y ↦ D.unit X ≫ f)) ∧
    (∀ X, IsIso (D.unit X) ↔ IsLocallyDerivedRingedIdealComplete O
      (image (ringedKoszulScalar O t)) (image.ι (ringedKoszulScalar O t)) X) := by
  obtain ⟨D₀, hc, hb, hi, _⟩ := ringedKoszulCompletionReflector O 1 (fun _ ↦ t)
    (image (ringedKoszulScalar O t)) (image.ι (ringedKoszulScalar O t))
    (principal_generators O t)
  obtain ⟨θ₀, hθ₀⟩ := exists_ringed_cech_koszul_hom_limit_comparison O 1 (fun _ ↦ t) D₀
  obtain ⟨θ, hθ⟩ := exists_ringed_cech_koszul_hom_limit_comparison O 1 (fun _ ↦ t) D
  let k := θ₀.symm ≪≫ θ
  have hk (X : ringedSiteDerived O) : D₀.unit X ≫ k.hom.app X = D.unit X := by
    rw [← hθ₀ X]
    simp only [k, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
      Iso.hom_inv_id_app_assoc]
    exact hθ X
  refine ⟨?_, ?_, ?_⟩
  · intro X
    exact complete_of_iso O _ _ (k.app X) (hc X)
  · intro X Y hY
    constructor
    · intro f g h
      apply (cancel_epi (k.hom.app X)).mp
      apply (hb X Y hY).1
      simpa only [← Category.assoc, hk] using h
    · intro f
      obtain ⟨g, hg⟩ := (hb X Y hY).2 f
      refine ⟨k.inv.app X ≫ g, ?_⟩
      rw [← hk]
      simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hg
  · intro X
    rw [← hk, isIso_comp_right_iff]
    exact hi X

omit [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
    (derivedChangeRingIndependentCoefficients J R))]
  [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
    (derivedChangeRingIndependentCoefficients J S))] in
private theorem finite_free_coordinates
    (A : SystemScalarModel.{u, u, u} a)
    (hfree : ∃ d : ℕ, Nonempty
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (SheafOfModules.unit (derivedChangeRingIndependentCoefficients J S)) ≅
        ∐ (fun _ : Fin d ↦
          SheafOfModules.unit (derivedChangeRingIndependentCoefficients J R)))) :
    ∃ d : ℕ, ∀ X : ringedSiteDerived R, Nonempty
      ((⨁ fun _ : Fin d ↦ X) ≅
        (FlatScalarKoszul.restrictDerived a).obj (A.model.T.obj X)) := by
  classical
  obtain ⟨d, ⟨e⟩⟩ := hfree
  let e' := e ≪≫ (Sigma.reindex (Equiv.ulift : ULift.{u} (Fin d) ≃ Fin d)
    (fun _ : Fin d ↦
      SheafOfModules.unit (derivedChangeRingIndependentCoefficients J R))).symm
  obtain ⟨AR, MR, _, _⟩ := ringedDerived_closed_symmetric_monoidal.{u, u, u, u + 1} J R
  obtain ⟨AS, MS, _, _⟩ := ringedDerived_closed_symmetric_monoidal.{u, u, u, u + 1} J S
  obtain ⟨κ, μ, hκ, hμ⟩ :=
    ringedFiniteFreeHomBaseChange_tensor.{u, u, u, u + 1} J a A.model AR AS MR MS
  obtain ⟨_, _, _, _, hc⟩ :=
    ringedFiniteFreeHomBaseChange_coordinates.{u, u, u, u + 1} J a d e'
      A.model.E A.model.obj_eq A.model.map_eq A.model.T A.model.ε A.model.universal
      AR AS MR MS κ μ hκ (by
        intro P Q hP hQ
        obtain ⟨hEP, hEQ, heq⟩ := hμ P Q hP hQ
        exact ⟨hEP, hEQ, A.model.computes P hP, A.model.computes Q hQ, heq⟩)
  refine ⟨d, fun X ↦ ?_⟩
  obtain ⟨_, q, _, _⟩ := hc X X
  exact ⟨q⟩

private theorem finite_free_flat
    (A : SystemScalarModel.{u, u, u} a)
    (hfree : ∃ d : ℕ, Nonempty
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (SheafOfModules.unit (derivedChangeRingIndependentCoefficients J S)) ≅
        ∐ (fun _ : Fin d ↦
          SheafOfModules.unit (derivedChangeRingIndependentCoefficients J R)))) :
    PreservesFiniteLimits (SheafOfModules.RingedTensor.tensorFunctor a) ∧
      PreservesFiniteColimits (SheafOfModules.RingedTensor.tensorFunctor a) := by
  obtain ⟨d, ⟨e⟩⟩ := hfree
  let e' := (Sigma.reindex (Equiv.ulift : ULift.{u} (Fin d) ≃ Fin d)
    (fun _ : Fin d ↦
      SheafOfModules.unit (derivedChangeRingIndependentCoefficients J R))) ≪≫ e.symm
  obtain ⟨hL, hC, _⟩ := finiteFreeStrictTowerTransport a A.model ⟨d, ⟨e'⟩⟩
  let k := Adjunction.leftAdjointUniq A.ordinaryAdj
    (SheafOfModules.RingedTensor.tensorAdjunction a)
  exact ⟨preservesFiniteLimits_of_natIso k, preservesFiniteColimits_of_natIso k⟩

private theorem restriction_complete_iff
    (hflat : PreservesFiniteLimits (SheafOfModules.RingedTensor.tensorFunctor a) ∧
      PreservesFiniteColimits (SheafOfModules.RingedTensor.tensorFunctor a))
    (t : (R.obj ⋙ forget CommRingCat).sections) (Y : ringedSiteDerived S) :
    IsLocallyDerivedRingedIdealComplete R
      (image (ringedKoszulScalar R t)) (image.ι (ringedKoszulScalar R t))
      ((FlatScalarKoszul.restrictDerived a).obj Y) ↔
    IsLocallyDerivedRingedIdealComplete S
      (image (ringedKoszulScalar S (FlatScalarKoszul.imageSections a (fun _ : Fin 1 ↦ t) 0)))
      (image.ι (ringedKoszulScalar S
        (FlatScalarKoszul.imageSections a (fun _ : Fin 1 ↦ t) 0))) Y := by
  obtain ⟨_, DB, DR, _, _, γ, _, _, hγ⟩ :=
    FlatScalarKoszul.flatScalarKoszulTowerComparison a hflat 1 (fun _ ↦ t)
  have hu := hγ.2.2.2.2.2.1
  have hR := (principal_reflector R t DR).2.2
  have hS := (principal_reflector S
    (FlatScalarKoszul.imageSections a (fun _ : Fin 1 ↦ t) 0) DB).2.2
  rw [← hR, ← hS, ← hu, isIso_comp_right_iff]
  have : (FlatScalarKoszul.restrictDerived a).ReflectsIsomorphisms :=
    siteDerivedRestrictScalars_reflectsIsomorphisms a
  constructor
  · intro h
    let := h
    exact isIso_of_reflects_iso _ (FlatScalarKoszul.restrictDerived a)
  · intro h
    let := h
    infer_instance

private theorem adjoint_reflector_transport
    {V W : Type*} [Category V] [Category W]
    (F : V ⥤ W) (U : W ⥤ V) (adj : F ⊣ U)
    (L : V ⥤ V) (K : W ⥤ W) (η : ∀ X, X ⟶ L.obj X) (ε : ∀ X, X ⟶ K.obj X)
    (P : V → Prop) (Q : W → Prop)
    (hn : ∀ {X Y} (f : X ⟶ Y), f ≫ η Y = η X ≫ L.map f)
    (hm : ∀ {X Y} (f : X ⟶ Y), f ≫ ε Y = ε X ≫ K.map f)
    (hc : ∀ X, P (L.obj X)) (hd : ∀ X, Q (K.obj X))
    (hb : ∀ X Y, P Y → Function.Bijective (fun f : L.obj X ⟶ Y ↦ η X ≫ f))
    (he : ∀ X Y, Q Y → Function.Bijective (fun f : K.obj X ⟶ Y ↦ ε X ≫ f))
    (hF : ∀ X, P X → Q (F.obj X)) (hU : ∀ Y, Q Y → P (U.obj Y)) :
    ∃ κ : L ⋙ F ≅ F ⋙ K, ∀ X, F.map (η X) ≫ κ.hom.app X = ε (F.obj X) := by
  classical
  have hj (X : V) (Y : W) (hY : Q Y) :
      Function.Bijective (fun f : F.obj (L.obj X) ⟶ Y ↦ F.map (η X) ≫ f) := by
    constructor
    · intro f g h
      apply (adj.homEquiv _ _).injective
      apply (hb X (U.obj Y) (hU Y hY)).1
      simpa only [← adj.homEquiv_naturality_left] using congrArg (adj.homEquiv X Y) h
    · intro f
      obtain ⟨g, hg⟩ := (hb X (U.obj Y) (hU Y hY)).2 ((adj.homEquiv X Y) f)
      refine ⟨(adj.homEquiv (L.obj X) Y).symm g, ?_⟩
      apply (adj.homEquiv X Y).injective
      rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
      exact hg
  let f (X : V) := (hj X (K.obj (F.obj X)) (hd _)).2 (ε (F.obj X)) |>.choose
  have hf (X : V) : F.map (η X) ≫ f X = ε (F.obj X) :=
    (hj X (K.obj (F.obj X)) (hd _)).2 (ε (F.obj X)) |>.choose_spec
  let g (X : V) := (he (F.obj X) (F.obj (L.obj X)) (hF _ (hc _))).2
    (F.map (η X)) |>.choose
  have hg (X : V) : ε (F.obj X) ≫ g X = F.map (η X) :=
    (he (F.obj X) (F.obj (L.obj X)) (hF _ (hc _))).2
      (F.map (η X)) |>.choose_spec
  let k (X : V) : F.obj (L.obj X) ≅ K.obj (F.obj X) :=
    { hom := f X
      inv := g X
      hom_inv_id := by
        apply (hj X _ (hF _ (hc X))).1
        dsimp only
        rw [← Category.assoc, hf, hg, Category.comp_id]
      inv_hom_id := by
        apply (he _ _ (hd (F.obj X))).1
        dsimp only
        rw [← Category.assoc, hg, hf, Category.comp_id] }
  refine ⟨NatIso.ofComponents k (fun {X Y} h ↦ ?_), hf⟩
  apply (hj X _ (hd (F.obj Y))).1
  change F.map (η X) ≫ (F.map (L.map h) ≫ f Y) =
    F.map (η X) ≫ (f X ≫ K.map (F.map h))
  rw [← Category.assoc, ← F.map_comp, ← hn, F.map_comp, Category.assoc, hf]
  rw [← Category.assoc, hf, hm]

/-- The unique unit-normalized finite-free completion comparison and preservation of
local derived completeness. Its uniqueness makes the comparison independent of a basis
and of the presentation of the unit-power relation.

Source: Stacks Project, algebraization.tex, Tags 099B and 0A0E, finite-free scalar
argument (blueprint: lem-weil-pbc-finite-free-completion-transport).

The coproduct in `hfree` is the finite direct sum of rank-one module sheaves; its
isomorphism is only asserted, not chosen. `D` and `E` are the existing strict Koszul
limit presentations, with their actual degree-zero units. The principal ideal is the
categorical image of multiplication, including sections divisible only locally.
We use standard derived localizations of module sheaves and arbitrary chosen standard-size
localizations of their strict tower categories; none of the complexes is bounded.

Proof:
1. Compare every prescribed Koszul presentation with the same Cech completion. The
   comparison preserves the actual units, so the reflector Hom bijection, its complete
   outputs and its unit criterion transfer to the given D and E, without changing them.
2. Finite-free strict tower transport supplies exactness of ordinary scalar extension.
   Uniqueness of its ordinary adjunction transports exactness to the tensor functor used
   by flatScalarKoszulTowerComparison. That theorem and conservativity of derived scalar
   restriction identify t-completeness after restriction with a(t)-completeness over S.
3. The existing finite-free scalar coordinate theorem identifies the restriction of
   C(X) with a finite biproduct of X. The complete triangulated subcategory is closed
   under finite products, hence these biproducts. The unit-power theorem identifies
   a(t)-completeness with v-completeness. Thus C preserves complete objects and its
   right adjoint carries v-complete objects to t-complete objects, including rank zero.
4. If Y is complete, the scalar adjunction and the R-reflector Hom bijection show that
   precomposition with C(etaR) is bijective for maps into Y. Both C(Lambda_R X) and
   Lambda_S(CX) are complete. Extend etaS across C(etaR), and extend C(etaR) across
   etaS. The same two bijections show that the extensions are inverse. Their uniqueness
   proves naturality, giving the required unit-preserving natural isomorphism.
5. The same injectivity proves uniqueness of every normalized comparison. The preceding
   finite-biproduct argument is also the required preservation of local completeness.
6. Naturality and idempotence of the Cech unit transfer to the prescribed Koszul unit.
   Precomposition with C(etaR) is therefore injective into any object with invertible
   S-unit, by conjugating with kappa. Shift compatibility of the units proves that the
   shifted completed target has invertible unit. The shift square then follows from
   scalar-shift naturality and the two unit equations, for every integer.
7. For identity scalars, naturality of the actual scalar unitor reduces its proposed
   comparison to etaR at C(X). For composition, naturality of the balanced associator
   and the two successive unit equations give the same normalized map as the direct
   comparison. In each case the preceding injectivity proves equality. -/
theorem finiteFreeCompletionTransport
    (A : SystemScalarModel.{u, u, u} a)
    (hfree : ∃ d : ℕ, Nonempty
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (SheafOfModules.unit (derivedChangeRingIndependentCoefficients J S)) ≅
        ∐ (fun _ : Fin d ↦
          SheafOfModules.unit (derivedChangeRingIndependentCoefficients J R))))
    (t : (R.obj ⋙ forget CommRingCat).sections)
    (v w : (S.obj ⋙ forget CommRingCat).sections) (e : ℕ)
    (hw : ∀ U : Cᵒᵖ, IsUnit (w.val U)) (he : 1 ≤ e)
    (hparam : ∀ U : Cᵒᵖ, a.hom.app U (t.val U) = w.val U * v.val U ^ e)
    (D : RingedKoszulLimitPresentation R 1 (fun _ ↦ t))
    (E : RingedKoszulLimitPresentation S 1 (fun _ ↦ v)) :
    (∃! κ : D.completion ⋙ A.model.T ≅ A.model.T ⋙ E.completion,
      ∀ M : ringedSiteDerived R,
        A.model.T.map (D.unit M) ≫ κ.hom.app M = E.unit (A.model.T.obj M)) ∧
    ∀ M : ringedSiteDerived R,
      IsLocallyDerivedRingedIdealComplete R
        (image (ringedKoszulScalar R t)) (image.ι (ringedKoszulScalar R t)) M →
      IsLocallyDerivedRingedIdealComplete S
        (image (ringedKoszulScalar S v)) (image.ι (ringedKoszulScalar S v))
        (A.model.T.obj M) := by
  classical
  let s := FlatScalarKoszul.imageSections a (fun _ : Fin 1 ↦ t) 0
  let P : ObjectProperty (ringedSiteDerived R) := IsLocallyDerivedRingedIdealComplete R
    (image (ringedKoszulScalar R t)) (image.ι (ringedKoszulScalar R t))
  let Q : ObjectProperty (ringedSiteDerived S) := IsLocallyDerivedRingedIdealComplete S
    (image (ringedKoszulScalar S v)) (image.ι (ringedKoszulScalar S v))
  let U := FlatScalarKoszul.restrictDerived a
  have hflat := finite_free_flat a A hfree
  have hpower := (unit_power_localDerivedComplete S s v w e hw he hparam).1
  have hrest (Y : ringedSiteDerived S) : P (U.obj Y) ↔ Q Y :=
    (restriction_complete_iff a hflat t Y).trans (hpower Y)
  obtain ⟨_, _, _, _, hPiso, hPtri⟩ := ringedCompleteTriangulated R 1 (fun _ ↦ t)
    (image (ringedKoszulScalar R t)) (image.ι (ringedKoszulScalar R t))
    (principal_generators R t)
  let : P.IsClosedUnderIsomorphisms := hPiso
  let : P.IsTriangulated := hPtri
  obtain ⟨d, hc⟩ := finite_free_coordinates a A hfree
  have hpres (X : ringedSiteDerived R) (hX : P X) : Q (A.model.T.obj X) := by
    apply (hrest _).mp
    obtain ⟨q⟩ := hc X
    apply P.prop_of_iso q
    exact P.prop_of_isLimit (biproduct.isLimit (fun _ : Fin d ↦ X)) (fun _ ↦ hX)
  obtain ⟨hD, hbD, _⟩ := principal_reflector R t D
  obtain ⟨hE, hbE, _⟩ := principal_reflector S v E
  obtain ⟨hnD, _, _⟩ := completion_unit_properties R 1 (fun _ ↦ t) D
  obtain ⟨hnE, hiE, hoE⟩ := completion_unit_properties S 1 (fun _ ↦ v) E
  obtain ⟨κ, hκ⟩ := adjoint_reflector_transport A.model.T U A.adjunction
    D.completion E.completion D.unit E.unit P Q
    (fun f ↦ hnD _ _ f) (fun f ↦ hnE _ _ f) hD hE hbD hbE
    hpres (fun Y hY ↦ (hrest Y).mpr hY)
  refine ⟨⟨κ, hκ, ?_⟩, hpres⟩
  intro κ' hκ'
  apply Iso.ext
  apply NatTrans.ext
  funext X
  have := hoE (A.model.T.obj X)
  apply transport_cancel A.model.T D.completion E.completion D.unit E.unit
    (fun f ↦ hnE _ _ f) hiE κ hκ
    (Y := E.completion.obj (A.model.T.obj X))
  rw [hκ', hκ]

/-- The normalized comparison commutes with all canonical cochain shifts. The shift
structures on completion are specified by their compatibility with the actual units,
as supplied by `ringedCompleteTriangulated`.

Source: Stacks Project, Tags 099B and 0A0E, scalar-extension shift normalization
(blueprint: lem-weil-pbc-finite-free-completion-transport).
Proof: precompose the shift square with C(etaR) at M[n]. Naturality of the scalar shift,
shift compatibility of etaR and etaS, and the two normalization equations reduce both
sides to etaS at CM shifted by n after the scalar shift. Idempotence makes the unit
invertible on the completed target; the specified shift-compatible etaS makes it
invertible on every shift. Conjugate by kappa and use idempotent-unit cancellation
as in finiteFreeCompletionTransport. This works for every integer n. -/
theorem finiteFreeCompletionTransport_shift
    (A : SystemScalarModel.{u, u, u} a)
    (t : (R.obj ⋙ forget CommRingCat).sections)
    (v : (S.obj ⋙ forget CommRingCat).sections)
    (D : RingedKoszulLimitPresentation R 1 (fun _ ↦ t))
    (E : RingedKoszulLimitPresentation S 1 (fun _ ↦ v))
    [A.model.T.CommShift ℤ] [D.completion.CommShift ℤ] [E.completion.CommShift ℤ]
    (ηR : 𝟭 (ringedSiteDerived R) ⟶ D.completion)
    (ηS : 𝟭 (ringedSiteDerived S) ⟶ E.completion)
    (hηR : ∀ M : ringedSiteDerived R, ηR.app M = D.unit M)
    (hηS : ∀ M : ringedSiteDerived S, ηS.app M = E.unit M)
    [NatTrans.CommShift ηR ℤ] [NatTrans.CommShift ηS ℤ]
    (κ : D.completion ⋙ A.model.T ≅ A.model.T ⋙ E.completion)
    (hκ : ∀ M : ringedSiteDerived R,
      A.model.T.map (D.unit M) ≫ κ.hom.app M = E.unit (A.model.T.obj M)) :
    NatTrans.CommShift κ.hom ℤ := by
  obtain ⟨hn, hi, ho⟩ := completion_unit_properties S 1 (fun _ ↦ v) E
  constructor
  intro n
  ext M
  have his : IsIso (ηS.app ((E.completion.obj (A.model.T.obj M))⟦n⟧)) := by
    rw [NatTrans.app_shift ηS n]
    have h : IsIso (ηS.app (E.completion.obj (A.model.T.obj M))) := by
      rw [hηS]
      exact ho _
    infer_instance
  have : IsIso (E.unit ((E.completion.obj (A.model.T.obj M))⟦n⟧)) := by
    rw [← hηS]
    exact his
  apply transport_cancel A.model.T D.completion E.completion D.unit E.unit
    (fun f ↦ hn _ _ f) hi κ hκ
    (Y := (E.completion.obj (A.model.T.obj M))⟦n⟧)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc]
  have hr := NatTrans.shift_app_comm ηR n M
  have hs := NatTrans.shift_app_comm ηS n (A.model.T.obj M)
  simp only [hηR, hηS, Functor.commShiftIso_id_hom_app, Functor.id_obj] at hr hs
  rw [← A.model.T.map_comp_assoc, ← hr, A.model.T.map_comp]
  simp only [A.model.T.map_id, Category.id_comp]
  have hc := (A.model.T.commShiftIso n).hom.naturality (D.unit M)
  dsimp only [Functor.comp_map] at hc
  rw [reassoc_of% hc]
  rw [← (shiftFunctor (ringedSiteDerived S) n).map_comp, hκ M]
  rw [← Category.assoc _ (κ.hom.app (M⟦n⟧)), hκ]
  rw [← reassoc_of% (hn _ _ ((A.model.T.commShiftIso n).hom.app M))]
  have hs' := congrArg (fun f ↦ (A.model.T.commShiftIso n).hom.app M ≫ f) hs
  erw [Category.id_comp] at hs'
  exact hs'

/-- At the identity coefficient map, the normalized comparison is the actual tensor-unit
comparison, whose ordinary formula is scalar multiplication.

Source: Stacks Project, Tags 099B and 0A0E, scalar-extension identity normalization
(blueprint: lem-weil-pbc-finite-free-completion-transport).
Proof: write u for systemScalarModelDerivedUnit; systemScalarModelDerivedUnit_rep
identifies it with multiplication on complexes. Naturality of u and of the completion
unit shows C(eta) followed by u at Lambda M then Lambda(u^-1 at M) equals eta at CM.
The target is complete. Uniqueness from the reflector Hom bijection, as in step 4 of
finiteFreeCompletionTransport, identifies this map with kappa. -/
theorem finiteFreeCompletionTransport_id
    (A : SystemScalarModel.{u, u, u} (𝟙 R))
    (t : (R.obj ⋙ forget CommRingCat).sections)
    (D : RingedKoszulLimitPresentation R 1 (fun _ ↦ t))
    (κ : D.completion ⋙ A.model.T ≅ A.model.T ⋙ D.completion)
    (hκ : ∀ M : ringedSiteDerived R,
      A.model.T.map (D.unit M) ≫ κ.hom.app M = D.unit (A.model.T.obj M))
    (M : ringedSiteDerived R) :
    κ.hom.app M =
      (systemScalarModelDerivedUnit.{u, u, u} rfl A).hom.app (D.completion.obj M) ≫
        D.completion.map ((systemScalarModelDerivedUnit.{u, u, u} rfl A).inv.app M) := by
  obtain ⟨hn, hi, ho⟩ := completion_unit_properties R 1 (fun _ ↦ t) D
  have := ho (A.model.T.obj M)
  apply transport_cancel A.model.T D.completion D.completion D.unit D.unit
    (fun f ↦ hn _ _ f) hi κ hκ
    (Y := D.completion.obj (A.model.T.obj M))
  rw [hκ M, ← Category.assoc,
    (systemScalarModelDerivedUnit.{u, u, u} rfl A).hom.naturality]
  dsimp only [Functor.id_map]
  simp only [Category.assoc]
  have hunit := hn M (A.model.T.obj M)
    ((systemScalarModelDerivedUnit.{u, u, u} rfl A).inv.app M)
  rw [← hunit, ← Category.assoc,
    (systemScalarModelDerivedUnit.{u, u, u} rfl A).hom_inv_id_app,
    Category.id_comp]

/-- Successive normalized completion comparisons agree with the direct comparison under
balanced derived tensor associativity. Iteration gives the equation for every finite tower.

Source: Stacks Project, Tags 099B and 0A0E, scalar-extension tower normalization
(blueprint: lem-weil-pbc-finite-free-completion-transport).
Proof: systemScalarModelDerivedComposition is the canonical balanced associator, with
its pure-tensor formula and universal cochain comparison fixed by the recorded coherence
node. Precompose both sides with C_b C_a(etaR). The two normalization equations on the
left and naturality of etaT reduce it to alpha followed by etaT. Naturality of alpha
and the direct normalization give the same map on the right. Transport precomposition
along alpha to C_ba(etaR). Its Hom map into the complete target is injective by the
Koszul reflector and the direct normalized comparison. Cancel to obtain the equation.
For successive finite-free maps the composite is finite free and
ba(t)=b(w)*u^e*z^(ef), with a unit coefficient and ef>=1, so the existence theorem
supplies all three comparisons. Induction on length gives every finite tower. -/
theorem finiteFreeCompletionTransport_comp
    {T : Sheaf J CommRingCat.{u}} (b : S ⟶ T)
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients J T))]
    (A : SystemScalarModel.{u, u, u} a) (B : SystemScalarModel.{u, u, u} b)
    (F : SystemScalarModel.{u, u, u} (a ≫ b))
    (t : (R.obj ⋙ forget CommRingCat).sections)
    (v : (S.obj ⋙ forget CommRingCat).sections)
    (z : (T.obj ⋙ forget CommRingCat).sections)
    (D : RingedKoszulLimitPresentation R 1 (fun _ ↦ t))
    (E : RingedKoszulLimitPresentation S 1 (fun _ ↦ v))
    (G : RingedKoszulLimitPresentation T 1 (fun _ ↦ z))
    (κa : D.completion ⋙ A.model.T ≅ A.model.T ⋙ E.completion)
    (κb : E.completion ⋙ B.model.T ≅ B.model.T ⋙ G.completion)
    (κab : D.completion ⋙ F.model.T ≅ F.model.T ⋙ G.completion)
    (ha : ∀ M : ringedSiteDerived R,
      A.model.T.map (D.unit M) ≫ κa.hom.app M = E.unit (A.model.T.obj M))
    (hb : ∀ N : ringedSiteDerived S,
      B.model.T.map (E.unit N) ≫ κb.hom.app N = G.unit (B.model.T.obj N))
    (hab : ∀ M : ringedSiteDerived R,
      F.model.T.map (D.unit M) ≫ κab.hom.app M = G.unit (F.model.T.obj M))
    (M : ringedSiteDerived R) :
    B.model.T.map (κa.hom.app M) ≫ κb.hom.app (A.model.T.obj M) ≫
        G.completion.map ((systemScalarModelDerivedComposition.{u, u, u} rfl A B F).hom.app M) =
      (systemScalarModelDerivedComposition.{u, u, u} rfl A B F).hom.app (D.completion.obj M) ≫
        κab.hom.app M := by
  obtain ⟨hn, hi, ho⟩ := completion_unit_properties T 1 (fun _ ↦ z) G
  have := ho (F.model.T.obj M)
  let α := systemScalarModelDerivedComposition.{u, u, u} rfl A B F
  apply (cancel_epi (α.inv.app (D.completion.obj M))).mp
  apply transport_cancel F.model.T D.completion G.completion D.unit G.unit
    (fun f ↦ hn _ _ f) hi κab hab
  have hα := α.inv.naturality (D.unit M)
  dsimp only [Functor.comp_map] at hα
  rw [← Category.assoc, hα]
  simp only [Category.assoc]
  rw [← B.model.T.map_comp_assoc, ha]
  rw [reassoc_of% hb (A.model.T.obj M), ← hn]
  change α.inv.app M ≫ α.hom.app M ≫ G.unit (F.model.T.obj M) =
    F.model.T.map (D.unit M) ≫ α.inv.app (D.completion.obj M) ≫
      α.hom.app (D.completion.obj M) ≫ κab.hom.app M
  simp only [Iso.inv_hom_id_app_assoc]
  exact (hab M).symm

end CategoryTheory
