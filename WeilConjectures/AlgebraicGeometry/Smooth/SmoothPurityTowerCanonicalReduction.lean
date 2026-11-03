/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
public import Mathlib.Algebra.Module.Hom
public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.Algebra.Homology.IndependentExtensionTensor.ExtensionTensorComparisonIndependent
public import WeilConjectures.Algebra.Homology.System.SystemEvaluationKFlat
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientRegularQuotients
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.EllCoefficientFiber
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact

/-! Strict ell-adic models and their bounded-free cone comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale
attribute [-instance] spCoefficientModulesAbelian
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
  (D : SpCoefficientTowersAbelian l E T)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

private instance (priority := 10000) tower_siteSmall :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _

private instance (priority := 10000) tower_sheafify :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} T

private instance (priority := 10000) tower_weakSheafify :
    HasWeakSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  HasSheafify.isRightAdjoint

private instance (priority := 10000) tower_locallyBijective :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} T

@[instance_reducible] private noncomputable def tower_descendedAction
    {A B : Type*} [Ring A] [Ring B] (p : A →+* B) (hp : Function.Surjective p)
    (M : Type*) [AddCommGroup M] [Module A M]
    (hk : ∀ a, p a = 0 → ∀ x : M, a • x = 0) : Module B M :=
  Module.compHom M (p.liftOfSurjective hp ⟨Module.toAddMonoidEnd A M, by
    intro a ha
    ext x
    exact hk a ha x⟩)

private lemma tower_descendedAction_smul
    {A B : Type*} [Ring A] [Ring B] (p : A →+* B) (hp : Function.Surjective p)
    (M : Type*) [AddCommGroup M] [Module A M]
    (hk : ∀ a, p a = 0 → ∀ x : M, a • x = 0) (a : A) (x : M) :
    let := tower_descendedAction p hp M hk
    p a • x = a • x := by
  have hker : RingHom.ker p ≤ RingHom.ker (Module.toAddMonoidEnd A M) := by
    intro b hb
    ext y
    exact hk b hb y
  change (p.liftOfSurjective hp ⟨Module.toAddMonoidEnd A M, hker⟩ (p a)) x = _
  rw [RingHom.liftOfSurjective_comp_apply]
  rfl

private noncomputable def tower_descendedSheaf
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (p : R ⟶ S)
    (hp : ∀ U, Function.Surjective (p.hom.app U)) (M : SheafOfModules.{u} R)
    (hk : ∀ U a, p.hom.app U a = 0 → ∀ x : M.val.obj U, a • x = 0) :
    SheafOfModules.{u} S where
  val :=
    { obj U := by
        let := tower_descendedAction (p.hom.app U).hom (hp U) (M.val.obj U) (hk U)
        exact ModuleCat.of (S.obj.obj U) (M.val.obj U)
      map {U V} f := by
        let := tower_descendedAction (p.hom.app U).hom (hp U) (M.val.obj U) (hk U)
        let := tower_descendedAction (p.hom.app V).hom (hp V) (M.val.obj V) (hk V)
        let MU := ModuleCat.of (S.obj.obj U) (M.val.obj U)
        let MV := ModuleCat.of (S.obj.obj V) (M.val.obj V)
        exact ModuleCat.ofHom (X := MU)
          (Y := (ModuleCat.restrictScalars (S.obj.map f).hom).obj MV)
          { toFun := fun x ↦ M.val.map f x
            map_add' := map_add _
            map_smul' := by
              intro b x
              obtain ⟨a, rfl⟩ := hp U b
              change (show M.val.obj V from M.val.map f (p.hom.app U a • x)) =
                S.obj.map f (p.hom.app U a) • (show M.val.obj V from M.val.map f x)
              rw [tower_descendedAction_smul]
              have hn := congrArg (fun k ↦ k a) (p.hom.naturality f)
              change p.hom.app V (R.obj.map f a) = S.obj.map f (p.hom.app U a) at hn
              rw [← hn, tower_descendedAction_smul]
              exact M.val.map_smul f a x }
      map_id U := by ext x; exact congrArg (fun k ↦ k x) (M.val.map_id U)
      map_comp f g := by ext x; exact M.val.map_comp_apply f g x }
  isSheaf := by exact M.isSheaf

private noncomputable def tower_descendedSheafIso
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (p : R ⟶ S)
    (hp : ∀ U, Function.Surjective (p.hom.app U)) (M : SheafOfModules.{u} R)
    (hk : ∀ U a, p.hom.app U a = 0 → ∀ x : M.val.obj U, a • x = 0) :
    (SheafOfModules.restrictScalars p).obj (tower_descendedSheaf p hp M hk) ≅ M := by
  let e U : ((SheafOfModules.restrictScalars p).obj
      (tower_descendedSheaf p hp M hk)).val.obj U ≅ M.val.obj U :=
    { hom := ModuleCat.ofHom (X := ((SheafOfModules.restrictScalars p).obj
        (tower_descendedSheaf p hp M hk)).val.obj U) (Y := M.val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ tower_descendedAction_smul (p.hom.app U).hom (hp U) _ (hk U) a x }
      inv := ModuleCat.ofHom (X := M.val.obj U)
        (Y := ((SheafOfModules.restrictScalars p).obj (tower_descendedSheaf p hp M hk)).val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ (tower_descendedAction_smul
            (p.hom.app U).hom (hp U) _ (hk U) a x).symm } }
  exact (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk e (by intro U V f; ext x; rfl))

private theorem tower_restriction_full
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (p : R ⟶ S)
    (hp : ∀ U, Function.Surjective (p.hom.app U)) :
    (SheafOfModules.restrictScalars.{u} p).Full where
  map_surjective {M N} f := by
    let g : M ⟶ N :=
      { val :=
          { app U := ModuleCat.ofHom
              { toFun := f.val.app U
                map_add' := map_add _
                map_smul' := by
                  intro b x
                  obtain ⟨a, rfl⟩ := hp U b
                  exact (f.val.app U).hom.map_smul a x }
            naturality := by
              intro U V k
              ext x
              exact PresheafOfModules.naturality_apply f.val k x } }
    exact ⟨g, rfl⟩

private theorem tower_restriction_faithful
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (p : R ⟶ S) :
    (SheafOfModules.restrictScalars.{u} p).Faithful where
  map_injective {M N} f g h := by
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h

private theorem tower_complex_in_restriction_image
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (p : R ⟶ S)
    (hp : ∀ U, Function.Surjective (p.hom.app U))
    (K : CochainComplex (SheafOfModules.{u} R) ℤ)
    (hk : ∀ i U a, p.hom.app U a = 0 → ∀ x : (K.X i).val.obj U, a • x = 0) :
    ∃ L : CochainComplex (SheafOfModules.{u} S) ℤ,
      Nonempty (((SheafOfModules.restrictScalars p).mapHomologicalComplex (.up ℤ)).obj L ≅ K) := by
  let T := SheafOfModules.restrictScalars.{u} p
  let : T.Full := tower_restriction_full p hp
  let : T.Faithful := tower_restriction_faithful p
  let M i := tower_descendedSheaf p hp (K.X i) (hk i)
  let e i : T.obj (M i) ≅ K.X i := tower_descendedSheafIso p hp (K.X i) (hk i)
  let L : CochainComplex (SheafOfModules.{u} S) ℤ :=
    { X := M
      d i j := T.preimage ((e i).hom ≫ K.d i j ≫ (e j).inv)
      shape i j h := by
        apply T.map_injective
        simp [K.shape i j h]
      d_comp_d' i j k _ _ := by
        apply T.map_injective
        simp }
  refine ⟨L, ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩⟩
  intro i j _
  change (e i).hom ≫ K.d i j =
    T.map (T.preimage ((e i).hom ≫ K.d i j ≫ (e j).inv)) ≫ (e j).hom
  simp only [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]

-- A cokernel in the larger category, lying in the image of the right adjoint,
-- identifies the adjunction unit with that cokernel.

private theorem tower_unit_cokernel
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasZeroMorphisms C]
    (R : B ⥤ A) (S : A ⥤ C) [S.Full] [S.Faithful]
    [R.Faithful] [R.Full] (L : A ⥤ B) (adj : L ⊣ R)
    (P : A) (v : S.obj P ⟶ S.obj P) [HasCokernel v]
    (hz : v ≫ S.map (adj.unit.app P) = 0)
    (himage : ∃ N : B, Nonempty (S.obj (R.obj N) ≅ cokernel v)) :
    IsIso (cokernel.desc v (S.map (adj.unit.app P)) hz) := by
  classical
  obtain ⟨N, ⟨e⟩⟩ := himage
  let q : P ⟶ R.obj N := S.preimage (cokernel.π v ≫ e.inv)
  let g : L.obj P ⟶ N := (adj.homEquiv P N).symm q
  have hg : adj.unit.app P ≫ R.map g = q :=
    (adj.homEquiv P N).apply_symm_apply q
  let d := cokernel.desc v (S.map (adj.unit.app P)) hz
  have hd : cokernel.π v ≫ d = S.map (adj.unit.app P) := cokernel.π_desc _ _ _
  have hfac : S.map (adj.unit.app P) ≫ S.map (R.map g) ≫ e.hom = cokernel.π v := by
    rw [← S.map_comp_assoc, hg, Functor.map_preimage]
    simp
  have hgiso : IsIso g := by
    apply isIso_of_coyoneda_map_bijective
    intro Z
    have hq : Function.Bijective (fun b : N ⟶ Z ↦ q ≫ R.map b) := by
      constructor
      · intro b c h
        apply R.map_injective
        apply S.map_injective
        apply (cancel_epi e.inv).1
        apply (cancel_epi (cokernel.π v)).1
        have hh := congrArg S.map h
        simpa only [Functor.map_comp, q, Functor.map_preimage, Category.assoc] using hh
      · intro b
        have hb : v ≫ S.map b = 0 := by
          -- Every map into R(Z) is the adjoint of a map out of L(P).
          obtain ⟨b', rfl⟩ := (adj.homEquiv P Z).surjective b
          rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, hz, zero_comp]
        let a := S.preimage (e.hom ≫ cokernel.desc v (S.map b) hb)
        refine ⟨R.preimage a, ?_⟩
        apply S.map_injective
        simp [q, a, Category.assoc]
    have heq : (fun b : N ⟶ Z ↦ q ≫ R.map b) =
        (fun b : L.obj P ⟶ Z ↦ adj.homEquiv P Z b) ∘ (fun b : N ⟶ Z ↦ g ≫ b) := by
      funext b
      simp only [Function.comp_apply, Adjunction.homEquiv_unit, Functor.map_comp,
        ← Category.assoc, hg]
    rw [heq] at hq
    exact hq.of_comp_left (adj.homEquiv P Z).injective
  have heq : d ≫ S.map (R.map g) ≫ e.hom = 𝟙 _ := by
    apply (cancel_epi (cokernel.π v)).1
    simpa only [← Category.assoc, hd, Category.comp_id] using hfac
  have : IsIso (S.map (R.map g) ≫ e.hom) := by infer_instance
  have hd' : d = inv (S.map (R.map g) ≫ e.hom) := by
    apply (cancel_mono (S.map (R.map g) ≫ e.hom)).1
    simpa using heq
  change IsIso d
  rw [hd']
  infer_instance

private lemma tower_zsmul_apply
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (r : ℤ) (f : M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U) :
    (r • f).val.app U x = r • f.val.app U x := by
  change ((SheafOfModules.forget R).map (r • f)).app U x = _
  rw [Functor.map_zsmul, PresheafOfModules.zsmul_app]
  rfl

private lemma tower_scalar_apply
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (K : CochainComplex (SheafOfModules.{u} R) ℤ)
    (r : ℤ) (i : ℤ) (U : Cᵒᵖ) (x : (K.X i).val.obj U) :
    ((r • 𝟙 K).f i).val.app U x = r • x := by
  rw [HomologicalComplex.zsmul_f_apply, tower_zsmul_apply]
  rfl

private theorem tower_isIso_natTrans_app
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (t : F ⟶ G) {X Y : A} (e : X ≅ Y) [IsIso (t.app Y)] : IsIso (t.app X) := by
  have he : t.app X = F.map e.hom ≫ t.app Y ≫ G.map e.inv := by
    rw [← Category.assoc, t.naturality e.hom, Category.assoc,
      ← G.map_comp, e.hom_inv_id, G.map_id, Category.comp_id]
  rw [he]
  infer_instance

private theorem tower_scalar_zero_of_iso
    {A : Type*} [Category A] [Preadditive A] {X Y : A}
    (e : X ≅ Y) (r : ℤ) (h : r • 𝟙 Y = 0) : r • 𝟙 X = 0 := by
  apply (cancel_mono e.hom).1
  calc
    (r • 𝟙 X) ≫ e.hom = e.hom ≫ (r • 𝟙 Y) := by simp
    _ = 0 ≫ e.hom := by rw [h, comp_zero, zero_comp]

private abbrev finiteEvaluation (n : ℕ) :=
  spCoefficientEvaluation l E T D.equivalence n

private instance finiteEvaluationLimits (n : ℕ) :
    PreservesFiniteLimits (finiteEvaluation l E T D n) := D.evaluationLimits n

private instance finiteEvaluationColimits (n : ℕ) :
    PreservesFiniteColimits (finiteEvaluation l E T D n) := D.evaluationColimits n

private instance finiteEvaluationAdditive (n : ℕ) :
    (finiteEvaluation l E T D n).Additive := Functor.additive_of_preserves_binary_products _

private abbrev finiteComplex (P : CochainComplex (spCoefficientTowers l E T) ℤ) (n : ℕ) :=
  ((finiteEvaluation l E T D n).mapHomologicalComplex (.up ℤ)).obj P

private theorem flat_representative (C : spDerivedCoefficientTowers l E T D) :
    ∃ (P : CochainComplex (spCoefficientTowers l E T) ℤ)
      (_z : (@DerivedCategory.Q _ _ _ D.hasDerived).obj P ≅ C),
      ∀ n : ℕ, systemLevelKFlat.{u + 1, u, u + 1} (spCoefficientCommRings.{u, u} l E T) n
        (finiteComplex l E T D P n) := by
  classical
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  let e := D.equivalence.mapHomologicalComplex (.up ℤ)
  let K := DerivedCategory.Q.objPreimage C
  obtain ⟨L, q, hL, hq⟩ := strictRingSystem_kFlatResolution
    (spCoefficientCommRings.{u, u} l E T) (e.functor.obj K)
  let P := e.inverse.obj L
  let f : P ⟶ K := e.inverse.map q ≫ e.unitIso.inv.app K
  have : QuasiIso q := hq
  have : QuasiIso (e.inverse.map q) := by
    change QuasiIso ((D.equivalence.inverse.mapHomologicalComplex (.up ℤ)).map q)
    infer_instance
  have : QuasiIso f := by dsimp only [f]; infer_instance
  refine ⟨P, asIso (DerivedCategory.Q.map f) ≪≫
    DerivedCategory.Q.objObjPreimageIso C, ?_⟩
  intro n
  let en := ((systemEvaluation (spCoefficientCommRings.{u, u} l E T) n).mapHomologicalComplex
    (.up ℤ)).mapIso (e.counitIso.app L)
  exact ⟨kFlat_iso_independent _ en.symm (hL n).1,
    fun i ↦ flatOnSite_of_iso _
      ((HomologicalComplex.eval _ (.up ℤ) i).mapIso en.symm) ((hL n).2 i)⟩

private theorem ell_projection_eq (n : ℕ) :
    spCompletedEllCommProjection l E T n = spCompletedEllCommRingProjection l E T n := by
  let H := sp_completed_coefficient_limit l E T
  have hc : H.exists.choose = H.choose := H.choose_spec.2 _ H.exists.choose_spec
  let F := sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  apply F.map_injective
  dsimp only [spCompletedEllCommProjection, spIntegralEllProjection, F]
  -- Unfold the interface projection on the left only; the regular quotient
  -- projection is already presented by its sectionwise ring map.
  erw [Functor.map_preimage]
  ext U x
  change ((H.exists.choose.hom ≫ limit.π _ (op n)).hom.app U) x =
    ((H.choose.hom ≫ limit.π _ (op n)).hom.app U) x
  rw [hc]

private theorem ell_projection_surjective (n : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Surjective ((spCompletedEllCommProjection l E T n).hom.app U) := by
  rw [ell_projection_eq]
  exact projection_surjective l E T _ (ell_normalized l E T n) U

private theorem ell_section (U : T.ProEtᵒᵖ) :
    (show (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U from
      (spCompletedScalarSection l E T l).val U) = l := by
  change scalarHom l E T U (l : Padic.coefficientExtensionIntegers l E) = _
  exact map_natCast _ _

private theorem ell_projection_kernel (n : ℕ) (U : T.ProEtᵒᵖ) :
    RingHom.ker ((spCompletedEllCommProjection l E T n).hom.app U).hom =
      Ideal.span {(l :
        (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U) ^
          (n + 1)} := by
  rw [ell_projection_eq]
  have h := ((sp_completed_coefficient_regular_quotients l E T).2.2.2.2.1 n).2.2 U |>.2
  simpa only [sectionPowerIdeal, ell_section, id_eq] using h

private theorem ell_regular (b : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Injective (fun x :
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U ↦
        (l : (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
          ^ b * x) := by
  cases b with
  | zero =>
    intro x y h
    simpa only [pow_zero, one_mul] using h
  | succ b =>
    have h := ((sp_completed_coefficient_regular_quotients l E T).2.2.2.1 b U).2
    simpa only [ell_section, id_eq] using h

private theorem ell_projection_zero (n : ℕ) (U : T.ProEtᵒᵖ) :
    (l : ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj U) ^ (n + 1) = 0 := by
  have h : (l :
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U) ^
        (n + 1) ∈ RingHom.ker ((spCompletedEllCommProjection l E T n).hom.app U).hom := by
    rw [ell_projection_kernel]
    exact Ideal.subset_span (Set.mem_singleton _)
  simpa only [RingHom.mem_ker, map_pow, map_natCast] using h

private abbrev completedComplex (P : CochainComplex (spCoefficientTowers l E T) ℤ) (n : ℕ) :=
  ((spCompletedEvaluation l E T D n).mapHomologicalComplex (.up ℤ)).obj P

private def completedMap (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    {m n : ℕ} (h : m ≤ n) :
    completedComplex l E T D P n ⟶ completedComplex l E T D P m where
  f i :=
    { val :=
        { app U := ModuleCat.ofHom
            (X := ((spCompletedEvaluation l E T D n).obj (P.X i)).val.obj U)
            (Y := ((spCompletedEvaluation l E T D m).obj (P.X i)).val.obj U)
            { toFun := fun x ↦
                (((D.equivalence.functor.obj (P.X i)).transition h).val.app U) x
              map_add' := map_add _
              map_smul' := by
                intro r x
                have he := congrArg (fun f ↦ f.hom.app U r)
                  (spCompletedEllCommProjection_comp l E T h)
                change ((spCoefficientCommRings.{u, u} l E T).map (homOfLE h).op).hom.app U
                  ((spCompletedEllCommProjection l E T n).hom.app U r) =
                    (spCompletedEllCommProjection l E T m).hom.app U r at he
                have hh := (((D.equivalence.functor.obj (P.X i)).transition h).val.app U).hom
                  |>.map_smul ((spCompletedEllCommProjection l E T n).hom.app U r)
                    (show ((D.equivalence.functor.obj (P.X i)).level n).val.obj U from x)
                exact hh.trans (congrArg
                  (fun a : ((spCoefficientCommRings.{u, u} l E T).obj (op m)).obj.obj U ↦ a •
                  (show ((D.equivalence.functor.obj (P.X i)).level m).val.obj U from
                    (((D.equivalence.functor.obj (P.X i)).transition h).val.app U) x)) he) }
          naturality := by
            intro U V f
            ext x
            exact PresheafOfModules.naturality_apply
              ((D.equivalence.functor.obj (P.X i)).transition h).val f x } }
  comm' i j _ := by
    ext U x
    exact (congrArg (fun a ↦ a.val.app U x)
      ((D.equivalence.functor.map (P.d i j)).comm h)).symm

private theorem completedMap_id (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (n : ℕ) : completedMap l E T D P (Nat.le_refl n) = 𝟙 _ := by
  ext i U x
  exact (D.equivalence.functor.obj (P.X i)).identity n U x

private theorem completedMap_comp (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    {r m n : ℕ} (h : r ≤ m) (k : m ≤ n) :
    completedMap l E T D P (h.trans k) =
      completedMap l E T D P k ≫ completedMap l E T D P h := by
  ext i U x
  exact (D.equivalence.functor.obj (P.X i)).compose h k U x

private def modelObject (P : CochainComplex (spCoefficientTowers l E T) ℤ) :
    ℕ → CochainComplex (WeilConjectures.scalarReductionSource.{u, u} l E T) ℤ
  | 0 => 0
  | n + 1 => completedComplex l E T D P n

private def modelMap (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    {m n : ℕ} (h : m ≤ n) :
    modelObject l E T D P n ⟶ modelObject l E T D P m := by
  cases m with
  | zero => exact 0
  | succ m =>
    cases n with
    | zero => omega
    | succ n => exact completedMap l E T D P (Nat.le_of_succ_le_succ h)

private def modelTower (P : CochainComplex (spCoefficientTowers l E T) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (WeilConjectures.scalarReductionSource.{u, u} l E T) ℤ where
  obj n := modelObject l E T D P n.unop
  map f := modelMap l E T D P (leOfHom f.unop)
  map_id n := by
    obtain ⟨n⟩ := n
    cases n with
    | zero => exact (isZero_zero _).eq_of_src _ _
    | succ n => exact completedMap_id l E T D P n
  map_comp {a b c} f g := by
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    obtain ⟨c⟩ := c
    have hf := leOfHom f.unop
    have hg := leOfHom g.unop
    dsimp only [unop_op] at hf hg
    cases c with
    | zero => exact (isZero_zero _).eq_of_tgt _ _
    | succ c =>
      cases b with
      | zero => omega
      | succ b =>
        cases a with
        | zero => omega
        | succ a =>
          exact completedMap_comp l E T D P
            (Nat.le_of_succ_le_succ hg) (Nat.le_of_succ_le_succ hf)

private theorem modelTower_annihilated
    (P : CochainComplex (spCoefficientTowers l E T) ℤ) (n : ℕ) :
    (l : ℤ) ^ n • 𝟙 ((modelTower l E T D P).obj (op n)) = 0 := by
  cases n with
  | zero => exact (isZero_zero _).eq_of_src _ _
  | succ n =>
    ext i U x
    rw [tower_scalar_apply]
    change ((l : ℤ) ^ (n + 1)) •
      (show ((D.equivalence.functor.obj (P.X i)).level n).val.obj U from x) = 0
    rw [← Int.cast_smul_eq_zsmul (R :=
      ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj U), Int.cast_pow,
      Int.cast_natCast, ell_projection_zero l E T n U, zero_smul]

private theorem finiteScalar_exact (a b n : ℕ) (hn : n + 1 = a + b)
    (U : T.ProEtᵒᵖ) :
    Function.Exact
      (fun x : ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj U ↦ (l : _) ^ a * x)
      (fun x ↦ (l : _) ^ b * x) := by
  let p := ((spCompletedEllCommProjection l E T n).hom.app U).hom
  intro x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := ell_projection_surjective l E T n U x
    have hz : (l :
        (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U) ^
          b * y ∈ RingHom.ker p := by
      change p _ = 0
      simpa only [map_mul, map_pow, map_natCast] using hx
    rw [ell_projection_kernel] at hz
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hz
    have hy : y = (l : _) ^ a * z := by
      apply ell_regular l E T b U
      dsimp only
      rw [← mul_assoc, ← pow_add, Nat.add_comm b a, ← hn]
      exact hz
    refine ⟨p z, ?_⟩
    change (l : _) ^ a * p z = p y
    rw [hy, map_mul, map_pow, map_natCast]
  · rintro ⟨y, rfl⟩
    dsimp only
    rw [← mul_assoc, ← pow_add, Nat.add_comm b a, ← hn, ell_projection_zero, zero_mul]

private theorem tower_flat_integer_exact
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{r} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r}) (a b : ℤ)
    (hzeroR : ∀ U : Cᵒᵖ, (a : R.obj.obj U) * (b : R.obj.obj U) = 0)
    (hexact : ∀ U : Cᵒᵖ,
      Function.Exact (fun x : R.obj.obj U ↦ a • x) (fun x ↦ b • x))
    (N : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R))
    (hflat : exactFunctor _ _ (@MonoidalCategory.tensorRight _ _
      (SheafOfModules.monoidalCategory R) N)) :
    ∃ hz, (ShortComplex.mk (a • 𝟙 N) (b • 𝟙 N) hz).Exact := by
  have hz (M : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) :
      (a • 𝟙 M) ≫ (b • 𝟙 M) = 0 := by
    ext U x
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, tower_zsmul_apply]
    change b • (a • x) = 0
    rw [smul_smul, ← Int.cast_smul_eq_zsmul (R := R.obj.obj U), Int.cast_mul,
      mul_comm (b : R.obj.obj U), hzeroR U, zero_smul]
  let A : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R) :=
    SheafOfModules.unit (derivedChangeRingIndependentCoefficients J R)
  let V := ShortComplex.mk (a • 𝟙 A) (b • 𝟙 A) (hz A)
  have hV : V.Exact := by
    apply (toSheaf.{r}
      (derivedChangeRingIndependentCoefficients J R)).reflects_exact_of_faithful
    apply (sheafToPresheaf J AddCommGrpCat.{r}).reflects_exact_of_faithful
    rw [ShortComplex.exact_iff_evaluation]
    intro U
    apply (ShortComplex.ab_exact_iff_function_exact _).2
    change Function.Exact (fun x ↦ (a • 𝟙 A).val.app U x)
      (fun x ↦ (b • 𝟙 A).val.app U x)
    simp only [tower_zsmul_apply]
    change Function.Exact (fun x : R.obj.obj U ↦ a • x) (fun x ↦ b • x)
    exact hexact U
  let F := @MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) N
  letI : PreservesFiniteLimits F := hflat.1
  letI : PreservesFiniteColimits F := hflat.2
  letI : F.Additive := Functor.additive_of_preserves_binary_products _
  let e := SheafOfModules.IndependentExtensionTensor.regularTensorIso (R := R) N
  refine ⟨hz N, (ShortComplex.exact_iff_of_iso
    (ShortComplex.isoMk e e e ?_ ?_)).1 (hV.map F)⟩
  · simp only [ShortComplex.map, V, CategoryTheory.Functor.map_zsmul,
      CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Category.comp_id]
  · simp only [ShortComplex.map, V, CategoryTheory.Functor.map_zsmul,
      CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Category.comp_id]

private theorem modelTower_exact
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (hflat : ∀ n : ℕ, systemLevelKFlat.{u + 1, u, u + 1} (spCoefficientCommRings.{u, u} l E T) n
      (finiteComplex l E T D P n)) (a b : ℕ) :
    (ShortComplex.mk
      ((l : ℤ) ^ a • 𝟙 ((modelTower l E T D P).obj (op (a + b))))
      ((l : ℤ) ^ b • 𝟙 ((modelTower l E T D P).obj (op (a + b)))) (by
        rw [Linear.smul_comp, Category.id_comp, smul_smul, ← pow_add, Nat.add_comm,
          modelTower_annihilated])).Exact := by
  have hex (n : ℕ) (hn : n + 1 = a + b) :
      ∃ hz, (ShortComplex.mk
        ((l : ℤ) ^ a • 𝟙 ((modelTower l E T D P).obj (op (n + 1))))
        ((l : ℤ) ^ b • 𝟙 ((modelTower l E T D P).obj (op (n + 1)))) hz).Exact := by
    have hz : ((l : ℤ) ^ a • 𝟙 ((modelTower l E T D P).obj (op (n + 1)))) ≫
        ((l : ℤ) ^ b • 𝟙 ((modelTower l E T D P).obj (op (n + 1)))) = 0 := by
      rw [Linear.smul_comp, Category.id_comp, smul_smul, ← pow_add, ← hn,
        modelTower_annihilated]
    refine ⟨hz, HomologicalComplex.exact_of_degreewise_exact _ fun i ↦ ?_⟩
    let R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
      (spCoefficientCommRings.{u, u} l E T).obj (op n)
    let N := (finiteComplex l E T D P n).X i
    have hN : IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := R) N := (hflat n).2 i
    have hf : exactFunctor _ _ (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory R) N) :=
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso.{u + 1, u, u + 1} R N) hN
    obtain ⟨hz', he⟩ := tower_flat_integer_exact R ((l : ℤ) ^ a) ((l : ℤ) ^ b)
      (by
        intro U
        simpa only [Int.cast_pow, Int.cast_natCast, ← pow_add, ← hn] using
          ell_projection_zero l E T n U)
      (by
        intro U
        simpa only [← Int.cast_smul_eq_zsmul (R := R.obj.obj U), Int.cast_pow,
          Int.cast_natCast, smul_eq_mul] using finiteScalar_exact l E T a b n hn U) N hf
    let F := spCompletedEllRestriction l E T n
    have he' := he.map F
    refine (ShortComplex.exact_iff_of_iso ?_).1 he'
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    all_goals
      simp only [ShortComplex.map, CategoryTheory.Functor.map_zsmul,
        CategoryTheory.Functor.map_id, Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl
  cases b with
  | succ b => exact (hex (a + b) rfl).choose_spec
  | zero =>
    cases a with
    | succ a => exact (hex a rfl).choose_spec
    | zero => exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero _)

private def finiteIso
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (C : spDerivedCoefficientTowers l E T D)
    (z : (@DerivedCategory.Q _ _ _ D.hasDerived).obj P ≅ C) (n : ℕ) :
    DerivedCategory.Q.obj (finiteComplex l E T D P n) ≅
      (spDerivedCoefficientEvaluation l E T D n).obj C :=
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits n
  letI := D.evaluationColimits n
  letI : (finiteEvaluation l E T D n).Additive :=
    Functor.additive_of_preserves_binary_products _
  ((finiteEvaluation l E T D n).mapDerivedCategoryFactors.app P).symm ≪≫
    (spDerivedCoefficientEvaluation l E T D n).mapIso z

private def modelIso
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (C : spDerivedCoefficientTowers l E T D)
    (z : (@DerivedCategory.Q _ _ _ D.hasDerived).obj P ≅ C) (n : ℕ) :
    DerivedCategory.Q.obj ((modelTower l E T D P).obj (op (n + 1))) ≅
      (spDerivedCompletedEvaluation l E T D n).obj C :=
  (spCompletedEvaluationFactors l E T D n |>.app P).symm ≪≫
    (spDerivedCompletedEvaluation l E T D n).mapIso z

private theorem completedMap_successor
    (P : CochainComplex (spCoefficientTowers l E T) ℤ) (n : ℕ) :
    completedMap l E T D P (Nat.le_succ n) =
      (NatTrans.mapHomologicalComplex (spCompletedTransition l E T D n) (.up ℤ)).app P := by
  ext i U x
  change (((D.equivalence.functor.obj (P.X i)).transition (Nat.le_succ n)).val.app U) x = _
  exact ((spCompletedTransition_existsUnique l E T D n).exists.choose_spec (P.X i) U x).symm

private theorem modelIso_successor
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (C : spDerivedCoefficientTowers l E T D)
    (z : (@DerivedCategory.Q _ _ _ D.hasDerived).obj P ≅ C) (n : ℕ) :
    DerivedCategory.Q.map ((modelTower l E T D P).map
        (homOfLE (Nat.succ_le_succ n.le_succ)).op) ≫ (modelIso l E T D P C z n).hom =
      (modelIso l E T D P C z (n + 1)).hom ≫
        (spDerivedCompletedTransition l E T D n).app C := by
  letI := D.hasDerived
  have ht := (spDerivedCompletedTransition_existsUnique l E T D n).exists.choose_spec P
  change (spDerivedCompletedTransition l E T D n).app (DerivedCategory.Q.obj P) ≫
      (spCompletedEvaluationFactors l E T D n).hom.app P =
    (spCompletedEvaluationFactors l E T D (n + 1)).hom.app P ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (spCompletedTransition l E T D n) (.up ℤ)).app P) at ht
  change DerivedCategory.Q.map (completedMap l E T D P n.le_succ) ≫ _ = _
  rw [completedMap_successor]
  apply (cancel_epi ((spCompletedEvaluationFactors l E T D (n + 1)).hom.app P)).1
  simp only [modelIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, ← ht, Category.assoc, Iso.hom_inv_id_app_assoc]
  exact ((spDerivedCompletedTransition l E T D n).naturality z.hom).symm

private theorem modelIso_finite
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (C : spDerivedCoefficientTowers l E T D)
    (z : (@DerivedCategory.Q _ _ _ D.hasDerived).obj P ≅ C) (n : ℕ) :
    (modelIso l E T D P C z n).hom =
      (spCompletedEllRestriction l E T n).mapDerivedCategoryFactors.inv.app
          (finiteComplex l E T D P n) ≫
        (spCompletedEllRestriction l E T n).mapDerivedCategory.map
          (finiteIso l E T D P C z n).hom := by
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits n
  letI := D.evaluationColimits n
  letI : (finiteEvaluation l E T D n).Additive :=
    Functor.additive_of_preserves_binary_products _
  simp only [modelIso, finiteIso, spCompletedEvaluationFactors, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rfl

private def tower_restrictionComp
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    restrictScalars.{u} g ⋙ restrictScalars.{u} f ≅ restrictScalars.{u} (f ≫ g) :=
  Iso.refl _

private def tower_restrictionCompTo
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (h : R ⟶ T) (he : f ≫ g = h) :
    restrictScalars.{u} g ⋙ restrictScalars.{u} f ≅ restrictScalars.{u} h :=
  tower_restrictionComp f g ≪≫ eqToIso (congrArg (restrictScalars.{u}) he)

private lemma tower_restrictionCompTo_apply
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (h : R ⟶ T) (he : f ≫ g = h) (M : SheafOfModules.{u} T)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    ((tower_restrictionCompTo f g h he).hom.app M).val.app U x = x := by
  subst h
  rfl

private def restrictionComp {m n : ℕ} (h : m ≤ n) :
    systemRestriction (spCoefficientCommRings.{u, u} l E T) h ⋙ spCompletedEllRestriction l E T n ≅
      spCompletedEllRestriction l E T m :=
  tower_restrictionCompTo
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (spCompletedEllCommProjection l E T n))
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((spCoefficientCommRings.{u, u} l E T).map (homOfLE h).op))
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (spCompletedEllCommProjection l E T m)) (by
      let F := sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      change F.map (spCompletedEllCommProjection l E T n) ≫
        F.map ((spCoefficientCommRings.{u, u} l E T).map (homOfLE h).op) =
          F.map (spCompletedEllCommProjection l E T m)
      rw [← F.map_comp, spCompletedEllCommProjection_comp])

private theorem restrictionComp_apply {m n : ℕ} (h : m ≤ n)
    (M : systemLevel.{u + 1, u, u + 1} (spCoefficientCommRings.{u, u} l E T) m) (U : T.ProEtᵒᵖ)
    (x : M.val.obj U) :
    ((restrictionComp l E T h).hom.app M).val.app U x = x := by
  unfold restrictionComp
  exact tower_restrictionCompTo_apply _ _ _ _ M U x

private def finiteTransition (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    {m n : ℕ} (h : m ≤ n) :
    finiteComplex l E T D P n ⟶
      ((systemRestriction (spCoefficientCommRings.{u, u} l E T) h).mapHomologicalComplex
        (.up ℤ)).obj (finiteComplex l E T D P m) where
  f i := (D.equivalence.functor.obj (P.X i)).transition h
  comm' i j _ := ((D.equivalence.functor.map (P.d i j)).comm h).symm

private theorem finiteTransition_restrict
    (P : CochainComplex (spCoefficientTowers l E T) ℤ) {m n : ℕ} (h : m ≤ n) :
    ((spCompletedEllRestriction l E T n).mapHomologicalComplex (.up ℤ)).map
        (finiteTransition l E T D P h) ≫
      (Functor.mapHomologicalComplexCompIso (restrictionComp l E T h) (.up ℤ)).hom.app
        (finiteComplex l E T D P m) = completedMap l E T D P h := by
  ext i U x
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact (restrictionComp_apply l E T h _ U _).trans (by rfl)

private theorem ordinaryReduction_quasiIso
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (C : spDerivedCoefficientTowers l E T D)
    (z : (@DerivedCategory.Q _ _ _ D.hasDerived).obj P ≅ C)
    (hflat : ∀ n : ℕ, systemLevelKFlat.{u + 1, u, u + 1} (spCoefficientCommRings.{u, u} l E T) n
      (finiteComplex l E T D P n))
    (hnorm : IsSpNormalizedTower l E T D C) {m n : ℕ} (h : m ≤ n) :
    QuasiIso ((NatTrans.mapHomologicalComplex (D.ordinaryReduction h) (.up ℤ)).app P) := by
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI : ∀ j : ℕ, (finiteEvaluation l E T D j).Additive :=
    fun j ↦ Functor.additive_of_preserves_binary_products _
  let L := systemDerivedTensor D.scalar (spCoefficientCommRings.{u, u} l E T) h
  let an := (finiteEvaluation l E T D n).mapDerivedCategoryFactors.app P
  let am := (finiteEvaluation l E T D m).mapDerivedCategoryFactors.app P
  let ε := (D.scalar ((spCoefficientCommRings.{u, u} l E T).map (homOfLE h).op)).model.ε
  let g := (NatTrans.mapHomologicalComplex (D.ordinaryReduction h) (.up ℤ)).app P
  have : IsIso ((D.reduction h).app C) := hnorm m n h
  have hred : IsIso ((D.reduction h).app (DerivedCategory.Q.obj P)) := by
    exact tower_isIso_natTrans_app (D.reduction h) z
  have hε : IsIso (ε.app (finiteComplex l E T D P n)) :=
    (D.scalar ((spCoefficientCommRings.{u, u} l E T).map (homOfLE h).op)).model.computes _
      (hflat n).1
  have he : DerivedCategory.Q.map g =
      inv (ε.app (finiteComplex l E T D P n)) ≫ L.map an.inv ≫
        (D.reduction h).app (DerivedCategory.Q.obj P) ≫ am.hom := by
    rw [D.reduction_rep]
    change _ = inv (ε.app _) ≫ L.map an.inv ≫
      (L.map an.hom ≫ ε.app _ ≫ DerivedCategory.Q.map g ≫ am.inv) ≫ am.hom
    simp only [Category.assoc, ← L.map_comp_assoc, Iso.inv_hom_id, L.map_id,
      Category.id_comp, IsIso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have : IsIso (DerivedCategory.Q.map g) := by rw [he]; infer_instance
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).1 this

private theorem scalar_cokernel_quasiIso
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (C : spDerivedCoefficientTowers l E T D)
    (z : (@DerivedCategory.Q _ _ _ D.hasDerived).obj P ≅ C)
    (hflat : ∀ n : ℕ, systemLevelKFlat.{u + 1, u, u + 1} (spCoefficientCommRings.{u, u} l E T) n
      (finiteComplex l E T D P n))
    (hnorm : IsSpNormalizedTower l E T D C) {m n : ℕ} (h : m ≤ n)
    (hz : ((l : ℤ) ^ (m + 1) • 𝟙 (completedComplex l E T D P n)) ≫
      completedMap l E T D P h = 0) :
    QuasiIso (cokernel.desc ((l : ℤ) ^ (m + 1) •
      𝟙 (completedComplex l E T D P n)) (completedMap l E T D P h) hz) := by
  classical
  letI := D.hasDerived
  let φ := (spCoefficientCommRings.{u, u} l E T).map (homOfLE h).op
  let R := systemRestriction (spCoefficientCommRings.{u, u} l E T) h
  let S := spCompletedEllRestriction l E T n
  let N := spCompletedEllRestriction l E T m
  let RC := R.mapHomologicalComplex (.up ℤ)
  let SC := S.mapHomologicalComplex (.up ℤ)
  let NC := N.mapHomologicalComplex (.up ℤ)
  let iC : RC ⋙ SC ≅ NC :=
    Functor.mapHomologicalComplexCompIso (restrictionComp l E T h) (.up ℤ)
  let F := finiteComplex l E T D P n
  let K := finiteComplex l E T D P m
  let A := D.scalar φ
  let EC := A.model.E.mapHomologicalComplex (.up ℤ)
  let adj : EC ⊣ RC := A.ordinaryAdj.mapHomologicalComplex (.up ℤ)
  let g : EC.obj F ⟶ K :=
    (NatTrans.mapHomologicalComplex (D.ordinaryReduction h) (.up ℤ)).app P
  have hg : QuasiIso g := ordinaryReduction_quasiIso l E T D P C z hflat hnorm h
  let v := (l : ℤ) ^ (m + 1) • 𝟙 (SC.obj F)
  have hpq (U : T.ProEtᵒᵖ) : Function.Surjective (φ.hom.app U) := by
    intro b
    obtain ⟨a, ha⟩ := ell_projection_surjective l E T m U b
    refine ⟨(spCompletedEllCommProjection l E T n).hom.app U a, ?_⟩
    exact (congrArg (fun k ↦ k.hom.app U a)
      (spCompletedEllCommProjection_comp l E T h)).trans ha
  letI : R.Full := tower_restriction_full _ hpq
  letI : R.Faithful := tower_restriction_faithful _
  letI : S.Full := tower_restriction_full _ (ell_projection_surjective l E T n)
  letI : S.Faithful := tower_restriction_faithful _
  have hscalar : (l : ℤ) ^ (m + 1) • 𝟙 (cokernel v) = 0 := by
    apply (cancel_epi (cokernel.π v)).1
    simpa only [Linear.comp_smul, Category.comp_id, comp_zero,
      Linear.smul_comp, Category.id_comp] using
      (show ((l : ℤ) ^ (m + 1) • 𝟙 (SC.obj F)) ≫ cokernel.π v = 0 from
        cokernel.condition v)
  have hker (j : ℤ) (U : T.ProEtᵒᵖ)
      (a : (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
      (ha : (spCompletedEllCommProjection l E T m).hom.app U a = 0)
      (x : ((cokernel v).X j).val.obj U) : a • x = 0 := by
    have ha' : a ∈ RingHom.ker ((spCompletedEllCommProjection l E T m).hom.app U).hom := ha
    rw [ell_projection_kernel] at ha'
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp ha'
    have hz' := congrArg (fun k ↦ (k.f j).val.app U (y • x)) hscalar
    rw [tower_scalar_apply] at hz'
    change ((l : ℤ) ^ (m + 1)) • (y • x) = 0 at hz'
    rw [← Int.cast_smul_eq_zsmul (R :=
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U),
      Int.cast_pow, Int.cast_natCast] at hz'
    rw [hy, mul_smul]
    exact hz'
  obtain ⟨K', ⟨e⟩⟩ := tower_complex_in_restriction_image
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (spCompletedEllCommProjection l E T m))
    (ell_projection_surjective l E T m) (cokernel v) hker
  have himage : ∃ X, Nonempty (SC.obj (RC.obj X) ≅ cokernel v) :=
    ⟨K', ⟨iC.app K' ≪≫ e⟩⟩
  let unitMap : SC.obj F ⟶ SC.obj (RC.obj (EC.obj F)) := SC.map (adj.unit.app F)
  have hzero : (l : ℤ) ^ (m + 1) • 𝟙 (SC.obj (RC.obj (EC.obj F))) = 0 := by
    have hzN : (l : ℤ) ^ (m + 1) • 𝟙 (NC.obj (EC.obj F)) = 0 := by
      ext j U x
      rw [tower_scalar_apply]
      change ((l : ℤ) ^ (m + 1)) •
        (show ((EC.obj F).X j).val.obj U from x) = 0
      rw [← Int.cast_smul_eq_zsmul (R :=
        ((spCoefficientCommRings.{u, u} l E T).obj (op m)).obj.obj U), Int.cast_pow,
        Int.cast_natCast, ell_projection_zero l E T m U, zero_smul]
    exact tower_scalar_zero_of_iso (iC.app (EC.obj F)) _ hzN
  have hzu : v ≫ unitMap = 0 := by
    change ((l : ℤ) ^ (m + 1) • 𝟙 _) ≫ unitMap = 0
    rw [Linear.smul_comp, Category.id_comp, ← Category.comp_id unitMap,
      ← Linear.comp_smul]
    change unitMap ≫ ((l : ℤ) ^ (m + 1) • 𝟙 (SC.obj (RC.obj (EC.obj F)))) = 0
    rw [hzero, comp_zero]
  let d := cokernel.desc v unitMap hzu
  have : IsIso d := tower_unit_cokernel RC SC EC adj F v hzu himage
  have ht : adj.unit.app F ≫ RC.map g = finiteTransition l E T D P h := by
    ext j : 1
    change A.ordinaryAdj.unit.app _ ≫ R.map ((D.ordinaryReduction h).app (P.X j)) = _
    rw [D.ordinaryReduction_eq]
    exact (A.ordinaryAdj.homEquiv _ _).apply_symm_apply _
  have hcomp : completedMap l E T D P h =
      unitMap ≫ SC.map (RC.map g) ≫ iC.hom.app K := by
    rw [← Category.assoc, ← SC.map_comp, ht]
    exact (finiteTransition_restrict l E T D P h).symm
  have heq : cokernel.desc v (completedMap l E T D P h) hz =
      d ≫ SC.map (RC.map g) ≫ iC.hom.app K := by
    apply (cancel_epi (cokernel.π v)).1
    rw [cokernel.π_desc, ← Category.assoc, ← Category.assoc, cokernel.π_desc]
    exact hcomp
  change QuasiIso (cokernel.desc v (completedMap l E T D P h) hz)
  rw [heq]
  infer_instance

private theorem modelTower_normalized
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (C : spDerivedCoefficientTowers l E T D)
    (z : (@DerivedCategory.Q _ _ _ D.hasDerived).obj P ≅ C)
    (hflat : ∀ n : ℕ, systemLevelKFlat.{u + 1, u, u + 1} (spCoefficientCommRings.{u, u} l E T) n
      (finiteComplex l E T D P n))
    (hnorm : IsSpNormalizedTower l E T D C) :
    CochainComplex.IsNormalizedAdicTower (l : ℤ) (modelTower l E T D P) := by
  refine ⟨modelTower_annihilated l E T D P, ?_, modelTower_exact l E T D P hflat⟩
  intro m n h
  cases m with
  | zero =>
    have hc : IsZero (cokernel ((l : ℤ) ^ 0 •
        𝟙 ((modelTower l E T D P).obj (op n)))) := by
      rw [pow_zero, one_smul]
      exact isZero_cokernel_of_epi _
    have hq (f : cokernel ((l : ℤ) ^ 0 •
        𝟙 ((modelTower l E T D P).obj (op n))) ⟶
          (modelTower l E T D P).obj (op 0)) : QuasiIso f := by
      have : IsIso f := hc.isIso (isZero_zero _) f
      infer_instance
    exact hq _
  | succ m =>
    cases n with
    | zero => omega
    | succ n =>
      exact scalar_cokernel_quasiIso l E T D P C z hflat hnorm
        (Nat.le_of_succ_le_succ h) _

/-- A normalized derived ell-power tower admits a strict normalized adic model.
Source: blueprint sk-lem-sp-tower.proof.md, flat-term strictification; Bhatt--Scholze,
Lemmas 3.5.4--3.5.5. (blueprint: lem-sp-tower-strict-normalized-adic-model).

Proof: transport a representative of C to strict coefficient systems and apply a
simultaneous K-flat resolution with flat terms at every finite level. Transport it
back through the equivalence. Its actual chain maps form a strict tower after
restriction to completed coefficients. Insert zero at index zero. Multiplication by
ell^(a+b) vanishes at level a+b, and flatness over that quotient identifies the kernel
of ell^b with the image of ell^a. Normalization and the specified derived adjunction
identify the quotient maps with the original reduction maps, so these are
quasi-isomorphisms. The chosen level isomorphisms commute with successor transitions,
and retain the finite complexes and their specified derived level identifications.
No boundedness or constructibility is used. The scalar action is the canonical integer
linear action, so the scalar l is the actual coefficient ell. -/
theorem spTower_strict_normalized_adic_model
    (C : spDerivedCoefficientTowers l E T D)
    (hnorm : IsSpNormalizedTower l E T D C) :
    ∃ (U : ℕᵒᵖ ⥤ CochainComplex
          (WeilConjectures.scalarReductionSource.{u, u} l E T) ℤ)
        (hU : CochainComplex.IsNormalizedAdicTower (l : ℤ) U)
        (eU : ∀ j : ℕ, DerivedCategory.Q.obj (U.obj (op (j + 1))) ≅
          (spDerivedCompletedEvaluation l E T D j).obj C),
        (∀ j : ℕ,
          DerivedCategory.Q.map (U.map
              (homOfLE (Nat.succ_le_succ j.le_succ)).op) ≫ (eU j).hom =
            (eU (j + 1)).hom ≫ (spDerivedCompletedTransition l E T D j).app C) ∧
        ∀ j : ℕ,
          ∃ (N : CochainComplex (Scheme.proEtaleRingModules T
              (Scheme.proEtaleConstantRing T (Padic.coefficientExtensionIntegers l E ⧸
                spEllIdeal l E ^ (j + 1)))) ℤ)
            (iN : U.obj (op (j + 1)) ≅
              ((spCompletedEllRestriction l E T j).mapHomologicalComplex (.up ℤ)).obj N)
            (eN : DerivedCategory.Q.obj N ≅
              (spDerivedCoefficientEvaluation l E T D j).obj C),
            (eU j).hom = DerivedCategory.Q.map iN.hom ≫
              (spCompletedEllRestriction l E T j).mapDerivedCategoryFactors.inv.app N ≫
              (spCompletedEllRestriction l E T j).mapDerivedCategory.map eN.hom  := by
  classical
  obtain ⟨P, z, hflat⟩ := flat_representative l E T D C
  refine ⟨modelTower l E T D P, modelTower_normalized l E T D P C z hflat hnorm,
    modelIso l E T D P C z, modelIso_successor l E T D P C z, ?_⟩
  intro n
  refine ⟨finiteComplex l E T D P n, Iso.refl _, finiteIso l E T D P C z n, ?_⟩
  change (modelIso l E T D P C z n).hom =
    DerivedCategory.Q.map (𝟙 (completedComplex l E T D P n)) ≫ _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact modelIso_finite l E T D P C z n

end AlgebraicGeometry.ProEtale
