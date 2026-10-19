/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.ExceptionalFiniteRealization
public import Sheaf.Paper.PurTwistSheafLocallyFree
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
/-! # Finite coordinates and projections on the actual pro-etale systems
Source: blueprint def-weil-exceptional-inverse-image. The scalar-unit equations and
exact localization squares fix all comparisons, including their maps.
(blueprint: def-pur-adic-proetale-realization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures
private def scalarCancel {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (α : R ⟶ S) (β : S ⟶ R)
    (h : α ≫ β = 𝟙 R) :
    restrictScalars.{u + 1} β ⋙ restrictScalars α ≅ 𝟭 (SheafOfModules.{u + 1} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private def scalarEquivalence {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (e : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R :=
  CategoryTheory.Equivalence.mk (restrictScalars e.hom) (restrictScalars e.inv)
    (scalarCancel e.inv e.hom e.inv_hom_id).symm
    (scalarCancel e.hom e.inv e.hom_inv_id)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The quotient ring is finite at every positive exponent.
Source: blueprint finite coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalFiniteQuotient (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- Finite realization on the pro-etale site, using only scalar restriction and the
explicit quotient equivalence. It retains each underlying section.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
def integralExceptionalProRealization (W : Scheme.{u}) (n : ℕ) :
    coefficientLevelModules (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n ⥤
    Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) :=
  letI := Scheme.purTwistForgetPreservesSheafification W
  SheafOfModules.restrictScalars
      ((constantCommuteCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (integralExceptionalQuotientRing l E n))).inv ⋙
    constantRingModuleRestriction (Scheme.ProEt.topology W)
      (integralExceptionalQuotientRing l E n) ⋙
      sheafCompose (Scheme.ProEt.topology W)
        (ModuleCat.restrictScalars (integralExceptionalQuotient l E n).symm.toRingHom)

/-- Pro-etale finite realization is an exact additive equivalence.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: its factors are restriction along the constant-ring presentation isomorphism,
the equivalence extending constant scalar actions to locally constant sections, and
restriction along a ring equivalence. Their inverses undo those operations. They
leave underlying maps unchanged and preserve kernels and cokernels. -/
theorem integralExceptionalProRealization_properties (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalProRealization l E W n).IsEquivalence ∧
      (integralExceptionalProRealization l E W n).Additive ∧
      PreservesFiniteLimits (integralExceptionalProRealization l E W n) ∧
      PreservesFiniteColimits (integralExceptionalProRealization l E W n) := by
  let J := Scheme.ProEt.topology W
  let R := integralExceptionalQuotientRing l E n
  let := Scheme.purTwistForgetPreservesSheafification W
  obtain ⟨e, he, ha, _, _⟩ := (constant_ring_module_sheaves J R).1
  have : (constantRingModuleRestriction J R).IsEquivalence := by
    rw [← he]
    infer_instance
  have : (constantRingModuleRestriction J R).Additive := by
    rw [← he]
    exact ha
  let c := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of R)
  have : (restrictScalars.{u + 1} c.inv).IsEquivalence :=
    (scalarEquivalence c.symm).isEquivalence_functor
  let F := ModuleCat.restrictScalars.{u + 1} (integralExceptionalQuotient l E n).symm.toRingHom
  have : (sheafCompose J F).IsEquivalence := by
    let a := (F.adjunction.whiskerRight W.ProEtᵒᵖ).restrictFullyFaithful
      (fullyFaithfulSheafToPresheaf J _) (fullyFaithfulSheafToPresheaf J _)
      (L := sheafCompose J F) (R := sheafCompose J F.inv) (Iso.refl _) (Iso.refl _)
    exact a.toEquivalence.isEquivalence_functor
  have : (integralExceptionalProRealization l E W n).IsEquivalence :=
    inferInstanceAs (restrictScalars c.inv ⋙ constantRingModuleRestriction J R ⋙
      sheafCompose J F).IsEquivalence
  have : (integralExceptionalProRealization l E W n).Additive :=
    inferInstanceAs (restrictScalars c.inv ⋙ constantRingModuleRestriction J R ⋙
      sheafCompose J F).Additive
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalProRealization_equivalence (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalProRealization l E W n).IsEquivalence :=
  (integralExceptionalProRealization_properties l E W n).1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalProRealization_additive (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalProRealization l E W n).Additive :=
  (integralExceptionalProRealization_properties l E W n).2.1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalProRealization_limits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (integralExceptionalProRealization l E W n) :=
  (integralExceptionalProRealization_properties l E W n).2.2.1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalProRealization_colimits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (integralExceptionalProRealization l E W n) :=
  (integralExceptionalProRealization_properties l E W n).2.2.2

variable (W : Scheme.{u})

/-- Cache existing sheafification at the precise site size.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance (priority := 4000) integralExceptionalProRingRightAdjoint :
    (sheafToPresheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).IsRightAdjoint :=
  inferInstance
/-- Restriction along the explicit ring map preserves addition.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalLevel_additive (n : ℕ) :
    (integralExceptionalLevel l E W n).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{u + 1}
    (integralExceptionalRingMap l E W n)).Additive
/-- Cache componentwise addition at the actual system sizes.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance (priority := 4000) integralExceptionalEvaluation_additive :
    ∀ n, (coefficientEvaluation.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology W) (O := integralExceptionalIntegers l E)
      (ell := integralExceptionalUniformizer l E) n).Additive :=
  fun n ↦ coefficientEvaluation_additive.{u + 1, u, u + 1} n
/-- Componentwise kernels are preserved by evaluation.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalEvaluation_limits (n : ℕ) :
    PreservesFiniteLimits (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n) :=
  (coefficientEvaluation_exact.{u + 1, u, u + 1}
    (J := Scheme.ProEt.topology W) (O := integralExceptionalIntegers l E)
    (ell := integralExceptionalUniformizer l E) n).1
/-- Componentwise cokernels are preserved by evaluation.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalEvaluation_colimits (n : ℕ) :
    PreservesFiniteColimits (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n) :=
  (coefficientEvaluation_exact.{u + 1, u, u + 1}
    (J := Scheme.ProEt.topology W) (O := integralExceptionalIntegers l E)
    (ell := integralExceptionalUniformizer l E) n).2

/-- The original finite-to-generic coordinate change is itself an equivalence.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: the ring map is induced by the explicit quotient ring equivalence. Restriction
along its inverse is a two-sided inverse on module sheaves. -/
theorem integralExceptionalLevel_equivalence (n : ℕ) :
    (integralExceptionalLevel l E W n).IsEquivalence := by
  let e := (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).mapIso
        (integralExceptionalQuotient l E n).toCommRingCatIso)
  exact (scalarEquivalence e).isEquivalence_functor
attribute [instance] integralExceptionalLevel_equivalence

private theorem constantForgetUnit (R : Type (u + 1)) [CommRing R]
    (U : W.ProEtᵒᵖ) (a : R) :
    (((constantCommuteCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of R)).inv.hom.app U)
        ((toSheafify (Scheme.ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of R))).app U a) =
      (toSheafify (Scheme.ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of R))).app U a := by
  let J := Scheme.ProEt.topology W
  let := Scheme.purTwistForgetPreservesSheafification W
  let c := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of R)
  have ht : Functor.whiskerRight
      (toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of R)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫ c.hom.hom =
      toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of R)) := by
    dsimp [c]
    rw [constantCommuteCompose_hom_app_hom, ← Category.assoc,
      sheafComposeIso_inv_fac]
    change toSheafify J _ ≫ sheafifyMap J (𝟙 _) = _
    rw [sheafifyMap_id, Category.comp_id]
    rfl
  have hc : c.hom.hom ≫ c.inv.hom = 𝟙 _ :=
    (sheafToPresheaf J RingCat.{u + 1}).mapIso c |>.hom_inv_id
  have h := congrArg (fun f ↦ f ≫ c.inv.hom) ht
  rw [Category.assoc, hc] at h
  dsimp [c, J] at h
  exact (ConcreteCategory.congr_hom (congr_app h U) a).symm

private theorem fixedScalar (n : ℕ) (U : W.ProEtᵒᵖ)
    (a : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :
    (integralExceptionalRingMap l E W n).hom.app U
      ((((constantCommuteCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (integralExceptionalQuotientRing l E n))).inv.hom.app U)
        ((toSheafify (Scheme.ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).obj
            (RingCat.of (integralExceptionalQuotientRing l E n)))).app U
              ((integralExceptionalQuotient l E n).symm a))) =
    (ProEtale.finiteCoefficientIntrinsicScalarMap W
      (Padic.coefficientExtensionRing l E (n + 1))).app U a := by
  rw [constantForgetUnit W]
  have h := congr_app (toSheafify_naturality (Scheme.ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).map
      (CommRingCat.ofHom (integralExceptionalQuotient l E n).toRingHom))) U
  have h' := (ConcreteCategory.congr_hom h
    ((integralExceptionalQuotient l E n).symm a)).symm
  change (integralExceptionalRingMap l E W n).hom.app U
      ((toSheafify (Scheme.ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of
          (integralExceptionalQuotientRing l E n)))).app U
          ((integralExceptionalQuotient l E n).symm a)) =
    (ProEtale.finiteCoefficientIntrinsicScalarMap W
      (Padic.coefficientExtensionRing l E (n + 1))).app U
        ((integralExceptionalQuotient l E n) ((integralExceptionalQuotient l E n).symm a)) at h'
  simpa only [RingEquiv.apply_symm_apply] using h'

/-- The coordinate realization of a fixed module is the same module. Its map is
specified on every scalar-unit section of the actual intrinsic realization.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: restriction leaves the underlying abelian sheaf unchanged. The scalar-unit
map becomes an isomorphism after extending and then restricting locally constant
coefficients. Its inverse satisfies the displayed section formula. Such sections
locally generate, so the natural isomorphism is unique. -/
theorem integralExceptionalFixedUnit_existsUnique (n : ℕ) :
    ∃! e : (Scheme.sfIntrinsicModuleEquivalence W
        (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
      integralExceptionalLevel l E W n ⋙ integralExceptionalProRealization l E W n ≅ 𝟭 _,
      ∀ (M : Sheaf (Scheme.ProEt.topology W)
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
        (U : W.ProEtᵒᵖ) (m : M.obj.obj U),
        (e.hom.app M).hom.app U
          (Scheme.sfIntrinsicRealizationUnit W
            (Padic.coefficientExtensionRing l E (n + 1)) M U m) = m := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))
  let J := Scheme.ProEt.topology W
  let α := ProEtale.finiteCoefficientIntrinsicScalarMap W
    (Padic.coefficientExtensionRing l E (n + 1))
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} α
  let P := ProEtale.finiteCoefficientModulePresheaf W.ProEt A
  let F := (Scheme.sfIntrinsicModuleEquivalence W
    (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
      integralExceptionalLevel l E W n ⋙ integralExceptionalProRealization l E W n
  let η : 𝟭 (Sheaf J (ModuleCat.{u + 1} A)) ⟶ F :=
    { app := fun M ↦
        { hom :=
          { app := fun U ↦ by
              let Y := (F.obj M).obj.obj U
              letI : Module A Y := Y.isModule
              exact ModuleCat.ofHom (R := A) (Y := Y)
                { toFun := Scheme.sfIntrinsicRealizationUnit W
                    (Padic.coefficientExtensionRing l E (n + 1)) M U
                  map_add' := fun x y ↦ ((adj.unit.app (P.obj M.obj)).app U).hom.map_add x y
                  map_smul' := fun a m ↦ by
                    change Scheme.sfIntrinsicRealizationUnit W
                        (Padic.coefficientExtensionRing l E (n + 1)) M U (a • m) =
                      (integralExceptionalRingMap l E W n).hom.app U
                        ((((constantCommuteCompose J
                          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
                            (CommRingCat.of (integralExceptionalQuotientRing l E n))).inv.hom.app U)
                          ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj
                            (RingCat.of (integralExceptionalQuotientRing l E n)))).app U
                              ((integralExceptionalQuotient l E n).symm a))) • _
                    rw [fixedScalar l E W n U a]
                    exact ((adj.unit.app (P.obj M.obj)).app U).hom.map_smul a m }
            naturality := fun U V f ↦ by
              ext m
              exact ConcreteCategory.congr_hom ((adj.unit.app (P.obj M.obj)).naturality f) m } }
      naturality := fun M N f ↦ by
        ext U m
        have h := congrArg (fun t ↦ t.app U) (adj.unit.naturality (P.map f.hom))
        exact ConcreteCategory.congr_hom h m }
  have hbij (M : Sheaf J (ModuleCat.{u + 1} A)) (U : W.ProEtᵒᵖ) :
      Function.Bijective ((η.app M).hom.app U) := by
    have : IsIso (toSheafify J (P.obj M.obj).presheaf) :=
      isIso_toSheafify J ((sheafCompose J
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj M).property
    exact ConcreteCategory.bijective_of_isIso
      ((toSheafify J (P.obj M.obj).presheaf).app U)
  have hη : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf J (ModuleCat.{u + 1} A))]
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    exact (ConcreteCategory.isIso_iff_bijective _).2 (hbij M U)
  let e := (asIso η).symm
  have he (M : Sheaf J (ModuleCat.{u + 1} A)) (U : W.ProEtᵒᵖ) (m : M.obj.obj U) :
      (e.hom.app M).hom.app U
        (Scheme.sfIntrinsicRealizationUnit W
          (Padic.coefficientExtensionRing l E (n + 1)) M U m) = m := by
    exact ConcreteCategory.congr_hom (congr_app (congrArg (fun t ↦ t.hom)
      (congr_app (asIso η).hom_inv_id M)) U) m
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  ext M U x
  obtain ⟨m, rfl⟩ := (hbij M U).2 x
  exact (he' M U m).trans (he M U m).symm

/-- The actual scalar-unit-normalized finite coordinate realization.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
def integralExceptionalFixedUnit (n : ℕ) :=
  (integralExceptionalFixedUnit_existsUnique l E W n).exists.choose

/-- Identification with the recorded inverse realization, normalized by its unit.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: compose the preceding scalar-unit comparison with the unit and counit of the
recorded realization equivalence. Its triangle identities give the displayed equation.Essential
 surjectivity of the realization and its unit determine every component. -/
theorem integralExceptionalLevelFixed_existsUnique (n : ℕ) :
    ∃! e : integralExceptionalLevel l E W n ⋙ integralExceptionalProRealization l E W n ≅
      (Scheme.sfIntrinsicModuleEquivalence W
        (Padic.coefficientExtensionRing l E (n + 1))).inverse,
      ∀ M, e.hom.app ((Scheme.sfIntrinsicModuleEquivalence W
        (Padic.coefficientExtensionRing l E (n + 1))).functor.obj M) ≫
        (Scheme.sfIntrinsicModuleEquivalence W
          (Padic.coefficientExtensionRing l E (n + 1))).unitIso.inv.app M =
          (integralExceptionalFixedUnit l E W n).hom.app M := by
  let e := Scheme.sfIntrinsicModuleEquivalence W
    (Padic.coefficientExtensionRing l E (n + 1))
  let H := (Functor.whiskeringLeft
    (Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
    (Scheme.proEtaleRingModules W
      (Scheme.proEtaleConstantRing W (Padic.coefficientExtensionRing l E (n + 1))))
    (Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).obj
        e.functor
  let ff : H.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  let t : H.obj (integralExceptionalLevel l E W n ⋙
      integralExceptionalProRealization l E W n) ≅ H.obj e.inverse :=
    integralExceptionalFixedUnit l E W n ≪≫ e.unitIso
  let i := ff.preimageIso t
  have hi (M) : i.hom.app (e.functor.obj M) ≫ e.unitIso.inv.app M =
      (integralExceptionalFixedUnit l E W n).hom.app M := by
    have h := congr_app (ff.map_preimage t.hom) M
    change i.hom.app (e.functor.obj M) = _ at h
    rw [h]
    simp [t]
  refine ⟨i, hi, ?_⟩
  intro i' hi'
  apply Iso.ext
  apply ff.map_injective
  apply NatTrans.ext
  funext M
  change i'.hom.app (e.functor.obj M) = i.hom.app (e.functor.obj M)
  have h := (hi' M).trans (hi M).symm
  change i'.hom.app (e.functor.obj M) ≫ e.unitIso.inv.app M =
    i.hom.app (e.functor.obj M) ≫ e.unitIso.inv.app M at h
  exact (Iso.cancel_iso_inv_right _ _ (e.unitIso.app M)).1 h

/-- The finite coordinate comparison, fixed by the recorded equivalence unit.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
def integralExceptionalLevelFixed (n : ℕ) :=
  (integralExceptionalLevelFixed_existsUnique l E W n).exists.choose

/-- The exact derived coordinate comparison, induced by the specified ordinary map.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
def integralExceptionalDerivedLevelFixed (n : ℕ) :
    (integralExceptionalLevel l E W n).mapDerivedCategory ⋙
      (integralExceptionalProRealization l E W n).mapDerivedCategory ≅
    (Scheme.sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).inverse :=
  letI := (Scheme.sfIntrinsicModuleEquivalence W
    (Padic.coefficientExtensionRing l E (n + 1))).inverse_additive
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (integralExceptionalLevelFixed l E W n)

/-- Coordinates preserve finite evaluation as an equality of actual ordinary functors.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: both functors take a strict system to its nth module with the quotient action
changed along the same ring equivalence. Their maps are the same nth component map;
functor extensionality gives equality. -/
theorem integralExceptionalCoordinatesEvaluation (n : ℕ) :
    integralExceptionalCoordinates l E W ⋙
      coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
        (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n =
    coefficientSequenceEvaluation l E W n ⋙ integralExceptionalLevel l E W n := by
  rfl

/-- Every normalized evaluation package has its unique exact-localization comparison.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: both functors factor termwise evaluation through quasi-isomorphism localization. The
two displayed factorization maps give existence. Uniqueness of factorization on
complexes and roofs proves uniqueness of the natural isomorphism. -/
theorem integralExceptionalProEvaluationModel_existsUnique
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
    (n : ℕ) :
    ∃! e : P.evaluation n ≅
      (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
        (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)
          n).mapDerivedCategory
          ,
      ∀ J, e.hom.app (DerivedCategory.Q.obj J) ≫
        (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
          (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)
            n).mapDerivedCategoryFactors.hom.app
             J = (P.evaluationFactors n).hom.app J := by
  let F := (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
    (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)
      n).mapDerivedCategory
  let ff := Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q (C := CoefficientSystem (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (HomologicalComplex.quasiIso _ (.up ℤ))
      (DerivedCategory (coefficientLevelModules (J := Scheme.ProEt.topology W)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n))
  let e : P.evaluation n ≅ F := ff.preimageIso
    (P.evaluationFactors n ≪≫ (coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology W) (O := integralExceptionalIntegers l E)
        (ell := integralExceptionalUniformizer l E) n).mapDerivedCategoryFactors.symm)
  refine ⟨e, ?_, ?_⟩
  · intro J
    have he := congr_app (ff.map_preimage
      (P.evaluationFactors n ≪≫ (coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology W) (O := integralExceptionalIntegers l E)
        (ell := integralExceptionalUniformizer l E) n).mapDerivedCategoryFactors.symm).hom) J
    change e.hom.app (DerivedCategory.Q.obj J) = _ at he
    rw [he]
    simp
  · intro e' he'
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
    intro J
    apply (cancel_mono ((coefficientEvaluation.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology W) (O := integralExceptionalIntegers l E)
      (ell := integralExceptionalUniformizer l E) n).mapDerivedCategoryFactors.hom.app J)).1
    rw [he']
    have he := congr_app (ff.map_preimage
      (P.evaluationFactors n ≪≫ (coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology W) (O := integralExceptionalIntegers l E)
        (ell := integralExceptionalUniformizer l E) n).mapDerivedCategoryFactors.symm).hom) J
    change e.hom.app (DerivedCategory.Q.obj J) = _ at he
    rw [he]
    simp

/-- The evaluation model, fixed on every strict complex.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
@[no_expose] def integralExceptionalProEvaluationModel
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
    (n : ℕ) :=
  (integralExceptionalProEvaluationModel_existsUnique l E W P n).exists.choose

/-- The direct coordinate/evaluation identification, obtained from the exact ordinary
coordinate equality and the scalar-unit-normalized finite realization.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
@[no_expose] def integralExceptionalCoordinatesFixed
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
    (N : coefficientSequenceDerived l E W) (n : ℕ) :
    (integralExceptionalProRealization l E W n).mapDerivedCategory.obj
      ((P.evaluation n).obj ((integralExceptionalDerivedCoordinates l E W).obj N)) ≅
    (Scheme.sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
        ((coefficientSequenceDerivedEvaluation l E W n).obj N) :=
  (integralExceptionalProRealization l E W n).mapDerivedCategory.mapIso
    ((integralExceptionalProEvaluationModel l E W P n).app _ ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm.app N ≪≫
      (Functor.mapDerivedCategoryNatIso
        (eqToIso (integralExceptionalCoordinatesEvaluation l E W n))).app N ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).app N) ≪≫
    (integralExceptionalDerivedLevelFixed l E W n).app _

/-- The inverse coordinate/evaluation identification uses the actual counit of the
coordinate equivalence, rather than any choice of levelwise lift.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
@[no_expose] def integralExceptionalCoordinatesInvFixed
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
    (N : DerivedCategory (CoefficientSystem (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E))) (n : ℕ) :
    (Scheme.sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
      ((coefficientSequenceDerivedEvaluation l E W n).obj
        ((integralExceptionalDerivedCoordinatesInv l E W).obj N)) ≅
    (integralExceptionalProRealization l E W n).mapDerivedCategory.obj ((P.evaluation n).obj N) :=
  letI : (integralExceptionalCoordinates l E W).asEquivalence.functor.Additive :=
    integralExceptionalCoordinates_additive l E W
  (integralExceptionalCoordinatesFixed l E W P
    ((integralExceptionalDerivedCoordinatesInv l E W).obj N) n).symm ≪≫
    (integralExceptionalProRealization l E W n).mapDerivedCategory.mapIso
      ((P.evaluation n).mapIso
        (((integralExceptionalCoordinates l E W).asEquivalence.mapDerivedCategory).counitIso.app
           N))
end WeilConjectures
