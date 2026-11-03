/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExactScalarPointCup
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfectGeneral
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.CondensedPointTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointFibreTensorModels
public import WeilConjectures.AlgebraicGeometry.FlatCohomologyDerivedTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LineCoefficientMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LineCrossProductNaturality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointLineCoordinates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointPerfectEvaluationAgreement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointPullbackTrivializationMonoidal2
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointTransportIntertwining
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SingleRealizationIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SingleRealizationNaturality

/-! # Point sections transport, cup compatibility and degreewise Frobenius

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-frobenius/sec-purity-duality-and-frobenius/sk-thm-frobenius/
thm-pod-equivariance-of-the-twisted-pairing.proof.md`, Steps 1 and 3
(blueprint: lem-pod-condensed-point-sections-transport).

The statement packages the canonical point-section functor, its normalized exact-sections
cup, Frobenius restriction transport, strict intertwining calculation, and the degree-zero
rank-one specialization. Every map is in the native condensed module derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj TensorProduct
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
attribute [local instance] AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj
attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] HasDerivedCategory.ofIsGrothendieckAbelian

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-! The following helpers are the canonical objects named in the node. -/

/-- The geometric point scheme attached to the finite-field datum.
Source: the point specialization in Steps 1 and 3 of the cited Frobenius proof
(blueprint: lem-pod-condensed-point-sections-transport). -/
abbrev pointScheme (D : WeilConjectures.FiniteFieldDatum.{u}) : Scheme.{u} :=
  Spec (.of D.k)

/-- Geometric Frobenius on the geometric point.
Source: the restriction map in Steps 1 and 3 of the cited Frobenius proof
(blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointGeometricFrobenius
    (D : WeilConjectures.FiniteFieldDatum.{u}) : pointScheme D ≅ pointScheme D := by
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  exact Scheme.Spec.mapIso
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingEquiv.toCommRingCatIso.op

/-- The monoidal structure on the pulled-back condensed coefficient.
Source: the coefficient pullback in Step 2 (blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable instance pointMonObj (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] :
    MonObj (condensedRingObj Λ (pointScheme D)) :=
  ((upperStarFromPoint (pointScheme D)).mapMon.obj (Mon.mk Λ)).mon

/-- The commutative monoidal structure on the pulled-back coefficient.
Source: the coefficient pullback in Step 2 (blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable instance pointIsCommMonObj (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :
    IsCommMonObj (condensedRingObj Λ (pointScheme D)) :=
  Functor.isCommMonObj_obj (F := upperStarFromPoint (pointScheme D))

/-- Native module objects at the geometric point.
Source: the native derived-category convention in Step 1
(blueprint: lem-pod-condensed-point-sections-transport). -/
abbrev pointModules (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (pointScheme D)) Ab.{u + 1})
    (condensedRingObj Λ (pointScheme D))

/-- The native unbounded derived category at the geometric point.
Source: the native derived-category convention in Step 1
(blueprint: lem-pod-condensed-point-sections-transport). -/
abbrev pointDerived (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  CohomologyTransport.D Λ (pointScheme D)

/-- Termwise exact scalar sections descended to the native derived category.
Source: exact sections in Step 1 (blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable abbrev scalarSections (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  TraceCupPoint.fiber Λ D.k

/-- The native relative derived tensor at the geometric point.
Source: the relative tensor in Step 1 (blueprint: lem-pod-condensed-point-sections-transport). -/
abbrev pointTensor (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  derivedTensor Λ (pointScheme D)

/-- Geometric-Frobenius pullback on the native derived category.
Source: the pullback `P = Lg_s^*` in Step 2
(blueprint: lem-pod-condensed-point-sections-transport). -/
abbrev pointAction (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  CohomologyTransport.L Λ (pointGeometricFrobenius D).hom

/-- The canonical monoidal tensor comparison for the Frobenius pullback.
Source: the tensor comparison δ in Steps 4 and 6 of the cited Frobenius proof
(blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointDelta (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (C E : pointDerived D Λ) :
    (pointAction D Λ).obj (MonoidalCategoryStruct.tensorObj C E) ≅
      MonoidalCategoryStruct.tensorObj ((pointAction D Λ).obj C)
        ((pointAction D Λ).obj E) := by
  letI : (pointAction D Λ).Monoidal :=
    Functor.Monoidal.transport
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (pointGeometricFrobenius D).hom).symm
  exact (Functor.Monoidal.μIso (pointAction D Λ) C E).symm

/-- The canonical coefficient-unit isomorphism of the monoidal Frobenius pullback.
Source: the coefficient datum e_s in Step 3 of the cited Frobenius proof
(blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointFrobeniusCoefficientUnit (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (pointAction D Λ).obj (MonoidalCategoryStruct.tensorUnit (pointDerived D Λ)) ≅
      MonoidalCategoryStruct.tensorUnit (pointDerived D Λ) := by
  letI : (pointAction D Λ).Monoidal :=
    Functor.Monoidal.transport
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (pointGeometricFrobenius D).hom).symm
  exact (Functor.Monoidal.εIso (pointAction D Λ)).symm

/-! The degreewise cross-product map is fixed by the normalized derived cup. -/

/-! The comparison below is the canonical terminal-evaluation comparison used by the
finite-point scalar-realization construction.  It is written here because the point
sections functor has scalar ring `Γ Λ`, while `CondensedGeometricPoint.fiber` has scalar
ring `condensedScalarRing Λ`; the displayed ring equivalence is part of the data. -/

/-- The reconstructed regular internal module is the unit section module. Its components
are the identity linear maps. Source: node proof Steps 1 and 7, internal/section-module
comparison (blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointRegularSectionIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (InternalAbelianSheafModule.sectionModuleEquivalence
      (coherentTopology Profinite.{u}) Λ).functor.obj (Mod.regular Λ) ≅
      SheafOfModules.unit ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (condensedSectionRing Λ)) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun Z ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    apply ConcreteCategory.hom_ext
    intro m
    rfl
  · intro Z W f
    ext
    rfl

/-- Evaluation at a terminal object identifies compatible sections with that value; the
inverse restricts along the unique arrows to the terminal object. Source: node proof
Step 7, terminal evaluation (blueprint: lem-pod-condensed-point-sections-transport). -/
def pointTerminalSectionsEquiv
    {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    (U : C) (hU : IsTerminal U) (M : SheafOfModules.{u + 1} R) :
    M.sections ≃ M.val.obj (op U) where
  toFun s := s.val (op U)
  invFun x := M.val.sectionsMk (fun V ↦ M.val.map (hU.from V.unop).op x) (by
    intro V W f
    rw [← PresheafOfModules.map_comp_apply]
    have hh : f.unop ≫ hU.from V.unop = hU.from W.unop := hU.hom_ext _ _
    exact M.val.congr_map_apply (by
      apply Quiver.Hom.unop_inj
      exact hh) x)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro V
    exact s.property (hU.from V.unop).op
  right_inv x := by
    change M.val.map (hU.from U).op x = x
    have hh : hU.from U = 𝟙 U := hU.hom_ext _ _
    rw [hh]
    simp

/-- A morphism out of the regular module is identified with its value on the unit section.
Source: node proof Steps 1 and 7, terminal evaluation and the coefficient identification
(blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointRegularSectionEquiv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    (Mod.regular Λ ⟶ M) ≃
      (Evaluation.sections (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u})).obj M :=
  let e := InternalAbelianSheafModule.sectionModuleEquivalence
    (coherentTopology Profinite.{u}) Λ
  e.fullyFaithfulFunctor.homEquiv.trans
    ((Iso.homCongr (pointRegularSectionIso Λ) (Iso.refl _)).trans
      ((SheafOfModules.unitHomEquiv (e.functor.obj M)).trans
        (pointTerminalSectionsEquiv (⊤_ Profinite.{u}) terminalIsTerminal
          (e.functor.obj M))))

/-- The canonical scalar-ring map sends a regular-module multiplication endomorphism
to its value at the unit. Source: node proof Steps 1 and 7, the identification of
coefficient sections (blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointScalarSectionHom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : MonObj.Γ Λ →+* condensedScalarRing Λ where
  toFun s := pointRegularSectionEquiv Λ (Mod.regular Λ) (Mod.regularEndRingHom s)
  map_one' := by
    rw [map_one]
    change (Evaluation.sections (coherentTopology Profinite.{u}) Λ
      (⊤_ Profinite.{u})).map (𝟙 (Mod.regular Λ)) (1 : condensedScalarRing Λ) =
        (1 : condensedScalarRing Λ)
    rfl
  map_mul' s t := by
    let S := Evaluation.sections (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u})
    let ms : condensedScalarRing Λ →ₗ[condensedScalarRing Λ] condensedScalarRing Λ :=
      (S.map (Mod.regularEndRingHom s)).hom
    let mt : condensedScalarRing Λ →ₗ[condensedScalarRing Λ] condensedScalarRing Λ :=
      (S.map (Mod.regularEndRingHom t)).hom
    rw [map_mul]
    change S.map (Mod.regularEndRingHom t ≫ Mod.regularEndRingHom s)
      (1 : condensedScalarRing Λ) = _
    rw [S.map_comp]
    change ms (mt 1) = ms 1 * mt 1
    calc
      ms (mt 1) = mt 1 * ms 1 := by
        simpa only [smul_eq_mul, _root_.mul_one] using ms.map_smul (mt 1) 1
      _ = ms 1 * mt 1 := mul_comm _ _
  map_zero' := by
    rw [map_zero]
    change (Evaluation.sections (coherentTopology Profinite.{u}) Λ
      (⊤_ Profinite.{u})).map (0 : Mod.regular Λ ⟶ Mod.regular Λ)
        (1 : condensedScalarRing Λ) = 0
    rw [Functor.map_zero]
    rfl
  map_add' s t := by
    simp only [map_add]
    rfl

/-- The canonical ring identification between native and condensed scalar sections.
Source: node proof Steps 1 and 7, coefficient sections at the terminal point
(blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointScalarSectionEquiv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : MonObj.Γ Λ ≃+* condensedScalarRing Λ :=
  RingEquiv.ofBijective (pointScalarSectionHom Λ)
    ((pointRegularSectionEquiv Λ (Mod.regular Λ)).bijective.comp
      Mod.regularEndRingHom_bijective)

/-- Native scalar sections of a condensed module, using the canonical regular-endomorphism
action. Source: node proof Steps 1 and 7, definition of scalar sections
(blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointCoyoneda
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  coyonedaSections ((Mod.regularEndRingHom.op).comp
    (RingEquiv.toOpposite (MonObj.Γ Λ)).toRingHom)

/-- The canonical scalar-linear terminal-evaluation comparison; its component sends
a regular-module morphism to its value at one. Source: node proof Steps 1 and 7
(blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointCoyonedaIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    pointCoyoneda Λ ≅ Evaluation.sections (coherentTopology Profinite.{u}) Λ
      (⊤_ Profinite.{u}) ⋙
        ModuleCat.restrictScalars.{u + 1} (pointScalarSectionEquiv Λ).toRingHom := by
  let S := Evaluation.sections (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u})
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply LinearEquiv.toModuleIso (X₁ := (pointCoyoneda Λ).obj M)
      (X₂ := (S ⋙ ModuleCat.restrictScalars.{u + 1}
        (pointScalarSectionEquiv Λ).toRingHom).obj M)
    refine
      { toEquiv := pointRegularSectionEquiv Λ M
        map_add' := fun f g ↦ by
          change S.map (f + g) (1 : condensedScalarRing Λ) =
            S.map f (1 : condensedScalarRing Λ) + S.map g (1 : condensedScalarRing Λ)
          rw [S.map_add]
          rfl
        map_smul' := fun s f ↦ by
          change S.map (Mod.regularEndRingHom s ≫ f) (1 : condensedScalarRing Λ) =
            pointScalarSectionHom Λ s • S.map f (1 : condensedScalarRing Λ)
          rw [S.map_comp]
          let lf : condensedScalarRing Λ →ₗ[condensedScalarRing Λ] S.obj M :=
            (S.map f).hom
          change lf (pointScalarSectionHom Λ s) =
            pointScalarSectionHom Λ s • lf 1
          simpa only [smul_eq_mul, _root_.mul_one] using
            lf.map_smul (pointScalarSectionHom Λ s) 1 }
  · intro M N f
    ext g
    change S.map (g ≫ f) (1 : condensedScalarRing Λ) =
      S.map f (S.map g (1 : condensedScalarRing Λ))
    rw [S.map_comp]
    rfl

/-- Pullback from the point has the composite of the two geometric-morphism adjunctions.
Source: node proof Step 7, point-topos identification
(blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable instance pointPullbackLeftAdjoint (X : Scheme.{u}) :
    (upperStarFromPoint X).IsLeftAdjoint :=
  (pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint

/-- The same point pullback is additive by its right exactness. Source: node proof
Step 7, exact point-topos identification
(blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable instance pointPullbackAdditive (X : Scheme.{u}) :
    (upperStarFromPoint X).Additive :=
  rightExactFunctor_le_additiveFunctor _ _ _ (by
    rw [rightExactFunctor_iff]
    infer_instance)

/-- Canonical scalar sections commute with point pullback: the component is the map
on regular-module morphisms, with coefficient-action normalization. Source: node proof
Steps 1 and 7 (blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointSectionsPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    pointCoyoneda Λ ≅ ((upperStarFromPoint (Spec (.of k))).mapMod Λ) ⋙
      condensedRingCoefficientSections Λ (Spec (.of k)) := by
  let H := (upperStarFromPoint (Spec (.of k))).mapMod Λ
  let c₁ := (Mod.regularEndRingHom.op).comp
    (RingEquiv.toOpposite (MonObj.Γ Λ)).toRingHom
  let c₂ := (Mod.regularEndRingHom.op).comp
    ((RingEquiv.toOpposite _).toRingHom.comp
      (condensedRingScalarSections Λ (Spec (.of k))))
  have h (a : MonObj.Γ Λ) : (Iso.refl (H.obj (Mod.regular Λ))).inv ≫
      H.map (c₁ a).unop = (c₂ ((RingHom.id _) a)).unop ≫
        (Iso.refl (H.obj (Mod.regular Λ))).inv := by
    simp only [Iso.refl_inv, Category.id_comp]
    exact CategoryTheory.Functor.mapMod_map_regularEndRingHom
      (upperStarFromPoint (Spec (.of k))) Λ a
  let τ := coyonedaSectionsMap (RingHom.id _) c₁ c₂ H (Iso.refl _) h
  have (M : _) : IsIso (τ.app M) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun f ↦ 𝟙 _ ≫ H.map f)
    simpa only [Category.id_comp] using
      (Functor.FullyFaithful.ofFullyFaithful H).map_bijective (Mod.regular Λ) M
  letI : IsIso τ := NatIso.isIso_of_isIso_app _
  exact asIso τ

/-- The heart comparison is the point equivalence counit followed by the canonical
regular-section and terminal-section comparisons, with the scalar ring identified.
Source: node proof Step 7 (blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointSectionsHeartIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    condensedRingCoefficientSections Λ (Spec (.of k)) ≅
      CondensedGeometricPoint.heartFiber Λ k ⋙
        ModuleCat.restrictScalars.{u + 1} (pointScalarSectionEquiv Λ).toRingHom := by
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  let F := condensedRingCoefficientSections Λ (Spec (.of k))
  exact (Functor.leftUnitor F).symm ≪≫
    Functor.isoWhiskerRight e.counitIso.symm F ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft e.inverse (pointSectionsPullbackIso Λ k).symm ≪≫
    Functor.isoWhiskerLeft e.inverse (pointCoyonedaIso Λ) ≪≫
    (Functor.associator _ _ _).symm

/-- Derive the fixed heart comparison using exact point sections and the published
heart-fiber/derived-fiber comparison. Source: node proof Step 7 and sk-lem-finite,
first proof paragraph (blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointActualSectionsDerivedIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    (condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor ≅
      CondensedGeometricPoint.fiber Λ k ⋙
        (ModuleCat.restrictScalars.{u + 1}
          (pointScalarSectionEquiv Λ).toRingHom).mapDerivedCategory := by
  have := (finite_point_sections_exact Λ k).1
  have := (finite_point_sections_exact Λ k).2
  exact Functor.rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.mapDerivedCategoryNatIso (pointSectionsHeartIso Λ k) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (CondensedGeometricPoint.heartFiberDerivedIso Λ k) _

/-- The canonical point-evaluation comparison, with its scalar-ring transport explicit.
Source: node proof Step 7 and sk-lem-finite, first proof paragraph
(blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointEvaluationComparison
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    scalarSections D Λ ≅ CondensedGeometricPoint.fiber Λ D.k ⋙
      (ModuleCat.restrictScalars.{u + 1}
        (pointScalarSectionEquiv Λ).toRingHom).mapDerivedCategory :=
  pointActualSectionsDerivedIso Λ D.k

/-- Scalar transport along the canonical ring identification is strong monoidal.
Its tensor map is the usual pure-tensor map of restriction of scalars, and its unit
map is the ring identification itself; neither is transported from the desired cup.
Source: the scalar identification in node proof Step 7, over blueprint Steps 1 and 3
(blueprint: lem-pod-condensed-point-sections-transport). -/
@[instance_reducible] noncomputable def pointScalarRestrictionMonoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (ModuleCat.restrictScalars.{u + 1}
      (pointScalarSectionEquiv Λ).toRingHom).Monoidal := by
  let e := pointScalarSectionEquiv Λ
  let F := ModuleCat.restrictScalars.{u + 1} e.toRingHom
  have (M N : ModuleCat.{u + 1} (condensedScalarRing Λ)) :
      IsIso (Functor.LaxMonoidal.μ F M N) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
    let : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm
    let em : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom) (F.obj M) M :=
      { toFun := id
        invFun := id
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    let en : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom) (F.obj N) N :=
      { toFun := id
        invFun := id
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hh : (Functor.LaxMonoidal.μ F M N : _ → _) = TensorProduct.congr em en := by
      funext z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul x y => exact ModuleCat.restrictScalars_μ_tmul e.toRingHom M N x y
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hh]
    exact (TensorProduct.congr em en).bijective
  have : IsIso (Functor.LaxMonoidal.ε F) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hh : (Functor.LaxMonoidal.ε F : _ → _) = e := by
      funext r
      exact ModuleCat.restrictScalars_η e.toRingHom r
    rw [hh]
    exact e.bijective
  exact Functor.Monoidal.ofLaxMonoidal F

/-- The derived scalar transport uses the canonical K-flat tensor comparison of the
ordinary restriction-of-scalars functor, whose tensor and unit maps were fixed above.
Source: node proof Step 7 and the derived comparison in blueprint Step 1
(blueprint: lem-pod-condensed-point-sections-transport). -/
@[instance_reducible] noncomputable def pointDerivedScalarRestrictionMonoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (ModuleCat.restrictScalars.{u + 1}
      (pointScalarSectionEquiv Λ).toRingHom).mapDerivedCategory.Monoidal := by
  let F := ModuleCat.restrictScalars.{u + 1} (pointScalarSectionEquiv Λ).toRingHom
  let eF : ModuleCat.{u + 1} (condensedScalarRing Λ) ≌
      ModuleCat.{u + 1} (MonObj.Γ Λ) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1, u + 1, u + 1}
      (pointScalarSectionEquiv Λ)
  letI : F.IsLeftAdjoint := eF.toAdjunction.isLeftAdjoint
  letI : F.IsRightAdjoint := eF.symm.toAdjunction.isRightAdjoint
  letI : F.Monoidal := pointScalarRestrictionMonoidal Λ
  letI : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  letI : F.mapDerivedCategory.OplaxMonoidal :=
    Functor.mapDerivedCategoryOplaxMonoidal.{u, u + 2, u + 2} F
  have (X Y : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ))) :
      IsIso (Functor.OplaxMonoidal.δ F.mapDerivedCategory X Y) := by
    change IsIso
      (((Functor.mapDerivedCategoryTensorComparison.{u, u + 2, u + 2} F).app X).app Y)
    infer_instance
  have : IsIso (Functor.OplaxMonoidal.η F.mapDerivedCategory) :=
    Functor.isIso_mapDerivedCategoryOplaxMonoidal_η.{u, u + 2, u + 2} F
  exact Functor.Monoidal.ofOplaxMonoidal F.mapDerivedCategory

/-- The canonical natural comparison restricted to the bounded constructible finite-Tor
subcategory. Its scalar transport is the displayed ring equivalence, not an arbitrary iso.
Source: node proof Step 7 and blueprint sk-lem-finite, first proof paragraph
(blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointEvaluationCTFComparison
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (CondensedGeometricPoint.ctf Λ D.k).ι ⋙ scalarSections D Λ ≅
      (CondensedGeometricPoint.ctf Λ D.k).ι ⋙ CondensedGeometricPoint.fiber Λ D.k ⋙
        (ModuleCat.restrictScalars.{u + 1}
          (pointScalarSectionEquiv Λ).toRingHom).mapDerivedCategory :=
  Functor.isoWhiskerLeft (CondensedGeometricPoint.ctf Λ D.k).ι
    (pointEvaluationComparison D Λ)

set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the inherited full-subcategory shift and closed structures needs more search.
set_option maxHeartbeats 1600000 in
-- The same statement includes the closed, triangulated and monoidal compatibility squares.
/-- Agreement with the geometric-point perfect realization uses one braided structure
for its equivalence, internal-Hom evaluation, and the cup and unit squares below.
The comparison in those squares is the defined `pointEvaluationCTFComparison`.
The geometric tensorator and unit are those of `restricted`, and scalar transport uses
the ordinary pure-tensor normalization fixed in `pointScalarRestrictionMonoidal`.
Source: node proof Step 7, blueprint sk-lem-finite, first proof paragraph
(blueprint: lem-pod-condensed-point-sections-transport). -/
structure PointEvaluationAgreement
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] where
  ctf_monoidal : ObjectProperty.IsMonoidal (CondensedGeometricPoint.ctf Λ D.k)
  perfect_monoidal : ObjectProperty.IsMonoidal (CondensedGeometricPoint.perfect Λ)
  ctf_closed : ObjectProperty.IsMonoidalClosed (CondensedGeometricPoint.ctf Λ D.k)
  perfect_closed : ObjectProperty.IsMonoidalClosed (CondensedGeometricPoint.perfect Λ)
  ctf_triangulated : (CondensedGeometricPoint.ctf Λ D.k).IsTriangulated
  perfect_triangulated : (CondensedGeometricPoint.perfect Λ).IsTriangulated
  perfect_values : ∀ K : (CondensedGeometricPoint.ctf Λ D.k).FullSubcategory,
    CondensedGeometricPoint.perfect Λ ((CondensedGeometricPoint.fiber Λ D.k).obj K.obj)
  agreement :
    letI := ctf_monoidal
    letI := perfect_monoidal
    letI := ctf_closed
    letI := perfect_closed
    letI := ctf_triangulated
    letI := perfect_triangulated
    letI := DerivedCategory.braidedCategory' (pointModules D Λ)
    letI := DerivedCategory.braidedCategory'
      (ModuleCat.{u + 1} (condensedScalarRing Λ))
    let G := (ModuleCat.restrictScalars.{u + 1}
      (pointScalarSectionEquiv Λ).toRingHom).mapDerivedCategory
    letI : G.Monoidal := pointDerivedScalarRestrictionMonoidal Λ
    let E := CondensedGeometricPoint.restricted Λ D.k perfect_values
    ∃ m : E.Braided,
      letI : E.Monoidal := m.toMonoidal
      E.IsEquivalence ∧
      (∃ s : E.CommShift ℤ, letI := s; E.IsTriangulated) ∧
      (∀ C H : (CondensedGeometricPoint.ctf Λ D.k).FullSubcategory,
        IsIso ((Functor.LaxMonoidal.ihomComparison E C).natTrans.app H)) ∧
      (∀ C H : (CondensedGeometricPoint.ctf Λ D.k).FullSubcategory,
        E.obj C ◁ (Functor.LaxMonoidal.ihomComparison E C).natTrans.app H ≫
            (ihom.ev (E.obj C)).app (E.obj H) =
          Functor.LaxMonoidal.μ E C ((ihom C).obj H) ≫ E.map ((ihom.ev C).app H)) ∧
      (∀ C : (CondensedGeometricPoint.ctf Λ D.k).FullSubcategory,
        Nonempty (E.obj ((ihom C).obj (𝟙_ _)) ≅
          (ihom (E.obj C)).obj (𝟙_ _))) ∧
      (∀ C H : (CondensedGeometricPoint.ctf Λ D.k).FullSubcategory,
        TraceCupPoint.tensor Λ D.k C.obj H.obj ≫
            (pointEvaluationCTFComparison D Λ).hom.app (C ⊗ H) =
          ((pointEvaluationCTFComparison D Λ).hom.app C ⊗ₘ
            (pointEvaluationCTFComparison D Λ).hom.app H) ≫
            Functor.LaxMonoidal.μ G (E.obj C).obj (E.obj H).obj ≫
            G.map ((Functor.LaxMonoidal.μ E C H).hom)) ∧
      (pointCoefficientUnit Λ D.k ≫
          (pointEvaluationCTFComparison D Λ).hom.app (𝟙_ _) =
        Functor.LaxMonoidal.ε G ≫ G.map (Functor.LaxMonoidal.ε E).hom)

/-- The degree-zero coefficient module used in the line specialization.
Source: node proof Step 8, over Steps 1 and 3 of the cited Frobenius proof.
(blueprint: lem-pod-condensed-point-sections-transport). -/
abbrev pointLineSections
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : pointDerived D Λ) : ModuleCat.{u + 1} (MonObj.Γ Λ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0).obj
    ((scalarSections D Λ).obj L)

/-- The canonical identification of a degree-zero line with a single module.
It is built from the given trivialization, the exact normalized unit comparison, and
the single-complex/homology comparison; hence it does not choose an arbitrary map.
Source: node proof Step 8, over Steps 1 and 3 of the cited Frobenius proof.
(blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointLineSingleIso
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : pointDerived D Λ)
    (hL : L ≅ MonoidalCategoryStruct.tensorUnit (pointDerived D Λ)) :
    (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0).obj
        (pointLineSections D Λ L) ≅ (scalarSections D Λ).obj L := by
  let F := condensedRingCoefficientSections Λ (Spec (.of D.k))
  let U := MonoidalCategoryStruct.tensorUnit (pointModules D Λ)
  let eBsingle : (scalarSections D Λ).obj L ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0).obj (F.obj U) :=
    (scalarSections D Λ).mapIso
        (hL ≪≫ (DerivedCategory.singleFunctorObjUnitIso
          (pointModules D Λ)).symm) ≪≫
      (TraceCupPoint.exactComparison Λ D.k).app
        ((DerivedCategory.singleFunctor (pointModules D Λ) 0).obj U) ≪≫
      (F.mapDerivedCategorySingleFunctor 0).app U
  let vIso : pointLineSections D Λ L ≅
      F.obj U :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0).mapIso eBsingle ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0).app (F.obj U)
  exact (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0).mapIso vIso ≪≫
    eBsingle.symm

/-- The canonical degree-`j` cross-product, defined by the cycle-level coefficient map
and then the normalized derived sections tensor. Its source is `H^j(Fib C) ⊗ V`, where
`V = H^0(Fib L)`, rather than `H^j(Fib L)`.
Source: node proof Step 9, over Steps 1 and 3 of the cited Frobenius proof.
(blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointCohomologyCrossProduct
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : pointDerived D Λ)
    (hL : L ≅ MonoidalCategoryStruct.tensorUnit (pointDerived D Λ))
    (C : pointDerived D Λ) (j : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) j).obj
        ((scalarSections D Λ).obj C) ⊗ pointLineSections D Λ L ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) j).obj
        ((scalarSections D Λ).obj (MonoidalCategoryStruct.tensorObj C L)) := by
  let R := MonObj.Γ Λ
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) j
  let A := (scalarSections D Λ).obj C
  let V := pointLineSections D Λ L
  let e := pointLineSingleIso D Λ L hL
  exact AlgebraicGeometry.Etale.canonicalCoefficientMap R A V j ≫
    H.map (((curriedTensor (DerivedCategory (ModuleCat.{u + 1} R))).obj A).map e.hom) ≫
    H.map (show
      ((curriedTensor (DerivedCategory (ModuleCat.{u + 1} R))).obj A).obj
          ((scalarSections D Λ).obj L) ⟶
        (scalarSections D Λ).obj (MonoidalCategoryStruct.tensorObj C L) from
      TraceCupPoint.tensor Λ D.k C L)

/-- Canonical sectionwise restriction before the native localization comparison.
Source: the normalized insertion comparison in `CohomologyTransport`.
(blueprint: lem-pod-condensed-point-sections-transport). -/
noncomputable def pointRhoSectionwise (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    TraceCupPoint.fiber Λ D.k ≅
      pointAction D Λ ⋙ TraceCupPoint.fiber Λ D.k := by
  letI : HasDerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (pointScheme D)) Ab.{u + 1})
        (condensedRingObj Λ (pointScheme D))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _
  exact
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ (pointGeometricFrobenius D).hom ≪≫
      Functor.mapDerivedCategoryNatIso
        (upperStarIsoIdOfIsSepClosed Λ (pointGeometricFrobenius D).hom) ≪≫
      Functor.mapDerivedCategoryIdIso _).symm) _

/-- The complete point-section transport data. The fields are maps and equations, so the
statement records the canonical maps rather than an unconstrained existence assertion.
Source: Steps 1 and 3 of the cited Frobenius proof
(blueprint: lem-pod-condensed-point-sections-transport).

Proof steps represented by the fields: (1) exact point sections and the normalized cup;
(2) sectionwise inverse-image restriction and its inverse; (3) scalar normalization;
(4) tensor-cup compatibility; (5) K-flat descent to derived objects; (6) strict
intertwining; (7) shifts and perfect evaluation; (8) the degree-zero line; (9) degreewise
Frobenius and independence of the temporary trivialization (`cross_product_independent`
says that the cross-product map, built with the temporary `h`, does not depend on it).
-/
structure PointSectionsTransportData
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsAdmissibleCoefficient Λ) where
  /-- The Frobenius restriction is the component of the published insertion iso. -/
  rho : ∀ C : pointDerived D Λ,
    (scalarSections D Λ).obj C ≅ (scalarSections D Λ).obj ((pointAction D Λ).obj C)
  rho_canonical : ∀ C : pointDerived D Λ,
    rho C = (pointRhoSectionwise D Λ).app C
  rho_inverse : ∀ C : pointDerived D Λ,
    (rho C).hom ≫ (rho C).inv = 𝟙 _ ∧ (rho C).inv ≫ (rho C).hom = 𝟙 _
  rho_natural : ∀ {C E : pointDerived D Λ} (f : C ⟶ E),
    (scalarSections D Λ).map f ≫ (rho E).hom =
      (rho C).hom ≫ (scalarSections D Λ).map ((pointAction D Λ).map f)
  rho_linear : ∀ (C : pointDerived D Λ) (n : ℤ),
    (scalarSections D Λ).map (n • 𝟙 C) ≫ (rho C).hom =
      (rho C).hom ≫ (scalarSections D Λ).map (n • 𝟙 ((pointAction D Λ).obj C))
  cup_transport : ∀ C E : pointDerived D Λ,
    TraceCupPoint.tensor Λ D.k C E ≫
          (rho (MonoidalCategoryStruct.tensorObj C E)).hom ≫
          (scalarSections D Λ).map (pointDelta D Λ C E).hom =
      MonoidalCategory.tensorHom (rho C).hom (rho E).hom ≫
        TraceCupPoint.tensor Λ D.k ((pointAction D Λ).obj C)
          ((pointAction D Λ).obj E)
  cup_isIso : ∀ C E : pointDerived D Λ,
    IsIso (TraceCupPoint.tensor Λ D.k C E)
  coefficient_unit :
    (rho (MonoidalCategoryStruct.tensorUnit (pointDerived D Λ))).hom ≫
        (scalarSections D Λ).map (pointFrobeniusCoefficientUnit D Λ).hom = 𝟙 _
  strict_intertwining : ∀ (C D' E : pointDerived D Λ)
      (φC : (pointAction D Λ).obj C ≅ C)
      (φD : (pointAction D Λ).obj D' ≅ D')
      (φE : (pointAction D Λ).obj E ≅ E)
      (u : MonoidalCategoryStruct.tensorObj C D' ⟶ E),
      (pointDelta D Λ C D').hom ≫ (φC.hom ⊗ₘ φD.hom) ≫ u =
        (pointAction D Λ).map u ≫ φE.hom →
      (TraceCupPoint.tensor Λ D.k C D' ≫ (scalarSections D Λ).map u) ≫
          (rho E).hom ≫ (scalarSections D Λ).map φE.hom =
        MonoidalCategory.tensorHom
            ((rho C).hom ≫ (scalarSections D Λ).map φC.hom)
            ((rho D').hom ≫ (scalarSections D Λ).map φD.hom) ≫
          TraceCupPoint.tensor Λ D.k C D' ≫ (scalarSections D Λ).map u
  strict_intertwining_shifted : ∀ (n : ℤ) {C D' E : pointDerived D Λ}
      (φC : (pointAction D Λ).obj ((shiftFunctor (pointDerived D Λ) n).obj C) ≅
        (shiftFunctor (pointDerived D Λ) n).obj C)
      (φD : (pointAction D Λ).obj D' ≅ D')
      (φE : (pointAction D Λ).obj ((shiftFunctor (pointDerived D Λ) n).obj E) ≅
        (shiftFunctor (pointDerived D Λ) n).obj E)
      (u : MonoidalCategoryStruct.tensorObj
        ((shiftFunctor (pointDerived D Λ) n).obj C) D' ⟶
          (shiftFunctor (pointDerived D Λ) n).obj E),
      (pointDelta D Λ ((shiftFunctor (pointDerived D Λ) n).obj C) D').hom ≫
          (φC.hom ⊗ₘ φD.hom) ≫ u =
        (pointAction D Λ).map u ≫ φE.hom →
      (TraceCupPoint.tensor Λ D.k ((shiftFunctor (pointDerived D Λ) n).obj C) D' ≫
          (scalarSections D Λ).map u) ≫
          (rho ((shiftFunctor (pointDerived D Λ) n).obj E)).hom ≫
            (scalarSections D Λ).map φE.hom =
        MonoidalCategory.tensorHom
            ((rho ((shiftFunctor (pointDerived D Λ) n).obj C)).hom ≫
              (scalarSections D Λ).map φC.hom)
            ((rho D').hom ≫ (scalarSections D Λ).map φD.hom) ≫
          TraceCupPoint.tensor Λ D.k ((shiftFunctor (pointDerived D Λ) n).obj C) D' ≫
            (scalarSections D Λ).map u
  perfect_evaluation :
    CondensedGeometricPoint.Statement Λ D.k ∧
      Nonempty (PointEvaluationAgreement D Λ)
  rank_one : ∀ (L : pointModules D Λ)
      (hL : L ≅ MonoidalCategoryStruct.tensorUnit (pointModules D Λ)),
      ∃ V : ModuleCat (condensedScalarRing Λ),
        Module.Free (condensedScalarRing Λ) V ∧
          Nonempty (Module.Basis (Fin 1) (condensedScalarRing Λ) V) ∧
          Nonempty ((CohomologyTransport.sections Λ (pointScheme D)).obj L ≅ V)
  rank_one_frobenius : ∀ (L : pointDerived D Λ)
      (hL : L ≅ MonoidalCategoryStruct.tensorUnit (pointDerived D Λ)),
      ∀ (φL : (pointAction D Λ).obj L ≅ L),
        φL.hom ≫ hL.hom =
            (pointAction D Λ).map hL.hom ≫ (pointFrobeniusCoefficientUnit D Λ).hom →
        (scalarSections D Λ).map hL.hom ≫
            ((rho (MonoidalCategoryStruct.tensorUnit (pointDerived D Λ))).hom ≫
              (scalarSections D Λ).map (pointFrobeniusCoefficientUnit D Λ).hom) =
          ((rho L).hom ≫ (scalarSections D Λ).map φL.hom) ≫
            (scalarSections D Λ).map hL.hom
  rank_one_cohomology : ∀ (L : pointDerived D Λ)
      (hL : L ≅ MonoidalCategoryStruct.tensorUnit (pointDerived D Λ))
      (j : ℤ),
      ∀ (φL : (pointAction D Λ).obj L ≅ L),
        φL.hom ≫ hL.hom =
            (pointAction D Λ).map hL.hom ≫ (pointFrobeniusCoefficientUnit D Λ).hom →
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) j).map
            ((scalarSections D Λ).map hL.hom) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) j).map
              ((rho (MonoidalCategoryStruct.tensorUnit (pointDerived D Λ))).hom ≫
                (scalarSections D Λ).map (pointFrobeniusCoefficientUnit D Λ).hom) =
          (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) j).map
            ((rho L).hom ≫ (scalarSections D Λ).map φL.hom) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) j).map
              ((scalarSections D Λ).map hL.hom)
  cohomology_cross_product : ∀ (L : pointDerived D Λ)
      (hL : L ≅ MonoidalCategoryStruct.tensorUnit (pointDerived D Λ))
      (C : pointDerived D Λ) (j : ℤ),
      ∀ (φC : (pointAction D Λ).obj C ≅ C)
        (φL : (pointAction D Λ).obj L ≅ L),
        IsIso (pointCohomologyCrossProduct D Λ L hL C j) ∧
          (pointCohomologyCrossProduct D Λ L hL C j) ≫
              (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) j).map
                ((rho (MonoidalCategoryStruct.tensorObj C L)).hom ≫
                  (scalarSections D Λ).map
                    ((pointDelta D Λ C L ≪≫ tensorIso φC φL).hom)) =
              MonoidalCategory.tensorHom
                  ((DerivedCategory.homologyFunctor
                    (ModuleCat.{u + 1} (MonObj.Γ Λ)) j).map
                    ((rho C).hom ≫ (scalarSections D Λ).map φC.hom))
                  ((DerivedCategory.homologyFunctor
                    (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0).map
                    ((rho L).hom ≫ (scalarSections D Λ).map φL.hom)) ≫
              pointCohomologyCrossProduct D Λ L hL C j
  trivialization_independent : ∀ (L : pointDerived D Λ)
      (h h' : L ≅ MonoidalCategoryStruct.tensorUnit (pointDerived D Λ)),
      ∀ (φ : (pointAction D Λ).obj L ≅ L),
        (scalarSections D Λ).map h.inv ≫
            ((rho L).hom ≫ (scalarSections D Λ).map φ.hom) ≫
            (scalarSections D Λ).map h.hom =
          (scalarSections D Λ).map h'.inv ≫
            ((rho L).hom ≫ (scalarSections D Λ).map φ.hom) ≫
            (scalarSections D Λ).map h'.hom
  cross_product_independent : ∀ (L : pointDerived D Λ)
      (h h' : L ≅ MonoidalCategoryStruct.tensorUnit (pointDerived D Λ))
      (C : pointDerived D Λ) (j : ℤ),
      pointCohomologyCrossProduct D Λ L h C j = pointCohomologyCrossProduct D Λ L h' C j

private theorem point_rho_hom
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (C : pointDerived D Λ) :
    ((pointRhoSectionwise D Λ).app C).hom =
      (scalarSections D Λ).map ((pointActionTrivialization D Λ).app C).inv := by
  change 𝟙 _ ≫ (scalarSections D Λ).map
    ((pointActionTrivialization D Λ).app C).inv = _
  exact Category.id_comp _

private def point_actual_ordinary_unit_iso
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (CohomologyTransport.sections Λ (pointScheme D)).obj (𝟙_ (pointModules D Λ)) ≅
      ModuleCat.of (condensedScalarRing Λ) (condensedScalarRing Λ) := by
  let S := CohomologyTransport.scalarMap Λ (pointScheme D)
  have hb : Function.Bijective S := by
    letI := Functor.additive_of_preserves_binary_products (upperStarFromPoint (pointScheme D))
    exact (InternalAbelianSheafModule.sectionGlobalEval_bijective
      (Scheme.ProEt.topology (pointScheme D)) (condensedRingObj Λ (pointScheme D))
      (Scheme.ProEt.mk (𝟙 (pointScheme D)))
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale (pointScheme D))).comp
      ((InternalAbelianSheafModule.globalMapFunctor_bijective
        (upperStarFromPoint (pointScheme D)) (Functor.FullyFaithful.ofFullyFaithful _) Λ).comp
        (InternalAbelianSheafModule.sectionGlobalEquiv (coherentTopology Profinite.{u}) Λ
          (⊤_ Profinite.{u}) terminalIsTerminal).symm.bijective)
  let e := RingEquiv.ofBijective S hb
  exact ModuleCat.restrictScalarsIsoOfEquiv e

private def point_ordinary_unit_iso
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (condensedRingCoefficientSections Λ (pointScheme D)).obj (𝟙_ (pointModules D Λ)) ≅
      ModuleCat.of (MonObj.Γ Λ) (MonObj.Γ Λ) := by
  let R := MonObj.Γ Λ
  let G := condensedRingCoefficientSections Λ (pointScheme D)
  let U := 𝟙_ (pointModules D Λ)
  let s := condensedRingScalarSections Λ (pointScheme D)
  have hb : Function.Bijective s := by
    letI := Functor.additive_of_preserves_binary_products (upperStarFromPoint (pointScheme D))
    exact InternalAbelianSheafModule.globalMapFunctor_bijective
      (upperStarFromPoint (pointScheme D)) (Functor.FullyFaithful.ofFullyFaithful _) Λ
  let f : R →ₗ[R] G.obj U := LinearMap.toSpanSingleton R (G.obj U) (𝟙 U)
  have hf : Function.Bijective f := by
    have he : (fun a ↦ f a) = fun a ↦ Mod.regularEndRingHom (s a) := by
      funext a
      change Mod.regularEndRingHom (s a) ≫ 𝟙 U = _
      exact Category.comp_id _
    change Function.Bijective (fun a ↦ f a)
    rw [he]
    exact Mod.regularEndRingHom_bijective.comp hb
  exact (LinearEquiv.toModuleIso (LinearEquiv.ofBijective f hf)).symm

private def point_line_module_iso
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : pointDerived D Λ) (hL : L ≅ 𝟙_ (pointDerived D Λ)) :
    pointLineSections D Λ L ≅ ModuleCat.of (MonObj.Γ Λ) (MonObj.Γ Λ) := by
  let F := condensedRingCoefficientSections Λ (pointScheme D)
  let U := 𝟙_ (pointModules D Λ)
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0).mapIso
      ((scalarSections D Λ).mapIso
          (hL ≪≫ (DerivedCategory.singleFunctorObjUnitIso (pointModules D Λ)).symm) ≪≫
        (TraceCupPoint.exactComparison Λ D.k).app
          ((DerivedCategory.singleFunctor (pointModules D Λ) 0).obj U) ≪≫
        (F.mapDerivedCategorySingleFunctor 0).app U) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0).app (F.obj U) ≪≫ point_ordinary_unit_iso D Λ

private theorem point_cup_natural
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {C C' E E' : pointDerived D Λ} (f : C ⟶ C') (g : E ⟶ E') :
    ((scalarSections D Λ).map f ⊗ₘ (scalarSections D Λ).map g) ≫
        TraceCupPoint.tensor Λ D.k C' E' =
      TraceCupPoint.tensor Λ D.k C E ≫ (scalarSections D Λ).map (f ⊗ₘ g) := by
  let F := condensedRingCoefficientSections Λ (pointScheme D)
  letI : F.mapDerivedCategory.LaxMonoidal := (TraceCupPoint.tensorData Λ D.k).derived
  unfold TraceCupPoint.tensor TraceCupPoint.exactTensor
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc,
    (TraceCupPoint.exactComparison Λ D.k).hom.naturality f,
    (TraceCupPoint.exactComparison Λ D.k).hom.naturality g,
    ← tensorHom_comp_tensorHom_assoc,
    Functor.LaxMonoidal.μ_natural_assoc,
    (TraceCupPoint.exactComparison Λ D.k).inv.naturality]

private theorem line_single_independent
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : pointDerived D Λ) (h h' : L ≅ 𝟙_ (pointDerived D Λ)) :
    (pointLineSingleIso D Λ L h).hom = (pointLineSingleIso D Λ L h').hom := by
  let F := condensedRingCoefficientSections Λ (pointScheme D)
  let U := 𝟙_ (pointModules D Λ)
  let a (h : L ≅ 𝟙_ (pointDerived D Λ)) :=
    (scalarSections D Λ).mapIso
        (h ≪≫ (DerivedCategory.singleFunctorObjUnitIso (pointModules D Λ)).symm) ≪≫
      (TraceCupPoint.exactComparison Λ D.k).app
        ((DerivedCategory.singleFunctor (pointModules D Λ) 0).obj U) ≪≫
      (F.mapDerivedCategorySingleFunctor 0).app U
  exact single_realization_independent
    (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0)
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0)
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0) (a h) (a h')

private theorem line_single_natural
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : pointDerived D Λ) (h : L ≅ 𝟙_ (pointDerived D Λ))
    (f : (scalarSections D Λ).obj L ⟶ (scalarSections D Λ).obj L) :
    (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0).map f) ≫
        (pointLineSingleIso D Λ L h).hom =
      (pointLineSingleIso D Λ L h).hom ≫ f := by
  let F := condensedRingCoefficientSections Λ (pointScheme D)
  let U := 𝟙_ (pointModules D Λ)
  let a := (scalarSections D Λ).mapIso
        (h ≪≫ (DerivedCategory.singleFunctorObjUnitIso (pointModules D Λ)).symm) ≪≫
      (TraceCupPoint.exactComparison Λ D.k).app
        ((DerivedCategory.singleFunctor (pointModules D Λ) 0).obj U) ≪≫
      (F.mapDerivedCategorySingleFunctor 0).app U
  exact single_realization_naturality
    (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0)
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0)
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u + 1} (MonObj.Γ Λ)) 0) a a f

/-- Point sections transport, cup compatibility and degreewise Frobenius.
Source: Steps 1 and 3 of the cited Frobenius proof
(blueprint: lem-pod-condensed-point-sections-transport).

The proof follows the nine steps documented in `PointSectionsTransportData`: exact sections;
sectionwise inverse-image restriction; scalar-unit normalization; chain-level tensor cup;
K-flat descent; strict intertwining; shifts and perfect evaluation; the rank-one line; and
cohomology operators with trivialization independence.
(blueprint: lem-pod-condensed-point-sections-transport). -/
theorem point_sections_transport
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsAdmissibleCoefficient Λ) :
    Nonempty (PointSectionsTransportData D ell Λ hΛ) := by
  let ρ := pointRhoSectionwise D Λ
  have hnat {C E : pointDerived D Λ} (f : C ⟶ E) :
      (scalarSections D Λ).map f ≫ (ρ.app E).hom =
        (ρ.app C).hom ≫ (scalarSections D Λ).map ((pointAction D Λ).map f) :=
    ρ.hom.naturality f
  let τ := pointActionTrivialization D Λ
  have hrho (C : pointDerived D Λ) :
      (ρ.app C).hom = (scalarSections D Λ).map (τ.app C).inv := point_rho_hom D Λ C
  letI : (pointAction D Λ).Monoidal :=
    Functor.Monoidal.transport
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (pointGeometricFrobenius D).hom).symm
  letI : NatTrans.IsMonoidal τ.hom := point_action_trivialization_monoidal D Λ
  have hdelta (C E : pointDerived D Λ) :
      (τ.app (C ⊗ E)).inv ≫ (pointDelta D Λ C E).hom =
        ((τ.app C).inv ⊗ₘ (τ.app E).inv) := by
    have ht := NatTrans.IsMonoidal.tensor (τ := τ.inv) C E
    simpa only [Functor.LaxMonoidal.id_μ, Category.id_comp, pointDelta,
      Iso.symm_hom, Functor.Monoidal.μIso_inv, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id, Iso.app_inv] using
      congrArg (fun t ↦ t ≫ (pointDelta D Λ C E).hom) ht
  have hcup (C E : pointDerived D Λ) :
      TraceCupPoint.tensor Λ D.k C E ≫ (ρ.app (C ⊗ E)).hom ≫
          (scalarSections D Λ).map (pointDelta D Λ C E).hom =
        ((ρ.app C).hom ⊗ₘ (ρ.app E).hom) ≫
          TraceCupPoint.tensor Λ D.k ((pointAction D Λ).obj C) ((pointAction D Λ).obj E) := by
    rw [hrho, ← Functor.map_comp, hdelta, ← point_cup_natural, hrho, hrho]
  have hstrict := realized_tensor_intertwining (pointAction D Λ) (scalarSections D Λ)
    (TraceCupPoint.tensor Λ D.k) (point_cup_natural D Λ) ρ.hom
    (fun C E ↦ (pointDelta D Λ C E).hom) hcup
  have hline (L : pointDerived D Λ)
      (hL : L ≅ MonoidalCategoryStruct.tensorUnit (pointDerived D Λ))
      (φL : (pointAction D Λ).obj L ≅ L)
      (hφ : φL.hom ≫ hL.hom =
        (pointAction D Λ).map hL.hom ≫ (pointFrobeniusCoefficientUnit D Λ).hom) :
      (scalarSections D Λ).map hL.hom ≫
          ((ρ.app (MonoidalCategoryStruct.tensorUnit (pointDerived D Λ))).hom ≫
            (scalarSections D Λ).map (pointFrobeniusCoefficientUnit D Λ).hom) =
        ((ρ.app L).hom ≫ (scalarSections D Λ).map φL.hom) ≫
          (scalarSections D Λ).map hL.hom := by
    rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp, ← hφ,
      Functor.map_comp, Category.assoc]
  refine ⟨{
    rho := fun C ↦ ρ.app C
    rho_canonical := fun _ ↦ rfl
    rho_inverse := fun C ↦ ⟨(ρ.app C).hom_inv_id, (ρ.app C).inv_hom_id⟩
    rho_natural := fun f ↦ hnat f
    rho_linear := ?_
    cup_transport := hcup
    cup_isIso := fun C E ↦ TraceCupPoint.tensor_isIso Λ D.k C E
    coefficient_unit := ?_
    strict_intertwining := fun C E H φC φE φH v hv ↦
      hstrict C E H φC.hom φE.hom φH.hom v hv
    strict_intertwining_shifted := fun n {C E H} φC φE φH v hv ↦
      hstrict _ _ _ φC.hom φE.hom φH.hom v hv
    perfect_evaluation := ?_
    rank_one := ?_
    rank_one_frobenius := hline
    rank_one_cohomology := ?_
    cohomology_cross_product := ?_
    trivialization_independent := ?_
    cross_product_independent := ?_ }⟩
  · intro C n
    simp only [Functor.map_zsmul, CategoryTheory.Functor.map_id, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Category.id_comp, Category.comp_id]
  · have hu := NatTrans.IsMonoidal.unit (τ := τ.inv)
    have he : (τ.app (𝟙_ (pointDerived D Λ))).inv ≫
        (pointFrobeniusCoefficientUnit D Λ).hom = 𝟙 (𝟙_ (pointDerived D Λ)) := by
      simpa only [Functor.LaxMonoidal.id_ε, Category.id_comp, pointFrobeniusCoefficientUnit,
        Iso.symm_hom, Functor.Monoidal.εIso_inv, Category.assoc,
        Functor.Monoidal.ε_η, Category.comp_id, Iso.app_inv] using
        congrArg (fun t ↦ t ≫ (pointFrobeniusCoefficientUnit D Λ).hom) hu
    rw [hrho, ← Functor.map_comp, he]
    simp
  · letI : Fintype D.k₀ := Fintype.ofFinite _
    letI : Fact D.p.Prime := ⟨D.prime⟩
    letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    exact ⟨CondensedGeometricPoint.condensed_geometric_point_perfect_general
      Λ D.k ell D.p hell.symm hΛ, point_perfect_evaluation_agreement D ell hell Λ hΛ⟩
  · intro L hL
    refine ⟨ModuleCat.of (condensedScalarRing Λ) (condensedScalarRing Λ),
      inferInstance, ⟨Module.Basis.singleton (Fin 1) (condensedScalarRing Λ)⟩, ?_⟩
    exact ⟨(CohomologyTransport.sections Λ (pointScheme D)).mapIso hL ≪≫
      point_actual_ordinary_unit_iso D Λ⟩
  · intro L hL j φL hφ
    simpa only [Functor.map_comp] using
      congrArg ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (MonObj.Γ Λ)) j).map) (hline L hL φL hφ)
  · intro L hL C j φC φL
    let R := MonObj.Γ Λ
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) j
    let A := (scalarSections D Λ).obj C
    let V := pointLineSections D Λ L
    let e := pointLineSingleIso D Λ L hL
    let f := (ρ.app C).hom ≫ (scalarSections D Λ).map φC.hom
    let g := (ρ.app L).hom ≫ (scalarSections D Λ).map φL.hom
    let k := (ρ.app (C ⊗ L)).hom ≫
      (scalarSections D Λ).map ((pointDelta D Λ C L ≪≫ tensorIso φC φL).hom)
    have ht : TraceCupPoint.tensor Λ D.k C L ≫ k =
        (f ⊗ₘ g) ≫ TraceCupPoint.tensor Λ D.k C L := by
      dsimp only [k, f, g]
      simp only [Iso.trans_hom, tensorIso_hom, Functor.map_comp, Category.assoc]
      rw [reassoc_of% hcup C L]
      rw [← point_cup_natural D Λ φC.hom φL.hom]
      simp only [tensorHom_comp_tensorHom_assoc]
    have hn := line_cross_product_naturality R e e f g
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) 0).map g)
      (line_single_natural D Λ L hL g) j
    constructor
    · haveI := line_coefficient_map_isIso R A V (point_line_module_iso D Λ L hL) j
      haveI := TraceCupPoint.tensor_isIso Λ D.k C L
      dsimp only [pointCohomologyCrossProduct]
      infer_instance
    · change pointCohomologyCrossProduct D Λ L hL C j ≫ H.map k =
        (H.map f ⊗ₘ
          (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) 0).map g) ≫
          pointCohomologyCrossProduct D Λ L hL C j
      unfold pointCohomologyCrossProduct
      change (Etale.canonicalCoefficientMap R A V j ≫
        H.map (A ◁ e.hom) ≫ H.map (TraceCupPoint.tensor Λ D.k C L)) ≫ H.map k = _
      rw [Category.assoc, Category.assoc, ← H.map_comp, ht, H.map_comp]
      simpa only [Category.assoc, curriedTensor_obj_map] using
        (congrArg (fun t ↦ t ≫ H.map (TraceCupPoint.tensor Λ D.k C L)) hn).symm
  · intro L h h' φ
    simp only [hrho, ← Functor.map_comp]
    exact congrArg (scalarSections D Λ).map
      (point_line_conjugation_independent ((τ.app L).inv ≫ φ.hom) h h')
  · intro L h h' C j
    have hh := line_single_independent D Λ L h h'
    simp only [pointCohomologyCrossProduct, hh]

end AlgebraicGeometry.ProEtale.CondensedRing
