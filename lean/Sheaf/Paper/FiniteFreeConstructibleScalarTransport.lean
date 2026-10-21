/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.FiniteFreeCoefficientTransport
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Mathlib.RingTheory.TensorProduct.Finite
import Sheaf.Paper.CompletedConstantSheafReduction
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import all Sheaf.Paper.CompletedAdicCoefficientDatum
import all Sheaf.Paper.AdicCoefficientDatumCompleted
import Sheaf.Paper.IntegralPadicLocalPerfectCriterion
import Sheaf.CategoryTheory.ConstantModuleFlat
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.RingIsomorphismTensorTransport

/-!
# Finite-free transport of integral constructible local models

Source: blueprint main-20261015, prop-weil-pbc-scalar-extension, exactness clause;
Bhatt--Scholze, Proposition 6.6.11; Stacks Tags 05CF, 08H3 and 03EL
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport).

The coefficient rings are the actual valuation rings. Every auxiliary comparison is
fixed by quotient projections, tensor sections, or the published derived counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
-- Avoid underdetermined max-universe instances from the auxiliary operations framework.
-- The fixed-size PBC instances still provide the same canonical structures.
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

private local instance fixedSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0} _

private noncomputable local instance fixedSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} T

private local instance fixedLocallyBijective (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T

variable (l : ℕ) [Fact l.Prime]
  (E F : Type (u + 1)) [Field E] [Field F]
  [Algebra (Padic l) E] [Algebra (Padic l) F]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
  (i : E →ₐ[Padic l] F)

/-- The existing algebraic extension functor, in the coefficient universe.
Source: Stacks 05CF; blueprint scalar-extension local formula
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
abbrev finiteFreeCoefficientExtension :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) ⥤
      ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l F) :=
  ModuleCat.extendScalars (WeilConjectures.integralScalarIntegerInclusion l E F i)

/-- Additivity inherited from the existing extension/restriction adjunction.
Source: Stacks 05CF; blueprint scalar-extension local formula
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
instance finiteFreeCoefficientExtension_additive :
    (finiteFreeCoefficientExtension l E F i).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (WeilConjectures.integralScalarIntegerInclusion l E F i)).left_adjoint_additive

/-- The literal termwise B tensor_A P, with differential 1 tensor d_P.
Source: Stacks 05CF; blueprint scalar-extension local formula
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
abbrev finiteFreeCoefficientComplex :=
  (finiteFreeCoefficientExtension l E F i).mapHomologicalComplex (.up ℤ)

private theorem coefficientComplex_bounds
    (P : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b] :
    CochainComplex.IsStrictlyGE ((finiteFreeCoefficientComplex l E F i).obj P) a ∧
      CochainComplex.IsStrictlyLE ((finiteFreeCoefficientComplex l E F i).obj P) b := by
  constructor <;> infer_instance

private theorem coefficientComplex_terms
    (P : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (hP : ∀ q : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l E) (P.X q) ∧
      Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X q)) (q : ℤ) :
    Module.Projective (Padic.coefficientExtensionIntegers l F)
        (((finiteFreeCoefficientComplex l E F i).obj P).X q) ∧
      Module.Finite (Padic.coefficientExtensionIntegers l F)
        (((finiteFreeCoefficientComplex l E F i).obj P).X q) := by
  let φ := WeilConjectures.integralScalarIntegerInclusion l E F i
  let := φ.toAlgebra
  have := (hP q).1
  have := (hP q).2
  change Module.Projective (Padic.coefficientExtensionIntegers l F)
      (TensorProduct (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionIntegers l F) (P.X q)) ∧
    Module.Finite (Padic.coefficientExtensionIntegers l F)
      (TensorProduct (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionIntegers l F) (P.X q))
  constructor <;> infer_instance

private theorem realization_kflat (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (b : ℤ) [P.IsStrictlyLE b]
    (hP : ∀ q : ℤ, Module.Projective A (P.X q)) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} (R := pbcAdicCompletion T d)
      (((integralConstantModule T d).mapHomologicalComplex (.up ℤ)).obj P) := by
  let pd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let := CompletedConstantReduction.constant_additive T A
  let C := ((adicLisseConstantModules T A).mapHomologicalComplex (.up ℤ)).obj P
  have : CochainComplex.IsStrictlyLE C b := by dsimp [C]; infer_instance
  have hflat (q : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := adicLisseConstantRing T A) (C.X q) := by
    have := hP q
    exact isFlatOnSite_constantModule.{u + 1, u} (ProEt.topology T) A (P.X q) inferInstance
  have hc : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := adicLisseConstantRing T A) C :=
    SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite.{u + 1, u, u + 1}
      (adicLisseConstantRing T A) C b hflat
  let φ := adicDatumScalar T pd
  let D := ((completedConstantExtension T φ).mapHomologicalComplex (.up ℤ)).obj C
  have hd : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := adicDatumRing T pd) D :=
    adicDatumExtension_kflat T φ C hc
  let c := (pbcCompletedComparison T d).symm
  let := HasDerivedCategory.standard (pbcModules T (pbcAdicCompletion T d))
  let := HasDerivedCategory.standard (completedConstantModules T (adicDatumRing T pd))
  let trans := (SheafOfModules.ringIso_tensor_transport.{u + 1, u, u + 1,
    u + 2, u + 2} c).some
  exact (trans.kflat_iff D).2 hd

/-- A pure section r tensor p in the published completed constant realization.
Source: Bhatt--Scholze 6.6.11; Stacks 03EK
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
def finiteFreeConstantTensor (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (N : ModuleCat.{u + 1} A) (U : T.ProEtᵒᵖ)
    (r : (pbcAdicCompletion T d).obj.obj U) (p : N) :
    ((integralConstantModule T d).obj N).val.obj U :=
  adicDatumTensorSection T
    (adicDatumScalar T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
        quotientFinite := d.quotientFinite })
    ((adicLisseConstantModules T A).obj N) U
    ((pbcCompletedComparison T d).inv.hom.app U r)
    (completedConstantGenerator T A N U p)

private theorem scalar_projection (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    pbcCompletedScalar T d ≫ pbcAdicProjection T d n =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
        (pbcLevelConstantComparison T d n).hom := by
  dsimp only [pbcCompletedScalar, pbcAdicProjection, pbcCompletedComparison]
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc]
  change (adicDatumScalar T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite } ≫ _) ≫ _ = _
  congr 1
  exact (adicDatumScalar_exists T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite }).exists.choose_spec n


private theorem level_comparison (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (pbcLevelConstantComparison T d n).hom =
      @AdicCoefficients.constantComparison T (A ⧸ d.ideal ^ (n + 1)) _
        (d.quotientFinite n) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings T d).obj (op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison T d n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists T d n).exists.choose_spec U b

private theorem finiteFree_scalar_square
    (l : ℕ) [Fact l.Prime] (E F : Type (u + 1)) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) (T : Scheme.{u}) :
    pbcCompletedScalar T (pbcPadicCoefficientDatum l E) ≫
        finiteFreeCompletedCoefficientMap l E F i T =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (WeilConjectures.integralScalarIntegerInclusion l E F i)) ≫
        pbcCompletedScalar T (pbcPadicCoefficientDatum l F) := by
  apply limit.hom_ext
  intro n
  change _ ≫ pbcAdicProjection T (pbcPadicCoefficientDatum l F) n.unop =
    _ ≫ pbcAdicProjection T (pbcPadicCoefficientDatum l F) n.unop
  have hc := (finiteFreeCompletedCoefficientMap_existsUnique l E F i T).exists.choose_spec n.unop
  change finiteFreeCompletedCoefficientMap l E F i T ≫ _ = _ at hc
  rw [Category.assoc, hc,
    ← Category.assoc, scalar_projection, Category.assoc, Category.assoc, scalar_projection,
    level_comparison, level_comparison]
  simp only [AdicCoefficients.constantComparison, AdicCoefficients.coefficientMap,
    constantSheaf, Functor.comp_map, ← Functor.map_comp]
  congr 1


private def constantPF (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))

private def constantPresheafHomEquiv (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) (M : ModuleCat.{u + 1} A)
    (F : _root_.PresheafOfModules.{u + 1} ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))) :
    ((constantPF X A).obj M ⟶ F) ≃ (M ⟶ F.obj (op T)) where
  toFun f := f.app (op T)
  invFun q :=
    { app U := q ≫ F.map (hT.from U.unop).op
      naturality := by
        intro U V a
        ext x
        symm
        change F.map a (F.map (hT.from U.unop).op (q x)) =
          F.map (hT.from V.unop).op (q x)
        rw [← F.map_comp_apply]
        have h : (hT.from U.unop).op ≫ a = (hT.from V.unop).op := by
          exact congrArg Quiver.Hom.op (hT.hom_ext _ _)
        rw [h] }
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact (PresheafOfModules.naturality_apply f (hT.from U.unop).op x).symm
  right_inv q := by
    have h : hT.from T = 𝟙 T := hT.hom_ext _ _
    ext x
    change F.map (hT.from T).op (q x) = q x
    rw [h]
    simp
    rfl

private def constantPFAdj (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) :
    constantPF X A ⊣ PresheafOfModules.evaluation _ (op T) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantPresheafHomEquiv X A T hT
      homEquiv_naturality_left_symm := by
        intros
        apply PresheafOfModules.hom_ext
        intro U
        rfl
      homEquiv_naturality_right := by intros; rfl }

private def constantGlobal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) :=
  SheafOfModules.forget (adicLisseRing X A) ⋙
    PresheafOfModules.restrictScalars (adicLisseConstantUnit X A) ⋙
      PresheafOfModules.evaluation _ (op T)

private def constantAdj (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) :
    adicLisseConstantModules X A ⊣ constantGlobal X A T :=
  (constantPFAdj X A T hT).comp
    (PresheafOfModules.sheafificationAdjunction (adicLisseConstantUnit X A))

private def integralGlobal {A : Type (u + 1)} [CommRing A]
    (X : Scheme.{u}) (d : AdicCoefficientDatum A) (T : X.ProEt) :=
  pbcRestrict (pbcCompletedScalar X d) ⋙ constantGlobal X A T

private def integralAdj {A : Type (u + 1)} [CommRing A]
    (X : Scheme.{u}) (d : AdicCoefficientDatum A) (T : X.ProEt) (hT : IsTerminal T) :
    integralConstantModule X d ⊣ integralGlobal X d T := by
  let pd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let e := proEtaleScalarEquivalence X
    ((adicLisseForget X).mapIso (pbcCompletedComparison X d).symm)
  let adj := ((constantAdj X A T hT).comp
    (adicDatumOrdinaryAdjunction X (adicDatumScalar X pd))).comp e.toAdjunction
  exact adj

private theorem integralAdj_unit (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (V : T.ProEt) (hV : IsTerminal V) (N : ModuleCat.{u + 1} A) (p : N) :
    ((integralAdj T d V hV).unit.app N) p =
      adicDatumTensorSection T
        (adicDatumScalar T
          { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
            quotientFinite := d.quotientFinite })
        ((adicLisseConstantModules T A).obj N) (op V) 1
        (completedConstantGenerator T A N (op V) p) := by
  let pd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let M := (completedConstantExtension T (adicDatumScalar T pd)).obj
    ((adicLisseConstantModules T A).obj N)
  change M.val.map (𝟙 (op V))
    (((adicDatumOrdinaryAdjunction T (adicDatumScalar T pd)).unit.app
      ((adicLisseConstantModules T A).obj N)).val.app (op V)
        (completedConstantGenerator T A N (op V) p)) = _
  rw [M.val.map_id]
  change ((adicDatumOrdinaryAdjunction T (adicDatumScalar T pd)).unit.app
    ((adicLisseConstantModules T A).obj N)).val.app (op V) _ = _
  erw [(adicDatumOrdinaryAdjunction_exists T (adicDatumScalar T pd)).choose_spec]
  exact (adicDatumOrdinaryUnit_exists T (adicDatumScalar T pd)
    ((adicLisseConstantModules T A).obj N)).exists.choose_spec (op V) _

private theorem integralAdj_hom (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (V : T.ProEt) (hV : IsTerminal V) (N : ModuleCat.{u + 1} A)
    (M : pbcModules T (pbcAdicCompletion T d))
    (f : (integralConstantModule T d).obj N ⟶ M) (p : N) :
    ((integralAdj T d V hV).homEquiv N M f) p =
      f.val.app (op V) (finiteFreeConstantTensor T d N (op V) 1 p) := by
  rw [Adjunction.homEquiv_unit]
  change f.val.app (op V) (((integralAdj T d V hV).unit.app N) p) = _
  rw [integralAdj_unit]
  simp only [finiteFreeConstantTensor, map_one]

private theorem finiteFree_section_square
    (l : ℕ) [Fact l.Prime] (E F : Type (u + 1)) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) (T : Scheme.{u}) (U : T.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    (finiteFreeCompletedCoefficientMap l E F i T).hom.app U
        (pbcCompletedSection T (pbcPadicCoefficientDatum l E) U a) =
      pbcCompletedSection T (pbcPadicCoefficientDatum l F) U
        (WeilConjectures.integralScalarIntegerInclusion l E F i a) := by
  let φ := WeilConjectures.integralScalarIntegerInclusion l E F i
  let C := constantSheaf (ProEt.topology T) CommRingCat.{u + 1}
  have hunit := congr_app (toSheafify_naturality (ProEt.topology T)
    (show (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
        (Padic.coefficientExtensionIntegers l E)) ⟶
      (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
        (Padic.coefficientExtensionIntegers l F)) from
      (Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom φ))) U
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app U) (finiteFree_scalar_square l E F i T))
    ((toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (Padic.coefficientExtensionIntegers l E)))).app U a)
  change _ = (pbcCompletedScalar T (pbcPadicCoefficientDatum l F)).hom.app U
    ((C.map (CommRingCat.ofHom φ)).hom.app U
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (CommRingCat.of (Padic.coefficientExtensionIntegers l E)))).app U a)) at h
  have hu := ConcreteCategory.congr_hom hunit a
  change _ = (C.map (CommRingCat.ofHom φ)).hom.app U _ at hu
  exact h.trans (congrArg
    ((pbcCompletedScalar T (pbcPadicCoefficientDatum l F)).hom.app U) hu.symm)

private def balanceRight
    (l : ℕ) [Fact l.Prime] (E F : Type (u + 1)) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) (T : Scheme.{u}) (V : T.ProEt) :
    pbcRestrict (finiteFreeCompletedCoefficientMap l E F i T) ⋙
        integralGlobal T (pbcPadicCoefficientDatum l E) V ≅
      integralGlobal T (pbcPadicCoefficientDatum l F) V ⋙
        ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (WeilConjectures.integralScalarIntegerInclusion l E F i) :=
  NatIso.ofComponents (fun M ↦
    { hom := ModuleCat.ofHom
        (X := (pbcRestrict (finiteFreeCompletedCoefficientMap l E F i T) ⋙
          integralGlobal T (pbcPadicCoefficientDatum l E) V).obj M)
        (Y := (integralGlobal T (pbcPadicCoefficientDatum l F) V ⋙
          ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
            (WeilConjectures.integralScalarIntegerInclusion l E F i)).obj M)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro a x
            let x' : M.val.obj (op V) := x
            change (finiteFreeCompletedCoefficientMap l E F i T).hom.app (op V)
                (pbcCompletedSection T (pbcPadicCoefficientDatum l E) (op V) a) • x' =
              pbcCompletedSection T (pbcPadicCoefficientDatum l F) (op V)
                (WeilConjectures.integralScalarIntegerInclusion l E F i a) • x'
            rw [finiteFree_section_square] }
      inv := ModuleCat.ofHom (X := (integralGlobal T (pbcPadicCoefficientDatum l F) V ⋙
          ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
            (WeilConjectures.integralScalarIntegerInclusion l E F i)).obj M)
        (Y := (pbcRestrict (finiteFreeCompletedCoefficientMap l E F i T) ⋙
          integralGlobal T (pbcPadicCoefficientDatum l E) V).obj M)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro a x
            let x' : M.val.obj (op V) := x
            change pbcCompletedSection T (pbcPadicCoefficientDatum l F) (op V)
                (WeilConjectures.integralScalarIntegerInclusion l E F i a) • x' =
              (finiteFreeCompletedCoefficientMap l E F i T).hom.app (op V)
                (pbcCompletedSection T (pbcPadicCoefficientDatum l E) (op V) a) • x'
            rw [finiteFree_section_square] }
      hom_inv_id := by ext x; rfl
      inv_hom_id := by ext x; rfl }) (by intros; ext x; rfl)

private def balanceIso
    (l : ℕ) [Fact l.Prime] (E F : Type (u + 1)) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) (T : Scheme.{u}) :
    integralConstantModule T (pbcPadicCoefficientDatum l E) ⋙
        pbcExtend (finiteFreeCompletedCoefficientMap l E F i T) ≅
      ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (WeilConjectures.integralScalarIntegerInclusion l E F i) ⋙
        integralConstantModule T (pbcPadicCoefficientDatum l F) :=
  Adjunction.leftAdjointUniq
    (((integralAdj T (pbcPadicCoefficientDatum l E) _ terminalIsTerminal).comp
      (pbcScalarAdjunction (finiteFreeCompletedCoefficientMap l E F i T))).ofNatIsoRight
        (balanceRight l E F i T _))
    ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      (WeilConjectures.integralScalarIntegerInclusion l E F i)).comp
        (integralAdj T (pbcPadicCoefficientDatum l F) _ terminalIsTerminal))


private theorem realizationSection_smul (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (N : ModuleCat.{u + 1} A) (U : T.ProEtᵒᵖ)
    (r : (pbcAdicCompletion T d).obj.obj U) (p : N) :
    finiteFreeConstantTensor T d N U r p =
      r • finiteFreeConstantTensor T d N U 1 p := by
  let pd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let M := ((adicLisseConstantModules T A).obj N)
  have h := normalizedTensor_smul T (adicDatumScalar T pd) M _
    (completedExtension_obj T (adicDatumScalar T pd) M) U
    ((pbcCompletedComparison T d).inv.hom.app U r) 1
    (completedConstantGenerator T A N U p)
  rw [mul_one] at h
  unfold finiteFreeConstantTensor
  simp only [map_one]
  exact h

private theorem pbcSection_smul (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (N : pbcModules T R) (U : T.ProEtᵒᵖ) (r : S.obj.obj U) (p : N.val.obj U) :
    pbcTensorSection φ N U r p = r • pbcTensorSection φ N U 1 p := by
  change completedAdicChangeTensor T φ N U r p = _
  have h := completedTensor_smul T φ N U r 1 p
  rw [mul_one] at h
  exact h

private theorem integralGenerator_natural (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (N : ModuleCat.{u + 1} A) {U V : T.ProEtᵒᵖ} (f : U ⟶ V) (p : N) :
    ((integralConstantModule T d).obj N).val.map f
        (finiteFreeConstantTensor T d N U 1 p) =
      finiteFreeConstantTensor T d N V 1 p := by
  let pd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let η := (adicDatumOrdinaryAdjunction T (adicDatumScalar T pd)).unit.app
    ((adicLisseConstantModules T A).obj N)
  have hη (W : T.ProEtᵒᵖ) : η.val.app W (completedConstantGenerator T A N W p) =
      finiteFreeConstantTensor T d N W 1 p := by
    dsimp only [η]
    erw [(adicDatumOrdinaryAdjunction_exists T (adicDatumScalar T pd)).choose_spec]
    have h := (adicDatumOrdinaryUnit_exists T (adicDatumScalar T pd)
      ((adicLisseConstantModules T A).obj N)).exists.choose_spec W
        (completedConstantGenerator T A N W p)
    unfold finiteFreeConstantTensor
    simp only [map_one]
    exact h
  rw [← hη U, ← hη V]
  change ((completedConstantExtension T (adicDatumScalar T pd)).obj _).val.map f
    (η.val.app U _) = _
  have h := (PresheafOfModules.naturality_apply η.val f
    (completedConstantGenerator T A N U p)).symm
  refine h.trans ?_
  congr 1
  exact (NatTrans.naturality_apply
    (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of N))) f p).symm


private theorem balanceIso_one
    (l : ℕ) [Fact l.Prime] (E F : Type (u + 1)) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) (T : Scheme.{u})
    (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) (p : N) :
    ((balanceIso l E F i T).hom.app N).val.app (op (⊤_ T.ProEt))
      (pbcTensorSection (finiteFreeCompletedCoefficientMap l E F i T)
        ((integralConstantModule T (pbcPadicCoefficientDatum l E)).obj N)
        (op (⊤_ T.ProEt)) 1
        (finiteFreeConstantTensor T (pbcPadicCoefficientDatum l E) N
          (op (⊤_ T.ProEt)) 1 p)) =
      finiteFreeConstantTensor T (pbcPadicCoefficientDatum l F) _
        (op (⊤_ T.ProEt)) 1
        ((1 : Padic.coefficientExtensionIntegers l F) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          WeilConjectures.integralScalarIntegerInclusion l E F i] p) := by
  let a1 := (((integralAdj T (pbcPadicCoefficientDatum l E) _ terminalIsTerminal).comp
    (pbcScalarAdjunction (finiteFreeCompletedCoefficientMap l E F i T))).ofNatIsoRight
      (balanceRight l E F i T _))
  let a2 := ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (WeilConjectures.integralScalarIntegerInclusion l E F i)).comp
      (integralAdj T (pbcPadicCoefficientDatum l F) _ terminalIsTerminal))
  have h := congrArg (fun q ↦ q p)
    (Adjunction.homEquiv_leftAdjointUniq_hom_app a1 a2 N)
  dsimp only [a1] at h
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
  change ((integralAdj T (pbcPadicCoefficientDatum l E) _ terminalIsTerminal).homEquiv
    N _ ((pbcScalarAdjunction (finiteFreeCompletedCoefficientMap l E F i T)).homEquiv _ _
      ((balanceIso l E F i T).hom.app N))) p = _ at h
  rw [integralAdj_hom, Adjunction.homEquiv_unit] at h
  change ((balanceIso l E F i T).hom.app N).val.app _
    (((pbcScalarAdjunction (finiteFreeCompletedCoefficientMap l E F i T)).unit.app
      ((integralConstantModule T (pbcPadicCoefficientDatum l E)).obj N)).val.app _
        (finiteFreeConstantTensor T (pbcPadicCoefficientDatum l E) N _ 1 p)) = _ at h
  erw [(pbcScalarAdjunction_exists
    (finiteFreeCompletedCoefficientMap l E F i T)).exists.choose_spec] at h
  dsimp only [a2] at h
  rw [Adjunction.comp_unit_app] at h
  change _ = ((integralAdj T (pbcPadicCoefficientDatum l F) _ terminalIsTerminal).unit.app
    ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (WeilConjectures.integralScalarIntegerInclusion l E F i)).obj N))
        ((1 : Padic.coefficientExtensionIntegers l F) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          WeilConjectures.integralScalarIntegerInclusion l E F i] p) at h
  rw [integralAdj_unit] at h
  simpa only [finiteFreeConstantTensor, map_one] using h


private theorem pbcUnit_natural (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (N : pbcModules T R) {U V : T.ProEtᵒᵖ} (f : U ⟶ V) (x : N.val.obj U) :
    ((pbcExtend φ).obj N).val.map f (pbcTensorSection φ N U 1 x) =
      pbcTensorSection φ N V 1 (N.val.map f x) := by
  let η := (pbcScalarAdjunction φ).unit.app N
  have h := (PresheafOfModules.naturality_apply η.val f x).symm
  erw [(pbcScalarAdjunction_exists φ).exists.choose_spec,
    (pbcScalarAdjunction_exists φ).exists.choose_spec] at h
  exact h

private theorem pbcUnit_smul (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (N : pbcModules T R) (U : T.ProEtᵒᵖ) (r : R.obj.obj U) (x : N.val.obj U) :
    pbcTensorSection φ N U 1 (r • x) =
      φ.hom.app U r • pbcTensorSection φ N U 1 x := by
  have h := (((pbcScalarAdjunction φ).unit.app N).val.app U).hom.map_smul r x
  erw [(pbcScalarAdjunction_exists φ).exists.choose_spec,
    (pbcScalarAdjunction_exists φ).exists.choose_spec] at h
  exact h

attribute [local irreducible] balanceIso finiteFreeConstantTensor pbcTensorSection

private theorem balanceIso_allOne
    (l : ℕ) [Fact l.Prime] (E F : Type (u + 1)) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) (T : Scheme.{u})
    (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
    (U : T.ProEtᵒᵖ) (p : N) :
    ((balanceIso l E F i T).hom.app N).val.app U
      (pbcTensorSection (finiteFreeCompletedCoefficientMap l E F i T)
        ((integralConstantModule T (pbcPadicCoefficientDatum l E)).obj N) U 1
        (finiteFreeConstantTensor T (pbcPadicCoefficientDatum l E) N U 1 p)) =
      finiteFreeConstantTensor T (pbcPadicCoefficientDatum l F) _ U 1
        ((1 : Padic.coefficientExtensionIntegers l F) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          WeilConjectures.integralScalarIntegerInclusion l E F i] p) := by
  let f : op (⊤_ T.ProEt) ⟶ U := (terminalIsTerminal.from U.unop).op
  let c := finiteFreeCompletedCoefficientMap l E F i T
  let M := (integralConstantModule T (pbcPadicCoefficientDatum l E)).obj N
  let N' := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (WeilConjectures.integralScalarIntegerInclusion l E F i)).obj N
  let p' : N' := (1 : Padic.coefficientExtensionIntegers l F)
    ⊗ₜ[Padic.coefficientExtensionIntegers l E,
      WeilConjectures.integralScalarIntegerInclusion l E F i] p
  let x := finiteFreeConstantTensor T (pbcPadicCoefficientDatum l E) N
    (op (⊤_ T.ProEt)) 1 p
  have hsrc := pbcUnit_natural T c M f x
  have hinner := integralGenerator_natural T (pbcPadicCoefficientDatum l E) N f p
  have hsrc' := hsrc.trans (congrArg (pbcTensorSection c M U 1) hinner)
  have hnat := PresheafOfModules.naturality_apply
    ((balanceIso l E F i T).hom.app N).val f
      (pbcTensorSection c M (op (⊤_ T.ProEt)) 1 x)
  have h₁ := congrArg (((balanceIso l E F i T).hom.app N).val.app U) hsrc'.symm
  have h₂ := congrArg (((integralConstantModule T (pbcPadicCoefficientDatum l F)).obj N').val.map f)
    (balanceIso_one l E F i T N p)
  exact h₁.trans (hnat.trans (h₂.trans
    (integralGenerator_natural T (pbcPadicCoefficientDatum l F) N' f p')))


private theorem balanceIso_formula
    (l : ℕ) [Fact l.Prime] (E F : Type (u + 1)) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) (T : Scheme.{u})
    (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
    (U : T.ProEtᵒᵖ) (r : (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)).obj.obj U)
    (s : (pbcAdicCompletion T (pbcPadicCoefficientDatum l F)).obj.obj U) (p : N) :
    ((balanceIso l E F i T).hom.app N).val.app U
      (pbcTensorSection (finiteFreeCompletedCoefficientMap l E F i T)
        ((integralConstantModule T (pbcPadicCoefficientDatum l E)).obj N) U s
        (finiteFreeConstantTensor T (pbcPadicCoefficientDatum l E) N U r p)) =
      finiteFreeConstantTensor T (pbcPadicCoefficientDatum l F) _ U
        ((finiteFreeCompletedCoefficientMap l E F i T).hom.app U r * s)
        ((1 : Padic.coefficientExtensionIntegers l F) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          WeilConjectures.integralScalarIntegerInclusion l E F i] p) := by
  rw [pbcSection_smul, map_smul, realizationSection_smul]
  erw [pbcUnit_smul, map_smul, balanceIso_allOne, ← mul_smul]
  rw [← realizationSection_smul, mul_comm s]


/-- The ordinary balancing isomorphism, specified on all tensor generators.
The formula is ((r tensor p) tensor s) ↦ c(r)s tensor (1 tensor p).
Source: Stacks 03EK; blueprint scalar-extension local formula
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport).
Proof: the displayed balanced section formula has inverse
s tensor (b tensor p) ↦ (1 tensor p) tensor sb. The A-balancing holds since the
coefficient square commutes; R- and B-balancing move their scalars into S. Both
composites are the identity. Sheafification gives inverse module maps, natural in
N and in restriction. These local generators determine the transformation uniquely. -/
theorem finiteFreeConstantBalance_existsUnique (T : Scheme.{u}) :
    ∃! b : integralConstantModule T (pbcPadicCoefficientDatum l E) ⋙
        pbcExtend (finiteFreeCompletedCoefficientMap l E F i T) ≅
      finiteFreeCoefficientExtension l E F i ⋙
        integralConstantModule T (pbcPadicCoefficientDatum l F),
      ∀ (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (U : T.ProEtᵒᵖ) (r : (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)).obj.obj U)
        (s : (pbcAdicCompletion T (pbcPadicCoefficientDatum l F)).obj.obj U) (p : N),
        (b.hom.app N).val.app U
          (pbcTensorSection (finiteFreeCompletedCoefficientMap l E F i T)
            ((integralConstantModule T (pbcPadicCoefficientDatum l E)).obj N) U s
            (finiteFreeConstantTensor T (pbcPadicCoefficientDatum l E) N U r p)) =
          finiteFreeConstantTensor T (pbcPadicCoefficientDatum l F) _ U
            ((finiteFreeCompletedCoefficientMap l E F i T).hom.app U r * s)
            ((1 : Padic.coefficientExtensionIntegers l F) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              WeilConjectures.integralScalarIntegerInclusion l E F i] p) := by
  let a1 := (((integralAdj T (pbcPadicCoefficientDatum l E) _ terminalIsTerminal).comp
    (pbcScalarAdjunction (finiteFreeCompletedCoefficientMap l E F i T))).ofNatIsoRight
      (balanceRight l E F i T _))
  have hcomp (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
      (M : pbcModules T (pbcAdicCompletion T (pbcPadicCoefficientDatum l F)))
      (f : (integralConstantModule T (pbcPadicCoefficientDatum l E) ⋙
        pbcExtend (finiteFreeCompletedCoefficientMap l E F i T)).obj N ⟶ M) (p : N) :
      (a1.homEquiv N M f) p = f.val.app (op (⊤_ T.ProEt))
        (pbcTensorSection (finiteFreeCompletedCoefficientMap l E F i T)
          ((integralConstantModule T (pbcPadicCoefficientDatum l E)).obj N)
          (op (⊤_ T.ProEt)) 1
          (finiteFreeConstantTensor T (pbcPadicCoefficientDatum l E) N
            (op (⊤_ T.ProEt)) 1 p)) := by
    dsimp only [a1]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change ((integralAdj T (pbcPadicCoefficientDatum l E) _ terminalIsTerminal).homEquiv
      N _ ((pbcScalarAdjunction (finiteFreeCompletedCoefficientMap l E F i T)).homEquiv
        _ _ f)) p = _
    rw [integralAdj_hom, Adjunction.homEquiv_unit]
    change f.val.app _
      (((pbcScalarAdjunction (finiteFreeCompletedCoefficientMap l E F i T)).unit.app
        ((integralConstantModule T (pbcPadicCoefficientDatum l E)).obj N)).val.app _ _) = _
    exact congrArg (f.val.app _) ((pbcScalarAdjunction_exists
      (finiteFreeCompletedCoefficientMap l E F i T)).exists.choose_spec _ _ _)
  refine ⟨balanceIso l E F i T, balanceIso_formula l E F i T, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply (a1.homEquiv N _).injective
  ext p
  rw [hcomp, hcomp]
  exact (hb N (op (⊤_ T.ProEt)) 1 1 p).trans
    (balanceIso_formula l E F i T N (op (⊤_ T.ProEt)) 1 1 p).symm


/-- The balancing fixed by the preceding pure-tensor formula, rather than a chosen model.
Source: Stacks 03EK; blueprint scalar-extension local formula
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
def finiteFreeConstantBalance (T : Scheme.{u}) :=
  (finiteFreeConstantBalance_existsUnique l E F i T).exists.choose

/-- Apply the specified balancing degreewise to complexes.
Source: Stacks 03EK; blueprint scalar-extension local formula
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
def finiteFreeConstantComplexBalance (T : Scheme.{u}) :=
  Functor.mapHomologicalComplexCompIso
    (F := integralConstantModule T (pbcPadicCoefficientDatum l E))
    (G := pbcExtend (finiteFreeCompletedCoefficientMap l E F i T)) (Iso.refl _) (.up ℤ) ≪≫
  NatIso.mapHomologicalComplex (finiteFreeConstantBalance l E F i T) (.up ℤ) ≪≫
  (Functor.mapHomologicalComplexCompIso
    (F := finiteFreeCoefficientExtension l E F i)
    (G := integralConstantModule T (pbcPadicCoefficientDatum l F)) (Iso.refl _) (.up ℤ)).symm

/-- The localization factorization for the published completed constant realization.
Source: Bhatt--Scholze 6.6.11
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
def finiteFreeConstantFactors (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    completedConstantQ (ModuleCat.{u + 1} A) ⋙ integralConstantDerived T d ≅
      (integralConstantModule T d).mapHomologicalComplex (.up ℤ) ⋙
        (DerivedCategory.Q.{u + 2, u + 1, u + 2}
          (C := pbcModules T (pbcAdicCompletion T d))) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  letI := (integralConstantModule_exact T d).1
  letI := (integralConstantModule_exact T d).2
  (integralConstantModule T d).mapDerivedCategoryFactors.{u + 2, u + 2,
    u + 1, u + 1, u + 2, u + 2}

/-- The canonical derived model map: localization factorization, K-flat counit,
ordinary balancing, and the inverse target realization factorization, in that order.
Source: Stacks 06YY and 08H3; blueprint scalar-extension local formula
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
def finiteFreeDerivedModelMap (T : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ) :
    (finiteFreeCompletedScalar l E F i T).obj
        ((integralConstantDerived T (pbcPadicCoefficientDatum l E)).obj
          ((completedConstantQ _).obj P)) ⟶
      (integralConstantDerived T (pbcPadicCoefficientDatum l F)).obj
        ((completedConstantQ _).obj ((finiteFreeCoefficientComplex l E F i).obj P)) :=
  (finiteFreeCompletedScalar l E F i T).map
      ((finiteFreeConstantFactors T (pbcPadicCoefficientDatum l E)).hom.app P) ≫
    pbcComplexCounit (finiteFreeCompletedCoefficientMap l E F i T)
      (((integralConstantModule T (pbcPadicCoefficientDatum l E)).mapHomologicalComplex
        (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map ((finiteFreeConstantComplexBalance l E F i T).hom.app P) ≫
    (finiteFreeConstantFactors T (pbcPadicCoefficientDatum l F)).inv.app
      ((finiteFreeCoefficientComplex l E F i).obj P)

/-- Transport a specified local model, using the normalized restriction comparison,
then scalar extension of that very isomorphism, then the displayed balancing map.
Source: Bhatt--Scholze 6.6.11; Stacks 03EL, 06YY and 08H3
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport). -/
def finiteFreeLocalModelMap {X T : Scheme.{u}} (g : X ⟶ T)
    (K : PbcCompletedDerived T (pbcPadicCoefficientDatum l E))
    (P : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (e : (pbcActualDerivedPull g (pbcPadicCoefficientDatum l E)).obj K ≅
      (integralConstantDerived X (pbcPadicCoefficientDatum l E)).obj
        ((completedConstantQ _).obj P)) :
    (pbcActualDerivedPull g (pbcPadicCoefficientDatum l F)).obj
        ((finiteFreeCompletedScalar l E F i T).obj K) ⟶
      (integralConstantDerived X (pbcPadicCoefficientDatum l F)).obj
        ((completedConstantQ _).obj ((finiteFreeCoefficientComplex l E F i).obj P)) :=
  (finiteFreeScalarRestriction l E F i g).hom.app K ≫
    (finiteFreeCompletedScalar l E F i X).map e.hom ≫
    finiteFreeDerivedModelMap l E F i X P

private theorem localModel_isIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : PbcCompletedDerived Y (pbcPadicCoefficientDatum l E))
    (P : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (b : ℤ) [P.IsStrictlyLE b]
    (hP : ∀ q : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l E) (P.X q))
    (e : (pbcActualDerivedPull g (pbcPadicCoefficientDatum l E)).obj K ≅
      (integralConstantDerived X (pbcPadicCoefficientDatum l E)).obj
        ((completedConstantQ _).obj P)) :
    IsIso (finiteFreeLocalModelMap l E F i g K P e) := by
  have hc := realization_kflat X (pbcPadicCoefficientDatum l E) P b hP
  have hε := pbcExtensionCounit_isIso (finiteFreeCompletedCoefficientMap l E F i X)
    (((integralConstantModule X (pbcPadicCoefficientDatum l E)).mapHomologicalComplex
      (.up ℤ)).obj P) hc
  have : IsIso (pbcComplexCounit (finiteFreeCompletedCoefficientMap l E F i X)
      (((integralConstantModule X (pbcPadicCoefficientDatum l E)).mapHomologicalComplex
        (.up ℤ)).obj P)) := by
    dsimp only [pbcComplexCounit]
    infer_instance
  have : IsIso (finiteFreeDerivedModelMap l E F i X P) := by
    dsimp only [finiteFreeDerivedModelMap]
    infer_instance
  dsimp only [finiteFreeLocalModelMap]
  infer_instance

/-- Finite-free coefficient extension preserves the full integral constructible category
and transports the specified finite-projective models on the same strata and covers.

Source: blueprint main-20261015, prop-weil-pbc-scalar-extension, exactness clause;
Bhatt--Scholze, Proposition 6.6.11; Stacks Tags 05CF, 08H3 and 03EL
(blueprint: lem-weil-pbc-finite-free-constructible-scalar-transport).

Proof: apply the forward integral stratified-perfect characterization to K to obtain
finite strata and pro-etale covering members with bounded finite-projective A-models.
For the precise assertion start with the supplied strata and isomorphism e instead.
In every degree choose finitely many generators of P and split the resulting finite
free surjection by projectivity. Tensor both splitting maps with B. Their composite
is still the identity; hence every B tensor_A P term is finite projective. Zero
terms remain zero, so the same interval [a,b] works, including the zero complex.
On the chosen stratum and its covering member, the completed coefficient comparison
identifies the inverse-image coefficients with the completed rings. Equivalently
work on the small pro-etale site of that covering scheme, canonically equivalent
to the slice site. The scalar coefficient square commutes at every finite quotient,
so it commutes at the limit. The published K-flat-normalized scalar/pullback
comparison therefore identifies restriction of C(K) with C of the restriction.
The strict-perfect pullback model computes the completed realization of P by its
termwise tensor complex and proves that complex K-flat; this is projectivity of
its coefficient modules, not projectivity in the global sheaf category.
Apply scalar extension to the supplied e. The universal K-flat counit, followed
by the ordinary balancing, identifies its model with S tensor_B (B tensor_A P).
The balancing is exactly ((r tensor p) tensor s) ↦ c(r)s tensor (1 tensor p),
with inverse s tensor (b tensor p) ↦ (1 tensor p) tensor sb. Its section formulas
respect balancing, restrictions and differentials. Thus finiteFreeLocalModelMap
is an isomorphism and retains the original model isomorphism, strata and covers.
Finally the reverse stratified-perfect characterization over B proves all three
membership conditions: intrinsic completeness, uniform bounded constructible
reductions with common models, and compatible etale-origin witnesses. -/
theorem finiteFreeConstructibleScalarTransport (T : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n) (_hl : IsUnit (l : Γ(T, ⊤)))
    (K : PbcCompletedDerived T (pbcPadicCoefficientDatum l E))
    (hK : PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E) K) :
    PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l F)
        ((finiteFreeCompletedScalar l E F i T).obj K) ∧
      ∀ (s : FiniteLocallyClosedStratification T)
        (V : ∀ k : Fin s.n, Sieve (⊤_ (s.domain k).ProEt)),
        (∀ k : Fin s.n, V k ∈ ProEt.topology (s.domain k) (⊤_ (s.domain k).ProEt)) →
        ∀ (P : ∀ (k : Fin s.n) (U : (s.domain k).ProEt)
            (f : U ⟶ ⊤_ (s.domain k).ProEt), V k f →
              CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
          (a b : ∀ (k : Fin s.n) (U : (s.domain k).ProEt)
            (f : U ⟶ ⊤_ (s.domain k).ProEt), V k f → ℤ),
          (∀ (k : Fin s.n) (U : (s.domain k).ProEt)
            (f : U ⟶ ⊤_ (s.domain k).ProEt) (hf : V k f),
            (P k U f hf).IsStrictlyGE (a k U f hf) ∧
            (P k U f hf).IsStrictlyLE (b k U f hf) ∧
            ∀ q : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l E)
                ((P k U f hf).X q) ∧
              Module.Finite (Padic.coefficientExtensionIntegers l E) ((P k U f hf).X q)) →
          ∀ e : ∀ (k : Fin s.n) (U : (s.domain k).ProEt)
              (f : U ⟶ ⊤_ (s.domain k).ProEt) (hf : V k f),
              (pbcActualDerivedPull (U.hom ≫ s.immersion k)
                (pbcPadicCoefficientDatum l E)).obj K ≅
              (integralConstantDerived U.left (pbcPadicCoefficientDatum l E)).obj
                ((completedConstantQ _).obj (P k U f hf)),
            ∀ (k : Fin s.n) (U : (s.domain k).ProEt)
              (f : U ⟶ ⊤_ (s.domain k).ProEt) (hf : V k f),
              CochainComplex.IsStrictlyGE
                  ((finiteFreeCoefficientComplex l E F i).obj (P k U f hf)) (a k U f hf) ∧
              CochainComplex.IsStrictlyLE
                  ((finiteFreeCoefficientComplex l E F i).obj (P k U f hf)) (b k U f hf) ∧
              (∀ q : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l F)
                  (((finiteFreeCoefficientComplex l E F i).obj (P k U f hf)).X q) ∧
                Module.Finite (Padic.coefficientExtensionIntegers l F)
                  (((finiteFreeCoefficientComplex l E F i).obj (P k U f hf)).X q)) ∧
              IsIso (finiteFreeLocalModelMap l E F i (U.hom ≫ s.immersion k) K
                (P k U f hf) (e k U f hf)) := by
  constructor
  · obtain ⟨s, hs⟩ := (integralPadicLocalPerfectCriterion T l E _hdim _hl K).mp hK
    apply (integralPadicLocalPerfectCriterion T l F _hdim _hl _).mpr
    refine ⟨s, fun k ↦ ?_⟩
    obtain ⟨V, hV, hmodels⟩ := hs k
    refine ⟨V, hV, fun U f hf ↦ ?_⟩
    obtain ⟨P, a, b, ha, hb, hterms, ⟨e⟩⟩ := hmodels U f hf
    let := ha
    let := hb
    have hbounds := coefficientComplex_bounds l E F i P a b
    have := localModel_isIso l E F i (U.hom ≫ s.immersion k) K P b
      (fun q ↦ (hterms q).1) e
    exact ⟨(finiteFreeCoefficientComplex l E F i).obj P, a, b, hbounds.1, hbounds.2,
      coefficientComplex_terms l E F i P hterms,
      ⟨asIso (finiteFreeLocalModelMap l E F i (U.hom ≫ s.immersion k) K P e)⟩⟩
  · intro s V _hV P a b hP e k U f hf
    obtain ⟨ha, hb, hterms⟩ := hP k U f hf
    let := ha
    let := hb
    have hbounds := coefficientComplex_bounds l E F i (P k U f hf)
      (a k U f hf) (b k U f hf)
    refine ⟨hbounds.1, hbounds.2, coefficientComplex_terms l E F i _ hterms, ?_⟩
    exact localModel_isIso l E F i (U.hom ≫ s.immersion k) K (P k U f hf)
      (b k U f hf) (fun q ↦ (hterms q).1) (e k U f hf)

end AlgebraicGeometry.Scheme
