/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleCondensedCoefficientFamily
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomCocycleNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal

/-! # Supported Hom for pulled-back condensed coefficients

Source: latest blueprint, lem-pur-supported-hom, evaluation and injective-resolution
construction (blueprint: lem-pur-supported-hom).
This interface uses internal modules over the actual pulled-back condensed ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.CondensedRing.Admissible

/-- The existing internal-module category. Source: det-def-sf-operations
(blueprint: lem-pur-supported-hom). -/
abbrev Modules (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)

/-- The regular coefficient unit. Source: lem-pur-supported-hom
(blueprint: lem-pur-supported-hom). -/
abbrev unit (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :=
  Mod.regular (condensedRingObj Λ.X X)

/-- The underived closed direct image, placed in degree zero only afterwards.
Source: lem-pur-supported-hom (blueprint: lem-pur-supported-hom). -/
abbrev source (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  (CondensedRing.lowerStar Λ.X i).obj (unit Λ Z)

/-- Kernel of restriction on the underlying sections, derived in the module category.
Source: def-pur-support-cohomology (blueprint: lem-pur-supported-hom). -/
abbrev sections (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Modules Λ X ⥤ Ab.{u + 1} :=
  Mod.forget _ ⋙ Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X)
    Ab.{u + 1} (supportRestrictionArrow i)

/-- The integral generator of the regular coefficient. Source: evaluation on one
(blueprint: lem-pur-supported-hom). -/
def generator (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ condensedRingObj Λ.X X :=
  (Functor.Monoidal.εIso (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1})).inv ≫ η

/-- Integral generator of the supported unit. Source: the closed restriction of one
(blueprint: lem-pur-supported-hom). -/
def supportedGenerator (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (ProEtale.lowerStar Ab.{u + 1} i).obj
      ((constantSheaf (Scheme.ProEt.topology Z) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ (source Λ i).X :=
  (ProEtale.lowerStar Ab.{u + 1} i).map (generator Λ Z)

/-- The underived evaluation comparison. Source: supported-Hom proof, steps 1--4
(blueprint: lem-pur-supported-hom). -/
abbrev Evaluation (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  preadditiveCoyoneda.obj (op (source Λ i)) ≅ sections Λ i

/-- Evaluation sends a module map to its value at the supported coefficient one.
Source: supported-Hom proof, step 4 (blueprint: lem-pur-supported-hom). -/
def EvaluationSpec (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (e : Evaluation Λ i) : Prop :=
  ∀ (M : Modules Λ X) (f : source Λ i ⟶ M),
    kernel.ι (M.X.obj.map (supportRestrictionArrow i).op) (e.hom.app M f) =
      ((constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
        (MorphismProperty.Over.mkIdTerminal _ X)).homEquiv _ _
          (Scheme.proEtaleConstantDirectImageMap i Ab.{u + 1}
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ supportedGenerator Λ i ≫ f.hom))
              (ULift.up 1)

/-- Evaluation on one uniquely determines the supported-sections comparison.
Source: lem-pur-supported-hom, steps 1--4 (blueprint: lem-pur-supported-hom).
Proof: the open/closed coefficient sequence presents i_*Λ as the cokernel of
j_!Λ_U → Λ_X. Maps from that cokernel are exactly sections vanishing on U.
Evaluation on one and multiplication by restricted coefficients are inverse;
the displayed value fixes every component, proving uniqueness. -/
theorem evaluation_existsUnique (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃! e : Evaluation Λ i, EvaluationSpec Λ i e := by
  sorry

/-- The uniquely evaluation-normalized underived comparison.
Source: lem-pur-supported-hom, step 4 (blueprint: lem-pur-supported-hom). -/
def evaluation (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] : Evaluation Λ i :=
  (evaluation_existsUnique Λ i).choose

/-- Actual derived kernel cohomology for bounded-below module complexes.
Source: def-pur-support-cohomology (blueprint: lem-pur-supported-hom). -/
abbrev H (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ) :=
  (sections Λ i).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor Ab.{u + 1} a

/-- The supported-Hom comparison in every integer degree.
Source: lem-pur-supported-hom (blueprint: lem-pur-supported-hom). -/
abbrev Identification (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  ∀ (K : DerivedCategory.Plus (Modules Λ X)) (a : ℤ),
    (H Λ i a).obj K ≃+
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (source Λ i) ⟶ K.obj⟦a⟧)

/-- Naturality and the injective-cocycle formula specify the actual comparison.
Source: supported-Hom proof, steps 5--6 (blueprint: lem-pur-supported-hom). -/
def IdentificationSpec (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (χ : Identification Λ i) : Prop :=
  (∀ (K L : DerivedCategory.Plus (Modules Λ X)) (v : K ⟶ L) (a : ℤ)
    (s : (H Λ i a).obj K),
    χ L a ((H Λ i a).map v s) = χ K a s ≫ (DerivedCategory.Plus.ι.map v)⟦a⟧') ∧
  (∀ (I : CochainComplex.Plus (Modules Λ X)) [∀ r : ℤ, Injective (I.obj.X r)]
    (a : ℤ) (f : source Λ i ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0)
    (s : (((sections Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).cycles a),
    (evaluation Λ i).hom.app (I.obj.X a) f =
      (((sections Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).iCycles a s →
    χ (DerivedCategory.Plus.Q.obj I) a
      (((sections Λ i).homologyRightDerivedFunctorPlusObjQIsoOfInjective I a).inv
        ((((sections Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).homologyπ a s)) =
      supportedHomLocalizedCocycle I.obj a f hf ≫
        ((DerivedCategory.quotientCompQhIso _).inv.app I.obj)⟦a⟧')

/-- All-admissible supported-Hom identification, with its evaluation/cocycle normalization.
Source: lem-pur-supported-hom, six proof steps (blueprint: lem-pur-supported-hom).
Proof: (1) use pulled-back coefficients to identify restrictions; (2) the closed
coefficient restriction is locally surjective; (3) its kernel is j_!Λ_U;
(4) evaluation gives the specified underived comparison; (5) apply it termwise
on a bounded-below injective resolution; (6) a supported cycle maps to the
single-source cocycle displayed above. Resolution comparison gives naturality
and independence, and these cocycles determine the comparison uniquely. -/
theorem supported_hom_existsUnique (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃! χ : Identification Λ i, IdentificationSpec Λ i χ := by
  sorry

/-- The canonical all-admissible supported-Hom map, fixed on injective cocycles.
Source: lem-pur-supported-hom, step 6 (blueprint: lem-pur-supported-hom). -/
def supportedHom (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] : Identification Λ i :=
  (supported_hom_existsUnique Λ i).choose

/-- Supported cohomology equals supported Hom for the standing finite-type scheme,
all admissible coefficients, all bounded-below complexes, and all integer degrees.
Source: latest blueprint lem-pur-supported-hom, entire statement and proof
(blueprint: lem-pur-supported-hom).
Proof: (1) resolve by bounded-below injectives; the kernel of restriction is
sections of the sheaf supported on the closed subset, giving derived supported
sections; (2) evaluation on the coefficient one identifies sections over the
closed scheme with Hom from its regular unit, and the displayed injective
cocycle formula realizes that identification in every degree; (3) the closed
support adjunction transposes this Hom to Hom from i_* of the unit on X.
All three comparisons are natural, and comparison of resolutions gives the
canonical derived identification specified by IdentificationSpec. -/
theorem supported_hom (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (_hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {Z X : Scheme.{u}} (b : X ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    IdentificationSpec Λ i (supportedHom Λ i) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.Admissible
