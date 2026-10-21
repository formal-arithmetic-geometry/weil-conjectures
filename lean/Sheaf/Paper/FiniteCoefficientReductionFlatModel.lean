/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.Paper.FiniteCoefficientFlatModel
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModelReduction
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import Mathlib.RingTheory.Flat.Stability
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Reduction of bounded flat models at finite coefficient levels

Source: Weil blueprint, sec-smooth-purity/sk-lem-sf-flat-model,
lem-sf-reduction-flat-model.md (blueprint: lem-sf-reduction-flat-model).

The pro-etale statement uses the recorded constant-ring module category and intrinsic
constructibility predicate. The etale statement uses the recorded finite-value
constructibility predicate.
All scalar extensions below use the canonical quotient map between the actual stages;
the upstream theorems provide the general proof ingredients without an encoding change.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Keep localization, tensor, and sheafification structures abstract during conversion.
attribute [local irreducible] _root_.DerivedCategory.monoidalClosed
  SheafOfModules.monoidalCategory CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.presheafToSheaf CategoryTheory.sheafCompose
  SheafOfModules.siteDerivedTensorIndependentCoefficients
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
  AlgebraicGeometry.Etale.derivedTensor
  AlgebraicGeometry.Etale.derivedTensorQObjSingleFunctorObjIso


universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

private theorem changeOfRings_flat_terms
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    {R S : Sheaf J CommRingCat.{u + 1}} (φ : R ⟶ S)
    (F : SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (ho : ∀ M, F.obj M = SheafOfModules.changeOfRings φ M)
    (hf : ∀ {M N} (g : M ⟶ N), F.map g = eqToHom (ho M) ≫
      SheafOfModules.changeOfRingsHom φ M g ≫ eqToHom (ho N).symm)
    [F.Additive]
    (P : CochainComplex
      (SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ i, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X i)) :
    ∀ i, SheafOfModules.IsFlatOnSite (J := J) (R := S)
      (((F.mapHomologicalComplex (.up ℤ)).obj P).X i) := by
  have hr (i : ℤ) : exactFunctor _ _
      (@tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X i)) :=
    (SheafOfModules.flat_to_cat R _ (hflat i)).2
  have hc := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    φ P F ho hf hk hr
  let := SheafOfModules.monoidalCategory S
  intro i
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} S _).symm (hc.2 i)

private theorem proEtale_torAmplitude_of_flatModel
    (T : Scheme.{u}) (A : Type u) [CommRing A] (a b : ℤ) (hab : a ≤ b)
    (K : proEtaleDerivedCategory T A)
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
      (R := proEtaleConstantRing T A) (P.X q))
    (hsupp : ∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q))
    (ei : K ≅ DerivedCategory.Q.obj P) : HasProEtaleTorAmplitude T A K a b := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let R := proEtaleConstantRing T A
  let C := proEtaleRingModules T R
  let := SheafOfModules.monoidalCategory R
  let := HasDerivedCategory.standard C
  have hle : P.IsStrictlyLE b :=
    (P.isStrictlyLE_iff b).2 (fun q hq ↦ hsupp q (.inr hq))
  have hk := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R P b hflat
  obtain ⟨c, _, _⟩ := SheafOfModules.ringed_kFlat_single_tensor_comparison R
  change a ≤ b ∧ _
  refine ⟨hab, ?_⟩
  rintro L P' ⟨e'⟩ f hf hP' M i hi
  have hk' : P'.IsKFlatIndependentCoefficients :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P').2 hP'
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
  let S₀ := (HomologicalComplex.single C (.up ℤ) 0).obj M
  let eqP : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P' :=
    ei.symm ≪≫ e'.symm ≪≫ (asIso (DerivedCategory.Q.map f)).symm
  let F := tensorRight M
  let PM := (F.mapHomologicalComplex (.up ℤ)).obj P
  have hzX : IsZero (PM.X i) := F.map_isZero (hsupp i hi)
  have hz : IsZero (PM.homology i) :=
    (PM.sc i).isZero_homology_of_isZero_X₂ hzX
  let eq : DerivedCategory.Q.obj
      (((SheafOfModules.KFlatFixedTensor.totalTensor R).obj P').obj S₀) ≅
      DerivedCategory.Q.obj PM :=
    DerivedCategory.Q.mapIso (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) M P') ≪≫
      (c P' hk' M).symm ≪≫
      (((SheafOfModules.KFlatFixedTensor.derivedTensor R).mapIso eqP.symm).app _) ≪≫
      c P hk M
  have ht : IsZero ((DerivedCategory.homologyFunctor C i).obj
      (DerivedCategory.Q.obj PM)) :=
    hz.of_iso ((DerivedCategory.homologyFunctorFactors C i).app PM)
  exact ht.of_iso ((DerivedCategory.homologyFunctor C i).mapIso eq)


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (m n : ℕ) (hmn : m ≤ n) (T : Scheme.{u})

/-- The quotient factor map between the actual finite coefficient rings, canonically
lifted to the coefficient universe. No flatness of this ring map is assumed.
Source: blueprint, lem-sf-reduction-flat-model.md, the map A_{E,n} to A_{E,m}
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionCoefficientMap :
    ULift.{u + 1} (Padic.coefficientExtensionRing l E n) →+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E m) :=
  RingHom.ulift
    (Ideal.Quotient.factor (S := Padic.coefficientExtensionIdeal l E n)
      (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))

/-- The canonical constant coefficient map from stage n to stage m.
Source: blueprint, lem-sf-reduction-flat-model.md, coefficient reduction
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionRingMap :
    proEtaleConstantRing T (Padic.coefficientExtensionRing l E n) ⟶
      proEtaleConstantRing T (Padic.coefficientExtensionRing l E m) :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (flatModelReductionCoefficientMap l E m n hmn))

set_option linter.defProp false in
/-- Canonical scalar extension with its specified object/map formulas and its universal
left-derived pair, specialized to the finite-level quotient map. The formulas determine
the ordinary functor; the universal property determines the derived pair up to unique
compatible isomorphism.
Source: Stacks Tags 03EK, 06YT and 06YY; blueprint, lem-sf-reduction-flat-model.md
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionData :=
  letI : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  letI : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  letI : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
      u + 2, u + 1, u + 1, u + 1} _
  letI := HasDerivedCategory.standard
    (proEtaleRingModules T (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)))
  letI := HasDerivedCategory.standard
    (proEtaleRingModules T (proEtaleConstantRing T (Padic.coefficientExtensionRing l E m)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    (flatModelReductionRingMap l E m n hmn T)

/-- Ordinary tensor along the specified quotient map, fixed on objects and maps by
sectionwise tensor followed by sheafification in the recorded change-of-rings theorem.
Source: blueprint, lem-sf-reduction-flat-model.md, ordinary tensor complex
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionChange :=
  (flatModelReductionData l E m n hmn T).choose

/-- Additivity of the specified scalar extension, from its universal construction.
Source: Stacks Tag 03EK; blueprint, lem-sf-reduction-flat-model.md
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable instance flatModelReductionChange_additive :
    (flatModelReductionChange l E m n hmn T).Additive :=
  (flatModelReductionData l E m n hmn T).choose_spec.choose_spec.choose_spec.choose

set_option linter.defProp false in
/-- The universal left-derived scalar-extension pair and its K-flat computation.
Source: Stacks Tags 06YT and 06YY; blueprint, lem-sf-reduction-flat-model.md
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionDerivedData :=
  (flatModelReductionData l E m n hmn T).choose_spec.choose_spec.choose_spec.choose_spec.2.2

/-- Derived reduction from finite coefficient stage n to stage m, as the universal
left-derived functor of the specified ordinary scalar extension.
Source: blueprint, lem-sf-reduction-flat-model.md, definition of K_m
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReduction :
    proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n) ⥤
      proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E m) :=
  (flatModelReductionDerivedData l E m n hmn T).choose

private theorem reductionChange_obj (M : proEtaleRingModules T
    (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) :
    (flatModelReductionChange l E m n hmn T).obj M =
      SheafOfModules.changeOfRings (flatModelReductionRingMap l E m n hmn T) M :=
  (flatModelReductionData l E m n hmn T).choose_spec.choose M

private theorem reductionChange_map
    {M N : proEtaleRingModules T
      (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))} (g : M ⟶ N) :
    (flatModelReductionChange l E m n hmn T).map g =
      eqToHom (reductionChange_obj l E m n hmn T M) ≫
        SheafOfModules.changeOfRingsHom (flatModelReductionRingMap l E m n hmn T) M g ≫
        eqToHom (reductionChange_obj l E m n hmn T N).symm :=
  (flatModelReductionData l E m n hmn T).choose_spec.choose_spec.choose g

private theorem homotopyCounit_modelIso
    {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{u + 2} C] [HasDerivedCategory.{u + 2} D]
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ)
    (hε : IsIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P))) :
    Nonempty (LF.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) := by
  let := hε
  exact ⟨LF.mapIso ((DerivedCategory.quotientCompQhIso C).app P).symm ≪≫
    asIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)) ≪≫
    (DerivedCategory.quotientCompQhIso D).app _⟩

private theorem chosenCounit_modelIso
    {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{u + 2} C] [HasDerivedCategory.{u + 2} D]
    (F : C ⥤ D) [F.Additive]
    (r : ∀ (LF : DerivedCategory C ⥤ DerivedCategory D),
      (DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) → Prop)
    (H : ∃ LF ε, r LF ε) (P : CochainComplex C ℤ)
    (h : ∀ LF ε, r LF ε →
      IsIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P))) :
    Nonempty (H.choose.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) := by
  exact homotopyCounit_modelIso F H.choose H.choose_spec.choose P
    (h _ _ H.choose_spec.choose_spec)

attribute [local irreducible] flatModelReductionData flatModelReductionDerivedData
  Functor.mapHomotopyCategory DerivedCategory.Qh DerivedCategory.Q
  SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom

private theorem reductionChange_modelIso
    (P : CochainComplex (proEtaleRingModules T
      (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) ℤ)
    (hk : P.IsKFlatIndependentCoefficients) :
    Nonempty ((flatModelReduction l E m n hmn T).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((flatModelReductionChange l E m n hmn T).mapHomologicalComplex (.up ℤ)).obj P)) := by
  let := HasDerivedCategory.standard
    (proEtaleRingModules T (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)))
  let := HasDerivedCategory.standard
    (proEtaleRingModules T (proEtaleConstantRing T (Padic.coefficientExtensionRing l E m)))
  exact chosenCounit_modelIso (flatModelReductionChange l E m n hmn T) _
    (flatModelReductionDerivedData l E m n hmn T) P
    (fun _ _ h ↦ h.2.2 P hk)


attribute [local irreducible] flatModelReductionChange flatModelReduction

/-- On the recorded pro-etale category, reduction of the supplied flat model is a flat
model in the same interval, and the derived reduction has that Tor amplitude.
Source: blueprint, sec-smooth-purity/sk-lem-sf-flat-model/
lem-sf-reduction-flat-model.md (blueprint: lem-sf-reduction-flat-model).

Proof:
1. The supplied model is bounded and termwise flat, hence K-flat by lem-sf-flat-model:
for every acyclic complex, tensor with each term is acyclic, and bounded totalization
preserves this acyclicity.
2. The universal change-of-rings counit therefore computes derived reduction on P by
its ordinary termwise scalar extension. Transport along the given isomorphism to K
produces the asserted isomorphism with K_m (def-weil-derived-tensor).
3. Each reduced term is flat over A_{E,m}: for an injection of A_{E,m}-module sheaves,
tensor associativity identifies its tensor with the reduced term with tensor by the
original A_{E,n}-flat term (lem-exc-constant-inverse-image-flat). Hence it stays injective.
4. Scalar extension sends zero to zero, so the support remains [a,b]. Tensoring this
bounded flat model with any test sheaf computes derived tensor and remains supported
in [a,b]; its cohomology vanishes outside that interval, as in lem-sf-flat-model.
The original amplitude hypothesis supplies the ordered-interval condition a ≤ b. -/
theorem finiteCoefficient_reduction_flatModel
    (_hm : 1 ≤ m) (hn : 1 ≤ n)
    [∀ x : T, Invertible (l : T.residueField x)]
    (K : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n))
    (_hK : intrinsicFiniteTorsionConstructible l E n hn T K)
    (a b : ℤ)
    (P : CochainComplex (proEtaleRingModules T
      (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) ℤ)
    (_hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
      (R := proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)) (P.X q))
    (_hsupp : ∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q))
    (_e : K ≅ DerivedCategory.Q.obj P) :
    (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
      (R := proEtaleConstantRing T (Padic.coefficientExtensionRing l E m))
      ((((flatModelReductionChange l E m n hmn T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).X q)) ∧
    (∀ q : ℤ, q < a ∨ b < q → IsZero
      ((((flatModelReductionChange l E m n hmn T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).X q)) ∧
    Nonempty ((flatModelReduction l E m n hmn T).obj K ≅ DerivedCategory.Q.obj
      (((flatModelReductionChange l E m n hmn T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) ∧
    (HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E n) K a b →
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E m)
        ((flatModelReduction l E m n hmn T).obj K) a b) := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let R := proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)
  let S := proEtaleConstantRing T (Padic.coefficientExtensionRing l E m)
  let F := flatModelReductionChange l E m n hmn T
  let Pm : CochainComplex (proEtaleRingModules T S) ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj P
  have hle : P.IsStrictlyLE b :=
    (P.isStrictlyLE_iff b).2 (fun q hq ↦ _hsupp q (.inr hq))
  have hk := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R P b _hflat
  have hfm := changeOfRings_flat_terms (flatModelReductionRingMap l E m n hmn T)
    F (reductionChange_obj l E m n hmn T)
    (fun {M N} g ↦ reductionChange_map l E m n hmn T g) P hk _hflat
  have hsm (q : ℤ) (hq : q < a ∨ b < q) : IsZero (Pm.X q) :=
    F.map_isZero (_hsupp q hq)
  obtain ⟨ep⟩ := reductionChange_modelIso l E m n hmn T P hk
  let ei := (flatModelReduction l E m n hmn T).mapIso _e ≪≫ ep
  refine ⟨hfm, hsm, ⟨ei⟩, ?_⟩
  intro hamp
  exact proEtale_torAmplitude_of_flatModel T (Padic.coefficientExtensionRing l E m)
    a b hamp.1 _ Pm hfm hsm ei

end AlgebraicGeometry.Scheme

-- Use the same ring projection for generic rings and the lifted coefficient rings.
-- Otherwise conversion repeatedly normalizes the chosen coefficient subring.
attribute [local instance 2000] CommRing.toRing

namespace AlgebraicGeometry.Etale

private theorem etale_extension_flat
    (T : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hM : ObjectProperty.flat M) :
    ObjectProperty.flat ((Sheaf.composeAndSheafify T.smallEtaleTopology
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)).obj M) := by
  let F := Sheaf.composeAndSheafify T.smallEtaleTopology
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  apply (flat_iff_forall_flat_sheafFiber_obj _).2
  intro Ω _ _ t
  let p : T.smallEtaleTopology.Point.{u + 1} :=
    (Scheme.pointSmallEtale t).ulift.{u + 1}
  let E' : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S :=
    ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ
  let : E'.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint
  let W := (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj E'
  let V := sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)
  let a' := presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} S)
  let e : F ⋙ p.sheafFiber ≅ p.sheafFiber ⋙ E' :=
    Functor.associator V (W ⋙ a') p.sheafFiber ≪≫
      Functor.isoWhiskerLeft V (Functor.associator W a' p.sheafFiber) ≪≫
      Functor.isoWhiskerLeft V (Functor.isoWhiskerLeft W
        (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} S))) ≪≫
      Functor.isoWhiskerLeft V (p.presheafFiberCompIso E') ≪≫
      (Functor.associator V p.presheafFiber E').symm
  apply ObjectProperty.prop_of_iso _ (e.app M).symm
  apply (ModuleCat.flat_iff_flat _).2
  let := (ModuleCat.flat_iff_flat _).1
    ((flat_iff_forall_flat_sheafFiber_obj _).1 hM t)
  let := φ.toAlgebra
  exact Module.Flat.baseChange R S ((p.sheafFiber (A := ModuleCat.{u + 1} R)).obj M)

private theorem extension_tensor_comparison
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    [HasSheafify J (ModuleCat.{u + 1} R)] [HasSheafify J (ModuleCat.{u + 1} S)]
    [(J.W (A := ModuleCat.{u + 1} R)).IsMonoidal]
    (φ : R →+* S) :
    Nonempty (Sheaf.composeAndSheafify J
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ) ⋙ Sheaf.restrictScalars J φ ≅
      tensorRight ((constantSheaf J (ModuleCat.{u + 1} R)).obj
        ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S)))) := by
  let F := Sheaf.composeAndSheafify J
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  let U := Sheaf.restrictScalars J φ
  let B := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S)
  let coeff := (Functor.const Cᵒᵖ).obj B
  let V := sheafToPresheaf J (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} S)
  let aR := presheafToSheaf J (ModuleCat.{u + 1} R)
  have : J.PreservesSheafification
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let VU := (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
  let adjS := sheafificationAdjunction J (ModuleCat.{u + 1} S)
  let adjR := sheafificationAdjunction J (ModuleCat.{u + 1} R)
  let ea : a' ⋙ U ≅ VU ⋙ aR :=
    (sheafComposeNatIso J
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
      adjS adjR).symm
  let ew : W ⋙ VU ≅ tensorRight coeff :=
    Functor.whiskeringRightObjCompIso _ _ ≪≫
      (Functor.whiskeringRight _ _ _).mapIso
        (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} φ) ≪≫
      whiskeringRightTensorRightIso _
  let ec : V ⋙ aR ≅ 𝟭 _ :=
    asIso (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit
  let e : F ⋙ U ≅ tensorRight (aR.obj coeff) := calc
    F ⋙ U ≅ V ⋙ ((W ⋙ a') ⋙ U) := Functor.associator V (W ⋙ a') U
    _ ≅ V ⋙ (W ⋙ (a' ⋙ U)) :=
      Functor.isoWhiskerLeft V (Functor.associator W a' U)
    _ ≅ V ⋙ (W ⋙ (VU ⋙ aR)) :=
      Functor.isoWhiskerLeft V (Functor.isoWhiskerLeft W ea)
    _ ≅ V ⋙ ((W ⋙ VU) ⋙ aR) :=
      Functor.isoWhiskerLeft V (Functor.associator W VU aR).symm
    _ ≅ V ⋙ (tensorRight coeff ⋙ aR) :=
      Functor.isoWhiskerLeft V (Functor.isoWhiskerRight ew aR)
    _ ≅ V ⋙ (aR ⋙ tensorRight (aR.obj coeff)) :=
      Functor.isoWhiskerLeft V (Sheaf.presheafToSheafCompTensorRightIso coeff).symm
    _ ≅ (V ⋙ aR) ⋙ tensorRight (aR.obj coeff) :=
      (Functor.associator V aR (tensorRight (aR.obj coeff))).symm
    _ ≅ (𝟭 _) ⋙ tensorRight (aR.obj coeff) :=
      Functor.isoWhiskerRight ec (tensorRight (aR.obj coeff))
    _ ≅ tensorRight (aR.obj coeff) := Functor.leftUnitor _
  exact ⟨e⟩

private theorem mapDerived_modelIso
    {C D E : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    [Category.{u + 1} E] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory.{u + 1} D] [HasDerivedCategory.{u + 1} E]
    (F : C ⥤ D) (U : D ⥤ E) (G : C ⥤ E)
    [F.Additive] [U.Additive] [G.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (e : F ⋙ U ≅ G) (P : CochainComplex C ℤ) :
    Nonempty (U.mapDerivedCategory.obj
      (_root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≅
      _root_.DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P)) := by
  exact ⟨U.mapDerivedCategoryFactors.app _ ≪≫ _root_.DerivedCategory.Q.mapIso
    ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).app P)⟩

private theorem etale_model_from_extension
    (T : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S))
    (U : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    [F.Additive] [F.PreservesZeroMorphisms] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (coeff : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (ec : F ⋙ U ≅ tensorRight coeff)
    (hF : ∀ M, ObjectProperty.flat M → ObjectProperty.flat (F.obj M))
    (a b : ℤ) (K : DerivedCategoryModule R T)
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
    (hP : IsBoundedFlatComplex R a b P) (eK : K ≅ (_root_.DerivedCategory.Q).obj P) :
    let Pm := (F.mapHomologicalComplex (.up ℤ)).obj P
    IsBoundedFlatComplex S a b Pm ∧
      Nonempty (U.mapDerivedCategory.obj ((_root_.DerivedCategory.Q).obj Pm) ≅
        ((derivedTensor (ModuleCat.{u + 1} R) T).obj K).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj coeff)) ∧
      DerivedCategory.hasTorAmplitudeIn S T a b ((_root_.DerivedCategory.Q).obj Pm) := by
  let Pm : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S)) ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj P
  obtain ⟨hge, hle, hf⟩ := isBoundedFlatComplex_iff.1 hP
  have hfm (q : ℤ) : ObjectProperty.flat (Pm.X q) := hF (P.X q) (hf q)
  let := hge
  let := hle
  have hmge : Pm.IsStrictlyGE a := inferInstance
  have hmle : Pm.IsStrictlyLE b := inferInstance
  refine ⟨isBoundedFlatComplex_iff.2 ⟨hmge, hmle, hfm⟩, ?_, ?_⟩
  · let t := derivedTensorQObjSingleFunctorObjIso (a := a) (b := b) P hf coeff
    let k := (((derivedTensor (ModuleCat.{u + 1} R) T).mapIso eK).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj coeff)).symm
    obtain ⟨q⟩ := mapDerived_modelIso F U (tensorRight coeff) ec P
    exact ⟨q ≪≫ t.symm ≪≫ k⟩
  · exact DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat Pm a b hfm)


private theorem etale_reduction_model
    (T : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (a b : ℤ) (K : DerivedCategoryModule R T)
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
    (hP : IsBoundedFlatComplex R a b P) (eK : K ≅ (_root_.DerivedCategory.Q).obj P) :
    let F := Sheaf.composeAndSheafify T.smallEtaleTopology
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
    letI : F.Additive := (Sheaf.adjunction T.smallEtaleTopology
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)).left_adjoint_additive
    letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
    let Pm := (F.mapHomologicalComplex (.up ℤ)).obj P
    IsBoundedFlatComplex S a b Pm ∧
      Nonempty ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategory.obj
        ((_root_.DerivedCategory.Q).obj Pm) ≅
        ((derivedTensor (ModuleCat.{u + 1} R) T).obj K).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
              ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj
                (ModuleCat.of S S))))) ∧
      DerivedCategory.hasTorAmplitudeIn S T a b ((_root_.DerivedCategory.Q).obj Pm) := by
  let F := Sheaf.composeAndSheafify T.smallEtaleTopology
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  have : F.Additive := (Sheaf.adjunction T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)).left_adjoint_additive
  have : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  have : U.Additive := inferInstance
  have : PreservesFiniteLimits U := inferInstance
  have : PreservesFiniteColimits U := inferInstance
  let coeff := (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
    ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S))
  have : (T.smallEtaleTopology.W (A := ModuleCat.{u + 1} R)).IsMonoidal := inferInstance
  obtain ⟨ec⟩ := extension_tensor_comparison
    (C := T.Etale) (R := R) (S := S) T.smallEtaleTopology φ
  exact etale_model_from_extension T F U coeff ec
    (fun M hM ↦ etale_extension_flat T φ M hM) a b K P hP eK


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (m n : ℕ) (hmn : m ≤ n) (T : Scheme.{u})

/-- Ordinary scalar extension on etale module sheaves: extend scalars on the underlying
presheaf and sheafify, with the induced tensor differentials on complexes.
Source: blueprint, lem-sf-reduction-flat-model.md, ordinary tensor model
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def etaleFlatModelReductionChange :
    Sheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) ⥤
      Sheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))) :=
  sheafToPresheaf _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (Scheme.flatModelReductionCoefficientMap l E m n hmn)) ⋙
    presheafToSheaf _ _

/-- Additivity inherited from presheaf scalar extension and sheafification.
Source: Stacks Tag 03EK; blueprint, lem-sf-reduction-flat-model.md
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable instance etaleFlatModelReductionChange_additive :
    (etaleFlatModelReductionChange l E m n hmn T).Additive :=
  letI : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (Scheme.flatModelReductionCoefficientMap l E m n hmn)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      (Scheme.flatModelReductionCoefficientMap l E m n hmn)).left_adjoint_additive
  inferInstanceAs ((sheafToPresheaf _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (Scheme.flatModelReductionCoefficientMap l E m n hmn)) ⋙
    presheafToSheaf _ _).Additive)

/-- Reduction of an etale flat model over the actual finite coefficient stages.
The derived tensor on the right of the comparison retains the original scalars;
the displayed scalar-restriction functor identifies its quotient-ring model.
Source: blueprint, lem-sf-reduction-flat-model.md, etale clause
(blueprint: lem-sf-reduction-flat-model).

Proof:
1. The bounded flat P is K-flat (lem-sf-flat-model), since tensoring an acyclic
complex with each flat term is exact and the bounded total complex is acyclic.
2. K-flat computation of derived tensor (def-weil-derived-tensor) identifies K_m
with ordinary termwise scalar extension, regarded with the original scalars.
3. For any injection of modules over A_{E,m}, tensor associativity identifies its
tensor by each reduced term with tensor by the original flat term. This preserves
injections (lem-exc-constant-inverse-image-flat), hence the terms are A_{E,m}-flat.
4. Scalar extension is additive and preserves zero, so the same degree interval
supports the reduced model. Its bounded flatness gives the final Tor amplitude by
lem-sf-flat-model. No constructibility of the terms of P is required. -/
theorem finiteCoefficient_etale_reduction_flatModel
    (_hm : 1 ≤ m) (hn : 1 ≤ n)
    [∀ x : T, Invertible (l : T.residueField x)]
    (K : DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T)
    (_hK : @DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n hn)) T K)
    (a b : ℤ)
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))) ℤ)
    (_hP : IsBoundedFlatComplex
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) a b P)
    (_e : K ≅ (_root_.DerivedCategory.Q).obj P) :
    IsBoundedFlatComplex (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)) a b
      (((etaleFlatModelReductionChange l E m n hmn T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ∧
    Nonempty ((Sheaf.restrictScalars T.smallEtaleTopology
      (Scheme.flatModelReductionCoefficientMap l E m n hmn)).mapDerivedCategory.obj
        ((_root_.DerivedCategory.Q).obj
          (((etaleFlatModelReductionChange l E m n hmn T).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) ≅
      ((derivedTensor (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) T).obj K).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1}
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))).obj
              ((ModuleCat.restrictScalars
                (Scheme.flatModelReductionCoefficientMap l E m n hmn)).obj
                (ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))
                  (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))))))) ∧
    DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)) T a b
      ((_root_.DerivedCategory.Q).obj
        (((etaleFlatModelReductionChange l E m n hmn T).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) := by
  exact etale_reduction_model T (Scheme.flatModelReductionCoefficientMap l E m n hmn)
    a b K P _hP _e

end AlgebraicGeometry.Etale
