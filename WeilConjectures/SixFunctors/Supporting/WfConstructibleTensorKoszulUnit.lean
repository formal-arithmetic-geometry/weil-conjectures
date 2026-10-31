/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Supporting.PbcWeilCategory
public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedQuotientUnitNormalization
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionProfile
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
import all WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralDetailedFiniteReduction
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import all WeilConjectures.SixFunctors.ProjectionTensorCoefficient.ProjectionCoefficientTensorTotal
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated

/-!
# Constructible tensor and its normalized Koszul completion unit

Source: blueprint sec-six-functors/sk-rem-sf-pf-done,
fix-prop-projection-formula.proof.md, Weil-equivariance sentence;
Bhatt--Scholze, Lemma 6.5.5 and Proposition 6.6.11; Stacks Tags 099M and 0A0E
(blueprint: lem-wf-constructible-tensor-koszul-unit).

The statements retain the actual quotient augmentation and intrinsic (u,0) unit.
The coefficient comparison is the published projection-normalized transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem transported_tensor_constructible
    (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [QuasiSeparatedSpace X]
    [∀ x : X, Invertible (l : X.residueField x)]
    [IsNoetherian X] (hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (hunit : IsUnit (l : Γ(X, ⊤)))
    (M N : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)) :
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((wfOrdinaryDerivedTensor X (pbcIntegralDatum l E)).obj (M.obj, N.obj)) := by
  have hInv (x : X) : IsUnit (l : X.presheaf.stalk x) := by
    simpa only [map_natCast] using hunit.map (X.presheaf.germ ⊤ x trivial).hom
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) :=
    (pbcIntegralUniformComplete_isTriangulated l E X hdim hInv).1
  let Φ := purCoefficientModel l E X
  let K := Φ.functor.obj M.obj
  let L := Φ.functor.obj N.obj
  have hK : sfIntegralConstructible l E X K := by
    apply (integralStratifiedPerfectDetailed X l E hdim hunit K).mpr
    exact ObjectProperty.prop_of_iso
      (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
      (Φ.unitIso.app M.obj) M.property
  have hL : sfIntegralConstructible l E X L := by
    apply (integralStratifiedPerfectDetailed X l E hdim hunit L).mpr
    exact ObjectProperty.prop_of_iso
      (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
      (Φ.unitIso.app N.obj) N.property
  obtain ⟨T, e, _, _, _, tau, _, htau⟩ := constructibleTensorCompletion l E X
  have hτ := (htau K L hK hL).2
  have hc := ((integralOperations_preserve_constructible l E (𝟙 X)).2
    X (Or.inl rfl) K L hK hL).1
  have hT : sfIntegralConstructible l E X (T.obj (K, L)) :=
    (sfIntegralConstructible l E X).prop_of_iso (asIso (tau.app (K, L))).symm hc
  have hresult := (integralStratifiedPerfectDetailed X l E hdim hunit _).mp hT
  obtain ⟨P, ⟨eP⟩⟩ := goodRepresentative l E X K
  obtain ⟨Q, ⟨eQ⟩⟩ := goodRepresentative l E X L
  let F := fdCoefficientTransport l E X
  let G := ProjectionTensorCoefficient.complexTransport l E X
  let transport := (SheafOfModules.ringIso_tensor_transport
    (ProjectionTensorCoefficient.coefficientIso l E X)).some
  have hgood (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
      proEtaleFlatRepresentatives X (pbcAdicCompletion X (pbcIntegralDatum l E))
        (G.obj P.obj) := by
    constructor
    · exact (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp
        ((transport.kflat_iff P.obj).mpr P.property.1)
    · intro n
      exact (transport.flat_iff (P.obj.X n)).mpr (P.property.2 n)
  let P' : (proEtaleFlatRepresentatives X
      (pbcAdicCompletion X (pbcIntegralDatum l E))).FullSubcategory := ⟨_, hgood P⟩
  let Q' : (proEtaleFlatRepresentatives X
      (pbcAdicCompletion X (pbcIntegralDatum l E))).FullSubcategory := ⟨_, hgood Q⟩
  let i : (integralDetailedTransport X l E).obj (T.obj (K, L)) ≅
      (wfOrdinaryDerivedTensor X (pbcIntegralDatum l E)).obj (M.obj, N.obj) :=
    (integralDetailedTransport X l E).mapIso
        ((T.mapIso (Iso.prod eP eQ)).symm ≪≫ (e.app (P, Q)).symm) ≪≫
      F.mapDerivedCategoryFactors.app ((constructibleTensorTotal l E X).obj (P.obj, Q.obj)) ≪≫
      DerivedCategory.Q.mapIso (ProjectionTensorCoefficient.totalIso l E X P.obj Q.obj) ≪≫
      (wfTensorModel X (pbcIntegralDatum l E)).representative.app (P', Q') ≪≫
      (wfOrdinaryDerivedTensor X (pbcIntegralDatum l E)).mapIso
        (Iso.prod
          ((F.mapDerivedCategoryFactors.app P.obj).symm ≪≫
            (integralDetailedTransport X l E).mapIso eP ≪≫ (Φ.unitIso.app M.obj).symm)
          ((F.mapDerivedCategoryFactors.app Q.obj).symm ≪≫
            (integralDetailedTransport X l E).mapIso eQ ≪≫ (Φ.unitIso.app N.obj).symm))
  exact ObjectProperty.prop_of_iso
    (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) i hresult

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (W₀ : Over (Spec (.of D.k₀))) [hsep : IsSeparated W₀.hom]
  [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)

include hsep

/-- The integral full subcategories coincide, with the same positive reductions after
canonical coefficient transport.
Source: Bhatt--Scholze, Proposition 6.6.11 and Section 6.5
(blueprint: lem-wf-constructible-tensor-koszul-unit).
Proof (step 1): separated finite type is preserved by geometric base change. Over a
field the resulting scheme is qcqs, Noetherian and finite-dimensional, and ell is
invertible since ell differs from p. Apply integralStratifiedPerfectDetailed.
The coefficient comparison is fixed by every finite quotient projection. Its exact
scalar restriction identifies the derived quotient extensions, so these are the same
reduction functors and the same full subcategory of the completed-coefficient D(B). -/
theorem wfConstructibleTensorCategories :
    (∀ K : DerivedCategory
        (scalarReductionSource.{u, u} c.l (pbcFiniteField.{u} c.l c.Qbar E)
          (D.geometricFiber W₀).left),
      sfIntegralConstructible c.l (pbcFiniteField.{u} c.l c.Qbar E)
          (D.geometricFiber W₀).left K ↔
        PbcIsBoundedConstructibleComplete (D.geometricFiber W₀).left
          (pbcStageDatum.{u} c.l c.Qbar E)
          ((integralDetailedTransport (D.geometricFiber W₀).left c.l
            (pbcFiniteField.{u} c.l c.Qbar E)).obj K)) ∧
    ∀ n : ℕ, Nonempty
      (integralDetailedTransport (D.geometricFiber W₀).left c.l
          (pbcFiniteField.{u} c.l c.Qbar E) ⋙
          pbcConstantReduction (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E) n ≅
        scalarReductionDerivedExtension.{u, u} c.l (pbcFiniteField.{u} c.l c.Qbar E)
          (D.geometricFiber W₀).left n ⋙
          pbcDerivedRestrict
            ((constantSheaf (ProEt.topology (D.geometricFiber W₀).left) CommRingCat.{u + 1}).map
              (integralCoefficientULift c.l (pbcFiniteField.{u} c.l c.Qbar E)
                n).toCommRingCatIso.hom)) := by
  obtain ⟨hnoeth, hdim, hinv⟩ := weilGeometricFiber_coefficientHypotheses D c W₀
  have : IsNoetherian (D.geometricFiber W₀).left := hnoeth
  have hunit : IsUnit (c.l : Γ((D.geometricFiber W₀).left, ⊤)) := by
    apply (D.geometricFiber W₀).left.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using hinv x
  exact ⟨fun K ↦ integralStratifiedPerfectDetailed _ c.l _ hdim hunit K,
    fun n ↦ ⟨detailedFiniteComparison _ c.l _ n⟩⟩

/-- The natural quotient/Koszul isomorphism carries the actual quotient unit to
exactly the specified intrinsic unit, including its zero shifted-product component.
Source: Stacks Tags 099L, 099M and 0A0E
(blueprint: lem-wf-constructible-tensor-koszul-unit).
Proof (steps 2--3): identify the whole strict quotient tensor tower with the completed
tensor tower by scalar reassociation, sending ((u tensor v) tensor a) to
(u tensor a) tensor (v tensor 1); the inverse multiplies the quotient scalars.
The augmentation clause of integralAmbientOperationModels preserves the quotient unit
and the zero shifted coordinate. The constant-completion equivalence compares the
quotient tower with the Koszul tower and their degree-zero inclusions. Apply its inverse
comparison to obtain the direction displayed here. Functoriality of strict derived
inverse limit gives naturality on all derived arrows. Thus the comparison carries the
actual quotient augmentation to the actual (u,0) intrinsic completion unit. -/
theorem wfConstructibleTensorKoszulComparison :
    ∃ ρ : completedReductionTower (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E) ⋙
        completedRlim (D.geometricFiber W₀).left
          ((pbcStageDatum.{u} c.l c.Qbar E).completedRing (D.geometricFiber W₀).left) ≅
      wfCompletion (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E) 1
        (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) ⋙ ObjectProperty.ι _,
      ∀ K : PbcCompletedDerived (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E),
        (completedQuotientCompletionUnit (D.geometricFiber W₀).left
            (pbcStageDatum.{u} c.l c.Qbar E)).app K ≫ ρ.hom.app K =
          wfCompletionUnit (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E) 1
            (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
            (wfUniformizer_generates D c E) K := by
  classical
  let X := (D.geometricFiber W₀).left
  let d := pbcStageDatum.{u} c.l c.Qbar E
  let a := fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E
  let ha := wfUniformizer_generates D c E
  let Q : PbcCompletedDerived X d ⥤ PbcCompletedDerived X d :=
    completedReductionTower X d ⋙ completedRlim X (d.completedRing X)
  let F := wfCompletion X d 1 a ha
  let η : 𝟭 (PbcCompletedDerived X d) ⟶ Q := completedQuotientCompletionUnit X d
  have hc (K : PbcCompletedDerived X d) :
      ∃ e : wfCompletionObj X d 1 a ha K ≅ Q.obj K,
        wfCompletionUnit X d 1 a ha K ≫ e.hom = η.app K := by
    obtain ⟨e, he⟩ := completedKoszulQuotientComparison X d 1 a ha K
      (wfCompletionRepresentative X d K) (DerivedCategory.Q.objObjPreimageIso K)
    refine ⟨e, ?_⟩
    simpa only [η, completedQuotientCompletionUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, wfCompletionUnit] using he
  choose e he using hc
  have hn {K L : PbcCompletedDerived X d} (f : K ⟶ L) :
      wfCompletionUnit X d 1 a ha K ≫ (F.map f).hom =
        f ≫ wfCompletionUnit X d 1 a ha L := by
    exact (Equiv.ofBijective _ ((wfCompletionReflector X d 1 a ha).2 K
      (wfCompletionObj X d 1 a ha L) ((wfCompletionReflector X d 1 a ha).1 L)
        )).apply_symm_apply _
  have hρ (K : PbcCompletedDerived X d) :
      η.app K ≫ (e K).inv = wfCompletionUnit X d 1 a ha K := by
    rw [← he K, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let ρ : Q ≅ F ⋙ ObjectProperty.ι _ := NatIso.ofComponents (fun K ↦ (e K).symm) (by
    intro K L f
    apply (cancel_epi (e K).hom).mp
    apply ((wfCompletionReflector X d 1 a ha).2 K
      (wfCompletionObj X d 1 a ha L) ((wfCompletionReflector X d 1 a ha).1 L)).1
    change wfCompletionUnit X d 1 a ha K ≫
        ((e K).hom ≫ (Q.map f ≫ (e L).inv)) =
      wfCompletionUnit X d 1 a ha K ≫
        ((e K).hom ≫ ((e K).inv ≫ (F.map f).hom))
    rw [← Category.assoc, he]
    have hnη : f ≫ η.app L = η.app K ≫ Q.map f := η.naturality f
    calc
      η.app K ≫ Q.map f ≫ (e L).inv = (η.app K ≫ Q.map f) ≫ (e L).inv :=
        (Category.assoc _ _ _).symm
      _ = (f ≫ η.app L) ≫ (e L).inv := congrArg (· ≫ (e L).inv) hnη.symm
      _ = f ≫ wfCompletionUnit X d 1 a ha L := by rw [Category.assoc, hρ]
      _ = wfCompletionUnit X d 1 a ha K ≫ (F.map f).hom := (hn f).symm
      _ = _ := by simp only [Iso.hom_inv_id_assoc])
  exact (fun (_ : IsSeparated W₀.hom) ↦ ⟨ρ, hρ⟩) hsep

/-- Ordinary tensor and its intrinsic completion are bounded constructible; the
specified intrinsic unit is invertible and natural for arbitrary integral arrows.
Source: Bhatt--Scholze, Lemma 6.5.5; Stacks Tags 099B and 0A0E
(blueprint: lem-wf-constructible-tensor-koszul-unit).
Proof (steps 1--5): the category identification in step 1 permits application of
constructibleTensorCompletion. Its quotient comparison is invertible; strict scalar
reassociation identifies it with the quotient unit used here (step 2). The natural
quotient/Koszul comparison of step 3 identifies that unit with the intrinsic unit.
IntegralOperationsPreserveConstructible applied to the identity morphism makes the
completed tensor constructible. Transfer the retained bounds, strata, local models,
compatible etale witnesses and their cocycles along the normalized isomorphisms to
obtain constructibility of the ordinary and Koszul tensors (step 4). Finally the Koszul
degree-zero inclusions commute with tensor of any two integral arrows; the induced
product/fiber map carries (u,0) to (u',0). Localization and the reflector unit's
naturality give the displayed equation, without any invertibility assumption on f,g. -/
theorem wfConstructibleTensorKoszulUnit :
    (∀ M N : PbcBoundedConstructibleComplete (D.geometricFiber W₀).left
        (pbcStageDatum.{u} c.l c.Qbar E),
      PbcIsBoundedConstructibleComplete (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E)
        ((wfOrdinaryDerivedTensor (D.geometricFiber W₀).left
          (pbcStageDatum.{u} c.l c.Qbar E)).obj (M.obj, N.obj)) ∧
      PbcIsBoundedConstructibleComplete (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E)
        ((wfCompletion (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E) 1
            (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
            (wfUniformizer_generates D c E)).obj
          ((wfOrdinaryDerivedTensor (D.geometricFiber W₀).left
            (pbcStageDatum.{u} c.l c.Qbar E)).obj (M.obj, N.obj))).obj ∧
      IsIso (wfCompletionUnit (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E) 1
        (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E)
        ((wfOrdinaryDerivedTensor (D.geometricFiber W₀).left
          (pbcStageDatum.{u} c.l c.Qbar E)).obj (M.obj, N.obj)))) ∧
    ∀ (M M' N N' : PbcBoundedConstructibleComplete (D.geometricFiber W₀).left
        (pbcStageDatum.{u} c.l c.Qbar E)) (f : M ⟶ M') (g : N ⟶ N'),
      (wfOrdinaryDerivedTensor (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E)).map
          (Prod.mkHom f.hom g.hom) ≫
        wfCompletionUnit (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E) 1
          (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
          (wfUniformizer_generates D c E)
          ((wfOrdinaryDerivedTensor (D.geometricFiber W₀).left
            (pbcStageDatum.{u} c.l c.Qbar E)).obj (M'.obj, N'.obj)) =
      wfCompletionUnit (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E) 1
          (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
          (wfUniformizer_generates D c E)
          ((wfOrdinaryDerivedTensor (D.geometricFiber W₀).left
            (pbcStageDatum.{u} c.l c.Qbar E)).obj (M.obj, N.obj)) ≫
        ((wfCompletion (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E) 1
            (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
            (wfUniformizer_generates D c E)).map
          ((wfOrdinaryDerivedTensor (D.geometricFiber W₀).left (pbcStageDatum.{u} c.l c.Qbar E)).map
            (Prod.mkHom f.hom g.hom))).hom := by
  classical
  let X := (D.geometricFiber W₀).left
  let d := pbcStageDatum.{u} c.l c.Qbar E
  let a := fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E
  let ha := wfUniformizer_generates D c E
  obtain ⟨hnoeth, hdim, hinv⟩ := weilGeometricFiber_coefficientHypotheses D c W₀
  have : IsNoetherian X := hnoeth
  have hunit : IsUnit (c.l : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using hinv x
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (PbcIsBoundedConstructibleComplete X d) :=
    (pbcIntegralUniformComplete_isTriangulated c.l
      (pbcFiniteField.{u} c.l c.Qbar E) X hdim hinv).1
  have hnatural {K L : PbcCompletedDerived X d} (f : K ⟶ L) :
      wfCompletionUnit X d 1 a ha K ≫ ((wfCompletion X d 1 a ha).map f).hom =
        f ≫ wfCompletionUnit X d 1 a ha L := by
    exact (Equiv.ofBijective _ ((wfCompletionReflector X d 1 a ha).2 K
      (wfCompletionObj X d 1 a ha L) ((wfCompletionReflector X d 1 a ha).1 L)
        )).apply_symm_apply _
  constructor
  · intro M N
    have : ∀ x : X, Invertible (c.l : X.residueField x) :=
      fun x ↦ (show IsUnit (c.l : X.residueField x) from by
        simpa only [map_natCast] using hunit.map (X.Γevaluation x).hom).invertible
    have hT := transported_tensor_constructible X c.l
      (pbcFiniteField.{u} c.l c.Qbar E) hdim hunit M N
    have hη : IsIso (wfCompletionUnit X d 1 a ha
        ((wfOrdinaryDerivedTensor X d).obj (M.obj, N.obj))) :=
      wfConstructible_complete X d 1 a ha ⟨_, hT⟩
    exact ⟨hT, ObjectProperty.prop_of_iso (PbcIsBoundedConstructibleComplete X d)
      (asIso (wfCompletionUnit X d 1 a ha _)) hT, hη⟩
  · intro M M' N N' f g
    exact (hnatural ((wfOrdinaryDerivedTensor X d).map (Prod.mkHom f.hom g.hom))).symm

end WeilConjectures
