/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Dualizing unit and composite tensor identifications

Source: main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality.proof.md, Step 1
(blueprint: lem-pur-dualizing-unit-composite).

We use the canonical etale-origin coordinates of def-pur-co-smoothness. In these
coordinates the published tensor transpose has source W tensor pullback K: it already
includes the symmetry in the node's definition of sigma. The exceptional compositor
is the published conjugate of the actual compact-support compositor. Comparison
pullback identifies these maps with the maps on the small pro-etale Dctf categories.
The rho hypothesis below is restricted to Dctf, not to an ambient derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

/-- A right-unital projection has the canonical tensor transpose at the unit.
This is the unit/counit calculation used in Step 1
(blueprint: lem-pur-dualizing-unit-composite). -/
private theorem projection_tensor_unit
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : D ⥤ C} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N))
    [∀ M N, IsIso (π M N)] (u : F.obj (𝟙_ D) ≅ 𝟙_ C)
    (hπ : π (R.obj (𝟙_ D)) (𝟙_ D) ≫
      L.map (R.obj (𝟙_ D) ◁ u.hom ≫ (ρ_ (R.obj (𝟙_ D))).hom) =
        (ρ_ (L.obj (R.obj (𝟙_ D)))).hom) :
    adj.projectionTensorMap π (𝟙_ D) (𝟙_ D) ≫ R.map (λ_ (𝟙_ D)).hom =
      R.obj (𝟙_ D) ◁ u.hom ≫ (ρ_ (R.obj (𝟙_ D))).hom := by
  apply Adjunction.ext_of_comp_counit (adj := adj)
  rw [Functor.map_comp, Category.assoc]
  erw [adj.counit_naturality]
  rw [Adjunction.map_projectionTensorMap_comp_counit_assoc]
  apply (cancel_epi (π (R.obj (𝟙_ D)) (𝟙_ D))).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, hπ]
  simpa only [Functor.comp_obj, Functor.id_obj, unitors_equal] using
    (rightUnitor_naturality (adj.counit.app (𝟙_ D)))

universe uA
section TensorHelpers
open AlgebraicGeometry.Etale
open scoped AlgebraicGeometry.Etale
variable {A : Type uA} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f] [IsIso (projectionMap A f)]
  {G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (adj : R(f)_![A] ⊣ G)

/-- Specialize the formal unit calculation to the published etale projection.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite). -/
private theorem tensor_unit :
    lowerShriekRightAdjointUnitTensorMap adj (𝟙_ _) =
      (G.obj (𝟙_ _)) ◁ (leftDerivedUpperStarUnitIso A f).hom ≫
        (ρ_ (G.obj (𝟙_ _))).hom := by
  exact projection_tensor_unit adj
    (fun M N ↦ ((projectionMap A f).app M).app N)
    (leftDerivedUpperStarUnitIso A f) (projectionMap_rightUnitality A f _)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the specified transpose in its coefficient input.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite). -/
private theorem tensor_naturality
    {K L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (v : K ⟶ L) :
    (G.obj (𝟙_ _)) ◁ (L((f)^*[A])).map v ≫
        lowerShriekRightAdjointUnitTensorMap adj L =
      lowerShriekRightAdjointUnitTensorMap adj K ≫ G.map v := by
  have hn := adj.projectionTensorMap_naturality_right
    (fun M N ↦ ((projectionMap A f).app M).app N)
    (fun M _ _ v ↦ ((projectionMap A f).app M).naturality v) (𝟙_ _) v
  dsimp only [lowerShriekRightAdjointUnitTensorMap, lowerShriekRightAdjointTensorMap]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    leftUnitor_naturality, Functor.map_comp, Category.assoc]

end TensorHelpers

namespace WeilConjectures.PurityFiniteSetting

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The coefficient unit as an object of Dctf in the canonical etale coordinates.
Its property is assembled from the existing constructible-single and flat-single results.
Source: purity conventions, coefficient unit (blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingUnitModel (X : Scheme.{u}) :
    Etale.DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  ⟨𝟙_ _,
    (Etale.DerivedCategory.boundedConstructible _ X).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0),
    0, 0, (Etale.DerivedCategory.torAmplitudeIn _ X 0 0).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩

/-- The coefficient-unit component of the specified exceptional conjugate.
Source: Step 1, c at A (blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingCompositeConjugate {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [HasCompactification a] [HasCompactification b] [HasCompactification (a ≫ b)]
    [QuasiCompact a] [QuasiCompact (a ≫ b)] :
    Etale.dualizingComplex Λ (a ≫ b) ≅
      (Etale.rightDerivedUpperShriek Λ a).obj
        (Etale.dualizingComplex Λ b) :=
  (finiteExceptionalComposition Λ a b).app
    (𝟙_ (_root_.DerivedCategory (Sheaf Z.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))))

/-- The specified sigma, with the tensor-transpose symmetry already included upstream.
Source: Step 1, dualizing composition formula
(blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingCompositeSigma {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [HasCompactification a] [HasCompactification b] [HasCompactification (a ≫ b)]
    [QuasiCompact a] [QuasiCompact (a ≫ b)] :
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (Etale.dualizingComplex Λ a)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor.obj
          (Etale.dualizingComplex Λ b)) ⟶
      Etale.dualizingComplex Λ (a ≫ b) :=
  Etale.dualizingComplexTensorMap Λ a
      (Etale.dualizingComplex Λ b) ≫
    (dualizingCompositeConjugate Λ a b).inv

/-- The specified t for any trivialization eta, including the pullback-unit comparison.
Source: Step 1, arbitrary trivialization formula
(blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingCompositeTrivialization {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [HasCompactification a] [HasCompactification b]
    (eta : Etale.dualizingComplex Λ b ≅ 𝟙_ _) :
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (Etale.dualizingComplex Λ a)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor.obj
          (Etale.dualizingComplex Λ b)) ≅
      Etale.dualizingComplex Λ a :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (Etale.dualizingComplex Λ a)).mapIso
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor.mapIso eta ≪≫
        Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) a) ≪≫
    Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) X
      (Etale.dualizingComplex Λ a)

/-- Unit normalization of the specified counit transpose, in W-first coordinates.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite).
Proof: the proper projection mate at the coefficient unit is the identity after unit
comparisons (lem-weil-pbc-ringed-projection-mate-exact). The normalized open projection
has the same property by adjunct uniqueness (lem-sf-open-tensor-normalization). Their
compactification composite therefore has this property. Transpose its inverse followed
by the counit. The adjunction triangle identifies the result with the displayed unitor.
No separatedness of either scheme over k is used. Apply open restriction to the equality;
functoriality and the stipulated operation/unit comparisons identify the result with
the restricted formula (node proof Step 7). -/
def dualizingUnitAssertion {X Y : Scheme.{u}} (a : X ⟶ Y)
    [HasCompactification a] : Prop :=
    Etale.dualizingComplexTensorMap Λ a (𝟙_ _) =
      ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        (Etale.dualizingComplex Λ a)).map
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) a).hom ≫
      (Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) X
            (Etale.dualizingComplex Λ a)).hom ∧
    ∀ (V : Scheme.{u}) (j : V ⟶ X) [IsOpenImmersion j],
      (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
          (Etale.dualizingComplexTensorMap Λ a (𝟙_ _)) =
        (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
          (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
            (Etale.dualizingComplex Λ a)).map
            (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) a).hom) ≫
        (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
          (Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) X
            (Etale.dualizingComplex Λ a)).hom

/-- The specified inverse formula for every eta, without a normalization on eta.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite).
Proof: inverse-projection naturality gives G(v) theta_K = theta_L (P(v) tensor 1).
Transpose using def-weil-exceptional-inverse-image. Apply this to eta and use the unit
normalization just above. Cancel the conjugate compositor c to obtain
sigma followed by c followed by G(eta) = t. Both t and c followed by G(eta) are
invertible, hence sigma is invertible. Postcompose this equality by its inverse.
The compact-support compositor and its conjugate are isomorphisms by
thm-sf-comp-composition and def-weil-pbc-adjunction-conjugate. The finite projection
formula supplies precisely the natural invertible projection components used here.
For open restriction, apply its functor to the equation and both inverse equations;
compatibility of the given data identifies these with the restricted maps (Step 7). -/
def dualizingInverseAssertion {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [HasCompactification a] [HasCompactification b] [HasCompactification (a ≫ b)]
    [QuasiCompact a] [QuasiCompact (a ≫ b)]
    (eta : Etale.dualizingComplex Λ b ≅ 𝟙_ _) : Prop :=
    ∃ s :
      ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        (Etale.dualizingComplex Λ a)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor.obj
            (Etale.dualizingComplex Λ b)) ≅
        Etale.dualizingComplex Λ (a ≫ b),
      s.hom = dualizingCompositeSigma Λ a b ∧
        s.inv ≫ (dualizingCompositeTrivialization Λ a b eta).hom =
          (dualizingCompositeConjugate Λ a b).hom ≫
            (Etale.rightDerivedUpperShriek Λ a).map eta.hom ∧
        ∀ (V : Scheme.{u}) (j : V ⟶ X) [IsOpenImmersion j],
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.mapIso s).inv ≫
              (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
                (dualizingCompositeTrivialization Λ a b eta).hom =
            (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
                ((dualizingCompositeConjugate Λ a b).hom) ≫
              (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
                ((Etale.rightDerivedUpperShriek Λ a).map
                  eta.hom)

/-- The dualizing object as an object of the stated finite-Tor constructible domain.
This is the existing exceptional preservation theorem applied to the coefficient unit.
Source: purity conventions and Dctf stability
(blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingCompositeModel (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    Etale.DerivedCategoryFiniteTor (ModuleCat.{u + 1} P.Coefficient) X :=
  letI := finiteComparedInvertibleExponent P aY
  ⟨Etale.dualizingComplex P.Coefficient f,
    Etale.constructibleFiniteTor_dualizingComplex P.Coefficient aY f
      (dualizingUnitModel P.Coefficient Y).property⟩

/-- The unit clause with Nagata compactification supplied from the node's hypotheses.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingFiniteUnitAssertion (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (a : X ⟶ Y) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] : Prop :=
  letI := (P.finiteComparedCompactification a (Y ↘ Spec (.of P.field.k))).hasCompactification
  dualizingUnitAssertion P.Coefficient a

/-- The arbitrary-trivialization clause with canonical compactification data.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingFiniteInverseAssertion (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (a : X ⟶ Y) (b : Y ⟶ Z)
    [a.IsOver (Spec (.of P.field.k))] [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b] : Prop :=
  letI := (P.finiteComparedCompactification a (Y ↘ Spec (.of P.field.k))).hasCompactification
  letI := (P.finiteComparedCompactification b (Z ↘ Spec (.of P.field.k))).hasCompactification
  letI := (P.finiteComparedCompactification (a ≫ b)
    (Z ↘ Spec (.of P.field.k))).hasCompactification
  ∀ eta : Etale.dualizingComplex P.Coefficient b ≅ 𝟙_ _,
    dualizingInverseAssertion P.Coefficient a b eta

/-- Unit normalization of the actual tensor transpose at the fixed purity coefficients.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite).
Proof: normalize the proper projection mate at the unit by the ringed projection-mate
lemma. The normalized open projection is the identity at the unit: its inverse and the
identity have the same open-adjunction adjunct. Their compactification composite is
therefore the identity at the unit. In the defining tensor transpose its inverse drops
out, and the exceptional-adjunction triangle makes the remaining adjunct the canonical
unitor with the pullback-unit comparison. Apply each compatible open restriction functor
to the equality and use its composition law and the supplied data compatibilities. -/
theorem dualizingTensor_unit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (a : X ⟶ Y) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    dualizingFiniteUnitAssertion P a := by
  let := (P.finiteComparedCompactification a
    (Y ↘ Spec (.of P.field.k))).hasCompactification
  have hu : Etale.dualizingComplexTensorMap P.Coefficient a (𝟙_ _) =
      ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj
        (Etale.dualizingComplex P.Coefficient a)).map
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) a).hom ≫
      (Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} P.Coefficient) X
        (Etale.dualizingComplex P.Coefficient a)).hom := by
    simpa only [Etale.dualizingComplexTensorMap, Etale.dualizingComplex,
      Etale.derivedTensorRightUnitor, Etale.derivedTensor_obj_map]
      using tensor_unit (Etale.rightDerivedUpperShriekAdjunction P.Coefficient a)
  change dualizingUnitAssertion P.Coefficient a
  constructor
  · exact hu
  · intro V j _
    simpa only [Functor.map_comp] using congrArg
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).leftDerivedFunctor.map) hu

/-- The inverse of the specified sigma, for every trivialization of W_b.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite).
Proof: the finite compact projection theorem makes the projection components used in
theta invertible. Naturality of their inverses, of the counit and of tensor symmetry,
transposed by the natural adjunction bijection, gives naturality of theta. Apply it to
eta, then apply the unit normalization. The conjugate of the compact-support compositor
is invertible, and cancellation gives sigma followed by c followed by a!(eta) equal to
the specified t. The last two arrows and t are invertible, so sigma is invertible;
compose with its inverse to get the displayed inverse equation. For compatible open
restriction apply the functor to the equality and the two inverse equations. It preserves
compositions and identities, so the restricted inverse and equation are the specified ones. -/
theorem dualizingComposite_inverse (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (a : X ⟶ Y) (b : Y ⟶ Z)
    [a.IsOver (Spec (.of P.field.k))] [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b] :
    dualizingFiniteInverseAssertion P a b := by
  let := (P.finiteComparedCompactification a
    (Y ↘ Spec (.of P.field.k))).hasCompactification
  let := (P.finiteComparedCompactification b
    (Z ↘ Spec (.of P.field.k))).hasCompactification
  let := (P.finiteComparedCompactification (a ≫ b)
    (Z ↘ Spec (.of P.field.k))).hasCompactification
  intro eta
  have hu := (dualizingTensor_unit P a).1
  have hn := tensor_naturality (Etale.rightDerivedUpperShriekAdjunction P.Coefficient a) eta.hom
  have heq : dualizingCompositeSigma P.Coefficient a b ≫
      (dualizingCompositeConjugate P.Coefficient a b).hom ≫
        (Etale.rightDerivedUpperShriek P.Coefficient a).map
          eta.hom = (dualizingCompositeTrivialization P.Coefficient a b eta).hom := by
    dsimp only [dualizingCompositeSigma]
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    change Etale.lowerShriekRightAdjointUnitTensorMap
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient a) _ ≫ _ = _
    rw [← hn]
    change _ ≫ Etale.dualizingComplexTensorMap P.Coefficient a (𝟙_ _) = _
    rw [hu]
    simp only [dualizingCompositeTrivialization, Iso.trans_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
    rfl
  have : IsIso (dualizingCompositeSigma P.Coefficient a b) := by
    have : IsIso (dualizingCompositeSigma P.Coefficient a b ≫
        (dualizingCompositeConjugate P.Coefficient a b).hom ≫
          (Etale.rightDerivedUpperShriek P.Coefficient a).map
            eta.hom) := by
      rw [heq]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((dualizingCompositeConjugate P.Coefficient a b).hom ≫
        (Etale.rightDerivedUpperShriek P.Coefficient a).map eta.hom)
  let s := asIso (dualizingCompositeSigma P.Coefficient a b)
  have hi : s.inv ≫ (dualizingCompositeTrivialization P.Coefficient a b eta).hom =
      (dualizingCompositeConjugate P.Coefficient a b).hom ≫
        (Etale.rightDerivedUpperShriek P.Coefficient a).map
          eta.hom := by
    apply (cancel_epi s.hom).1
    simp only [Iso.hom_inv_id_assoc]
    exact heq.symm
  refine ⟨s, rfl, hi, ?_⟩
  intro V j _
  simpa only [Functor.map_comp, Functor.mapIso_inv] using congrArg
    ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).leftDerivedFunctor.map) hi

end WeilConjectures.PurityFiniteSetting
