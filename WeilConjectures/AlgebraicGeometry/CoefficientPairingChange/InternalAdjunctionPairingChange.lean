/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensor
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomThickLocus
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleDirectScalarProjection
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorCoherence
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarExchange

/-! # Coefficient change of the stratum internal-adjunction pairing

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
thm-coef-finite-hom, proof paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change).

The helpers expand the specified closed/open factorization. Ordinary direct image
is written as Rg_* Rj_*, using the canonical composition identification. Tensor
arguments are reversed from the displayed pairing, consistently with the published
left-tensor/Hom adjunction. Thus the projection is the closed proper projection
followed by the inverse open projection, and the last arrow is the pasted counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite TwoSquare
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.CoefficientPairingChange

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
variable {S Z X : Scheme.{u}}

/-- The given factorized compact-support functor, not a chosen compactification.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
abbrev shriek (A : Type (u + 1)) [CommRing A]
    (g : Z ⟶ X) (j : S ⟶ Z) [IsOpenImmersion j] :=
  derivedExtension (A := A) j ⋙ R(lowerStar (ModuleCat A) g)

/-- Ordinary direct image through the canonical composition identification.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
abbrev star (A : Type (u + 1)) [CommRing A] (g : Z ⟶ X) (j : S ⟶ Z) :=
  R(lowerStar (ModuleCat A) j) ⋙ R(lowerStar (ModuleCat A) g)

/-- The actual closed exceptional right adjoint followed by exact open restriction.
Source: thm-coef-finite-hom, paragraph 4; lem-exc-closed-ambient
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
abbrev exceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j] :=
  (R(lowerStar (ModuleCat A) g)).rightAdjoint ⋙ derivedRestriction (A := A) j

/-- The exceptional counit is the counit of the composite open/closed adjunction.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def counit (A : Type (u + 1)) [CommRing A] [Finite A]
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j]
    (M : DerivedCategoryModule A X) :
    (shriek A g j).obj ((exceptional A g j).obj M) ⟶ M :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).comp
    (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat A) g)))).counit.app M

/-- The ordinary inverse-image/direct-image counit for the composite factorization.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def ordinaryCounit (A : Type (u + 1)) [CommRing A]
    (g : Z ⟶ X) (j : S ⟶ Z) (Q : DerivedCategoryModule A S) :
    L(upperStar (ModuleCat A) j).obj
      (L(upperStar (ModuleCat A) g).obj ((star A g j).obj Q)) ⟶ Q :=
  ((derivedUpperStarLowerStarAdjunction (ModuleCat A) g).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat A) j)).counit.app Q

/-- The specified inverse compact-support projection: closed proper projection
followed by the inverse open tensor map. Its tensor order matches left-tensor/Hom.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def projection (A : Type (u + 1)) [CommRing A]
    (g : Z ⟶ X) (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (T : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat A) X).obj ((shriek A g j).obj L)).obj T ⟶
      (shriek A g j).obj
        (((derivedTensor (ModuleCat A) S).obj L).obj
          (L(upperStar (ModuleCat A) j).obj (L(upperStar (ModuleCat A) g).obj T))) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat A) g).app
      ((derivedExtension (A := A) j).obj L)).app T ≫
    R(lowerStar (ModuleCat A) g).map
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat A) j).inv.app L).app
        (L(upperStar (ModuleCat A) g).obj T))

/-- The internal-adjunction arrow, defined by exactly the stated evaluation pairing.
The ordinary counit is applied before evaluation, and the exceptional counit last.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def internalAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X) :
    (star A g j).obj
        (((derivedHom (ModuleCat A) S).obj (op L)).obj ((exceptional A g j).obj M)) ⟶
      ((derivedHom (ModuleCat A) X).obj (op ((shriek A g j).obj L))).obj M :=
  ((derivedTensorHomAdjunction (ModuleCat A) ((shriek A g j).obj L)).homEquiv _ _)
    (projection A g j L _ ≫
      (shriek A g j).map
        (((derivedTensor (ModuleCat A) S).obj L).map
            (ordinaryCounit A g j _) ≫
          (derivedTensorHomAdjunction (ModuleCat A) L).counit.app
            ((exceptional A g j).obj M)) ≫ counit A g j M)

/-- The specified compact-support coefficient map: c_g followed by g_*(q_j).
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def compactComparison (φ : A →+* B) (g : Z ⟶ X) (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) :
    (scalarExtension φ X).obj ((shriek A g j).obj L) ⟶
      (shriek B g j).obj ((scalarExtension φ S).obj L) :=
  finiteCoefficientDirectImageMap φ g ((derivedExtension (A := A) j).obj L) ≫
    R(lowerStar (ModuleCat B) g).map ((openScalarExtension φ j).hom.app L)

/-- The ordinary counit-defined coefficient comparison in composition coordinates.
Source: thm-coef-finite-hom, paragraph 4; lem-coef-finite-direct-image
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def ordinaryComparison (φ : A →+* B) (g : Z ⟶ X) (j : S ⟶ Z)
    (Q : DerivedCategoryModule A S) :
    (scalarExtension φ X).obj ((star A g j).obj Q) ⟶
      (star B g j).obj ((scalarExtension φ S).obj Q) :=
  finiteCoefficientDirectImageMap φ g (R(lowerStar (ModuleCat A) j).obj Q) ≫
    R(lowerStar (ModuleCat B) g).map (finiteCoefficientDirectImageMap φ j Q)

/-- The coefficient Hom map is the transpose of coefficient change of evaluation.
No inverse of this map is used or assumed.
Source: thm-coef-finite-hom, paragraph 1 and paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def evaluationComparison (φ : A →+* B) (T : Scheme.{u})
    (K M : DerivedCategoryModule A T) :
    (scalarExtension φ T).obj (((derivedHom (ModuleCat A) T).obj (op K)).obj M) ⟶
      ((derivedHom (ModuleCat B) T).obj (op ((scalarExtension φ T).obj K))).obj
        ((scalarExtension φ T).obj M) :=
  ((derivedTensorHomAdjunction (ModuleCat B) ((scalarExtension φ T).obj K)).homEquiv _ _)
    ((etaleHomTensorComparison T φ K _).hom ≫
      (scalarExtension φ T).map ((derivedTensorHomAdjunction (ModuleCat A) K).counit.app M))

/-- The displayed normalization of the specified exceptional comparison.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def CounitCompatible [Finite A] [Finite B] (φ : A →+* B)
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j]
    (M : DerivedCategoryModule A X)
    (b : (scalarExtension φ S).obj ((exceptional A g j).obj M) ≅
      (exceptional B g j).obj ((scalarExtension φ X).obj M)) : Prop :=
  compactComparison φ g j ((exceptional A g j).obj M) ≫
      (shriek B g j).map b.hom ≫ counit B g j ((scalarExtension φ X).obj M) =
    (scalarExtension φ X).map (counit A g j M)

/-- The exact equality of arrows in the node, with every comparison expanded by
its fixed construction above. This transparent proposition has no further data.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def PairingChangeEquation [Finite A] [Finite B] (φ : A →+* B)
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X)
    (b : (scalarExtension φ S).obj ((exceptional A g j).obj M) ≅
      (exceptional B g j).obj ((scalarExtension φ X).obj M)) : Prop :=
  ordinaryComparison φ g j _ ≫
      (star B g j).map
        (evaluationComparison φ S L _ ≫
          ((derivedHom (ModuleCat B) S).obj
            (op ((scalarExtension φ S).obj L))).map b.hom) ≫
      internalAdjunction B g j ((scalarExtension φ S).obj L) ((scalarExtension φ X).obj M) ≫
      ((derivedHom (ModuleCat B) X).map (compactComparison φ g j L).op).app
        ((scalarExtension φ X).obj M) =
    (scalarExtension φ X).map (internalAdjunction A g j L M) ≫
      evaluationComparison φ X ((shriek A g j).obj L) M

/-- The positive-level quotient ring with the standard module-universe lift.
Source: thm-coef-finite-hom, paragraph 4; def-weil-l-adic-coefficient-extension
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
abbrev coefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ+) :=
  ULift.{u + 1} (Padic.coefficientExtensionRing l E n)

/-- Finiteness is the dependency theorem at the positive level, with a universe lift.
Source: def-weil-l-adic-coefficient-extension, clause 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
instance coefficientFinite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ+) :
    Finite (coefficient l E n) :=
  Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n n.property)

/-- Reduction is the quotient factor map of the actual uniformizer-power ideals.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def reduction (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n m : ℕ+) (hmn : m ≤ n) :
    coefficient l E n →+* coefficient l E m :=
  RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E n)
    (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))

set_option backward.defeqAttrib.useBackward true

private theorem finiteComparison_eq_mate (φ : A →+* B) (g : Z ⟶ X)
    (K : DerivedCategoryModule A Z) :
    finiteCoefficientDirectImageMap φ g K = (scalarMate φ g).app K := by
  rw [finiteCoefficientDirectImageMap_eq_mate]
  rfl

private theorem tensorComparison_eq (φ : A →+* B) (T : Scheme.{u})
    (K L : DerivedCategoryModule A T) :
    etaleHomTensorComparison T φ K L =
      ((ExceptionalCoefficients.tensorIso φ T).app (K, L)).symm := by
  let E := ProEtale.etaleSheafExtendScalars φ T
  let := (ProEtale.etaleSheafExtendScalarsAdjunction φ T).isLeftAdjoint
  let := (ProEtale.etaleSheafExtendScalarsAdjunction φ T).leftAdjointOplaxMonoidal
  have hδ : ExceptionalCoefficients.TensorNormalization φ T
      (ExceptionalCoefficients.tensorIso φ T) := by
    have he := eq_of_heq (ExceptionalCoefficients.siteTensorIso_existsUnique φ T).choose_spec.1
    change ExceptionalCoefficients.TensorNormalization φ T
      (ExceptionalCoefficients.siteTensorIso_existsUnique φ T).choose
    rw [he]
    exact (ExceptionalCoefficients.tensorIso_existsUnique φ T).choose_spec.1
  have hc : IsEtaleHomTensorCanonical T φ
      (fun P Q ↦ ((ExceptionalCoefficients.tensorIso φ T).app (P, Q)).symm) := by
    refine ⟨ExceptionalCoefficients.productIso_natural₁ _ _ _ _,
      ExceptionalCoefficients.productIso_natural₂ _ _ _ _, ?_⟩
    exact ExceptionalCoefficients.site_normalization_flat (ModuleCat A) (ModuleCat B)
      T E (scalarExtension φ T) (scalarExtensionRepresentative φ T) _ hδ
  have he := (etaleHomTensorComparison_existsUnique T φ).choose_spec.2 _ hc
  exact (congrFun (congrFun he K) L).symm

private theorem directProjection_change (φ : A →+* B) (g : Z ⟶ X)
    (K : DerivedCategoryModule A Z) (T : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat B) X).map (finiteCoefficientDirectImageMap φ g K)).app
        ((scalarExtension φ X).obj T) ≫
      ((rightDerivedLowerStarProjectionMap (ModuleCat B) g).app
        ((scalarExtension φ Z).obj K)).app ((scalarExtension φ X).obj T) ≫
      R(lowerStar (ModuleCat B) g).map
        (((derivedTensor (ModuleCat B) Z).obj ((scalarExtension φ Z).obj K)).map
            ((scalarPullbackIso φ g).hom.app T) ≫
          (etaleHomTensorComparison Z φ K (L(upperStar (ModuleCat A) g).obj T)).hom) =
    (etaleHomTensorComparison X φ (R(lowerStar (ModuleCat A) g).obj K) T).hom ≫
      (scalarExtension φ X).map
        (((rightDerivedLowerStarProjectionMap (ModuleCat A) g).app K).app T) ≫
      finiteCoefficientDirectImageMap φ g
        (((derivedTensor (ModuleCat A) Z).obj K).obj (L(upperStar (ModuleCat A) g).obj T)) := by
  let QA := scalarExtension φ X
  let QZ := scalarExtension φ Z
  let LA := L(upperStar (ModuleCat A) g)
  let LB := L(upperStar (ModuleCat B) g)
  let RB := R(lowerStar (ModuleCat B) g)
  let TA := derivedTensor (ModuleCat A) X
  let TB := derivedTensor (ModuleCat B) X
  let UA := derivedTensor (ModuleCat A) Z
  let UB := derivedTensor (ModuleCat B) Z
  let a := scalarPullbackIso φ g
  let dX := curryComparison TA TB QA (ExceptionalCoefficients.tensorIso φ X).hom
  let dZ := curryComparison UA UB QZ (ExceptionalCoefficients.tensorIso φ Z).hom
  have hc (P Q : DerivedCategoryModule A X) :
      LB.map ((dX.app P).app Q) ≫
        ((leftDerivedUpperStarTensorComparison (ModuleCat B) g).app
          (QA.obj P)).app (QA.obj Q) ≫
        (UB.map (a.hom.app P)).app (LB.obj (QA.obj Q)) ≫
        (UB.obj (QZ.obj (LA.obj P))).map (a.hom.app Q) =
      a.hom.app ((TA.obj P).obj Q) ≫
        QZ.map (((leftDerivedUpperStarTensorComparison (ModuleCat A) g).app P).app Q) ≫
        (dZ.app (LA.obj P)).app (LA.obj Q) := by
    simpa only [dX, dZ, QA, QZ, LA, LB, TA, UB, a,
      MonoidalCategory.tensorHom_def, curryComparison,
      leftDerivedUpperStarTensorIso_hom,
      MonoidalCategory.curriedTensor_map_app, MonoidalCategory.curriedTensor_obj_map,
      derivedTensor, Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
      Functor.postcompose₂_obj_obj_obj_obj, MonoidalCategory.curriedTensor_obj_obj,
      Category.assoc] using (etaleScalarPullback_tensor φ g P Q).symm
  have hm := Adjunction.rightAdjointProjectionMap_mate
    (derivedUpperStarLowerStarAdjunction (ModuleCat A) g)
    (derivedUpperStarLowerStarAdjunction (ModuleCat B) g)
    (leftDerivedUpperStarTensorComparison (ModuleCat A) g)
    (leftDerivedUpperStarTensorComparison (ModuleCat B) g)
    dX dZ a.hom (scalarMate φ g) hc
    (fun M ↦ mateEquiv_counit
      (derivedUpperStarLowerStarAdjunction (ModuleCat A) g)
      (derivedUpperStarLowerStarAdjunction (ModuleCat B) g)
      (TwoSquare.mk _ _ _ _ a.hom) M) K T
  have hh := congrArg (fun z ↦
    (ExceptionalCoefficients.tensorIso φ X).inv.app
        (R(lowerStar (ModuleCat A) g).obj K, T) ≫ z ≫
      RB.map ((ExceptionalCoefficients.tensorIso φ Z).inv.app (K, LA.obj T))) hm
  dsimp only [dX, dZ, curryComparison] at hh
  simp only [Category.assoc] at hh
  erw [← RB.map_comp] at hh
  erw [(ExceptionalCoefficients.tensorIso φ Z).hom_inv_id_app (K, LA.obj T)] at hh
  erw [RB.map_id, Category.comp_id] at hh
  erw [reassoc_of% (ExceptionalCoefficients.tensorIso φ X).inv_hom_id_app
    (R(lowerStar (ModuleCat A) g).obj K, T)] at hh
  erw [← RB.map_comp] at hh
  simpa only [tensorComparison_eq, Iso.symm_hom, Iso.app_inv,
    finiteComparison_eq_mate, rightDerivedLowerStarProjectionMap, Category.assoc] using hh.symm

private theorem openProjection_change (φ : A →+* B) (j : S ⟶ Z)
    [IsOpenImmersion j] (K : DerivedCategoryModule A S) (T : DerivedCategoryModule A Z) :
    ((derivedTensor (ModuleCat B) Z).map ((openScalarExtension φ j).hom.app K)).app
        ((scalarExtension φ Z).obj T) ≫
      ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat B) j).inv.app
        ((scalarExtension φ S).obj K)).app ((scalarExtension φ Z).obj T) ≫
      (derivedExtension (A := B) j).map
        (((derivedTensor (ModuleCat B) S).obj ((scalarExtension φ S).obj K)).map
            ((scalarPullbackIso φ j).hom.app T) ≫
          (etaleHomTensorComparison S φ K (L(upperStar (ModuleCat A) j).obj T)).hom) =
    (etaleHomTensorComparison Z φ ((derivedExtension (A := A) j).obj K) T).hom ≫
      (scalarExtension φ Z).map
        (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat A) j).inv.app K).app T) ≫
      (openScalarExtension φ j).hom.app
        (((derivedTensor (ModuleCat A) S).obj K).obj
          (L(upperStar (ModuleCat A) j).obj T)) := by
  let F := scalarExtension φ Z
  let G := scalarExtension φ S
  let JA := derivedExtension (A := A) j
  let JB := derivedExtension (A := B) j
  let UA := (derivedTensor (ModuleCat A) S).obj K
  let UB := (derivedTensor (ModuleCat B) S).obj (G.obj K)
  let eA := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) j
  let eB := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat B) j
  let q := openScalarExtension φ j
  have hr : eB.inv.app (F.obj T) ≫ (scalarPullbackIso φ j).hom.app T =
      (openScalarRestriction φ j).inv.app T ≫ G.map (eA.inv.app T) := by
    have he : openScalarRestriction φ j = (properOpenCoefficientPullbackIso φ j).symm :=
      Iso.ext (openScalarRestriction_eq φ j)
    have hi := congrArg Iso.inv he
    have hh := congrArg (fun η ↦ η.app T) hi
    simp only [Iso.symm_inv] at hh
    rw [hh]
    simp only [properOpenCoefficientPullbackIso, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      eA, eB, G, F, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      _root_.CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  have hmix := (etaleOpenTensorComparisons φ j).mixed_tensor_scalar K T
  have hnat := q.inv.naturality (UA.map (eA.inv.app T))
  dsimp only [Functor.comp_map] at hnat
  have hμ := (etaleHomTensorComparison_existsUnique S φ).choose_spec.1.2.1 K
    (eA.inv.app T)
  have hγ (R : Type (u + 1)) [CommRing R]
      (P : DerivedCategoryModule R S) (V : DerivedCategoryModule R Z) :
      canonicalGammaExact (ModuleCat R) j P V ≫
        ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat R) j).inv.app P).app V =
      (derivedExtension (A := R) j).map
        (((derivedTensor (ModuleCat R) S).obj P).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat R) j).inv.app V)) := by
    unfold canonicalGammaExact
    let e := (derivedOpenImmersionLowerShriekProjectionIso (ModuleCat R) j).app P
    have hi := e.hom_inv_id_app V
    simp only [e, Iso.app_hom, Iso.app_inv,
      derivedOpenImmersionLowerShriekProjectionIso_hom] at hi
    rw [Category.assoc, hi]
    erw [Category.comp_id]
  have : IsIso (canonicalGammaExact (ModuleCat B) j (G.obj K) (F.obj T)) := by
    unfold canonicalGammaExact
    infer_instance
  let TZ := derivedTensor (ModuleCat B) Z
  have hcancel : (TZ.map (q.inv.app K)).app (F.obj T) ≫
      (TZ.map (q.hom.app K)).app (F.obj T) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← TZ.map_comp, Iso.inv_hom_id_app, TZ.map_id,
      NatTrans.id_app]
  apply (cancel_epi (canonicalGammaExact (ModuleCat B) j (G.obj K) (F.obj T) ≫
    (TZ.map (q.inv.app K)).app (F.obj T))).mp
  simp only [Category.assoc]
  conv_lhs =>
    erw [reassoc_of% hcancel]
    erw [reassoc_of% hγ]
  rw [reassoc_of% hmix]
  erw [← F.map_comp_assoc, hγ]
  rw [← reassoc_of% hnat]
  erw [q.inv_hom_id_app]
  erw [Category.comp_id]
  repeat erw [← JB.map_comp]
  apply congrArg JB.map
  rw [Category.assoc]
  erw [← hμ]
  rw [← UB.map_comp_assoc, ← UB.map_comp_assoc, hr]
  try rfl

private def pullComparison (φ : A →+* B) (g : Z ⟶ X) (j : S ⟶ Z) :
    scalarExtension φ X ⋙ L(upperStar (ModuleCat B) g) ⋙
        L(upperStar (ModuleCat B) j) ⟶
      L(upperStar (ModuleCat A) g) ⋙ L(upperStar (ModuleCat A) j) ⋙ scalarExtension φ S :=
  Functor.whiskerRight (scalarPullbackIso φ g).hom L(upperStar (ModuleCat B) j) ≫
    Functor.whiskerLeft L(upperStar (ModuleCat A) g) (scalarPullbackIso φ j).hom

/-- Pasting two projection squares and their naturality squares. -/
private theorem projectionPasting
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : C} {d₀ d₁ d₂ d₃ d₄ d₅ : D}
    {k : a₀ ⟶ a₁} {l : a₁ ⟶ a₂} {v : a₂ ⟶ a₃} {w : a₃ ⟶ a₄}
    {s : a₀ ⟶ a₅} {k' : a₅ ⟶ a₆} {t : a₁ ⟶ a₆} {l' : a₆ ⟶ a₃}
    {a : a₅ ⟶ a₇} {r : a₇ ⟶ a₈} {q : a₈ ⟶ a₄}
    {x : d₀ ⟶ d₁} {y : d₁ ⟶ d₂} {p : d₂ ⟶ R.obj a₁}
    {p₀ : d₁ ⟶ R.obj a₀} {u : d₀ ⟶ d₃} {f : d₃ ⟶ d₄}
    {c : d₄ ⟶ R.obj a₇} {z : d₄ ⟶ d₅} {c' : d₅ ⟶ R.obj a₈}
    (hp : y ≫ p = p₀ ≫ R.map k) (hq : s ≫ k' = k ≫ t)
    (ht : t ≫ l' = l ≫ v) (ho : k' ≫ l' ≫ w = a ≫ r ≫ q)
    (hd : x ≫ p₀ ≫ R.map (s ≫ a) = u ≫ f ≫ c)
    (hn : z ≫ c' = c ≫ R.map r) :
    x ≫ y ≫ p ≫ R.map l ≫ R.map v ≫ R.map w =
      u ≫ f ≫ z ≫ c' ≫ R.map q := by
  have hm : k ≫ l ≫ v ≫ w = s ≫ a ≫ r ≫ q := by
    rw [← reassoc_of% ht, ← reassoc_of% hq, ho]
  calc
    _ = x ≫ p₀ ≫ R.map (k ≫ l ≫ v ≫ w) := by
      rw [reassoc_of% hp]
      simp only [Functor.map_comp]
    _ = x ≫ p₀ ≫ R.map (s ≫ a ≫ r ≫ q) := by rw [hm]
    _ = (x ≫ p₀ ≫ R.map (s ≫ a)) ≫ R.map r ≫ R.map q := by
      simp only [Functor.map_comp, Category.assoc]
    _ = u ≫ f ≫ (c ≫ R.map r) ≫ R.map q := by
      rw [hd]
      simp only [Category.assoc]
    _ = _ := by rw [← hn]; simp only [Category.assoc]

private theorem projection_change (φ : A →+* B) (g : Z ⟶ X) (j : S ⟶ Z)
    [IsOpenImmersion j] (K : DerivedCategoryModule A S) (T : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat B) X).map (compactComparison φ g j K)).app
        ((scalarExtension φ X).obj T) ≫
      projection B g j ((scalarExtension φ S).obj K) ((scalarExtension φ X).obj T) ≫
      (shriek B g j).map
        (((derivedTensor (ModuleCat B) S).obj ((scalarExtension φ S).obj K)).map
            ((pullComparison φ g j).app T) ≫
          (etaleHomTensorComparison S φ K
            (L(upperStar (ModuleCat A) j).obj (L(upperStar (ModuleCat A) g).obj T))).hom) =
    (etaleHomTensorComparison X φ ((shriek A g j).obj K) T).hom ≫
      (scalarExtension φ X).map (projection A g j K T) ≫
      compactComparison φ g j
        (((derivedTensor (ModuleCat A) S).obj K).obj
          (L(upperStar (ModuleCat A) j).obj (L(upperStar (ModuleCat A) g).obj T))) := by
  let RB := R(lowerStar (ModuleCat B) g)
  let TB := derivedTensor (ModuleCat B) X
  let UB := derivedTensor (ModuleCat B) Z
  let JB := derivedExtension (A := B) j
  let FL := (scalarExtension φ S).obj K
  let q := (openScalarExtension φ j).hom.app K
  let σ := (scalarPullbackIso φ g).hom.app T
  have hp := NatTrans.congr_app
    ((rightDerivedLowerStarProjectionMap (ModuleCat B) g).naturality q)
    ((scalarExtension φ X).obj T)
  change (TB.map (RB.map q)).app ((scalarExtension φ X).obj T) ≫
      ((rightDerivedLowerStarProjectionMap (ModuleCat B) g).app (JB.obj FL)).app
        ((scalarExtension φ X).obj T) =
    ((rightDerivedLowerStarProjectionMap (ModuleCat B) g).app
        ((scalarExtension φ Z).obj ((derivedExtension (A := A) j).obj K))).app
        ((scalarExtension φ X).obj T) ≫
      RB.map ((UB.map q).app
        (L(upperStar (ModuleCat B) g).obj ((scalarExtension φ X).obj T))) at hp
  let eb := (derivedOpenImmersionLowerShriekProjectionIso (ModuleCat B) j).inv.app FL
  have hopen := eb.naturality σ
  change (UB.obj (JB.obj FL)).map σ ≫
      ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat B) j).inv.app FL).app
        ((scalarExtension φ Z).obj (L(upperStar (ModuleCat A) g).obj T)) =
    ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat B) j).inv.app FL).app
        (L(upperStar (ModuleCat B) g).obj ((scalarExtension φ X).obj T)) ≫
      JB.map (((derivedTensor (ModuleCat B) S).obj FL).map
        (L(upperStar (ModuleCat B) j).map σ)) at hopen
  have hq := (UB.map q).naturality σ
  have ho := openProjection_change φ j K (L(upperStar (ModuleCat A) g).obj T)
  have hd := directProjection_change φ g ((derivedExtension (A := A) j).obj K) T
  have hn := finiteCoefficientDirectImageMap_naturality φ g
    (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat A) j).inv.app K).app
      (L(upperStar (ModuleCat A) g).obj T))
  have hh := projectionPasting RB hp hq hopen ho hd hn
  simpa only [RB, TB, UB, JB, FL, q, σ, scalarExtension,
    derivedTensorWhiskeringRightLeftDerivedUpperStar,
    Functor.postcompose₂_obj_obj_obj_obj, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    compactComparison, projection, pullComparison, shriek, Functor.comp_obj, Functor.id_obj,
    Functor.comp_map, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc] using hh

private theorem ordinaryComparison_counit (φ : A →+* B) (g : Z ⟶ X) (j : S ⟶ Z)
    (Q : DerivedCategoryModule A S) :
    L(upperStar (ModuleCat B) j).map
        (L(upperStar (ModuleCat B) g).map (ordinaryComparison φ g j Q)) ≫
        ordinaryCounit B g j ((scalarExtension φ S).obj Q) =
      (pullComparison φ g j).app ((star A g j).obj Q) ≫
        (scalarExtension φ S).map (ordinaryCounit A g j Q) := by
  let a := derivedUpperStarLowerStarAdjunction (ModuleCat A) g
  let a' := derivedUpperStarLowerStarAdjunction (ModuleCat B) g
  let b := derivedUpperStarLowerStarAdjunction (ModuleCat A) j
  let b' := derivedUpperStarLowerStarAdjunction (ModuleCat B) j
  let α := TwoSquare.mk _ _ _ _ (scalarPullbackIso φ g).hom
  let β := TwoSquare.mk _ _ _ _ (scalarPullbackIso φ j).hom
  have h := mateEquiv_counit (a.comp b) (a'.comp b') (α ≫ᵥ β) Q
  rw [mateEquiv_hcomp] at h
  simpa only [a, a', b, b', α, β, ordinaryComparison, ordinaryCounit,
    finiteComparison_eq_mate, scalarMate, pullComparison,
    TwoSquare.hComp, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.comp_obj, TwoSquare.mk,
    Functor.associator_hom_app, Functor.associator_inv_app,
    _root_.CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.assoc] using h

private theorem compactComparison_naturality (φ : A →+* B)
    (g : Z ⟶ X) (j : S ⟶ Z) [IsOpenImmersion j]
    {K K' : DerivedCategoryModule A S} (f : K ⟶ K') :
    (scalarExtension φ X).map ((shriek A g j).map f) ≫ compactComparison φ g j K' =
      compactComparison φ g j K ≫
        (shriek B g j).map ((scalarExtension φ S).map f) := by
  unfold compactComparison
  dsimp only [shriek, Functor.comp_map]
  rw [← Category.assoc, finiteCoefficientDirectImageMap_naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  erw [(openScalarExtension φ j).hom.naturality]
  rfl

private theorem projection_naturality (R : Type (u + 1)) [CommRing R]
    (g : Z ⟶ X) (j : S ⟶ Z) [IsOpenImmersion j]
    (K : DerivedCategoryModule R S) {T T' : DerivedCategoryModule R X} (f : T ⟶ T') :
    ((derivedTensor (ModuleCat R) X).obj ((shriek R g j).obj K)).map f ≫
        projection R g j K T' =
      projection R g j K T ≫ (shriek R g j).map
        (((derivedTensor (ModuleCat R) S).obj K).map
          (L(upperStar (ModuleCat R) j).map (L(upperStar (ModuleCat R) g).map f))) := by
  let RA := R(lowerStar (ModuleCat R) g)
  let JA := derivedExtension (A := R) j
  let LA := L(upperStar (ModuleCat R) g)
  let p := (rightDerivedLowerStarProjectionMap (ModuleCat R) g).app (JA.obj K)
  let e := (derivedOpenImmersionLowerShriekProjectionIso (ModuleCat R) j).inv.app K
  have hp := p.naturality f
  change ((derivedTensor (ModuleCat R) X).obj (RA.obj (JA.obj K))).map f ≫ p.app T' =
    p.app T ≫ RA.map
      (((derivedTensor (ModuleCat R) Z).obj (JA.obj K)).map (LA.map f)) at hp
  have he := e.naturality (LA.map f)
  change ((derivedTensor (ModuleCat R) Z).obj (JA.obj K)).map (LA.map f) ≫
      e.app (LA.obj T') = e.app (LA.obj T) ≫ JA.map
      (((derivedTensor (ModuleCat R) S).obj K).map
        (L(upperStar (ModuleCat R) j).map (LA.map f))) at he
  change ((derivedTensor (ModuleCat R) X).obj (RA.obj (JA.obj K))).map f ≫
      (p.app T' ≫ RA.map (e.app (LA.obj T'))) =
    (p.app T ≫ RA.map (e.app (LA.obj T))) ≫ RA.map
      (JA.map (((derivedTensor (ModuleCat R) S).obj K).map
        (L(upperStar (ModuleCat R) j).map (LA.map f))))
  rw [← Category.assoc, hp, Category.assoc, ← RA.map_comp, he, RA.map_comp]
  simp only [Category.assoc]

private theorem evaluationComparison_transpose (φ : A →+* B) (T : Scheme.{u})
    (K M : DerivedCategoryModule A T) :
    ((derivedTensorHomAdjunction (ModuleCat B) ((scalarExtension φ T).obj K)).homEquiv
      _ _).symm (evaluationComparison φ T K M) =
      (etaleHomTensorComparison T φ K _).hom ≫
        (scalarExtension φ T).map
          ((derivedTensorHomAdjunction (ModuleCat A) K).counit.app M) := by
  unfold evaluationComparison
  exact Equiv.symm_apply_apply _ _

private theorem innerEvaluation_change (φ : A →+* B) (g : Z ⟶ X) (j : S ⟶ Z)
    (K N : DerivedCategoryModule A S) (N' : DerivedCategoryModule B S)
    (b : (scalarExtension φ S).obj N ⟶ N') :
    let Q := ((derivedHom (ModuleCat A) S).obj (op K)).obj N
    let Q' := ((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj K))).obj N'
    let h := ordinaryComparison φ g j Q ≫ (star B g j).map
      (evaluationComparison φ S K N ≫
        ((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj K))).map b)
    ((derivedTensor (ModuleCat B) S).obj ((scalarExtension φ S).obj K)).map
        (L(upperStar (ModuleCat B) j).map (L(upperStar (ModuleCat B) g).map h)) ≫
      (((derivedTensor (ModuleCat B) S).obj ((scalarExtension φ S).obj K)).map
          (ordinaryCounit B g j Q') ≫
        (derivedTensorHomAdjunction (ModuleCat B) ((scalarExtension φ S).obj K)).counit.app
          N') =
      ((derivedTensor (ModuleCat B) S).obj ((scalarExtension φ S).obj K)).map
          ((pullComparison φ g j).app ((star A g j).obj Q)) ≫
        (etaleHomTensorComparison S φ K
          (L(upperStar (ModuleCat A) j).obj
            (L(upperStar (ModuleCat A) g).obj ((star A g j).obj Q)))).hom ≫
        (scalarExtension φ S).map
          (((derivedTensor (ModuleCat A) S).obj K).map (ordinaryCounit A g j Q) ≫
            (derivedTensorHomAdjunction (ModuleCat A) K).counit.app N) ≫ b := by
  dsimp only
  let Q := ((derivedHom (ModuleCat A) S).obj (op K)).obj N
  let Q' := ((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj K))).obj N'
  let w := evaluationComparison φ S K N ≫
    ((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj K))).map b
  let PB := L(upperStar (ModuleCat B) g) ⋙ L(upperStar (ModuleCat B) j)
  let TB := (derivedTensor (ModuleCat B) S).obj ((scalarExtension φ S).obj K)
  let a := (derivedUpperStarLowerStarAdjunction (ModuleCat B) g).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat B) j)
  have hc : PB.map (ordinaryComparison φ g j Q ≫ (star B g j).map w) ≫
      ordinaryCounit B g j Q' =
    (pullComparison φ g j).app ((star A g j).obj Q) ≫
      (scalarExtension φ S).map (ordinaryCounit A g j Q) ≫ w := by
    rw [PB.map_comp, Category.assoc]
    erw [a.counit_naturality w]
    change PB.map (ordinaryComparison φ g j Q) ≫
        ordinaryCounit B g j ((scalarExtension φ S).obj Q) ≫ w = _
    dsimp only [PB, Functor.comp_map]
    rw [reassoc_of% ordinaryComparison_counit]
    rfl
  have hew : TB.map w ≫
      (derivedTensorHomAdjunction (ModuleCat B) ((scalarExtension φ S).obj K)).counit.app N' =
      (etaleHomTensorComparison S φ K Q).hom ≫
        (scalarExtension φ S).map
          ((derivedTensorHomAdjunction (ModuleCat A) K).counit.app N) ≫ b := by
    change ((derivedTensor (ModuleCat B) S).obj ((scalarExtension φ S).obj K)).map w ≫
      (derivedTensorHomAdjunction (ModuleCat B) ((scalarExtension φ S).obj K)).counit.app
        N' = _
    erw [← Adjunction.homEquiv_counit]
    unfold w
    rw [Adjunction.homEquiv_naturality_right_symm, evaluationComparison_transpose]
    simp only [Category.assoc]
    rfl
  change TB.map (PB.map (ordinaryComparison φ g j Q ≫ (star B g j).map w)) ≫
    (TB.map (ordinaryCounit B g j Q') ≫ _) = _
  rw [← Category.assoc, ← TB.map_comp, hc]
  simp only [TB.map_comp, Category.assoc]
  rw [hew]
  have hn := (etaleHomTensorComparison_existsUnique S φ).choose_spec.1.2.1 K
    (ordinaryCounit A g j Q)
  erw [reassoc_of% hn]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- Naturality and a counit square paste after applying a functor. -/
private theorem counitPasting {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {K U N M : C} {U' N' V' : D}
    (p : K ⟶ U) (e : U ⟶ N) (c : N ⟶ M)
    (qU : F.obj U ⟶ U') (qe : U' ⟶ N') (qN : F.obj N ⟶ N')
    (b : N' ⟶ V') (cB : V' ⟶ F.obj M)
    (hn : F.map e ≫ qN = qU ≫ qe)
    (hb : qN ≫ b ≫ cB = F.map c) :
    F.map p ≫ qU ≫ qe ≫ b ≫ cB = F.map (p ≫ e ≫ c) := by
  rw [← reassoc_of% hn, hb]
  simp only [Functor.map_comp]

/-- Transposition moves the two source maps and the contravariant parameter map. -/
private theorem transposeChain {C : Type*} [Category C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C) (a : T ⊣₂ H)
    {K K' V W U M : C} (f : K ⟶ K') (c : V ⟶ W) (d : W ⟶ U)
    (p : (T.obj K').obj U ⟶ M) :
    a.homEquiv.symm (c ≫ d ≫ a.homEquiv p ≫ (H.map f.op).app M) =
      (T.map f).app V ≫ (T.obj K').map (c ≫ d) ≫ p := by
  rw [← Category.assoc, ← Category.assoc, a.homEquiv_symm_naturality_one,
    a.homEquiv_symm_naturality_two]
  simp only [Equiv.symm_apply_apply]

/-- Evaluation cancels the transpose without unfolding the adjunction construction. -/
private theorem counitTranspose {C : Type*} [Category C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C) (a : T ⊣₂ H)
    {K U M : C} (p : (T.obj K).obj U ⟶ M) :
    (T.obj K).map (a.homEquiv p) ≫ (a.adj K).counit.app M = p := by
  exact ((a.adj K).homEquiv U M).symm_apply_apply p

/-- Inverse transposition takes precomposition to tensoring the source map. -/
private theorem transposePrecompose {C : Type*} [Category C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C) (a : T ⊣₂ H)
    {K U V M : C} (f : V ⟶ U) (p : (T.obj K).obj U ⟶ M) :
    a.homEquiv.symm (f ≫ a.homEquiv p) = (T.obj K).map f ≫ p := by
  rw [a.homEquiv_symm_naturality_two, Equiv.symm_apply_apply]

/-- Equality of the two explicit tensor pairings gives equality of their transposes. -/
private theorem pairingTranspose {C : Type*} [Category C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C) (a : T ⊣₂ H)
    {K K' V W U U' M : C} (f : K ⟶ K') (c : V ⟶ W) (d : W ⟶ U)
    (p : (T.obj K').obj U ⟶ M) (r : V ⟶ U') (q : (T.obj K).obj U' ⟶ M)
    (h : (T.map f).app V ≫ (T.obj K').map (c ≫ d) ≫ p = (T.obj K).map r ≫ q) :
    c ≫ d ≫ a.homEquiv p ≫ (H.map f.op).app M = r ≫ a.homEquiv q := by
  apply a.homEquiv.symm.injective
  rw [transposeChain, transposePrecompose]
  exact h

/-- The parameterized transpose formula, keeping the geometric maps shared. -/
private theorem internalAdjunction_formula (R : Type (u + 1)) [CommRing R] [Finite R]
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule R S) (M : DerivedCategoryModule R X) :
    internalAdjunction R g j L M =
      (derivedTensorHomAdjunction₂ (ModuleCat R) X).homEquiv
        (projection R g j L _ ≫
          (shriek R g j).map
            (((derivedTensor (ModuleCat R) S).obj L).map
                (ordinaryCounit R g j _) ≫
              (derivedTensorHomAdjunction (ModuleCat R) L).counit.app
                ((exceptional R g j).obj M)) ≫ counit R g j M) := by
  let p := projection R g j L _ ≫
    (shriek R g j).map
      (((derivedTensor (ModuleCat R) S).obj L).map (ordinaryCounit R g j _) ≫
        (derivedTensorHomAdjunction (ModuleCat R) L).counit.app
          ((exceptional R g j).obj M)) ≫ counit R g j M
  exact congrArg (fun z : _ ≃ _ ↦ z p)
    (ParametrizedAdjunction.homEquiv_eq
      (derivedTensorHomAdjunction₂ (ModuleCat R) X)).symm

/-- The parameterized transpose formula for the specified evaluation comparison. -/
private theorem evaluationComparison_formula (φ : A →+* B) (T : Scheme.{u})
    (K M : DerivedCategoryModule A T) :
    evaluationComparison φ T K M =
      (derivedTensorHomAdjunction₂ (ModuleCat B) T).homEquiv
        ((etaleHomTensorComparison T φ K _).hom ≫
          (scalarExtension φ T).map
            (((derivedTensorHomAdjunction₂ (ModuleCat A) T).adj K).counit.app M)) := by
  rfl

set_option maxHeartbeats 0 in
-- Kernel checking this specialized tensor-Hom calculation exceeds the default heartbeat budget.
set_option cleanup.letToHave false in
private theorem pairing_change [Finite A] [Finite B] (φ : A →+* B)
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X)
    (b : (scalarExtension φ S).obj ((exceptional A g j).obj M) ≅
      (exceptional B g j).obj ((scalarExtension φ X).obj M))
    (_hb : CounitCompatible φ g j M b) : PairingChangeEquation φ g j L M b := by
  let a := derivedTensorHomAdjunction₂ (ModuleCat A) X
  let a' := derivedTensorHomAdjunction₂ (ModuleCat B) X
  let F := scalarExtension φ X
  let G := scalarExtension φ S
  let E' := shriek B g j
  let N := (exceptional A g j).obj M
  let Q := ((derivedHom (ModuleCat A) S).obj (op L)).obj N
  let N' := (exceptional B g j).obj (F.obj M)
  let e := ((derivedTensor (ModuleCat A) S).obj L).map
      (ordinaryCounit A g j
        (((derivedHom (ModuleCat A) S).obj (op L)).obj
          ((derivedRestriction j).obj (R(lowerStar (ModuleCat A) g).rightAdjoint.obj M)))) ≫
    (derivedTensorHomAdjunction (ModuleCat A) L).counit.app
      ((derivedRestriction j).obj (R(lowerStar (ModuleCat A) g).rightAdjoint.obj M))
  unfold PairingChangeEquation
  as_aux_lemma =>
    rw [internalAdjunction_formula B g j ((scalarExtension φ S).obj L)
        ((scalarExtension φ X).obj M),
      internalAdjunction_formula A g j L M,
      evaluationComparison_formula φ X ((shriek A g j).obj L) M]
    as_aux_lemma =>
      apply pairingTranspose (derivedTensor (ModuleCat B) X)
        (derivedHom (ModuleCat B) X) (derivedTensorHomAdjunction₂ (ModuleCat B) X)
        (K := (scalarExtension φ X).obj ((shriek A g j).obj L))
        (K' := (shriek B g j).obj ((scalarExtension φ S).obj L))
        (U := (star B g j).obj
          (((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj L))).obj
            ((exceptional B g j).obj ((scalarExtension φ X).obj M))))
        (U' := (scalarExtension φ X).obj
          (((derivedHom (ModuleCat A) X).obj (op ((shriek A g j).obj L))).obj M))
        (M := (scalarExtension φ X).obj M)
      as_aux_lemma =>
        dsimp only [shriek, Functor.comp_obj, Functor.id_obj]
        rw [reassoc_of% (projection_naturality B g j ((scalarExtension φ S).obj L) _)]
        as_aux_lemma =>
          let PB := L(upperStar (ModuleCat B) g) ⋙ L(upperStar (ModuleCat B) j)
          let UB := (derivedTensor (ModuleCat B) S).obj (G.obj L)
          let Q' := ((derivedHom (ModuleCat B) S).obj (op (G.obj L))).obj N'
          let h := ordinaryComparison φ g j Q ≫ (star B g j).map
            (evaluationComparison φ S L N ≫
              ((derivedHom (ModuleCat B) S).obj (op (G.obj L))).map b.hom)
          let eB := UB.map (ordinaryCounit B g j Q') ≫
            (derivedTensorHomAdjunction (ModuleCat B) (G.obj L)).counit.app N'
          have hi : UB.map (PB.map h) ≫ eB =
              UB.map ((pullComparison φ g j).app ((star A g j).obj Q)) ≫
                (etaleHomTensorComparison S φ L
                  (L(upperStar (ModuleCat A) j).obj
                    (L(upperStar (ModuleCat A) g).obj ((star A g j).obj Q)))).hom ≫
                G.map e ≫ b.hom := innerEvaluation_change φ g j L N N' b.hom
          have hi' := congrArg E'.map hi
          simp only [E'.map_comp] at hi'
          dsimp only [E', shriek, Functor.comp_map, UB, PB, G, h, eB, Q', N', F, Q, N] at hi'
          dsimp only [shriek, star, exceptional, Functor.comp_map, Functor.comp_obj] at hi' ⊢
          rw [reassoc_of% hi']
          as_aux_lemma =>
            have hp := projection_change φ g j L ((star A g j).obj Q)
            dsimp only [E', shriek, Functor.comp_map, G, F, Q, N] at hp
            dsimp only [shriek, star, exceptional, Functor.comp_map, Functor.comp_obj] at hp
            simp only [Functor.map_comp] at hp
            rw [reassoc_of% hp]
            as_aux_lemma =>
              have hμ : IsEtaleHomTensorCanonical X φ (etaleHomTensorComparison X φ) := by
                unfold etaleHomTensorComparison
                exact (etaleHomTensorComparison_existsUnique X φ).choose_spec.1
              rw [reassoc_of% (hμ.2.1 _ _)]
              simp only [← (scalarExtension φ X).map_comp]
              rw [counitTranspose]
              have hn := compactComparison_naturality φ g j e
              dsimp only [Q, N, star, exceptional, shriek, Functor.comp_map,
                Functor.comp_obj, Functor.id_obj] at hn
              dsimp only [CounitCompatible, shriek, Functor.comp_map, Functor.comp_obj] at _hb
              have hc := counitPasting (scalarExtension φ X)
                (projection A g j L ((star A g j).obj Q))
                ((shriek A g j).map e) (counit A g j M)
                _ _ _ _ _ hn _hb
              dsimp only [Q, N, star, exceptional, shriek, Functor.comp_map,
                Functor.comp_obj] at hc
              exact congrArg (fun z ↦
                (etaleHomTensorComparison X φ ((shriek A g j).obj L)
                  ((star A g j).obj Q)).hom ≫ z) hc

/-- The stratum internal-adjunction comparison is exactly the evaluation transpose.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change).

Proof:
1. The mate-counit identity for the composite geometric adjunction identifies
   ordinary coefficient change followed by the B counit with the scalar pullback
   comparison followed by scalar extension of the A counit.
2. Tensor-Hom naturality moves the Hom image of b through evaluation. The defining
   transpose of evaluationComparison and naturality of its tensor comparison then
   identify the inner B evaluation pairing with scalar extension of the A pairing,
   followed by b.
3. Uniqueness of the normalized tensor comparison identifies its inverse with
   the representative-normalized scalar tensor isomorphism. The geometric mate
   projection identity and scalar/pullback tensor coherence give the direct-image
   projection square in the tensor order used by projection.
4. The mixed open tensor/scalar equation gives the open projection square after
   cancelling the open projection and scalar comparison isomorphisms. Naturality
   transports exact restriction to left-derived pullback, using the prescribed
   open scalar restriction comparison.
5. Paste these two squares using naturality of the direct projection, the open
   projection and the direct-image coefficient comparison. This gives the scalar
   projection square for the actual factorization g_* j_!.
6. Transpose the desired equation under tensor-Hom adjunction. Naturality moves
   the ordinary comparison through the projection. Steps 2 and 5 rewrite the
   result as scalar extension of the A pairing followed by compactComparison,
   shriek_B(b), and the B exceptional counit.
7. Naturality of compactComparison and the assumed counit compatibility replace
   these last factors by scalar extension of the A exceptional counit. The right
   side has the same transpose by the definition of evaluationComparison.
8. Injectivity of the tensor-Hom bijection proves the equation. No inverse of the
   evaluation comparison is used.
-/
theorem internalAdjunction_pairing_change
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n m : ℕ+) (hmn : m ≤ n)
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    {S Z : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (M : DerivedCategoryModule (coefficient l E n) X)
    (L : DerivedCategoryModule (coefficient l E n) S)
    (_hM : WeilConjectures.finiteTorConstructibleEtale l E n n.property X M)
    (_hL : WeilConjectures.finiteTorConstructibleEtale l E n n.property S L)
    (_hN : WeilConjectures.finiteTorConstructibleEtale l E n n.property S
      ((exceptional (coefficient l E n) g j).obj M))
    (_hQ : WeilConjectures.finiteTorConstructibleEtale l E n n.property S
      (((derivedHom (ModuleCat (coefficient l E n)) S).obj (op L)).obj
        ((exceptional (coefficient l E n) g j).obj M)))
    (b : (scalarExtension (reduction l E n m hmn) S).obj
        ((exceptional (coefficient l E n) g j).obj M) ≅
      (exceptional (coefficient l E m) g j).obj
        ((scalarExtension (reduction l E n m hmn) X).obj M))
    (_hb : CounitCompatible (reduction l E n m hmn) g j M b) :
    PairingChangeEquation (reduction l E n m hmn) g j L M b := by
  exact pairing_change (reduction l E n m hmn) g j L M b _hb

end AlgebraicGeometry.Etale.CoefficientPairingChange
