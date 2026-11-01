/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomComparisonTower
import all WeilConjectures.SixFunctors.Normalized.NormalizedDVRCompletedRestrictionCoherence
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomIntrinsicTensorComposition

/-! # A component of finite Hom site descent

Source: blueprint `lem-coef-finite-hom-site-descent`, final site comparison argument.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local implicit_reducible] CategoryTheory.uniformProd CategoryTheory.prod
  CategoryTheory.prod' CategoryTheory.catToReflQuiver CoefficientClosedStructure.tensor

section ClosedCalculus
variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
  {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
  (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
  (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)

private theorem comparison_transpose (T K M : A) (f : SA.tensor.obj (T, K) ⟶ M) :
    F.map (SA.transpose T K M f) ≫ coefficientBaseChangeHom SA SB F μ K M =
      SB.transpose (F.obj T) (F.obj K) (F.obj M) (μ.inv.app (T, K) ≫ F.map f) := by
  apply (SB.transpose _ _ _).symm.injective
  rw [scalarUncurry_pre, scalarBaseChangeHom_beta, Equiv.symm_apply_apply]
  have hn := μ.inv.naturality (Prod.mkHom (SA.transpose T K M f) (𝟙 K))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [F.map_id] at hn
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, ← scalarUncurry,
    Equiv.symm_apply_apply]

private theorem comparison_composition
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (s : CoefFiniteHomStrong SA SB F μ) (P Q V : A) :
    F.map (SA.composition P Q V) ≫ coefficientBaseChangeHom SA SB F μ P V =
      μ.hom.app (HA.obj (op Q, V), HA.obj (op P, Q)) ≫
        SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ Q V)
          (coefficientBaseChangeHom SA SB F μ P Q)) ≫
        SB.composition (F.obj P) (F.obj Q) (F.obj V) := by
  let := SA.monoidal
  let := SB.monoidal
  let := s.val.toMonoidal
  have hμ (X Y : A) : Functor.LaxMonoidal.μ F X Y = μ.inv.app (X, Y) := by
    change (s.val.μIso X Y).hom = _
    rw [s.property]
    rfl
  have hAssoc (X Y Z : A) :
      SB.tensor.map (Prod.mkHom (μ.inv.app (X, Y)) (𝟙 (F.obj Z))) ≫
        μ.inv.app (SA.tensor.obj (X, Y), Z) ≫
          F.map (SA.monoidal.associator X Y Z).hom =
      (SB.monoidal.associator (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj X)) (μ.inv.app (Y, Z))) ≫
          μ.inv.app (X, SA.tensor.obj (Y, Z)) := by
    simpa only [← hμ, CoefficientClosedStructure.tensor, Functor.comp_obj,
      Functor.prod_obj, tensor_obj, tensor_map, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom] using
      Functor.LaxMonoidal.associativity F X Y Z
  apply (cancel_epi (μ.inv.app (HA.obj (op Q, V), HA.obj (op P, Q)))).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply (SB.transpose _ (F.obj P) (F.obj V)).symm.injective
  rw [scalarUncurry_pre, scalarUncurry_pre, scalarBaseChangeHom_beta,
    scalarUncurry_pre]
  have hn := μ.inv.naturality (Prod.mkHom (SA.composition P Q V) (𝟙 P))
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hn
  rw [reassoc_of% hn, ← F.map_comp, ← scalarUncurry]
  simp only [CoefficientClosedStructure.composition, Equiv.symm_apply_apply, F.map_comp]
  rw [reassoc_of% hAssoc]
  have hn' := μ.inv.naturality
    (Prod.mkHom (𝟙 (HA.obj (op Q, V))) (SA.evaluation P Q))
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hn'
  rw [← reassoc_of% hn']
  have hβ (X Y : A) :
      SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ X Y)
          (𝟙 (F.obj X))) ≫ SB.evaluation (F.obj X) (F.obj Y) =
        μ.inv.app (HA.obj (op X, Y), X) ≫ F.map (SA.evaluation X Y) := by
    rw [← scalarUncurry, scalarBaseChangeHom_beta]
  let v := coefficientBaseChangeHom SA SB F μ
  have hn'' :
      SB.tensor.map (Prod.mkHom (SB.tensor.map (Prod.mkHom (v Q V) (v P Q)))
          (𝟙 (F.obj P))) ≫
        (SB.monoidal.associator (HB.obj (op (F.obj Q), F.obj V))
          (HB.obj (op (F.obj P), F.obj Q)) (F.obj P)).hom =
      (SB.monoidal.associator (F.obj (HA.obj (op Q, V)))
          (F.obj (HA.obj (op P, Q))) (F.obj P)).hom ≫
        SB.tensor.map (Prod.mkHom (v Q V)
          (SB.tensor.map (Prod.mkHom (v P Q) (𝟙 (F.obj P))))) := by
    simpa only [CoefficientClosedStructure.tensor, tensor_map] using
      MonoidalCategory.associator_naturality (v Q V) (v P Q) (𝟙 (F.obj P))
  rw [reassoc_of% hn'']
  have hex :
      SB.tensor.map (Prod.mkHom (v Q V)
          (SB.tensor.map (Prod.mkHom (v P Q) (𝟙 (F.obj P))))) ≫
        SB.tensor.map (Prod.mkHom (𝟙 (HB.obj (op (F.obj Q), F.obj V)))
          (SB.evaluation (F.obj P) (F.obj Q))) =
      SB.tensor.map (Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V))))
          (SB.tensor.map (Prod.mkHom (v P Q) (𝟙 (F.obj P))) ≫
            SB.evaluation (F.obj P) (F.obj Q))) ≫
        SB.tensor.map (Prod.mkHom (v Q V) (𝟙 (F.obj Q))) := by
    simp only [← SB.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [reassoc_of% hex, hβ P Q, hβ Q V]
  have hp : Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V))))
      (μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q)) =
      Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V)))) (μ.inv.app (HA.obj (op P, Q), P)) ≫
        Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V)))) (F.map (SA.evaluation P Q)) := by
    ext <;> simp
  rw [hp, SB.tensor.map_comp]
  simp only [Category.assoc]

end ClosedCalculus

private theorem tensor_identity_of_self_composition
    {A : Type a} [Category.{v} A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (F : A ⥤ A)
    (μ : S.tensor ⋙ F ≅ F.prod F ⋙ S.tensor) (e : F ≅ 𝟭 A)
    (ht : ∀ X Y : A,
      F.map (μ.hom.app (X, Y)) ≫ μ.hom.app (F.obj X, F.obj Y) ≫
        S.tensor.map (Prod.mkHom (F.map (e.hom.app X)) (F.map (e.hom.app Y))) =
      F.map (e.hom.app (S.tensor.obj (X, Y))) ≫ μ.hom.app (X, Y)) (X Y : A) :
    S.tensor.map (Prod.mkHom (e.inv.app X) (e.inv.app Y)) =
      e.inv.app (S.tensor.obj (X, Y)) ≫ μ.hom.app (X, Y) := by
  let : F.Faithful := Functor.Faithful.of_iso e.symm
  have hn := μ.hom.naturality (Prod.mkHom (e.hom.app X) (e.hom.app Y))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  have hh := ht X Y
  rw [← hn, ← F.map_comp_assoc] at hh
  have he : μ.hom.app (X, Y) ≫
      S.tensor.map (Prod.mkHom (e.hom.app X) (e.hom.app Y)) =
      e.hom.app (S.tensor.obj (X, Y)) :=
    F.map_injective ((cancel_mono (μ.hom.app (X, Y))).mp hh)
  apply (cancel_mono
    ((S.tensor.mapIso (Iso.prod (e.app X) (e.app Y))).hom)).mp
  change S.tensor.map (Prod.mkHom (e.inv.app X) (e.inv.app Y)) ≫
    S.tensor.map (Prod.mkHom (e.hom.app X) (e.hom.app Y)) =
      (e.inv.app (S.tensor.obj (X, Y)) ≫ μ.hom.app (X, Y)) ≫
        S.tensor.map (Prod.mkHom (e.hom.app X) (e.hom.app Y))
  rw [Category.assoc, he, Iso.inv_hom_id_app]
  rw [← S.tensor.map_comp]
  simp

private theorem intrinsic_restriction_self_unit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) (n : ℕ) :
    normalizedDVRResComp l E X (Nat.le_refl n) (Nat.le_refl n) =
      Functor.isoWhiskerRight (normalizedDVRResUnit l E X n)
        (normalizedDVRRes l E X (Nat.le_refl n)) ≪≫
          Functor.leftUnitor (normalizedDVRRes l E X (Nat.le_refl n)) := by
  let := HasDerivedCategory.standard (normalizedDVRModules l E X n)
  let q := normalizedDVRQuotient l E X (Nat.le_refl n)
  have hq : q = 𝟙 _ := (integralCoefficientSheafSystem l E X).map_id (op n)
  have hqq : q ≫ q = q := by rw [hq, Category.id_comp]
  ext P
  change (Functor.mapDerivedCategoryCompNatIso
    (normalizedDVRRestrictionComp q q q hqq)).hom.app P = _
  rw [restrictionUnit q q hq]
  change _ = (normalizedDVRRes l E X (Nat.le_refl n)).map
    ((normalizedDVRResUnit l E X n).hom.app P) ≫ 𝟙 _
  rw [Category.comp_id]
  exact derivedUnit
    (normalizedDVRModuleRes l E X (Nat.le_refl n))
    (normalizedDVRModuleRes l E X (Nat.le_refl n))
    (eqToIso (congrArg (fun f ↦ SheafOfModules.restrictScalars.{u + 1} f) hq)) P

private theorem intrinsic_associator_self_unit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) (n : ℕ)
    (P : normalizedDVRDerived l E X n) :
    (finiteHomIntrinsicAssoc l E X (Nat.le_refl n) (Nat.le_refl n)).hom.app P =
      (coefficientFiniteQuotientDerived l E X (Nat.le_refl n)).map
        ((coefFiniteHomProUnit l E X n).hom.app P) := by
  have h := Adjunction.leftAdjointCompIso_comp_id
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction
      (Nat.le_refl n))
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction
      (Nat.le_refl n))
    (normalizedDVRResComp l E X (Nat.le_refl n) (Nat.le_refl n))
    (normalizedDVRResUnit l E X n) (intrinsic_restriction_self_unit l E X n)
  have hp := congrArg (fun z ↦ z.hom.app P) h
  change (finiteHomIntrinsicAssoc l E X (Nat.le_refl n) (Nat.le_refl n)).hom.app P =
    (coefFiniteHomProUnit l E X n).hom.app
      ((coefficientFiniteQuotientDerived l E X (Nat.le_refl n)).obj P) ≫ 𝟙 _ at hp
  rw [Category.comp_id] at hp
  rw [hp]
  apply (cancel_mono ((coefFiniteHomProUnit l E X n).hom.app P)).mp
  exact ((coefFiniteHomProUnit l E X n).hom.naturality
    ((coefFiniteHomProUnit l E X n).hom.app P)).symm

/-- Descent of the naturality, transpose, composition, and coefficient-tower laws.
This is conditional on the geometric tensor squares and descent, and asserts no
new tensor normalization or Hom invertibility.
Source: blueprint `lem-coef-finite-hom-site-descent`, proof step 7
(blueprint: lem-coef-finite-hom-site-equation-descent).

Proof: on etale-origin objects apply monoidal-square Hom transport. Identify its
left closed adjunction with the specified right tensor-Hom adjunction by the signed
symmetry; both comparisons are transposes of the same evaluation. The inverse site
component occurs in the contravariant input. Cancel the invertible site Hom maps to
carry naturality, all transposes, and internal composition through the square.
For each quotient tower, paste the two squares and use the supplied quotient
coherence to cancel the site components. The assumed etale tower equation then
gives the intrinsic one. For the identity quotient use the mate of the identity
restriction: its unit is coefFiniteHomProUnit, and on the etale side it is the
specified normalizedOriginScalarUnit. Finally choose finite-Tor constructible
etale witnesses of every intrinsic input using the descent hypothesis. Naturality
of the comparisons and the fixed associators conjugates each obtained identity by
these witness isomorphisms. Their inverses cancel, so the resulting equation holds
for the original objects independently of witnesses. Apply the same argument to
every object in a triple for internal composition. -/
theorem finiteHomSiteEquationDescent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (hdescent : ∀ n : ℕ, CoefFiniteHomDescent l E X n)
    (hsquare : ∀ (n m : ℕ) (h : m ≤ n), CoefFiniteHomSquare l E X h)
    (hmonoidal : ∀ (n m : ℕ) (h : m ≤ n),
      CoefFiniteHomMonoidalSquare
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
            (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
            (finiteHomNu l E X n) (finiteHomNu l E X m)
            (finiteHomEtaleTensor l E X h) (coefFiniteHomProTensor l E X h)
            (finiteHomNuTensor l E X n) (finiteHomNuTensor l E X m)
            (coefFiniteHomSiteIso l E X h))
    (hquotient : ∀ (n m : ℕ) (h : m ≤ n), CoefFiniteHomQuotientCoherence l E X h) :
    ∀ (n m : ℕ) (h : m ≤ n),
      (CoefFiniteHomLawsOn
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h)
            (finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X) →
            CoefFiniteHomLawsOn
              (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
              (coefficientFiniteQuotientDerived l E X h) (coefFiniteHomProTensor l E X h)
              (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X)) ∧
          CoefFiniteHomSuccessive l E X h := by
  -- The equations hold on the ambient category, so the site hypotheses are redundant.
  have _ := hdescent
  have _ := hsquare
  have _ := hquotient
  intro n m h
  obtain ⟨sF, sG, sU, sV, hmono⟩ := hmonoidal n m h
  refine ⟨?_, ?_⟩
  · intro _
    refine ⟨?_, ?_, ?_⟩
    · intro K M K' M' _ _ _ _ f g
      exact scalarBaseChangeHom_naturality _ _ _ _ K M K' M' f g
    · intro K M _ _ T f
      exact comparison_transpose _ _ _ _ T K M f
    · intro K L M _ _ _
      exact comparison_composition _ _ _ _ sG K L M
  · intro _
    constructor
    · intro r k K M _ _
      exact (scalarBaseChangeHom_tower
        (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
        (finiteIntrinsicClosed l E X r) _ _ _
        (coefFiniteHomProTensor l E X h) (coefFiniteHomProTensor l E X k)
        (coefFiniteHomProTensor l E X (k.trans h)) (finiteHomIntrinsicAssoc l E X h k)
        (finiteHomIntrinsic_tensorComposition l E X h k) K M).symm
    · intro K M _ _
      apply scalarBaseChangeHom_identity (finiteIntrinsicClosed l E X n)
        (coefficientFiniteQuotientDerived l E X (Nat.le_refl n))
        (coefFiniteHomProTensor l E X (Nat.le_refl n)) (coefFiniteHomProUnit l E X n)
      intro P Q
      apply tensor_identity_of_self_composition
      intro U V
      simpa only [intrinsic_associator_self_unit, coefFiniteHomProTensor,
        finiteIntrinsicClosed] using
        finiteHomIntrinsic_tensorComposition l E X (Nat.le_refl n) (Nat.le_refl n) U V

end WeilConjectures
