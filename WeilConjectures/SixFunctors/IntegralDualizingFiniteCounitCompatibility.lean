/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingSystemTraceData
import WeilConjectures.SixFunctors.CoefPairingNativeOperations
import WeilConjectures.SixFunctors.IntegralDualizingSystemUnitTransition
import WeilConjectures.SixFunctors.IntegralDualizingFiniteCounitQuotient

/-! # Compatibility of the finite exceptional counit family

Source: prop-coef-integral-dualizing, paragraph 2, and finite coefficient counit change.
(blueprint: lem-coef-system-finite-counit-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem support_counit_square
    {Cₘ Cₙ Dₘ Dₙ : Type*} [Category Cₘ] [Category Cₙ] [Category Dₘ] [Category Dₙ]
    (F : Cₘ ⥤ Dₘ) (G : Cₙ ⥤ Dₙ) (RX : Cₙ ⥤ Cₘ) (RY : Dₙ ⥤ Dₘ)
    (ρ : RX ⋙ F ⟶ G ⋙ RY)
    {Qₘ Ωₘ : Cₘ} {Qₙ Ωₙ : Cₙ} {Tₘ Uₘ : Dₘ} {Tₙ Uₙ : Dₙ}
    (aₘ : Tₘ ⟶ F.obj Qₘ) (aₙ : Tₙ ⟶ G.obj Qₙ)
    (eₘ : Qₘ ⟶ Ωₘ) (eₙ : Qₙ ⟶ Ωₙ)
    (δ : Qₘ ⟶ RX.obj Qₙ) (τ : Ωₘ ⟶ RX.obj Ωₙ)
    (t : Tₘ ⟶ RY.obj Tₙ) (q : Uₘ ⟶ RY.obj Uₙ)
    (εₘ : F.obj Ωₘ ⟶ Uₘ) (εₙ : G.obj Ωₙ ⟶ Uₙ)
    (hδ : δ ≫ RX.map eₙ = eₘ ≫ τ)
    (ha : t ≫ RY.map aₙ = aₘ ≫ F.map δ ≫ ρ.app Qₙ)
    (hε : F.map τ ≫ ρ.app Ωₙ ≫ RY.map εₙ = εₘ ≫ q) :
    aₘ ≫ F.map eₘ ≫ εₘ ≫ q = t ≫ RY.map (aₙ ≫ G.map eₙ ≫ εₙ) := by
  have hn := ρ.naturality eₙ
  dsimp only [Functor.comp_map] at hn
  rw [← hε]
  rw [← F.map_comp_assoc, ← hδ, F.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← reassoc_of% ha]
  simp only [Functor.map_comp]

private theorem trace_natural_square
    {C Dₘ Dₙ : Type*} [Category C] [Category Dₘ] [Category Dₙ]
    (Eₘ : C ⥤ Dₘ) (Eₙ : C ⥤ Dₙ) (R : Dₙ ⥤ Dₘ) (t : Eₘ ⟶ Eₙ ⋙ R)
    {A B U : C} (c : A ⟶ B) {Vₘ : Dₘ} {Vₙ : Dₙ}
    (eₘ : Eₘ.obj U ≅ Vₘ) (eₙ : Eₙ.obj U ≅ Vₙ)
    (vₘ : Eₘ.obj B ⟶ Vₘ) (vₙ : Eₙ.obj B ⟶ Vₙ) (q : Vₘ ⟶ R.obj Vₙ)
    (hu : t.app U ≫ R.map eₙ.hom = eₘ.hom ≫ q)
    (hv : vₘ ≫ q = t.app B ≫ R.map vₙ) :
    (Eₘ.map c ≫ vₘ ≫ eₘ.inv) ≫ t.app U =
      t.app A ≫ R.map (Eₙ.map c ≫ vₙ ≫ eₙ.inv) := by
  apply (cancel_mono (R.map eₙ.hom)).mp
  simp only [Category.assoc, Functor.map_comp]
  rw [← R.map_comp eₙ.inv eₙ.hom, Iso.inv_hom_id, R.map_id, Category.comp_id,
    hu, Iso.inv_hom_id_assoc, hv]
  exact (t.naturality_assoc c (R.map vₙ)).trans (by simp only [Functor.comp_map])

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The prescribed finite trace word. It is a morphism only at the specified
finite level and makes no assertion that it lifts to a system morphism.
Source: prop-coef-integral-dualizing, paragraph 2.
(blueprint: lem-coef-system-finite-counit-compatibility). -/
def integralDualizingFiniteTraceWord
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (c : G.openModules.mapDerivedCategory ⋙ G.properModules.rightDerivedFunctor ≅
      ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).i ⋙
        ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).g)
    (eU : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj
        G.baseTensors.systemClosed.monoidal.tensorUnit ≅
      (finiteDualizingRealization l E (Spec (.of D.k)) n).obj
        (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k))))
    (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj
        (G.properModules.rightDerivedFunctor.obj
          (G.openModules.mapDerivedCategory.obj (coefTraceInput l E X Q))) ⟶
      (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj
        G.baseTensors.systemClosed.monoidal.tensorUnit :=
  (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).map
      (c.hom.app (coefTraceInput l E X Q)) ≫
    (compactSupportSystemEvaluation l E (finiteDualizingCompactification D X) n).hom.app
      (coefTraceInput l E X Q) ≫
    (sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
      (Padic.coefficientExtensionRing l E (n + 1))).map (eQ n).hom ≫
    integralDualizingFiniteSystemCounit D l E X n ≫ (eU n).inv

/-- The finite counits, with the actual support and unit identifications, commute
with adjacent quotient arrows. This asserts no lift to the derived system category.

Source: prop-coef-integral-dualizing, paragraph 2; the counit identity in
lem-coef-finite-dualizing and the native compact-support evaluation comparison.
(blueprint: lem-coef-system-finite-counit-compatibility).

Proof: identify the ordinary open and proper functors with their native varying-ring
models using openRestriction and properRestriction. Restriction to constant integral
scalars is fully faithful on quotient module sheaves: locally the quotient scalar
map is surjective, so integral-linear maps between quotient modules are quotient-linear.
These identifications retain the actual underlying sheaf maps. Exact restriction and
the derived composition comparisons then give the natural support comparison c.
The tensor model identifies the base monoidal unit with the coefficient ring complex
in degree zero, by the unit universal property. Evaluate this one system isomorphism
and use the generator-normalized finiteDualizingIntrinsicUnit to obtain eU. Thus the
transitions of the evaluated unit are the genuine quotient maps.
For the counit square, expand integralDualizingFiniteTraceWord. Naturality moves c
past the source transition. The native evaluation square identifies the next factor
with the compact-support image of the quotient-semilinear transition of Q. Substitute
hQ to replace that transition by the scalar adjunct of the finite dualizing comparison.
Transport the resulting word to the ordinary etale site by finiteDualizingOrigin and
the canonical compact-support site comparison. The counit equation in
finiteDualizingCoefficientComparisons cancels the compact-support coefficient mate.
Naturality of the scalar-adjunction unit turns the remaining composite into the
quotient map of coefficient units after the old counit. The unit normalization of eU
identifies this with the actual target system transition. Transport back to intrinsic
coefficients and compose with the inverse eU maps, obtaining exactly the displayed
square. No equality of whole-system maps is inferred from their evaluations.
The argument remains valid for the empty scheme, zero complexes, and the residue
level n=0, and uses no flatness of a quotient map. -/
theorem integralDualizingFiniteCounit_compatible (hl : l ≠ D.p)
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (hQ : ∀ {m n : ℕ} (h : n ≤ m),
      (coefficientSequenceDerivedTransition l E X h).app (coefTraceInput l E X Q) ≫
          (normalizedDVRRes l E X h).map (eQ n).hom =
        (eQ m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h)) :
    ∃ (c : G.openModules.mapDerivedCategory ⋙ G.properModules.rightDerivedFunctor ≅
      ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).i ⋙
        ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).g)
      (eU : ∀ n : ℕ,
        (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj
          G.baseTensors.systemClosed.monoidal.tensorUnit ≅
        (finiteDualizingRealization l E (Spec (.of D.k)) n).obj
          (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))),
      ∀ n : ℕ,
        integralDualizingFiniteTraceWord D l E X S G Q eQ c eU (n + 1) ≫
            (coefficientSequenceDerivedTransition l E (Spec (.of D.k))
              (Nat.le_succ n)).app G.baseTensors.systemClosed.monoidal.tensorUnit =
          (coefficientSequenceDerivedTransition l E (Spec (.of D.k))
              (Nat.le_succ n)).app
              (G.properModules.rightDerivedFunctor.obj
                (G.openModules.mapDerivedCategory.obj (coefTraceInput l E X Q))) ≫
            (normalizedDVRRes l E (Spec (.of D.k)) (Nat.le_succ n)).map
              (integralDualizingFiniteTraceWord D l E X S G Q eQ c eU n) := by
  obtain ⟨jo, ⟨jp⟩⟩ := coefPairing_native_operations l E
    (finiteDualizingCompactification D X) S G
  have := ProEtale.VaryingRing.extensionAdditive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E)
      (finiteDualizingCompactification D X).i
  have := ProEtale.VaryingRing.extensionLimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E)
      (finiteDualizingCompactification D X).i
  have := ProEtale.VaryingRing.extensionColimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E)
      (finiteDualizingCompactification D X).i
  have := ProEtale.VaryingRing.push_additive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E)
      (finiteDualizingCompactification D X).g
  let c : G.openModules.mapDerivedCategory ⋙ G.properModules.rightDerivedFunctor ≅
      ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).i ⋙
        ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).g :=
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso jo)
      G.properModules.rightDerivedFunctor ≪≫
        Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso jp)
  obtain ⟨e⟩ := integralDualizingSystemUnit_iso l E (Spec (.of D.k)) G.baseTensors
  let eU := fun n ↦
    (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).mapIso e ≪≫
      integralDualizingRegularUnitEvaluation l E (Spec (.of D.k)) n
  have hu {m n : ℕ} (h : n ≤ m) :
      (coefficientSequenceDerivedTransition l E (Spec (.of D.k)) h).app
          G.baseTensors.systemClosed.monoidal.tensorUnit ≫
        (normalizedDVRRes l E (Spec (.of D.k)) h).map (eU n).hom =
      (eU m).hom ≫ integralDualizingFiniteUnitQuotient l E (Spec (.of D.k)) h := by
    dsimp only [eU, Iso.trans_hom, Functor.mapIso_hom]
    have he := (coefficientSequenceDerivedTransition l E (Spec (.of D.k)) h).naturality e.hom
    dsimp only [Functor.comp_map] at he
    rw [Functor.map_comp, ← Category.assoc, ← he]
    simp only [Category.assoc]
    rw [integralDualizingRegularUnit_transition]
  let M := coefTraceInput l E X Q
  let F := fun k ↦ sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
    (Padic.coefficientExtensionRing l E (k + 1))
  let v := fun k ↦ (compactSupportSystemEvaluation l E
    (finiteDualizingCompactification D X) k).hom.app M ≫
      (F k).map (eQ k).hom ≫ integralDualizingFiniteSystemCounit D l E X k
  have hv {m n : ℕ} (h : n ≤ m) :
      v m ≫ integralDualizingFiniteUnitQuotient l E (Spec (.of D.k)) h =
      (coefficientSequenceDerivedTransition l E (Spec (.of D.k)) h).app
          ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).i ⋙
            ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
              (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).g).obj M) ≫
        (normalizedDVRRes l E (Spec (.of D.k)) h).map (v n) := by
    let γX := integralDualizingNativeRestriction l E X h
    let γY := integralDualizingNativeRestriction l E (Spec (.of D.k)) h
    let RX := (proEtaleCoefficientRestrictScalars X
      (compactSupportLevelQuotient l E m n h)).mapDerivedCategory
    let RY := (proEtaleCoefficientRestrictScalars (Spec (.of D.k))
      (compactSupportLevelQuotient l E m n h)).mapDerivedCategory
    have hx := hQ h
    simp only [integralDualizingFiniteComparison, Equiv.apply_symm_apply] at hx
    have hx' := congrArg (fun f ↦ f ≫ γX.hom.app
      (integralDualizingFiniteTerm l E D X n)) hx
    have hg := γX.hom.naturality (eQ n).hom
    have htX := NatTrans.congr_app (integralDualizingNativeTransition_eq l E X h) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at htX
    have hxN : (compactSupportCoefficientTransition l E X h).app M ≫ RX.map (eQ n).hom =
        (eQ m).hom ≫ integralDualizingExceptionalTransition l E D X hl h ≫
          γX.hom.app (integralDualizingFiniteTerm l E D X n) := by
      simpa only [Category.assoc, hg, ← htX] using hx'
    have hs := compactSupportNativeSystemTransition l E
      (finiteDualizingCompactification D X) h M
    have hc := integralDualizingFiniteCounit_quotient l E D X hl h
    let Un := (finiteDualizingRealization l E (Spec (.of D.k)) n).obj
      (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))
    apply (cancel_mono (γY.hom.app Un)).1
    simp only [Category.assoc]
    rw [γY.hom.naturality]
    have htY := NatTrans.congr_app
      (integralDualizingNativeTransition_eq l E (Spec (.of D.k)) h)
      ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).i ⋙
        ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).g).obj M)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at htY
    erw [reassoc_of% htY]
    simpa only [v, RY, Functor.comp_obj, Category.assoc] using
      support_counit_square (F m) (F n) RX RY
      (sfCompactSupportRestriction (finiteDualizingCompactification D X)
        (compactSupportLevelQuotient l E m n h)).hom
      ((compactSupportSystemEvaluation l E (finiteDualizingCompactification D X) m).hom.app M)
      ((compactSupportSystemEvaluation l E (finiteDualizingCompactification D X) n).hom.app M)
      (eQ m).hom (eQ n).hom
      ((compactSupportCoefficientTransition l E X h).app M)
      (integralDualizingExceptionalTransition l E D X hl h ≫
        γX.hom.app (integralDualizingFiniteTerm l E D X n))
      ((compactSupportCoefficientTransition l E (Spec (.of D.k)) h).app _)
      (integralDualizingFiniteUnitQuotient l E (Spec (.of D.k)) h ≫ γY.hom.app Un)
      (integralDualizingFiniteSystemCounit D l E X m)
      (integralDualizingFiniteSystemCounit D l E X n) hxN hs hc
  refine ⟨c, eU, ?_⟩
  intro n
  simpa only [integralDualizingFiniteTraceWord, v, M, F, Functor.comp_obj,
    Category.assoc] using
    trace_natural_square
      (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) (n + 1))
      (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n)
      (normalizedDVRRes l E (Spec (.of D.k)) (Nat.le_succ n))
      (coefficientSequenceDerivedTransition l E (Spec (.of D.k)) (Nat.le_succ n))
      (c.hom.app M) (eU (n + 1)) (eU n) (v (n + 1)) (v n)
      (integralDualizingFiniteUnitQuotient l E (Spec (.of D.k)) (Nat.le_succ n))
      (hu (Nat.le_succ n)) (hv (Nat.le_succ n))

end WeilConjectures
