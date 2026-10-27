module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.ScalarCompletionAssociator
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.PbcCommonStageCones
public import Sheaf.Paper.FdCoefficientComparison
public import Sheaf.Paper.FdCompletionInverseScalarCoherence
public import Sheaf.Paper.FdHomLinearEquivalence
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Triangulated.Adjunction
import Sheaf.Paper.FdIntegralIdentityRationalEquivalence
import Sheaf.Paper.FdCommonStageComparisonDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.CharP.CharAndCard
import Sheaf.Paper.FdCompletionFiniteStageLinear

/-! # Framework and PBC coefficients before smooth purity transport

Source: current blueprint, sec-smooth-purity/sk-thm-purity-transport,
proof Steps 2 and 4; the extracted framework/PBC comparison interface
(blueprint: lem-pur-framework-pbc-coefficient-category-comparison).

The existing comparison datum retains the actual integral coefficient transport,
raw localizations, normalized completion maps and literal common-stage categories.
The additional conclusions specify inverse formulas, units and Hom-colimit bijections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
-- Some statement binders select dependent instances without occurring by name.
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w a b v v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem rawCategoryHEq
    (l : ℕ) [Fact l.Prime] {A B : Type u}
    [fa : Field A] [fb : Field B]
    [aa : Algebra ℚ_[l] A] [ab : Algebra ℚ_[l] B]
    [na : FiniteDimensional ℚ_[l] A] [nb : FiniteDimensional ℚ_[l] B]
    (T : Scheme.{u}) (h : A = B) (hf : HEq fa fb) (ha : HEq aa ab) :
    HEq (inferInstance : Category (sfRationalConstructibleCategory l A T))
      (inferInstance : Category (sfRationalConstructibleCategory l B T)) := by
  cases h
  cases hf
  cases ha
  rfl

private theorem finiteCategoryHEq
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) :
    HEq (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω T E)
      (inferInstance : Category
        (sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)) := by
  exact rawCategoryHEq l T (by rfl) (by
    unfold pbcFiniteFieldField
    rfl) (by
    unfold pbcFiniteFieldAlgebra
    rfl)

private theorem inverseIsoHEq {A : Type*} [Category A] {X Y X' Y' : A}
    (e : X ≅ Y) (f : X' ≅ Y') (hx : X = X') (hy : Y = Y')
    (h : HEq e.hom f.hom) : HEq e.inv f.inv := by
  subst X'
  subst Y'
  have h' : e = f := Iso.ext (eq_of_heq h)
  subst f
  rfl

private theorem propOfEqHEq {A : Sort*} {B : A → Sort*}
    (P : ∀ a, B a → Prop) {a a' : A} {b : B a} {b' : B a'}
    (ha : a = a') (hb : HEq b b') (h : P a' b') : P a b := by
  cases ha
  cases hb
  exact h

private theorem equivalenceOfHEq
    {A B : Type a} {D : Type b} [ca : Category.{v} A] [cb : Category.{v} B]
    [Category.{v'} D]
    (hAB : A = B) (hab : HEq ca cb) (F : A ⥤ D) (e : B ≌ D)
    (h : HEq F e.functor) : F.IsEquivalence := by
  subst B
  have hab' : ca = cb := eq_of_heq hab
  subst cb
  have h' : F = e.functor := eq_of_heq h
  subst F
  infer_instance

private theorem comparisonInclusions
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ B) (f : C ≌ D) (i : C ⥤ A) (j : D ⥤ B)
    (γ : i ⋙ e.functor ≅ f.functor ⋙ j) :
    ∃ α : j ⋙ e.inverse ≅ f.inverse ⋙ i,
      ∀ K, ∃ ε : e.functor.obj (i.obj (f.inverse.obj K)) ≅ j.obj K,
        ε.hom = γ.hom.app (f.inverse.obj K) ≫ j.map (f.counitIso.hom.app K) ∧
        e.functor.map (α.hom.app K) ≫ ε.hom = e.counitIso.hom.app (j.obj K) := by
  let ε : (f.inverse ⋙ i) ⋙ e.functor ≅ j :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft f.inverse γ ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight f.counitIso j ≪≫ j.leftUnitor
  let δ : (j ⋙ e.inverse) ⋙ e.functor ≅ (f.inverse ⋙ i) ⋙ e.functor :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft j e.counitIso ≪≫
      j.rightUnitor ≪≫ ε.symm
  let α := Functor.fullyFaithfulCancelRight e.functor δ
  refine ⟨α, fun K ↦ ⟨ε.app K, ?_, ?_⟩⟩
  · simp [ε]
  · change e.functor.map (e.functor.preimage (δ.hom.app K)) ≫ _ = _
    rw [Functor.map_preimage]
    simp [δ]

private theorem stageInclusionComponents
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {A : I → Type*} [∀ i, Category (A i)]
    {B : I → Type*} [∀ i, Category (B i)]
    {S : StageSystem A} {P : StageSystem B} (J : S.Morphism P) (i : I) :
    ∀ X, ∃ hx : (S.ι i ⋙ J.functor).obj X = (J.Φ i ⋙ P.ι i).obj X,
      (J.ιCompFunctorIso i).hom.app X = eqToHom hx := by
  intro X
  exact ⟨rfl, rfl⟩

private theorem eqToIsoComponents
    {A B : Type*} [Category A] [Category B] {F G H : A ⥤ B}
    (h : F = G) (η : G ≅ H)
    (hη : ∀ X, ∃ hx : G.obj X = H.obj X, η.hom.app X = eqToHom hx) :
    ∀ X, ∃ hx : F.obj X = H.obj X,
      (eqToIso h ≪≫ η).hom.app X = eqToHom hx := by
  subst G
  simpa using hη

private theorem comparisonInclusionsHEq
    {A B : Type*} {C C' : Type a} {D : Type*}
    [Category A] [Category B] [cc : Category.{v} C] [cc' : Category.{v} C']
    [Category D] (e : A ≌ B) (f : C' ≌ D) (i : C ⥤ A) (j : D ⥤ B)
    (F : C ⥤ D) (ht : C = C') (hc : HEq cc cc') (hF : HEq F f.functor)
    (γ : i ⋙ e.functor ≅ F ⋙ j)
    (hγ : ∀ X, ∃ h : (i ⋙ e.functor).obj X = (F ⋙ j).obj X,
      γ.hom.app X = eqToHom h) :
    ∃ R : D ⥤ C, HEq R f.inverse ∧
      ∃ α : j ⋙ e.inverse ≅ R ⋙ i,
        ∀ K, ∃ ε : e.functor.obj (i.obj (R.obj K)) ≅ j.obj K,
          HEq ε.hom (j.map (f.counitIso.hom.app K)) ∧
          e.functor.map (α.hom.app K) ≫ ε.hom = e.counitIso.hom.app (j.obj K) := by
  subst C'
  have hc' := eq_of_heq hc
  subst cc'
  have hF' := eq_of_heq hF
  subst F
  obtain ⟨α, hα⟩ := comparisonInclusions e f i j γ
  refine ⟨f.inverse, HEq.rfl, α, fun K ↦ ?_⟩
  obtain ⟨ε, hε, hε'⟩ := hα K
  refine ⟨ε, ?_, hε'⟩
  obtain ⟨h, hh⟩ := hγ (f.inverse.obj K)
  rw [hε, hh]
  exact eqToHom_comp_heq _ _

section FiniteConstruction
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (stage : ∀ E, FdRationalStageComparison l Ω T E)
  (c : FdCompletionScalarComparison l Ω T stage)

@[irreducible] private def completionFinite : FdFiniteCoefficientComparison l Ω T :=
  { stage := stage
    family := c.family
    finite_functor := c.finite_functor
    finite_shift := c.finite_shift
    finite_shift_normalization := c.finite_shift_normalization
    scalar_shift := fun h ↦ (c.scalar_shift h).1
    ordinary := c.integral.ordinary
    integral_scalar := c.integral.comparison
    integral_scalar_lift := fun h ↦
      ⟨c.integral.integral h, c.integral.restriction h, c.scalar_lift h⟩
    chi := c.integral.chi }

private theorem completionFinite_spec :
    (completionFinite l Ω T stage c).stage = stage ∧
    (completionFinite l Ω T stage c).family = c.family ∧
    HEq (completionFinite l Ω T stage c).finite_shift c.finite_shift := by
  unfold completionFinite
  exact ⟨rfl, rfl, HEq.rfl⟩

private theorem adjointComparisonExists (C : FdCoefficientComparison l Ω T) :
    ∃ C' : FdCoefficientComparison l Ω T,
      C'.stage = C.stage ∧ C'.family = C.family ∧
      HEq C'.finite_shift C.finite_shift ∧
      (fun [s : C'.equivalence.inverse.CommShift ℤ] ↦
        C'.equivalence.toAdjunction.CommShift ℤ) (s := C'.pair_inverse_shift) := by
  let := C.pair_additive
  let := C.pair_exact
  let r := C.equivalence.commShiftInverse ℤ
  let := r
  have hadj : C.equivalence.toAdjunction.CommShift ℤ :=
    C.equivalence.commShift_of_functor ℤ
  refine ⟨{ C with pair_inverse_shift := r
                   pair_inverse_exact := ?_ }, rfl, rfl, HEq.rfl, hadj⟩
  let := hadj
  exact C.equivalence.toAdjunction.isTriangulated_rightAdjoint

end FiniteConstruction

/-- The specified identity comparison of integral coefficients induces coherent exact
linear equivalences on raw rational stages and their literal common-stage categories.
Source: current blueprint, smooth-purity transport proof, Steps 2 and 4
(blueprint: lem-pur-framework-pbc-coefficient-category-comparison).

Proof:
1. Finite type over Spec k makes W locally Noetherian and quasi-compact, hence
Noetherian. Apply exists_topologicalKrullDim_le. The finite-field cardinality
identifies the characteristic with p, so ell is a unit in k and in every stalk.
2. Apply fdIntegralIdentityRationalEquivalence at each finite field, retaining its
inverse object, tensor, scalar and shift formulas. Uniqueness identifies its
coefficient lift with purCoefficientIso. Apply fdCompletionInverseScalarCoherence
to these stages, and assemble its integral/scalar data as a finite comparison.
3. Apply fdNormalizedCommonStageDescent, retaining the equalities of stage, family
and forward shift. The smaller theorem fdCompletionFiniteStageLinear supplies
finite-field linearity. Exactness gives additivity; the finite_functor comparison
and an abstract transport of the source category give finite equivalences.
4. Invert the scalar unit comparison. Apply fdHomLinearEquivalence to obtain the
specified Hom-colimit bijections and pair linearity. Mathlib gives inverse
additivity and linearity. Choose the adjunction-induced inverse shift, for which
Mathlib gives adjunction compatibility and exactness. Full faithfulness and
forward exactness give reflection of the existing common-stage triangles.
5. The forward inclusion isomorphism has equality-transport components. Compose
it with the included finite counit and cancel the fully faithful pair functor
to construct the inverse inclusion isomorphism. Its defining cancellation
equation is the required pair counit equation. The equality-transport components
identify the included counit heterogeneously with the required finite counit.
No Karoubi completion is used. -/
theorem purFrameworkPbcCoefficientCategoryComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (W : Over (Spec (.of D.k))) [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    [IsSeparated W.hom] :
    ∃ (hN : IsNoetherian W.left)
      (hD : Fact (∃ n : ℕ, topologicalKrullDim W.left ≤ n))
      (hI : Fact (∀ x : W.left, IsUnit (l : W.left.presheaf.stalk x))),
    (fun [nW : IsNoetherian W.left]
      [dW : Fact (∃ n : ℕ, topologicalKrullDim W.left ≤ n)]
      [iW : Fact (∀ x : W.left, IsUnit (l : W.left.presheaf.stalk x))] ↦
      ∃ C : FdCoefficientComparison l Ω W.left,
        (∀ E : Padic.FiniteCoefficientFields l Ω,
          (∀ K : pbcStageCategory l Ω W.left E,
            (C.stage E).rational.inverse.obj K = ⟨(C.stage E).integral.inverse.obj K.obj⟩) ∧
          (∀ (K H : pbcIntegralStage l Ω W.left E)
            (a : Localization.Away (pbcStageUniformizer.{u} l Ω E)) (f : K ⟶ H),
            HEq ((C.stage E).rational.inverse.map
              (fdRawTensor (pbcStageUniformizer.{u} l Ω E) a f))
              (fdRawTensor
                (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E))
                ((sfRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E)).symm
                  (pbcRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E) a))
                ((C.stage E).integral.inverse.map f))) ∧
          (∀ (K H : pbcStageCategory l Ω W.left E)
            (a : Localization.Away (pbcStageUniformizer.{u} l Ω E)) (f : K ⟶ H),
            (C.stage E).rational.inverse.map
                (fdRawScale (pbcStageUniformizer.{u} l Ω E) a f) =
              fdRawScale
                (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E))
                ((sfRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E)).symm
                  (pbcRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E) a))
                ((C.stage E).rational.inverse.map f)) ∧
          (∃ si : (C.stage E).integral.inverse.CommShift ℤ,
            (fun [inverseIntegralShift : (C.stage E).integral.inverse.CommShift ℤ]
              [inverseRationalShift : (C.stage E).rational.inverse.CommShift ℤ] ↦
              (∀ (n : ℤ) (K : pbcIntegralStage l Ω W.left E),
                HEq ((C.stage E).rational.inverse.map
                    (((pbcStageLocalization l Ω W.left E).commShiftIso n).hom.app K) ≫
                  ((C.stage E).rational.inverse.commShiftIso n).hom.app
                    ((pbcStageLocalization l Ω W.left E).obj K))
                  ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E)
                        W.left).map
                      (((C.stage E).integral.inverse.commShiftIso n).hom.app K) ≫
                    ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E)
                        W.left).commShiftIso n).hom.app ((C.stage E).integral.inverse.obj K))) ∧
              (∀ (n : ℤ) (K : pbcIntegralStage l Ω W.left E),
                HEq ((sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) W.left).ι.map
                      (((C.stage E).integral.inverse.commShiftIso n).hom.app K) ≫
                    ((sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) W.left).ι.commShiftIso
                      n).hom.app ((C.stage E).integral.inverse.obj K))
                  ((pbcDerivedRestrict
                      (purCoefficientIso l (pbcFiniteField.{u} l Ω E) W.left).inv).map
                      (((pbcStageInclusion l Ω W.left E).commShiftIso n).hom.app K) ≫
                    (((pbcRestrict
                        (purCoefficientIso l (pbcFiniteField.{u} l Ω E) W.left).inv)
                      |>.mapDerivedCategory).commShiftIso n).hom.app K.obj)))
              (inverseIntegralShift := si)
              (inverseRationalShift := (C.stage E).inverse_exact)) ∧
          (C.stage E).integral.inverse ⋙
              (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) W.left).ι =
            pbcStageInclusion l Ω W.left E ⋙
              pbcDerivedRestrict (purCoefficientIso l (pbcFiniteField.{u} l Ω E) W.left).inv) ∧
        (∀ E, (C.family.Φ E).Linear E.val) ∧
        FdInverseScalarCoherence C.family ∧
        (∀ (E : Padic.FiniteCoefficientFields l Ω)
          (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω W.left E),
          HEq ((C.family.β (le_refl E)).inv.app K)
            ((C.family.Φ E).map
              ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω W.left E).hom.app K))) ∧
        C.equivalence.functor.Linear Ω ∧ C.equivalence.inverse.Linear Ω ∧
        C.equivalence.inverse.Additive ∧
        (fun [inversePairShift : C.equivalence.inverse.CommShift ℤ] ↦
          C.equivalence.toAdjunction.CommShift ℤ)
          (inversePairShift := C.pair_inverse_shift) ∧
        (∀ A : Triangle (generalAlgebraicallyClosedConstructibleCategory l Ω W.left),
          C.equivalence.functor.mapTriangle.obj A ∈ distTriang (pbcQbarCategory l Ω W.left) ↔
            A ∈ distTriang (generalAlgebraicallyClosedConstructibleCategory l Ω W.left)) ∧
        (∃ he : ∀ E, (C.family.Φ E).IsEquivalence,
          (fun [eqv : ∀ E, (C.family.Φ E).IsEquivalence] ↦
            FdHomLinearEquivalence l Ω W.left C.family) (eqv := he)) ∧
        (∀ E, ∃ R : pbcStageCategory l Ω W.left E ⥤
            GeneralAlgebraicallyClosedCoefficients.Stage l Ω W.left E,
          HEq R (C.stage E).rational.inverse ∧
          ∃ α : (pbcScalarSystem l Ω W.left dW.out iW.out).ι E ⋙ C.equivalence.inverse ≅
              R ⋙ (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W.left).ι E,
          ∀ K, ∃ ε : C.equivalence.functor.obj
                (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W.left).ι E).obj
                  (R.obj K)) ≅
              ((pbcScalarSystem l Ω W.left dW.out iW.out).ι E).obj K,
            HEq ε.hom (((pbcScalarSystem l Ω W.left dW.out iW.out).ι E).map
              ((C.stage E).rational.counitIso.hom.app K)) ∧
            C.equivalence.functor.map (α.hom.app K) ≫ ε.hom =
              C.equivalence.counitIso.hom.app
                (((pbcScalarSystem l Ω W.left dW.out iW.out).ι E).obj K)))
      (nW := hN) (dW := hD) (iW := hI) := by
  classical
  have : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  have : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace W.hom
  let hN : IsNoetherian W.left := ⟨⟩
  let hD : Fact (∃ n : ℕ, topologicalKrullDim W.left ≤ n) :=
    ⟨exists_topologicalKrullDim_le W.hom⟩
  have hinv : ∀ x : W.left, IsUnit (l : W.left.presheaf.stalk x) := by
    let : Fintype D.k₀ := Fintype.ofFinite _
    have : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
    have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    have hl0 : (l : D.k) ≠ 0 :=
      CharP.cast_ne_zero_of_ne_of_prime _ (Fact.out : l.Prime) _hl.symm
    intro x
    let φ := ((Scheme.ΓSpecIso (.of D.k)).inv ≫
      W.hom.appTop ≫ W.left.presheaf.Γgerm x).hom
    simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hl0).map φ
  let hI : Fact (∀ x : W.left, IsUnit (l : W.left.presheaf.stalk x)) := ⟨hinv⟩
  refine ⟨hN, hD, hI, ?_⟩
  let := hN
  let := hD
  let := hI
  obtain ⟨stage, stage_spec⟩ := Classical.axiomOfChoice
    (fun E : Padic.FiniteCoefficientFields l Ω ↦
      fdIntegralIdentityRationalEquivalence D l _hl Ω W.left E)
  obtain ⟨c⟩ := fdCompletionInverseScalarCoherence D l _hl Ω W.left stage
  let finite := completionFinite l Ω W.left stage c
  have hs := completionFinite_spec l Ω W.left stage c
  obtain ⟨C, hstage, hfamily, hshift, _⟩ := fdNormalizedCommonStageDescent l Ω W.left finite
  obtain ⟨C', hstageC, hfamilyC, hshiftC, hadj⟩ :=
    adjointComparisonExists l Ω W.left C
  let := C'.pair_additive
  let := C'.pair_exact
  let := C'.pair_inverse_shift
  have hstage' : C'.stage = stage := hstageC.trans (hstage.trans hs.1)
  have hfamily' : C'.family = c.family := hfamilyC.trans (hfamily.trans hs.2.1)
  have hlin : ∀ E, (C'.family.Φ E).Linear E.val := by
    rw [hfamily']
    exact fdCompletionFiniteStageLinear l Ω W.left stage c
  have hexact : ∀ E, (C'.family.Φ E).IsTriangulated := by
    exact propOfEqHEq
      (fun (J : StageSystem.Morphism
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W.left)
          (pbcScalarSystem l Ω W.left hD.out hI.out))
        (s : ∀ E, (J.Φ E).CommShift ℤ) ↦
        ∀ E, @Functor.IsTriangulated _ _ _ _ _ _ (J.Φ E) (s E) _ _ _ _ _ _ _ _)
      hfamily'
      (show HEq C'.finite_shift c.finite_shift from hshiftC.trans (hshift.trans hs.2.2))
      c.exact
  have hadd : ∀ E, (C'.family.Φ E).Additive := by
    intro E
    let := hexact E
    infer_instance
  have hequiv : ∀ E, (C'.family.Φ E).IsEquivalence := by
    intro E
    apply equivalenceOfHEq (F := C'.family.Φ E) (e := (C'.stage E).rational)
      (by
        dsimp only [GeneralAlgebraicallyClosedCoefficients.Stage,
          AlgebraicallyClosedCoefficients.Coefficient, pbcFiniteField]
        rfl)
      (finiteCategoryHEq l Ω W.left E)
    exact C'.finite_functor E
  have hunit : ∀ E (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω W.left E),
      HEq ((C'.family.β (le_refl E)).inv.app K)
        ((C'.family.Φ E).map
          ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω W.left E).hom.app K)) := by
    rw [hfamily']
    exact c.unit
  have hunit' : ∀ E (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω W.left E),
      HEq ((C'.family.β (le_refl E)).hom.app K)
        ((C'.family.Φ E).map
          ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω W.left E).inv.app K)) := by
    intro E K
    have h := inverseIsoHEq ((C'.family.β (le_refl E)).symm.app K)
      ((C'.family.Φ E).mapIso
        ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω W.left E).app K))
      (by
        exact congrArg (fun F ↦ (C'.family.Φ E).obj (F.obj K))
          ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
            l Ω W.left).exists.choose_spec.1 E E (le_refl E)))
      (by
        exact congrArg (fun F ↦ F.obj ((C'.family.Φ E).obj K))
          (pbcScalarSystem_units l Ω W.left hD.out hI.out (le_refl E)).1)
      (hunit E K)
    exact h
  let := hequiv
  have hhom := fdHomLinearEquivalence l Ω W.left C'.family D _hl
    hadd hlin hexact C'.scalar_shift hunit'
  have hlinear : C'.equivalence.functor.Linear Ω := by
    rw [C'.pair_functor]
    obtain ⟨_, _, _, _, _, hom, _, _, _, _, hh, _⟩ := hhom
    exact hh
  let := hlinear
  refine ⟨C', ?_, hlin, ?_, hunit, hlinear, inferInstance,
    C'.equivalence.toAdjunction.right_adjoint_additive, hadj,
    ?_, ⟨hequiv, hhom⟩, ?_⟩
  · intro E
    rw [hstage']
    obtain ⟨si, ha, hb, hc, hd, he, hf, ho, ht, hscale, hiscale, hshift,
      e, heq, hi, hishift, _⟩ := stage_spec E
    have he : e = purCoefficientIso l (pbcFiniteField.{u} l Ω E) W.left :=
      (purCoefficientIso_existsUnique l (pbcFiniteField.{u} l Ω E) W.left).unique
        heq (purCoefficientIso_existsUnique l (pbcFiniteField.{u} l Ω E)
          W.left).exists.choose_spec
    subst e
    exact ⟨ho, ht, hiscale, ⟨si, hshift, hishift⟩, hi⟩
  · rw [hfamily']
    exact c.coherence
  · let := C'.pair_exact
    exact C'.equivalence.functor.map_distinguished_iff
  · intro E
    let γ : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W.left).ι E ⋙
        C'.equivalence.functor ≅ C'.family.Φ E ⋙
          (pbcScalarSystem l Ω W.left hD.out hI.out).ι E :=
      eqToIso (congrArg (fun F ↦
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W.left).ι E ⋙ F)
        C'.pair_functor) ≪≫ C'.family.ιCompFunctorIso E
    apply comparisonInclusionsHEq C'.equivalence (C'.stage E).rational
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W.left).ι E)
      ((pbcScalarSystem l Ω W.left hD.out hI.out).ι E) (C'.family.Φ E)
      (by rfl) (finiteCategoryHEq l Ω W.left E) (C'.finite_functor E) γ
    exact eqToIsoComponents _ _ (stageInclusionComponents C'.family E)

end WeilConjectures
