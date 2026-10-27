module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.CompletedDerivedInverseLimit
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.NormalizedDVRKFlatTransition
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Roos realization with prescribed quotient-linear reductions

Source: blueprint main-20261015, sec-smooth-purity, sk-thm-purity-transport,
thm-pur-adic-reconstruction.proof.md, final sentence; Stacks Tags 08TC, 0941 and 07A6
(blueprint: lem-pur-adic-roos-realization-reductions).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.AdicRoos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  normalizedDVRResCompletedComp normalizedDVRKFlatComparison
  scalarReductionDerivedExtension scalarReductionCounit
private abbrev localSize : EssentiallySmall.{max u (t + 1)} W.ProEt :=
  essentiallySmallSelf.{u} W.ProEt
attribute [local instance 4000] localSize

private abbrev localSheafify : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} W
attribute [local instance] localSheafify

private abbrev localLocallyBijective :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} W
attribute [local instance] localLocallyBijective

/-- A Roos triangle makes its projections a cone on adjacent transitions. -/
private theorem adjacentRoosProjection
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K : ℕ → C} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    (L : C) (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle f L p δ) (n : ℕ) :
    p ≫ Pi.π K (n + 1) ≫ f n = p ≫ Pi.π K n := by
  have hz : p ≫ towerTransitionEndomorphism f = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₁₂ _ hc
  have hn := congrArg (fun a ↦ a ≫ Pi.π K n) hz
  simp only [towerTransitionEndomorphism, Preadditive.comp_sub, Category.comp_id,
    Preadditive.sub_comp, Category.assoc, towerProductShift, Pi.lift_π,
    zero_comp] at hn
  exact (sub_eq_zero.mp hn).symm

/-- Transpose a cone equation across the two completed scalar adjunctions. -/
private theorem adjointTransition
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (S : B ⥤ A) (e : S ⋙ Rm ≅ Rn)
    {M : C} {P : A} {Q : B} (a : M ⟶ Rm.obj P) (b : M ⟶ Rn.obj Q)
    (v : P ⟶ S.obj Q) (h : a ≫ Rm.map v ≫ e.hom.app Q = b) :
    (am.homEquiv M P).symm a ≫ v =
      (am.homEquiv M (S.obj (Ln.obj M))).symm
          (an.unit.app M ≫ e.inv.app (Ln.obj M)) ≫
        S.map ((an.homEquiv M Q).symm b) := by
  apply (am.homEquiv M (S.obj Q)).injective
  rw [am.homEquiv_naturality_right, Equiv.apply_symm_apply,
    am.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply (cancel_mono (e.hom.app Q)).1
  simp only [Category.assoc]
  have he := e.hom.naturality ((an.homEquiv M Q).symm b)
  dsimp only [Functor.comp_map] at he
  rw [he]
  rw [Iso.inv_hom_id_app_assoc]
  rw [← an.homEquiv_unit, Equiv.apply_symm_apply]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedDVRTransition_comp {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    normalizedDVRTowerTransition l E W D hl hrm ≫
        normalizedDVRTowerTransition l E W D hl hmn =
      normalizedDVRTowerTransition l E W D hl (le_trans hmn hrm) := by
  dsimp only [normalizedDVRTowerTransition]
  rw [Localization.comp_liftNatTrans]
  congr 1
  ext K
  change DerivedCategory.Q.map (K.asFunctor.map (homOfLE hrm).op) ≫
    DerivedCategory.Q.map (K.asFunctor.map (homOfLE hmn).op) =
    DerivedCategory.Q.map (K.asFunctor.map (homOfLE (le_trans hmn hrm)).op)
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedDVRTransition_refl (n : ℕ) :
    normalizedDVRTowerTransition l E W D hl (Nat.le_refl n) =
      𝟙 (normalizedDVRTowerEvaluation l E W D hl n) := by
  have he : (evaluation ℕᵒᵖ (completedIntegralModuleSheaves l E W D hl)).map
      (homOfLE (Nat.le_refl n)).op = 𝟙 _ :=
    (evaluation ℕᵒᵖ (completedIntegralModuleSheaves l E W D hl)).map_id (op n)
  dsimp only [normalizedDVRTowerTransition]
  rw [he, NatTrans.mapHomologicalComplex_id, Functor.whiskerRight_id',
    Localization.liftNatTrans_id]

private theorem normalizedDVRRoosProjection (T : NormalizedDVRTower l E W D hl)
    (M : completedIntegralDerivedCategory l E W D hl)
    [HasProduct (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E W D hl n).obj T.tower)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E W D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E W D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E W D hl n.le_succ).app T.tower)
      M p δ) {m n : ℕ} (h : n ≤ m) :
    p ≫ Pi.π _ m ≫ (normalizedDVRTowerTransition l E W D hl h).app T.tower =
      p ≫ Pi.π _ n := by
  induction m, h using Nat.le_induction with
  | base => simp only [normalizedDVRTransition_refl, NatTrans.id_app, Category.comp_id]
  | succ m h ih =>
    rw [← normalizedDVRTransition_comp l E W D hl m.le_succ h, NatTrans.comp_app]
    calc
      _ = (p ≫ Pi.π _ (m + 1) ≫
          (normalizedDVRTowerTransition l E W D hl m.le_succ).app T.tower) ≫
          (normalizedDVRTowerTransition l E W D hl h).app T.tower := by
        simp only [Category.assoc]
      _ = _ := by rw [adjacentRoosProjection _ M p δ hc m]
                  simpa only [Category.assoc] using ih

private theorem representativeComparison_isIso (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)}
      (J := AlgebraicGeometry.Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) P) :
    IsIso (normalizedDVRKFlatComparison l E W n P) := by
  unfold normalizedDVRKFlatComparison
  exact IsIso.comp_isIso'
    (@Functor.map_isIso _ _ _ _ _ _ _ _
      (unrestrictedTowerCounit_isIso l E W n P hP))
    (NatIso.hom_app_isIso _ _)

open CategoryTheory.Pretriangulated in
/-- Transport a Roos triangle while retaining both specified product instances. -/
private theorem roosTransportFixed
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {X Y : ℕ → C} [HasProduct X] [HasProduct Y]
    (f : ∀ n, X (n + 1) ⟶ X n) (g : ∀ n, Y (n + 1) ⟶ Y n)
    (M : C) (p : M ⟶ ∏ᶜ X) (δ : (∏ᶜ X) ⟶ M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle f M p δ)
    (a : ∀ n, X n ≅ Y n) (q : ∀ n, M ⟶ Y n)
    (ht : ∀ n, f n ≫ (a n).hom = (a (n + 1)).hom ≫ g n)
    (hp : ∀ n, p ≫ Pi.π X n ≫ (a n).hom = q n) :
    ∃ δ' : (∏ᶜ Y) ⟶ M⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle g M (Pi.lift q) δ' := by
  let A : (∏ᶜ X) ≅ (∏ᶜ Y) :=
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc]
      inv_hom_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc] }
  refine ⟨A.inv ≫ δ, ?_⟩
  apply isomorphic_distinguished _ hc _
  refine Triangle.isoMk _ _ (Iso.refl M) A.symm A.symm ?_ ?_ ?_
  · change Pi.lift q ≫ A.inv = 𝟙 M ≫ p
    apply Pi.hom_ext
    intro n
    simp only [A, Category.assoc, Limits.Pi.map_π, Pi.lift_π_assoc,
      Category.id_comp]
    apply (cancel_mono (a n).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using (hp n).symm
  · exact (towerTransitionEndomorphism_natural_backward g f
      (fun n ↦ (a n).inv) (fun n ↦ by
        apply (cancel_mono (a n).hom).1
        simpa [Category.assoc] using
          congrArg (fun k ↦ (a (n + 1)).inv ≫ k) (ht n))).symm
  · change (A.inv ≫ δ) ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 M) = A.inv ≫ δ
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

open CategoryTheory.Pretriangulated in
/-- Rotated TR3 compares two Roos triangles over the same transition endomorphism. -/
private theorem roosComparison
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {X : ℕ → C} [HasProduct X] (f : ∀ n, X (n + 1) ⟶ X n)
    {K L : C} (p : K ⟶ ∏ᶜ X) (q : L ⟶ ∏ᶜ X)
    (δ : ∏ᶜ X ⟶ K⟦(1 : ℤ)⟧) (ε : ∏ᶜ X ⟶ L⟦(1 : ℤ)⟧)
    (hp : IsDerivedLimitTriangle f K p δ) (hq : IsDerivedLimitTriangle f L q ε) :
    ∃ e : K ≅ L, e.hom ≫ q = p := by
  let T := Triangle.mk p (towerTransitionEndomorphism f) δ
  let U := Triangle.mk q (towerTransitionEndomorphism f) ε
  let a := isoTriangleOfIso₁₂ T.rotate U.rotate
    ((rotate_distinguished_triangle _).mp hp)
    ((rotate_distinguished_triangle _).mp hq)
    (Iso.refl _) (Iso.refl _) (by simp [T, U])
  let e := (shiftFunctor C (1 : ℤ)).preimageIso (Triangle.π₃.mapIso a)
  refine ⟨e, ?_⟩
  apply (shiftFunctor C (1 : ℤ)).map_injective
  have h := a.hom.comm₃
  have ha : a.hom.hom₁ = 𝟙 _ := by simp [a]
  rw [ha] at h
  simpa [e, T, U, CategoryTheory.Functor.map_comp] using h.symm

/-- The normalized completed-to-finite scalar adjunction supplied by the recorded theorem.
Source: Stacks Tag 07A6 (blueprint: lem-pur-adic-roos-realization-reductions). -/
def adjunction (n : ℕ) :
    scalarReductionDerivedExtension l E W n ⊣ normalizedDVRResCompleted l E W D hl n :=
  (derivedScalarExtensionRestrictionAdjunction l E W n).choose

/-- The quotient-linear reduction transition, as the transpose of the next reduction unit.
This is the restriction-adjoint form of the canonical scalar associator. In particular
no finite quotient is assumed flat.
Source: Stacks Tags 07A6 and 0D6D
(blueprint: lem-pur-adic-roos-realization-reductions). -/
def quotientUnit (P : completedIntegralDerivedCategory l E W D hl)
    {m n : ℕ} (h : n ≤ m) :
    (scalarReductionDerivedExtension l E W m).obj P ⟶
      (normalizedDVRRes l E W h).obj ((scalarReductionDerivedExtension l E W n).obj P) :=
  ((adjunction l E W D hl m).homEquiv _ _).symm
    ((adjunction l E W D hl n).unit.app P ≫
      (normalizedDVRResCompletedComp l E W D hl h).inv.app
        ((scalarReductionDerivedExtension l E W n).obj P))

/-- The evaluated strict tower, retaining the canonical derived transition maps.
Source: Stacks Tag 0941 (blueprint: lem-pur-adic-roos-realization-reductions). -/
def evaluated (Z : normalizedDVRDerivedTowers l E W D hl) :
    ℕᵒᵖ ⥤ completedIntegralDerivedCategory l E W D hl :=
  Functor.ofOpSequence
    (X := fun n ↦ (normalizedDVRTowerEvaluation l E W D hl n).obj Z) (fun n ↦
    (normalizedDVRTowerTransition l E W D hl (Nat.le_succ n)).app Z)

/-- The actual projection at a finite level, expressed in its quotient scalar category
by the specified evaluation identification.
Source: Stacks Tag 0941 (blueprint: lem-pur-adic-roos-realization-reductions). -/
def projection
    (RF : normalizedDVRDerivedTowers l E W D hl ⥤ completedIntegralDerivedCategory l E W D hl)
    [HasCountableProducts (completedIntegralDerivedCategory l E W D hl)]
    (p : ∀ Z, RF.obj Z ⟶ ∏ᶜ (fun n : ℕ ↦ (evaluated l E W D hl Z).obj (op n)))
    (T : NormalizedDVRTower l E W D hl) (n : ℕ) :
    RF.obj T.tower ⟶ (normalizedDVRResCompleted l E W D hl n).obj (T.M n) :=
  p T.tower ≫ Pi.π _ n ≫ (T.evaluationIso n).hom

/-- The quotient-linear adjoint of the actual limit projection, not a chosen comparison.
Source: Stacks Tag 07A6 (blueprint: lem-pur-adic-roos-realization-reductions). -/
def reduction
    (RF : normalizedDVRDerivedTowers l E W D hl ⥤ completedIntegralDerivedCategory l E W D hl)
    [HasCountableProducts (completedIntegralDerivedCategory l E W D hl)]
    (p : ∀ Z, RF.obj Z ⟶ ∏ᶜ (fun n : ℕ ↦ (evaluated l E W D hl Z).obj (op n)))
    (T : NormalizedDVRTower l E W D hl) (n : ℕ) :
    (scalarReductionDerivedExtension l E W n).obj (RF.obj T.tower) ⟶ T.M n :=
  ((adjunction l E W D hl n).homEquiv _ _).symm (projection l E W D hl RF p T n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedDVRKFlatUnit (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)}
      (J := AlgebraicGeometry.Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) P) :
    (adjunction l E W D hl n).unit.app
        (DerivedCategory.Q.obj P) ≫ normalizedDVRKFlatComparison l E W n P =
      DerivedCategory.Q.map (integralTowerUnit l E W D hl P n) := by
  have h := (derivedScalarExtensionRestrictionAdjunction l E W n).choose_spec P hP
  have hu := Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ)
    (scalarReductionExtension_adjunction l E W n).choose P
  have hq : DerivedCategory.Qh.map
      (((scalarReductionExtension_adjunction l E W n).choose.mapHomotopyCategory
        (.up ℤ)).unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      DerivedCategory.Q.map (unrestrictedTowerUnit l E W P n) :=
    congrArg (DerivedCategory.Qh.map) hu
  have hg : integralTowerUnit l E W D hl P n = unrestrictedTowerUnit l E W P n := by
    ext i U x
    exact ((integralTowerMaps_existUnique l E W D hl P).exists.choose_spec.1 n i U x).trans
      (unrestrictedTowerUnit_condition l E W P n i U x).symm
  have h' := h.trans hq
  unfold normalizedDVRKFlatComparison adjunction
  dsimp only [DerivedCategory.Qh, HomologicalComplexUpToQuasiIso.Qh,
    Functor.mapHomotopyCategory, CategoryTheory.Quotient.lift, Functor.comp_obj] at h' ⊢
  exact h'.trans (congrArg DerivedCategory.Q.map hg.symm)

attribute [local irreducible] adjunction

/-- Realization and its prescribed reductions for unbounded completed-coefficient objects.
Natural-number level n means exponent n+1. Quotient compatibility is written in its
adjoint form: transpose the scalar-associator equation first across finite scalar
extension and then across completed scalar extension. Thus it is an equation in
D(B_m), not an inference from faithfulness of scalar restriction.

Source: blueprint main-20261015, sec-smooth-purity, sk-thm-purity-transport,
thm-pur-adic-reconstruction.proof.md, final sentence
(blueprint: lem-pur-adic-roos-realization-reductions).

Proof:
1. Derived completeness gives the augmented reduction Roos triangle. The compatible
bS identify its factors and transitions with the evaluated S tower. Their product
transports that distinguished triangle, with first map given by the reduction units.
2. Rotate this triangle and the specified limit triangle to the same arrow 1-s.
TR3 completes the two identity components to e; the two-out-of-three triangle
criterion makes e invertible. Its first square gives every projection equation.
There is no uniqueness assertion.
3. The natural Roos triangles supplied by the ringed strict-tower homotopy-limit
lemma apply to G. Its product components are the restricted g. These are invertible,
so the triangle criterion makes RF.map G invertible. Naturality gives its projections
and therefore the asserted equation for gamma=e followed by RF.map G.
4. Transpose that equation using the normalized scalar adjunction. Naturality in
both arguments gives red(gamma) followed by bT = bS followed by g in D(B_n).
Since the other three maps are invertible, so is bT.
5. For each m>=n transpose the desired quotient normalization twice. The canonical
composite-unit identity of successive derived quotient normalization identifies the
right transpose with p_n, and the left with p_m followed by the restricted tau.
These agree because the limit projections are a cone. The identity quotient and
successive quotients use the unit and cocycle of the normalized tower. -/
theorem realization_reductions
    (P : completedIntegralDerivedCategory l E W D hl)
    (_hcomplete : IsDerivedComplete l E W D hl P)
    (S : normalizedDVRDerivedTowers l E W D hl)
    (Sfinite : ∀ n : ℕ, normalizedDVRDerived l E W n)
    (Siso : ∀ n : ℕ, (normalizedDVRTowerEvaluation l E W D hl n).obj S ≅
      (normalizedDVRResCompleted l E W D hl n).obj (Sfinite n))
    (bS : ∀ n : ℕ, (scalarReductionDerivedExtension l E W n).obj P ≅ Sfinite n)
    (_hbS : ∀ {m n : ℕ} (h : n ≤ m),
      (Siso m).inv ≫ (normalizedDVRTowerTransition l E W D hl h).app S ≫
          (Siso n).hom =
        (normalizedDVRResCompleted l E W D hl m).map
          ((bS m).inv ≫ quotientUnit l E W D hl P h ≫
            (normalizedDVRRes l E W h).map (bS n).hom) ≫
          (normalizedDVRResCompletedComp l E W D hl h).hom.app (Sfinite n))
    (T : NormalizedDVRTower l E W D hl)
    (G : S ⟶ T.tower) (g : ∀ n : ℕ, Sfinite n ≅ T.M n)
    (_hG : ∀ n : ℕ,
      (normalizedDVRTowerEvaluation l E W D hl n).map G ≫ (T.evaluationIso n).hom =
        (Siso n).hom ≫
          (normalizedDVRResCompleted l E W D hl n).map (g n).hom)
    (RF : normalizedDVRDerivedTowers l E W D hl ⥤ completedIntegralDerivedCategory l E W D hl)
    (η : (lim : (ℕᵒᵖ ⥤ completedIntegralModuleSheaves l E W D hl) ⥤
        completedIntegralModuleSheaves l E W D hl).mapHomologicalComplex (.up ℤ) ⋙
        (@DerivedCategory.Q (completedIntegralModuleSheaves l E W D hl) _ _
          (HasDerivedCategory.standard _)) ⟶
        (@DerivedCategory.Q (ℕᵒᵖ ⥤ completedIntegralModuleSheaves l E W D hl) _ _
          (HasDerivedCategory.standard _)) ⋙ RF)
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ completedIntegralModuleSheaves l E W D hl)
        (.up ℤ)))
    [HasCountableProducts (completedIntegralDerivedCategory l E W D hl)]
    (p : ∀ Z, RF.obj Z ⟶ ∏ᶜ (fun n : ℕ ↦ (evaluated l E W D hl Z).obj (op n)))
    (δ : ∀ Z, (∏ᶜ (fun n : ℕ ↦ (evaluated l E W D hl Z).obj (op n))) ⟶
      (RF.obj Z)⟦(1 : ℤ)⟧)
    (_hroos : ∀ Z, IsDerivedLimitTriangle
      (fun n : ℕ ↦ (evaluated l E W D hl Z).map (homOfLE (Nat.le_succ n)).op)
      (RF.obj Z) (p Z) (δ Z))
    (_hnatural : ∀ {Z Z' : normalizedDVRDerivedTowers l E W D hl} (v : Z ⟶ Z'),
      RF.map v ≫ p Z' = p Z ≫ Limits.Pi.map (fun n : ℕ ↦
        (normalizedDVRTowerEvaluation l E W D hl n).map v)) :
    IsIso (RF.map G) ∧ ∃ e : P ≅ RF.obj S,
      (∀ n : ℕ, e.hom ≫ p S ≫ Limits.Pi.π _ n ≫ (Siso n).hom =
        (adjunction l E W D hl n).unit.app P ≫
          (normalizedDVRResCompleted l E W D hl n).map (bS n).hom) ∧
      (∀ n : ℕ, IsIso (reduction l E W D hl RF p T n)) ∧
      (∀ n : ℕ, (e.hom ≫ RF.map G) ≫ projection l E W D hl RF p T n =
        (adjunction l E W D hl n).unit.app P ≫
          (normalizedDVRResCompleted l E W D hl n).map (bS n).hom ≫
          (normalizedDVRResCompleted l E W D hl n).map (g n).hom) ∧
      (∀ n : ℕ, (scalarReductionDerivedExtension l E W n).map (e.hom ≫ RF.map G) ≫
        reduction l E W D hl RF p T n = (bS n).hom ≫ (g n).hom) ∧
      (∀ {m n : ℕ} (h : n ≤ m),
        reduction l E W D hl RF p T m ≫ T.tau h =
          quotientUnit l E W D hl (RF.obj T.tower) h ≫
            (normalizedDVRRes l E W h).map (reduction l E W D hl RF p T n)) := by
  classical
  let : HasDerivedCategory (completedIntegralModuleSheaves l E W D hl) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (ℕᵒᵖ ⥤ completedIntegralModuleSheaves l E W D hl) :=
    HasDerivedCategory.standard _
  have hEval (n : ℕ) : IsIso ((normalizedDVRTowerEvaluation l E W D hl n).map G) := by
    have hc : IsIso ((normalizedDVRTowerEvaluation l E W D hl n).map G ≫
        (T.evaluationIso n).hom) := by
      rw [_hG n]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (T.evaluationIso n).hom
  have hGI : IsIso G := by
    rw [DerivedCategory.isIso_iff]
    intro j
    let : ∀ n : ℕᵒᵖ,
        IsIso (((DerivedCategory.homologyFunctor _ j).map G).app n) := fun n ↦ by
      have := hEval n.unop
      let V := (CategoryTheory.evaluation ℕᵒᵖ
        (completedIntegralModuleSheaves l E W D hl)).obj n
      exact (NatIso.isIso_map_iff (V.mapDerivedCategoryHomologyFunctorIso j) G).2
        (show IsIso ((DerivedCategory.homologyFunctor _ j).map
          ((normalizedDVRTowerEvaluation l E W D hl n.unop).map G)) from inferInstance)
    exact NatIso.isIso_of_isIso_app _
  have hFI : IsIso (RF.map G) := inferInstance
  obtain ⟨K, H, q, hq, eH, hp, ε, hε⟩ := _hcomplete
  let := hp
  let : QuasiIso q := hq.1
  let eK : DerivedCategory.Q.obj K ≅ P := asIso (DerivedCategory.Q.map q) ≪≫ eH
  have hi (n : ℕ) : IsIso (normalizedDVRKFlatComparison l E W n K) :=
    representativeComparison_isIso l E W n K hq.2
  let a (n : ℕ) :
      (normalizedDVRResCompleted l E W D hl n).obj
          ((scalarReductionDerivedExtension l E W n).obj P) ≅
        (integralReductionTower l E W D hl K).obj (op n) :=
    (normalizedDVRResCompleted l E W D hl n).mapIso
        ((scalarReductionDerivedExtension l E W n).mapIso eK.symm) ≪≫
      @asIso _ _ _ _ (normalizedDVRKFlatComparison l E W n K) (hi n)
  let b (n : ℕ) := Siso n ≪≫
    (normalizedDVRResCompleted l E W D hl n).mapIso (bS n).symm ≪≫ a n
  have ht (n : ℕ) :
      (normalizedDVRTowerTransition l E W D hl n.le_succ).app S ≫ (b n).hom =
        (b (n + 1)).hom ≫
          (integralReductionTower l E W D hl K).map (homOfLE n.le_succ).op := by
    have hs := _hbS n.le_succ
    have hk := normalizedDVR_kflat_transition l E W D hl K hq.2 P eK n
      (adjunction l E W D hl (n + 1)) (adjunction l E W D hl n)
      (normalizedDVRKFlatUnit l E W D hl (n + 1) K hq.2)
      (normalizedDVRKFlatUnit l E W D hl n K hq.2)
    apply (cancel_epi (Siso (n + 1)).inv).1
    dsimp only [b, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% hs]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← reassoc_of% (normalizedDVRResCompletedComp l E W D hl n.le_succ).hom.naturality
      (bS n).inv]
    have hcanc :
        (normalizedDVRResCompleted l E W D hl (n + 1)).map
            ((normalizedDVRRes l E W n.le_succ).map (bS n).hom) ≫
          (normalizedDVRResCompleted l E W D hl (n + 1)).map
            ((normalizedDVRRes l E W n.le_succ).map (bS n).inv) = 𝟙 _ := by
      simp only [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id]
    rw [reassoc_of% hcanc]
    dsimp only [a, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom]
    have hk' := congrArg
      (fun f ↦ (normalizedDVRResCompleted l E W D hl (n + 1)).map (bS (n + 1)).inv ≫ f) hk
    simp only [integralReductionTower, Functor.ofOpSequence_map_homOfLE_succ,
      quotientUnit, Category.assoc]
    with_unfolding_all exact hk' 
  have hu (n : ℕ) :
      (adjunction l E W D hl n).unit.app P ≫ (a n).hom =
        eK.inv ≫ DerivedCategory.Q.map (integralTowerUnit l E W D hl K n) := by
    have hn := (adjunction l E W D hl n).unit.naturality eK.inv
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    dsimp only [a, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom]
    rw [← Category.assoc, ← hn, Category.assoc]
    exact congrArg (fun f ↦ eK.inv ≫ f) (normalizedDVRKFlatUnit l E W D hl n K hq.2)
  let c (n : ℕ) : P ⟶ (normalizedDVRTowerEvaluation l E W D hl n).obj S :=
    (adjunction l E W D hl n).unit.app P ≫
    (normalizedDVRResCompleted l E W D hl n).map (bS n).hom ≫ (Siso n).inv
  have hc (n : ℕ) : c n ≫ (b n).hom =
      (Pi.lift (fun n : ℕ ↦
        ((integralReductionTowerCone l E W D hl q hq).extend eH.inv).π.app (op n))) ≫
          Pi.π _ n := by
    dsimp only [c, b, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp, Pi.lift_π]
    rw [hu]
    simp only [eK, Iso.trans_inv, asIso_inv, integralReductionTowerCone,
      Cone.extend_π, integralReductionTowerMap, integralTowerAugmentationIso,
      NatTrans.comp_app, Functor.const_map_app, Category.assoc]
  obtain ⟨εS, hεS⟩ := roosTransportFixed
    (fun n ↦ (integralReductionTower l E W D hl K).map (homOfLE n.le_succ).op)
    (fun n ↦ (normalizedDVRTowerTransition l E W D hl n.le_succ).app S)
    P _ ε hε (fun n ↦ (b n).symm) c
    (fun n ↦ by
      apply (cancel_mono (b n).hom).1
      simpa only [Category.assoc, Iso.inv_hom_id, Iso.symm_hom, Category.comp_id,
        Iso.inv_hom_id_assoc] using
        congrArg (fun f ↦ (b (n + 1)).inv ≫ f) (ht n).symm)
    (fun n ↦ by
      apply (cancel_mono (b n).hom).1
      simpa only [Category.assoc, Iso.inv_hom_id, Iso.symm_hom, Category.comp_id] using
        (hc n).symm)
  have hεS' : IsDerivedLimitTriangle
      (fun n ↦ (evaluated l E W D hl S).map (homOfLE n.le_succ).op)
      P (Pi.lift c) εS := by
    simpa only [evaluated, Functor.ofOpSequence_map_homOfLE_succ] using hεS
  obtain ⟨e, he⟩ := roosComparison _ (Pi.lift c) (p S) εS (δ S) hεS' (_hroos S)
  have heproj (n : ℕ) :
      e.hom ≫ p S ≫ Pi.π _ n ≫ (Siso n).hom =
        (adjunction l E W D hl n).unit.app P ≫
          (normalizedDVRResCompleted l E W D hl n).map (bS n).hom := by
    rw [← Category.assoc, ← Category.assoc, he]
    change (Pi.lift c ≫ Pi.π
      (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E W D hl n).obj S) n) ≫
        (Siso n).hom = _
    rw [Pi.lift_π]
    simp only [c, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hgamma (n : ℕ) : (e.hom ≫ RF.map G) ≫ projection l E W D hl RF p T n =
      (adjunction l E W D hl n).unit.app P ≫
        (normalizedDVRResCompleted l E W D hl n).map (bS n).hom ≫
        (normalizedDVRResCompleted l E W D hl n).map (g n).hom := by
    change (e.hom ≫ RF.map G) ≫ p T.tower ≫ Pi.π
      (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E W D hl n).obj T.tower) n ≫
        (T.evaluationIso n).hom = _
    rw [Category.assoc, ← Category.assoc (RF.map G), _hnatural G]
    simp only [Category.assoc, Pi.map_π_assoc]
    rw [_hG]
    simpa only [Category.assoc] using congrArg
      (fun f ↦ f ≫ (normalizedDVRResCompleted l E W D hl n).map (g n).hom) (heproj n)
  have hred (n : ℕ) :
      (scalarReductionDerivedExtension l E W n).map (e.hom ≫ RF.map G) ≫
        reduction l E W D hl RF p T n = (bS n).hom ≫ (g n).hom := by
    apply ((adjunction l E W D hl n).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, reduction, Equiv.apply_symm_apply,
      Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp]
    exact hgamma n
  refine ⟨hFI, e, heproj, ?_, hgamma, hred, ?_⟩
  · intro n
    have : IsIso ((scalarReductionDerivedExtension l E W n).map
        (e.hom ≫ RF.map G) ≫ reduction l E W D hl RF p T n) := by
      rw [hred]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((scalarReductionDerivedExtension l E W n).map (e.hom ≫ RF.map G))
      (reduction l E W D hl RF p T n)
  · intro m n h
    apply adjointTransition (adjunction l E W D hl m) (adjunction l E W D hl n)
      (normalizedDVRRes l E W h) (normalizedDVRResCompletedComp l E W D hl h)
    have hcT := _hroos T.tower
    simp only [evaluated, Functor.ofOpSequence_map_homOfLE_succ] at hcT
    change (p T.tower ≫ Pi.π
      (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E W D hl n).obj T.tower) m ≫
        (T.evaluationIso m).hom) ≫ _ ≫ _ = p T.tower ≫ Pi.π
      (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E W D hl n).obj T.tower) n ≫
        (T.evaluationIso n).hom
    simp only [Category.assoc]
    rw [← T.tower_tau h]
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ (T.evaluationIso n).hom)
      (normalizedDVRRoosProjection l E W D hl T _ (p T.tower) (δ T.tower) hcT h)

end WeilConjectures.AdicRoos
