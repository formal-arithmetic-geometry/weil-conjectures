module

public import Sheaf.Paper.ConstantComplexStrictBaseChangeData
import Sheaf.Paper.ConstantComplexNormalizedReductions
import Sheaf.Paper.ConstantComplexFinitePullback
import Sheaf.Paper.ConstantComplexCompletedPullback
import Sheaf.Algebra.Homology.SignedMappingCoconeShift

/-! # Strict constant-complex base change

Source: Stacks Project, Tags 03EL, 03EK, 015F, 014E and 08TC.
(blueprint: lem-a1-constant-complex-strict-base-change)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
attribute [-instance] AlgebraicGeometry.Scheme.coefficientProEtaleModelBaseChange_isContinuous
  WeilConjectures.integralOperationsSiteSmall WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsAbSheafify
namespace AlgebraicGeometry.ConstantComplexBaseChange

section ConeCalculus
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem completedCoconeLift_f (M : Type*) [Category* M] [Abelian M]
    {C K L : CochainComplex M ℤ} (φ : K ⟶ L) (u : C ⟶ K)
    (hu : u ≫ φ = 0) (p : ℤ) :
    (CochainComplex.mappingCocone.lift φ u 0 (by simp [hu])).f p =
      u.f p ≫ (CochainComplex.mappingCocone.inl φ).v p p (add_zero p) := by
  let l := CochainComplex.mappingCocone.lift φ u 0 (by simp [hu])
  have h := CochainComplex.mappingCocone.id_X φ p (p + -1) rfl
  calc
    l.f p = l.f p ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = _ := by
      rw [← h, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
        CochainComplex.mappingCocone.lift_f_fst_f,
        CochainComplex.mappingCocone.lift_f_snd_v]
      simp

private theorem completedCoconeLift_natural (M : Type*) [Category* M] [Abelian M]
    {C D K₁ K₂ L₁ L₂ : CochainComplex M ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : φ₁ ≫ b = a ≫ φ₂) (α : C ⟶ D) (u : C ⟶ K₁) (v : D ⟶ K₂)
    (hu : u ≫ φ₁ = 0) (hv : v ≫ φ₂ = 0) (hn : α ≫ v = u ≫ a) :
    α ≫ CochainComplex.mappingCocone.lift φ₂ v 0 (by simp [hv]) =
      CochainComplex.mappingCocone.lift φ₁ u 0 (by simp [hu]) ≫
        SignedCoconeShift.coconeMap φ₁ φ₂ (Arrow.homMk a b h.symm) := by
  apply HomologicalComplex.hom_ext
  intro p
  have hi : (CochainComplex.mappingCocone.inl φ₁).v p p (add_zero p) ≫
      (SignedCoconeShift.coconeMap φ₁ φ₂ (Arrow.homMk a b h.symm)).f p =
      a.f p ≫ (CochainComplex.mappingCocone.inl φ₂).v p p (add_zero p) := by
    exact SignedCoconeShift.coconeMap_inl φ₁ φ₂ (Arrow.homMk a b h.symm) p
  change α.f p ≫ _ = (CochainComplex.mappingCocone.lift φ₁ u 0 (by simp [hu])).f p ≫ _
  rw [completedCoconeLift_f M φ₂ v hv p, completedCoconeLift_f M φ₁ u hu p]
  calc
    α.f p ≫ v.f p ≫ (CochainComplex.mappingCocone.inl φ₂).v p p (add_zero p) =
        (u.f p ≫ a.f p) ≫
          (CochainComplex.mappingCocone.inl φ₂).v p p (add_zero p) := by
      simpa only [HomologicalComplex.comp_f, Category.assoc] using
        congrArg (fun z ↦ z.f p ≫
          (CochainComplex.mappingCocone.inl φ₂).v p p (add_zero p)) hn
    _ = _ := by rw [Category.assoc, ← hi, ← Category.assoc]

private theorem towerProductKernel
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) {C : CochainComplex A ℤ}
    (α : ∀ n : ℕ, C ⟶ T.obj (op n))
    (hα : ∀ n, α (n + 1) ≫ T.map (homOfLE n.le_succ).op = α n) :
    Pi.lift α ≫ towerTransitionEndomorphism (K := fun n ↦ T.obj (op n))
      (WeilConjectures.integralOperationsTowerStep T) = 0 := by
  apply Pi.hom_ext
  intro n
  simp [towerTransitionEndomorphism, towerProductShift,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
    WeilConjectures.integralOperationsTowerStep, hα]

private def towerRoosLift
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) {C : CochainComplex A ℤ}
    (α : ∀ n : ℕ, C ⟶ T.obj (op n))
    (hα : ∀ n, α (n + 1) ≫ T.map (homOfLE n.le_succ).op = α n) :
    C ⟶ WeilConjectures.integralOperationsRoosFunctor.obj T :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism (K := fun n ↦ T.obj (op n))
      (WeilConjectures.integralOperationsTowerStep T))
    (Pi.lift α) 0 (by simp [towerProductKernel T α hα])

private theorem towerRoosLift_fst
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) {C : CochainComplex A ℤ}
    (α : ∀ n : ℕ, C ⟶ T.obj (op n))
    (hα : ∀ n, α (n + 1) ≫ T.map (homOfLE n.le_succ).op = α n) :
    towerRoosLift T α hα ≫ CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism (K := fun n ↦ T.obj (op n))
      (WeilConjectures.integralOperationsTowerStep T)) =
        Pi.lift α :=
  CochainComplex.mappingCocone.lift_fst _ _ _ _

private theorem towerRoosLift_snd
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) {C : CochainComplex A ℤ}
    (α : ∀ n : ℕ, C ⟶ T.obj (op n))
    (hα : ∀ n, α (n + 1) ≫ T.map (homOfLE n.le_succ).op = α n) (r : ℤ) :
    (towerRoosLift T α hα).f r ≫
      (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism (K := fun n ↦ T.obj (op n))
      (WeilConjectures.integralOperationsTowerStep T))).v
          r (r + -1) rfl = 0 :=
  CochainComplex.mappingCocone.lift_f_snd_v _ _ _ _ _ _ _

private theorem towerRoosLift_natural
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {T U : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : T ⟶ U)
    {C D : CochainComplex A ℤ} (g : C ⟶ D)
    (α : ∀ n : ℕ, C ⟶ T.obj (op n)) (β : ∀ n : ℕ, D ⟶ U.obj (op n))
    (hα : ∀ n, α (n + 1) ≫ T.map (homOfLE n.le_succ).op = α n)
    (hβ : ∀ n, β (n + 1) ≫ U.map (homOfLE n.le_succ).op = β n)
    (h : ∀ n, g ≫ β n = α n ≫ f.app (op n)) :
    g ≫ towerRoosLift U β hβ =
      towerRoosLift T α hα ≫ WeilConjectures.integralOperationsRoosFunctor.map f := by
  have hn : g ≫ Pi.lift β = Pi.lift α ≫ Limits.Pi.map (fun n ↦ f.app (op n)) := by
    apply Pi.hom_ext
    intro n
    simpa only [Category.assoc, Pi.lift_π, Pi.lift_π_assoc, Limits.Pi.map_π] using h n
  exact completedCoconeLift_natural A _ _ _ _
    (WeilConjectures.integralOperationsRoos_square f) g _ _
    (towerProductKernel T α hα) (towerProductKernel U β hβ) hn

end ConeCalculus

attribute [local irreducible] towerRoosLift


attribute [local irreducible] extension extensionPresheaf
  commutativeSiteConstantModuleFunctor proEtaleModuleInverseImage
attribute [local irreducible] completedComplex finiteComplex finiteOverScalar
  finiteOverCompleted

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem sequenceCompatible
    {C D : Type*} [Category* C] [Category* D]
    {F : ℕ → C ⥤ D} (step : ∀ n, F (n + 1) ⟶ F n)
    {P : C} {M : D} (α : ∀ n, M ⟶ (F n).obj P)
    (h : ∀ n, α (n + 1) ≫ (step n).app P = α n) (n : ℕ) :
    α (n + 1) ≫ ((Functor.ofOpSequence step).map (homOfLE n.le_succ).op).app P =
      α n := by
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  exact h n

private theorem normalizedTower_compatible
    (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    {d : FiniteTower W I} (e : ReductionData W I d) (he : e.IsNormalized W I)
    (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P) (n : ℕ) :
    e.alpha (n + 1) P hP ≫ ((e.tower W I).obj P).map (homOfLE n.le_succ).op =
      e.alpha n P hP := by
  exact sequenceCompatible e.step (fun n ↦ e.alpha n P hP)
    (he.2.2.2.2.2.2.2.2.2.2 · P hP) n

private def normalizedRoos
    (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    {d : FiniteTower W I} (e : ReductionData W I d) (he : e.IsNormalized W I) :
    RoosAugmentation W I e where
  beta P hP := towerRoosLift
    (A := proEtaleRingModules W (completed W I))
    (C := (completedComplex W I e.coefficient).obj P)
    ((e.tower W I).obj P) (fun n ↦ e.alpha n P hP)
    (normalizedTower_compatible W I e he P hP)


private theorem normalized_roos_exists
    (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    {d : FiniteTower W I} (e : ReductionData W I d) (he : e.IsNormalized W I) :
    ∃ a : RoosAugmentation W I e, a.IsNormalized W I := by
  refine ⟨normalizedRoos W I e he, ?_⟩
  unfold RoosAugmentation.IsNormalized
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP
    exact towerProductKernel ((e.tower W I).obj P) (fun n ↦ e.alpha n P hP)
      (normalizedTower_compatible W I e he P hP)
  · intro P hP
    exact heq_of_eq (towerRoosLift_fst
      (A := proEtaleRingModules W (completed W I))
      (C := (completedComplex W I e.coefficient).obj P)
      ((e.tower W I).obj P) (fun n ↦ e.alpha n P hP)
      (normalizedTower_compatible W I e he P hP))
  · intro P hP r
    dsimp only [normalizedRoos, ReductionData.roosArrow]
    exact towerRoosLift_snd
      (A := proEtaleRingModules W (completed W I))
      (C := (completedComplex W I e.coefficient).obj P)
      ((e.tower W I).obj P) (fun n ↦ e.alpha n P hP)
      (normalizedTower_compatible W I e he P hP) r
  · intro P Q hP hQ f
    dsimp only [normalizedRoos]
    exact towerRoosLift_natural
      (A := proEtaleRingModules W (completed W I))
      (T := (e.tower W I).obj P) (U := (e.tower W I).obj Q)
      (C := (completedComplex W I e.coefficient).obj P)
      (D := (completedComplex W I e.coefficient).obj Q)
      ((e.tower W I).map f) ((completedComplex W I e.coefficient).map f)
      (fun n ↦ e.alpha n P hP) (fun n ↦ e.alpha n Q hQ)
      (normalizedTower_compatible W I e he P hP) (normalizedTower_compatible W I e he Q hQ)
      (fun n ↦ he.2.2.2.2.2.2.2.2.2.1 n P Q hP hQ f)


/-- Strict constant-complex pullback at every positive quotient level, with its
normalized finite reductions and signed Roos augmentation.

Source: Stacks Project, sites-modules.tex, Tags 03EL and 03EK; sites.tex, Tags 0H7J
and 00YV; derived.tex, Tags 015F, 014E and 08TC.
(blueprint: lem-a1-constant-complex-strict-base-change).

Proof:
1. The constant-ring inverse-image map fixes constant sections and is an isomorphism.
The constant-module inverse-image comparison is natural in every scalar linear map.
Compose it with inverse image's tensor comparison. Its value on a constant tensor is
`a tensor p`, and the inverse comparisons give its inverse on sheaves.
2. Naturality in the scalar differential, consecutive quotient map, and scalar chain
map gives respectively the common values `a tensor dp`, `q(a) tensor p`, and
`a tensor f(p)`. The local tensor generators give sheaf-map equalities. The resulting
chain isomorphisms and their inverses therefore define a natural strict tower isomorphism.
3. Pullback over each identified constant ring is exact. The exact-functor derived
factorization localizes the strict comparison to the ambient derived category,
including unbounded scalar complexes. This is `FiniteComparison.derived`.
4. Balanced tensor associativity gives the finite reduction map with value
`a * pr(b) tensor p`. Its inverse sends `a tensor p` to `(1 tensor p) tensor a`.
The balancing relations show that both composites are identities. These maps commute
with the original differential and every scalar chain map, without choosing splittings.
5. The constant coefficient comparisons and inverse images of the limit projections
form a cone. Its limit map is the completed coefficient map; no inverse is required.
Tensor and constant-module comparison identify the completed pullback with the target
completed complex. The formula is `b' tensor (b tensor p)` mapped to
`b' * c(b) tensor p`. Applying a projection verifies the normalized geometric reduction
square, including its quotient unit.
6. The quotient unit sends `m` to `m tensor 1`. Consecutive quotient transitions
preserve this unit and the balanced reduction, since consecutive projections agree.
The generator calculations prove equalities of chain maps; in particular all scalar
differentials are retained and no finite-free splitting enters the construction.
7. Assemble the normalized maps alpha into their product map. Its composite with
`1-s` is zero, because its nth component is alpha_n minus the transition after
alpha_(n+1). In the signed mapping cocone, the zero shifted-product component and
this product map form a chain map. The two projections specify this augmentation,
and their formulas prove naturality in scalar chain maps.
-/
theorem strict_constant_complex_base_change
    (R : Type u) [CommRing R] (I : Ideal R)
    (hfinite : ∀ n : ℕ, Finite (Quotient R I n))
    {T T' : Scheme.{u}} (g : T' ⟶ T) :
    ∃ (dT : FiniteTower T I) (dT' : FiniteTower T' I)
      (eT : ReductionData T I dT) (eT' : ReductionData T' I dT')
      (f : FiniteComparison g I dT dT'),
      dT.IsNormalized T I ∧ dT'.IsNormalized T' I ∧
      eT.IsNormalized T I ∧ eT'.IsNormalized T' I ∧ f.IsNormalized g I ∧
      (∃ a : RoosAugmentation T I eT, a.IsNormalized T I) ∧
      (∃ a : RoosAugmentation T' I eT', a.IsNormalized T' I) ∧
      (∃ e : GeometricReduction g I eT eT' f, e.IsNormalized g I) ∧
      ∀ n : ℕ, (proEtaleConstantRingPullback (Quotient R I n) g).Additive ∧
        PreservesFiniteLimits (proEtaleConstantRingPullback (Quotient R I n) g) ∧
        PreservesFiniteColimits (proEtaleConstantRingPullback (Quotient R I n) g) := by
  have _ := hfinite
  obtain ⟨dT, eT, hdT, heT⟩ := normalized_reductions_exist T I
  obtain ⟨dT', eT', hdT', heT'⟩ := normalized_reductions_exist T' I
  obtain ⟨f, hf⟩ := normalized_finite_pullback_exists g I dT dT' hdT hdT'
  obtain ⟨aT, haT⟩ := normalized_roos_exists T I eT heT
  obtain ⟨aT', haT'⟩ := normalized_roos_exists T' I eT' heT'
  obtain ⟨e, he⟩ := normalized_completed_pullback_exists g I eT eT' heT heT' f hf
  exact ⟨dT, dT', eT, eT', f, hdT, hdT', heT, heT', hf, ⟨aT, haT⟩,
    ⟨aT', haT'⟩, ⟨e, he⟩, fun _ ↦ ⟨inferInstance, inferInstance, inferInstance⟩⟩

end AlgebraicGeometry.ConstantComplexBaseChange
