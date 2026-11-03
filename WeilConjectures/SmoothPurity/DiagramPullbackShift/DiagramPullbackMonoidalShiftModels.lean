/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.DiagramPullbackShift.DiagramGeometricTensorPresentations
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import WeilConjectures.CategoryTheory.DerivedCategory.NativeDerivedMonoidalConstraintShifts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift

/-! # Simultaneous native pullback, tensor and shift coherence

The coefficient on X is the fixed condensed coefficient sheaf p_X^* Λ. The geometric
presentation is that of `DiagramGeometricTensorPresentations`; all shifts and tensor
constraints below are the existing native derived-category comparisons.

Source: the maps-used sentence of the latest blueprint `fix-prop-coherence.proof.md`;
Stacks 06YS, 07A4, 0FPQ, 0FPT and More on Algebra 0FNH.
(blueprint: lem-pur-diagram-pullback-monoidal-shift-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale (condensedRingObj condensedPullbackHom)
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures.DiagramPullbackShift
open AlgebraicGeometry.ProEtale.CondensedRing DerivedCategory

attribute [local instance] DerivedCategory.braidedCategory'

set_option hygiene false in
local notation "𝔻(" X ")" => DerivedCategory
  (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
set_option hygiene false in
local notation "𝐊(" X ")" => HomotopyCategory
  (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) (.up ℤ)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The existing canonical module-pullback shift structure, displayed at the native functor
so type-class search need not unfold the named module-functor interface.
Source: blueprint maps-used sentence and `def-sfb-module-derived-functor-shifts`.
(blueprint: def-pur-native-monoidal-shift-models). -/
abbrev nativeDerivedPullbackCommShift : (upperStar Λ p).leftDerivedFunctor.CommShift ℤ :=
  modulePullbackDerivedCommShift Λ p

attribute [local instance] nativeDerivedPullbackCommShift

/-- The universal counit has the shifts of the canonical exact comparison. -/
private theorem nativeCounitCommShift :
    NatTrans.CommShift (upperStar Λ p).leftDerivedFunctorCounit ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ p).hom ℤ :=
    (module_derived_functors_exact_and_comparison_shifts Λ p).2.2.1
  rw [← (upperStar Λ p).leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  exact inferInstanceAs (NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Qh
    (leftDerivedUpperStarIsoMapDerivedCategory Λ p).hom ≫ _) ℤ)

attribute [local instance] nativeCounitCommShift

/-- The tensor comparison `Lp^*(K ⊗ᴸ L) ⟶ Lp^*K ⊗ᴸ Lp^*L` commutes with the shifts in `L`:
the native `ProjectionMapShift` instance, at the canonical module-pullback shifts. -/
private theorem tensorSecondShift (K : 𝔻(Y)) :
    NatTrans.CommShift (F₁ := (curriedTensor 𝔻(Y)).obj K ⋙ L((p)^*⟦Λ⟧))
      (F₂ := L((p)^*⟦Λ⟧) ⋙ (curriedTensor 𝔻(X)).obj (L((p)^*⟦Λ⟧).obj K))
      ((leftDerivedUpperStarTensor Λ p).app K) ℤ :=
  commShift_leftDerivedUpperStarTensor_app Λ p K

/-- The tensor comparison `Lp^*(K ⊗ᴸ L) ⟶ Lp^*K ⊗ᴸ Lp^*L` commutes with the shifts in `K`:
the native `ProjectionMapShift` instance, at the canonical module-pullback shifts. -/
private theorem tensorFirstShift (K : 𝔻(Y)) :
    NatTrans.CommShift (F₁ := (curriedTensor 𝔻(Y)).flip.obj K ⋙ L((p)^*⟦Λ⟧))
      (F₂ := L((p)^*⟦Λ⟧) ⋙ (curriedTensor 𝔻(X)).flip.obj (L((p)^*⟦Λ⟧).obj K))
      (Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ p) K) ℤ :=
  commShift_leftDerivedUpperStarTensor_flipApp Λ p K

/-- Simultaneous coherence of the specified native comparisons. K-flat models are chosen
only up to their displayed isomorphism in the derived category. Tensor, compositor and
unit maps themselves are fixed constructions. Source: blueprint maps-used sentence;
Stacks 06YS, 07A4, 0FPQ, 0FPT and 0FNH.
(blueprint: def-pur-native-monoidal-shift-models). -/
structure MonoidalShiftModels : Prop where
  geometric : GeometricTensorPresentations Λ
  resolutions : ∀ (W : Scheme.{u}) (n : ℕ) (E : Fin n → 𝔻(W)),
    ∃ P : Fin n → 𝐊(W), ∀ i,
      (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat (P i) ∧
        Nonempty (Qh.obj (P i) ≅ E i)
  monoidal : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    Nonempty ((upperStar Λ f).leftDerivedFunctor.Monoidal)
  tensorator : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (K L : 𝔻(Y)),
    Functor.LaxMonoidal.μ (upperStar Λ f).leftDerivedFunctor K L =
      (((leftDerivedUpperStarTensorIso Λ f).app K).app L).inv
  tensor_unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    Functor.LaxMonoidal.ε (upperStar Λ f).leftDerivedFunctor =
      (leftDerivedUpperStarUnitIso Λ f).inv
  tensor_second : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (K : 𝔻(Y)),
    NatTrans.CommShift
      (F₁ := (curriedTensor 𝔻(Y)).obj K ⋙ (upperStar Λ f).leftDerivedFunctor)
      (F₂ := (upperStar Λ f).leftDerivedFunctor ⋙
        (curriedTensor 𝔻(X)).obj ((upperStar Λ f).leftDerivedFunctor.obj K))
      ((leftDerivedUpperStarTensor Λ f).app K) ℤ
  tensor_first : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (K : 𝔻(Y)),
    NatTrans.CommShift
      (F₁ := (curriedTensor 𝔻(Y)).flip.obj K ⋙ (upperStar Λ f).leftDerivedFunctor)
      (F₂ := (upperStar Λ f).leftDerivedFunctor ⋙
        (curriedTensor 𝔻(X)).flip.obj ((upperStar Λ f).leftDerivedFunctor.obj K))
      (Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ f) K) ℤ
  associator_first : ∀ (W : Scheme.{u}) (K L : 𝔻(W)),
    NatTrans.CommShift (associatorNatTrans₁ 𝔻(W) K L) ℤ
  associator_second : ∀ (W : Scheme.{u}) (K L : 𝔻(W)),
    NatTrans.CommShift (associatorNatTrans₂ 𝔻(W) K L) ℤ
  associator_third : ∀ (W : Scheme.{u}) (K L : 𝔻(W)),
    NatTrans.CommShift (associatorNatTrans₃ 𝔻(W) K L) ℤ
  left_unitor : ∀ (W : Scheme.{u}) (K : 𝔻(W)) (n : ℤ),
    (((curriedTensor 𝔻(W)).obj (𝟙_ _)).commShiftIso n).hom.app K ≫
      (λ_ K).hom⟦n⟧' = (λ_ (K⟦n⟧)).hom
  right_unitor : ∀ (W : Scheme.{u}) (K : 𝔻(W)) (n : ℤ),
    (((curriedTensor 𝔻(W)).flip.obj (𝟙_ _)).commShiftIso n).hom.app K ≫
      (ρ_ K).hom⟦n⟧' = (ρ_ (K⟦n⟧)).hom
  symmetry : ∀ (W : Scheme.{u}) (K L : 𝔻(W)) (n : ℤ),
    (β_ K (L⟦n⟧)).hom ≫
      (((curriedTensor 𝔻(W)).flip.obj K).commShiftIso n).hom.app L =
      (((curriedTensor 𝔻(W)).obj K).commShiftIso n).hom.app L ≫
        (β_ K L).hom⟦n⟧'
  compositor : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    NatTrans.CommShift (leftDerivedUpperStarComp Λ f g).hom ℤ ∧
      NatTrans.CommShift (leftDerivedUpperStarComp Λ f g).inv ℤ

/-- The native geometric, tensor and shift comparisons satisfy all their slotwise
coherence equations, simultaneously for every scheme and commutative condensed ring.
Source: latest blueprint `fix-prop-coherence.proof.md`, maps-used sentence; Stacks 06YS,
07A4, 0FPQ, 0FPT and 0FNH.
(blueprint: lem-pur-diagram-pullback-monoidal-shift-models).

Proof: use the geometric presentation theorem. Choose finitely many K-flat models
through the K-flat localization. Its native tensor gives the signed two-slot shift
structure. On K-flat models the tensor comparison is normalized by the derived counit;
the ordinary oplax monoidal comparison commutes with shifts. Cancellation gives its
shift squares on models, and naturality transports them along model isomorphisms to
all derived objects. The same localization gives associator compatibility in all
three slots and the Koszul symmetry square. The left unitor descends from the unit
complex. The symmetry square and the left unitor give the right unitor. The exact
derived compositor and its inverse commute with shifts by localization. -/
theorem diagramPullbackMonoidalShiftModels : MonoidalShiftModels Λ := by
  refine
    { geometric := diagramGeometricTensorPresentations Λ
      resolutions := ?_
      monoidal := fun _ ↦ ⟨inferInstance⟩
      tensorator := fun _ _ _ ↦ rfl
      tensor_unit := fun _ ↦ rfl
      tensor_second := tensorSecondShift Λ
      tensor_first := tensorFirstShift Λ
      associator_first := fun _ K L ↦
        ((DerivedCategory.nativeDerivedMonoidalConstraintShifts _).1 K L).1
      associator_second := fun _ K L ↦
        ((DerivedCategory.nativeDerivedMonoidalConstraintShifts _).1 K L).2.1
      associator_third := fun _ K L ↦
        ((DerivedCategory.nativeDerivedMonoidalConstraintShifts _).1 K L).2.2
      left_unitor := fun _ ↦ (DerivedCategory.nativeDerivedMonoidalConstraintShifts _).2.1
      right_unitor := ?_
      symmetry := fun _ ↦ (DerivedCategory.nativeDerivedMonoidalConstraintShifts _).2.2
      compositor := fun f g ↦ module_pullback_compositor_commShift Λ f g }
  · intro W n E
    classical
    choose P hP using fun i ↦ DerivedCategory.exists_kFlat_iso (E i)
    exact ⟨P, hP⟩
  · intro W K n
    apply (cancel_epi (β_ (𝟙_ 𝔻(W)) (K⟦n⟧)).hom).1
    rw [← Category.assoc, DerivedCategory.braiding_hom_commShiftIso_hom_app,
      Category.assoc, ← (shiftFunctor 𝔻(W) n).map_comp,
      braiding_rightUnitor, braiding_rightUnitor]
    exact DerivedCategory.leftUnitor_commShift_app _ K n

end WeilConjectures.DiagramPullbackShift
