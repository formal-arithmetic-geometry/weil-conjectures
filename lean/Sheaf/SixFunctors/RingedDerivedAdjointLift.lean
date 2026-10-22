/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.SixFunctors.RingedDerivedComparisonData
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Sheaf.SixFunctors.SuppliedTensorAdjunctionNormalization
import all Sheaf.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.Algebra.Homology.KFlatResolution
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Paper.RingedTopoiTensorSections

/-! # Normalized derived adjoint lifts of ringed-topos morphisms

Source: Stacks Project, Modules on Sites, Tag 03D7, and Cohomology on Sites,
Tags 06YY and 07A6.
(blueprint: lem-sfb-ringed-derived-adjoint-lift).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits WeilConjectures SheafOfModules

namespace CategoryTheory.RingedDerivedComparisons

attribute [local irreducible] SheafOfModules.monoidalCategory RingedTensor.tensorFunctor

/-- The adjunction portion of a normalized lift, prior to tensor coherence.
Source: Stacks Project, Tags 03D7, 06YY and 07A6.
(blueprint: lem-sfb-ringed-derived-adjoint-lift). -/
structure AdjointLift {X Y : Site.{u, w}} (f : Morphism X Y) where
  edge : RingedTensorEdge Y.corner X.corner
  inverse_eq : edge.inverse = f.inverse
  direct_eq : edge.direct = f.direct
  geometric_adjunction : HEq edge.adjunction f.adj
  pushforward_eq : edge.pushforward = f.modules
  structural_map :
    edge.algebraic.ringUnderlying.hom ≫
        (sheafCompose X.J (CategoryTheory.forget CommRingCat.{u})).map edge.ringMap =
      eqToHom (congrArg (fun F ↦ F.obj
        ((sheafCompose Y.J (CategoryTheory.forget CommRingCat.{u})).obj Y.A)) inverse_eq) ≫
          f.ringMap
  ordinary_adjunction : ∀ (M : Y.modules) (N : X.modules) (v : edge.pullback.obj M ⟶ N),
    Y.sets.map (edge.moduleAdjunction.homEquiv M N v) ≫
      (Functor.whiskerRight (eqToHom pushforward_eq) Y.sets).app N ≫
        f.underlying.hom.app N =
      f.adj.homEquiv (Y.sets.obj M) (X.sets.obj N)
        (eqToHom (congrArg (fun F ↦ F.obj (Y.sets.obj M)) inverse_eq.symm) ≫
          edge.insertion M ≫ X.sets.map v)
  [right_additive : edge.pushforward.Additive]
  eta : edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{w} (C := Y.modules) ⟶
    DerivedCategory.Q.{w} (C := X.modules) ⋙ edge.right
  isRightDerived : edge.right.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso X.modules (ComplexShape.up ℤ))
  eta_injective : ∀ I : CochainComplex X.modules ℤ, I.IsKInjective → IsIso (eta.app I)
  epsilon_flat : ∀ P : CochainComplex Y.modules ℤ,
    Y.corner.mateFlat P → IsIso (derivedPullbackComplexComparison
      edge.pullback edge.left edge.epsilon P)
  canonical_adjunction : ∀ (P : CochainComplex Y.modules ℤ)
    (I : CochainComplex X.modules ℤ), Y.corner.mateFlat P → I.IsKInjective →
    ∀ b : P ⟶ (edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I,
      (edge.derivedAdjunction.homEquiv (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj I)).symm (DerivedCategory.Q.map b ≫ eta.app I) =
      derivedPullbackComplexComparison edge.pullback edge.left edge.epsilon P ≫
        DerivedCategory.Q.map
          (((edge.moduleAdjunction.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv P I).symm b)

attribute [instance] AdjointLift.right_additive

private theorem complexComparison_eq_epsilon
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (M : CochainComplex A ℤ) :
    derivedPullbackComplexComparison F L ε M =
      ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj M) := by
  dsimp only [derivedPullbackComplexComparison, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
    CategoryTheory.Quotient.lift.isLift_hom, CategoryTheory.Quotient.lift.isLift_inv]
  change L.map (𝟙 _) ≫ ε.app _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  simp only [Functor.map_id, Category.id_comp, Category.comp_id]
  exact Category.comp_id _

set_option maxHeartbeats 600000 in
-- Comparing the supplied scalar presentation and derived adjunction uses dependent instances.
/-- Each ringed-topos morphism has normalized ordinary and derived module adjunctions.
Source: Stacks Project, Modules on Sites, Tag 03D7, and Cohomology on Sites,
Tags 06YY and 07A6.
(blueprint: lem-sfb-ringed-derived-adjoint-lift).

Proof: transport the ring and its modules along the finite-limit-preserving inverse
image, and extend scalars along the given structural map. The supplied normalized
scalar-extension adjunction gives exactly the recorded underlying-sheaf Hom formula.
The K-flat resolving class constructs the universal left derived functor, while
K-injective derivability constructs the universal right derived functor. The
resolving-class derived adjunction gives the required transpose formula. Its
comparison maps are invertible on the two resolving classes. -/
theorem adjointLift_exists {X Y : Site.{u, w}} (f : Morphism X Y) :
    Nonempty (AdjointLift f) := by
  let _ := f.leftExact
  obtain ⟨RI, ⟨I⟩⟩ := algebraic_image Y.J X.J f.inverse f.direct f.adj Y.A
  obtain ⟨c, hc⟩ := structural_map X.J Y.J X.A Y.A f RI I
  let F := I.modules ⋙ RingedTensor.tensorFunctor c
  have hobj (M : Y.modules) : F.obj M = changeOfRings c (I.modules.obj M) := by
    unfold F RingedTensor.tensorFunctor
    rfl
  have hmap {M N : Y.modules} (a : M ⟶ N) : F.map a = eqToHom (hobj M) ≫
      changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm := by
    unfold F RingedTensor.tensorFunctor
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  obtain ⟨⟨k⟩, _⟩ := canonicalRingedTensorComparison_existsUnique
    Y.A X.A RI f.inverse I c F hobj f.direct f.adj hmap
  obtain ⟨adj, hadj⟩ := suppliedTensorAdjunction_normalized f RI I c hc F hobj hmap k
  let _ : PreservesColimits F := adj.leftAdjoint_preservesColimits
  let _ : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let _ : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  obtain ⟨L, ε, hL, _, hpres, hε, _⟩ :=
    ringedTopoiDerivedPullback f.inverse f.direct f.adj I c F hobj hmap
  let _ := (grothendieckAbelian_and_functorial_kInjective_resolutions X.J X.A).1
  obtain ⟨RF, η, hRF, hη⟩ := CategoryTheory.exists_derived f.modules
  let π := HomotopyCategory.quotient Y.modules (.up ℤ)
  let GF := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w}
  let P : Set (HomotopyCategory Y.modules (.up ℤ)) :=
    {T | ∃ M : CochainComplex Y.modules ℤ, π.obj M = T ∧
      M.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (M.X n).IsFlat}
  have hres : ∀ T : HomotopyCategory Y.modules (.up ℤ),
      ∃ (T' : HomotopyCategory Y.modules (.up ℤ)) (s : T' ⟶ T),
        T' ∈ P ∧ HomotopyCategory.quasiIso Y.modules (.up ℤ) s := by
    intro T
    obtain ⟨T, rfl⟩ := HomotopyCategory.quotient_obj_surjective T
    obtain ⟨M, s, hM, hf, hs, _⟩ := CochainComplex.exists_isKFlatResolution T
    exact ⟨π.obj M, π.map s, ⟨M, rfl, hM, hf⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv : ∀ (T T' : HomotopyCategory Y.modules (.up ℤ)) (s : T ⟶ T'),
      T ∈ P → T' ∈ P → HomotopyCategory.quasiIso Y.modules (.up ℤ) s →
        IsIso (GF.map s) := by
    intro T T' s hT hT' hs
    obtain ⟨T, rfl, hT, hfT⟩ := hT
    obtain ⟨T', rfl, hT', hfT'⟩ := hT'
    obtain ⟨s, rfl⟩ := π.map_surjective s
    have hq := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs
    have ht := hpres s hT hfT hT' hfT' hq
    change IsIso (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map (π.map s)))
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.modules (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
  obtain ⟨d, hd⟩ := derivedAdjunctionOfResolvingClass F f.modules adj P hres hinv
    L ε hL RF η hRF
  let e : RingedTensorEdge Y.corner X.corner := {
    inverse := f.inverse
    direct := f.direct
    adjunction := f.adj
    finiteLimits := f.leftExact
    inverseRing := RI
    algebraic := I
    ringMap := c
    pullback := F
    object_eq := hobj
    map_eq := hmap
    additive := inferInstance
    ordinaryTensor := k
    pushforward := f.modules
    moduleAdjunction := adj
    left := L
    epsilon := ε
    isLeftDerived := hL
    right := RF
    derivedAdjunction := d }
  refine ⟨{
    edge := e
    inverse_eq := rfl
    direct_eq := rfl
    geometric_adjunction := HEq.rfl
    pushforward_eq := rfl
    structural_map := ?_
    ordinary_adjunction := ?_
    right_additive := f.additive
    eta := η
    isRightDerived := hRF
    eta_injective := hη
    epsilon_flat := ?_
    canonical_adjunction := ?_ }⟩
  · change I.ringUnderlying.hom ≫ _ = 𝟙 _ ≫ f.ringMap
    rw [hc, Iso.hom_inv_id_assoc, Category.id_comp]
  · intro M N v
    change Y.sets.map ((adj.homEquiv M N) v) ≫ Y.sets.map (𝟙 (f.modules.obj N)) ≫
      f.underlying.hom.app N = f.adj.homEquiv (Y.sets.obj M) (X.sets.obj N)
        (𝟙 _ ≫ (I.moduleUnderlying.inv.app M ≫ k.q M) ≫ X.sets.map v)
    simpa only [Functor.map_id, Category.comp_id, Category.id_comp, Category.assoc] using
      hadj M N v
  · intro M hM
    change IsIso (derivedPullbackComplexComparison F L ε M)
    rw [complexComparison_eq_epsilon]
    exact hε M hM.1 hM.2
  · intro M N _ _ b
    dsimp only [e]
    change (d.homEquiv _ _).symm (DerivedCategory.Q.map b ≫ η.app N) =
      derivedPullbackComplexComparison F L ε M ≫
        DerivedCategory.Q.map (((adj.mapHomologicalComplex (.up ℤ)).homEquiv M N).symm b)
    rw [complexComparison_eq_epsilon]
    apply (d.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    symm
    simpa only [Equiv.apply_symm_apply] using
      hd M N (((adj.mapHomologicalComplex (.up ℤ)).homEquiv M N).symm b)

end CategoryTheory.RingedDerivedComparisons
