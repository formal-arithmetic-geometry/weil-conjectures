/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerCanonicalReduction
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBoundedFreeCone
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.ProperBaseChange.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-! # Finite reduction of the projection from a normalized tower limit

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, finite-reduction paragraph.
(blueprint: lem-sp-tower-projection-finite-reduction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale

attribute [-instance] spCoefficientModulesAbelian
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
  (D : SpCoefficientTowersAbelian l E T)

private theorem completed_derived_products :
    Nonempty (HasLimitsOfShape (Discrete ℕ)
      (DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))) := by
  let A := WeilConjectures.scalarReductionSource.{u, u} l E T
  let R := WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T
  let : CountableAB4Star A := by
    constructor
    intro I _
    have : (lim : (Discrete I ⥤ A) ⥤ A).PreservesEpimorphisms := by
      constructor
      intro B C f hf
      let eB := HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := B))
      let eC := HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := C))
      have h (i : I) : Epi (f.app ⟨i⟩) := inferInstance
      have : Epi (Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩)) :=
        (Scheme.ProEt.countableProducts_exact.{u, u, 0} T R).2.2 I _ _ _ h
      have hh : lim.map f = eB.hom ≫ Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩) ≫ eC.inv := by
        apply limit.hom_ext
        rintro ⟨i⟩
        dsimp only [eB, eC]
        simp only [Category.assoc, HasLimit.isoOfNatIso_inv_π,
          Discrete.natIsoFunctor_inv_app]
        change lim.map f ≫ limit.π C ⟨i⟩ =
          (HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := B))).hom ≫
            Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩) ≫ Pi.π _ i
        rw [Pi.map_π, HasLimit.isoOfNatIso_hom_π_assoc]
        simp
      rw [hh]
      infer_instance
    exact hasExactLimitsOfShape_of_preservesEpi (C := A) (Discrete I)
  obtain ⟨hP, _⟩ := derivedCategory_countableProducts_core.{0} A
  let := hP
  exact ⟨inferInstance⟩

private theorem exactDerived_reflects_iso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory A} (f : K ⟶ L)
    (hf : IsIso (F.mapDerivedCategory.map f)) : IsIso f := by
  have := hf
  rw [DerivedCategory.isIso_iff]
  intro i
  have hm : IsIso (F.map ((DerivedCategory.homologyFunctor A i).map f)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso i) f).mpr
      (by dsimp only [Functor.comp_map]; infer_instance)
  have := hm
  have : Mono ((DerivedCategory.homologyFunctor A i).map f) :=
    F.mono_of_mono_map inferInstance
  have : Epi ((DerivedCategory.homologyFunctor A i).map f) :=
    F.epi_of_epi_map inferInstance
  exact isIso_of_mono_of_epi _

/-- The finite reduction calculation for one specified projection. No boundedness or
constructibility assumption is used.
Source: current blueprint, sk-lem-sp-tower.proof.md, first paragraph, through
"the reduction formula follows"; Stacks 0940 and 099P
(blueprint: lem-sp-tower-projection-finite-reduction).

Proof: choose the simultaneous flat-term K-flat model of
lem-sp-semilinear-kflat-tower-model, retaining the original reductions and projections.
The model's counit equation and normalization make its ordinary reduction maps
quasi-isomorphisms. Fix exponent m+1 and delete the first m terms of the tower.
The coefficient-fiber lemma identifies the fiber of the augmented Koszul complex
with the smaller coefficient ring in degree -1; its transitions are multiplication
by the corresponding powers of ell. Tensor with the K-flat level complexes.
The normalized-error-tower lemma makes the left error tower pro-zero: every m+1
successive transitions vanish. Its derived limit is zero, while the right constant
tower has the given level as limit. Thus the middle Koszul tower has that same limit.
The Koszul--Roos projection comparison identifies it with reduction of M, retaining
the m-th projection. Its adjunction normalization identifies the resulting arrow with
the displayed spTowerReconstructionMap. Exact scalar restriction detects isomorphisms,
so the map is invertible in the finite-coefficient category itself. -/
theorem spTower_projection_finite_reduction
    (C : spDerivedCoefficientTowers l E T D)
    (hnorm : IsSpNormalizedTower l E T D C)
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    [HasProduct (fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)
    (δ : (∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C) ⟶ M⟦(1 : ℤ)⟧)
    (hlim : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (spDerivedCompletedTransition l E T D n).app C) M p δ) (m : ℕ) :
    IsIso (spTowerReconstructionMap l E T D C M p m) := by
  obtain ⟨hprod⟩ := completed_derived_products l E T
  let := hprod
  obtain ⟨U, hU, eU, heU, hfinite⟩ :=
    spTower_strict_normalized_adic_model l E T D C hnorm
  obtain ⟨N, iN, eN, hN⟩ := hfinite m
  obtain ⟨c, hc, a, he⟩ :=
    spTower_bounded_free_cone_comparison l E T D C M p δ hlim m U hU eU heU N iN eN hN
  have hi := hU.isIso_π_comp (m + 1) hc
  have hm : IsIso ((spCompletedEllRestriction l E T m).mapDerivedCategory.map
      (spTowerReconstructionMap l E T D C M p m)) := by
    rw [he]
    simpa only [Category.assoc] using
      (IsIso.comp_isIso' (inferInstance : IsIso a.hom)
        (IsIso.comp_isIso' hi (inferInstance : IsIso (eU m).hom)))
  have : (spCompletedEllRestriction l E T m).Faithful := ⟨by
    intro K L f g h
    ext V x
    exact congrArg (fun k ↦ (k.val.app V) x) h⟩
  exact exactDerived_reflects_iso (spCompletedEllRestriction l E T m) _ hm

end AlgebraicGeometry.ProEtale
