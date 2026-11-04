/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Curve.FLCFiber
public import WeilConjectures.AlgebraicGeometry.Curve.PointedEtaleStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.CategoryTheory.Sites.UnitHomEval
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # The canonical morphism between two scalar-reduction towers

Source: the coefficient-heart argument, reductions of an integral morphism.
(blueprint: lem-sfb-coefficient-heart-quotient-map)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower
variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {X : Scheme.{u}} {pi : A} {M N : Modules A X}

/-- Scalar multiplication commutes with every native module morphism.
Source: naturality of the left unitor and interchange for tensor products.
(blueprint: lem-sfb-coefficient-heart-quotient-map)
Proof: move the morphism past the scalar endomorphism of the tensor unit by interchange,
then apply naturality of the inverse left unitor. -/
theorem scalar_naturality (h : M ⟶ N) (a : A) :
    scalar A X M a ≫ h = h ≫ scalar A X N a := by
  simp only [scalar, Category.assoc]
  rw [← leftUnitor_naturality]
  let e : 𝟙_ (Modules A X) ⟶ 𝟙_ (Modules A X) :=
    (modelRegularIso A X).inv ≫ (FiniteConstantModel.modelFunctor A X).map
      (ModuleCat.ofHom (a • LinearMap.id)) ≫ (modelRegularIso A X).hom
  change (λ_ M).inv ≫ e ▷ M ≫ 𝟙_ (Modules A X) ◁ h ≫ (λ_ N).hom =
    h ≫ (λ_ N).inv ≫ e ▷ N ≫ (λ_ N).hom
  rw [← whisker_exchange_assoc e h, ← leftUnitor_inv_naturality_assoc]

/-- A reduction projection is epimorphic since it is a cokernel projection.
Source: the scalar-cokernel universal property, blueprint coefficient-heart reductions.
(blueprint: lem-sfb-coefficient-heart-quotient-map)
Proof: its specified colimit cofork makes it a cokernel, hence an epimorphism. -/
theorem Reduction.projection_epi (R : Reduction A X pi M) (n : ℕ) :
    Epi (R.projection.app (op n)) :=
  Cofork.IsColimit.epi (R.quotient n)

/-- The unique map on scalar quotients induced by an integral module morphism.
Source: blueprint coefficient-heart reductions.
(blueprint: lem-sfb-coefficient-heart-quotient-map)
The composite with the target projection kills the source scalar map by scalar naturality;
the specified cokernel universal property therefore produces the map. -/
def Reduction.quotientMapApp (R : Reduction A X pi M) (S : Reduction A X pi N)
    (h : M ⟶ N) (n : ℕ) : R.quotients.obj (op n) ⟶ S.quotients.obj (op n) :=
  (R.quotient n).desc (CokernelCofork.ofπ (h ≫ S.projection.app (op n)) (by
    rw [← Category.assoc, scalar_naturality, Category.assoc, S.killed, comp_zero]))

/-- The quotient map is normalized by the original integral morphism.
Source: the cokernel factorization equation.
(blueprint: lem-sfb-coefficient-heart-quotient-map)
Proof: this is the factorization equation of the specified colimit cofork. -/
theorem Reduction.quotientMapApp_fac (R : Reduction A X pi M) (S : Reduction A X pi N)
    (h : M ⟶ N) (n : ℕ) :
    R.projection.app (op n) ≫ R.quotientMapApp S h n = h ≫ S.projection.app (op n) := by
  exact (R.quotient n).fac _ WalkingParallelPair.one

/-- The canonical maps of quotients commute with all tower arrows.
Source: coefficient-heart proof (1), descent of the reductions of `h`.
(blueprint: lem-sfb-coefficient-heart-quotient-map)
Proof: precompose with a source quotient projection, which is epimorphic. Both composites
then equal the original map followed by the corresponding target projection. -/
def Reduction.quotientMap (R : Reduction A X pi M) (S : Reduction A X pi N)
    (h : M ⟶ N) : R.quotients ⟶ S.quotients where
  app n := R.quotientMapApp S h n.unop
  naturality {i j} f := by
    have := R.projection_epi i.unop
    apply (cancel_epi (R.projection.app i)).1
    have hR : R.projection.app i ≫ R.quotients.map f = R.projection.app j := by
      simpa using (R.projection.naturality f).symm
    have hS : S.projection.app i ≫ S.quotients.map f = S.projection.app j := by
      simpa using (S.projection.naturality f).symm
    simp only [← Category.assoc, hR]
    rw [R.quotientMapApp_fac S h j.unop, R.quotientMapApp_fac S h i.unop,
      Category.assoc, hS]

/-- The quotient transformation is the reduction of the specified integral morphism.
Source: the cokernel factorization equation at each level.
(blueprint: lem-sfb-coefficient-heart-quotient-map)
Proof: natural transformations agree componentwise, and each component is the defining
cokernel factorization equation. -/
theorem Reduction.quotientMap_natural (R : Reduction A X pi M) (S : Reduction A X pi N)
    (h : M ⟶ N) :
    (Functor.const ℕᵒᵖ).map h ≫ S.projection = R.projection ≫ R.quotientMap S h := by
  apply NatTrans.ext
  funext n
  exact (R.quotientMapApp_fac S h n.unop).symm

/-- Compatibility with the projections uniquely determines the entire quotient map.
Source: the cokernel uniqueness equation at each level.
(blueprint: lem-sfb-coefficient-heart-quotient-map)
Proof: precompose each component with its epimorphic quotient projection. The two composites
coincide by the supplied square and by the canonical factorization equation. -/
theorem Reduction.quotientMap_unique (R : Reduction A X pi M) (S : Reduction A X pi N)
    (h : M ⟶ N) (q : R.quotients ⟶ S.quotients)
    (hq : (Functor.const ℕᵒᵖ).map h ≫ S.projection = R.projection ≫ q) :
    q = R.quotientMap S h := by
  apply NatTrans.ext
  funext n
  have := R.projection_epi n.unop
  apply (cancel_epi (R.projection.app n)).1
  exact (NatTrans.congr_app hq n).symm.trans (R.quotientMapApp_fac S h n.unop).symm

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
