/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Picard.VerdierExchange.VerdierExchangeData
public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit

/-! # Evaluation-normalized closed-adjunction exchange

Source: latest blueprint, sec-poincare-duality/sk-thm-frobenius/
prop-weil-operations.proof.md, fifth sentence; fix-lem-tensor-adjunction.proof.md, Step 1.
(blueprint: lem-pod-normalized-closed-adjunction-exchange).

All maps below use the specified closed structures. In particular the exchange is
constructed from projection inverse and evaluation, rather than chosen from its endpoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u₁ v₁ u₂ v₂ u
open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace CategoryTheory.NormalizedClosedExchange

variable {X : Type u₁} [Category.{v₁} X] [MonoidalCategory X]
  [sX : SymmetricCategory X] [MonoidalClosed X]
  {Y : Type u₂} [Category.{v₂} Y] [MonoidalCategory Y]
  [sY : SymmetricCategory Y] [MonoidalClosed Y]

/-- The specified projection isomorphism, with naturality in both variables.
Source: latest blueprint fix-lem-tensor-adjunction.proof.md, Step 1.
(blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
abbrev Projection (U : Y ⥤ X) (F : X ⥤ Y) :=
  curriedTensorInsertFunctor₁ F ≅
    curriedTensorPost F ⋙ (Functor.whiskeringLeft Y X Y).obj U

/-- Regard a componentwise invertible natural projection as a natural isomorphism.
This uses the given morphisms and their unique inverses, without changing any component.
Source: latest blueprint fix-lem-tensor-adjunction.proof.md, Step 1.
(blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
def projectionOfNatTrans {U : Y ⥤ X} {F : X ⥤ Y}
    (p : curriedTensorInsertFunctor₁ F ⟶
      curriedTensorPost F ⋙ (Functor.whiskeringLeft Y X Y).obj U)
    [∀ (M : X) (L : Y), IsIso ((p.app M).app L)] : Projection U F :=
  letI (M : X) : IsIso (p.app M) := NatIso.isIso_of_isIso_app _
  letI : IsIso p := NatIso.isIso_of_isIso_app _
  asIso p

/-- The five-bijection chain on an arbitrary test morphism. Its first arrow is
inverse closed transposition and its second is precomposition by projection inverse.
Source: latest blueprint fix-lem-tensor-adjunction.proof.md, Step 1.
(blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
def homChain {U : Y ⥤ X} {V : X ⥤ Y} {F : X ⥤ Y} {R : Y ⥤ X}
    (adjU : U ⊣ V) (adjF : F ⊣ R) (π : Projection U F)
    (M : X) (N L : Y) (h : L ⟶ (ihom (F.obj M)).obj N) :
    L ⟶ V.obj ((ihom M).obj (R.obj N)) :=
  adjU.homEquiv _ _ (curry (adjF.homEquiv _ _
    (((π.app M).app L).inv ≫ uncurry h)))

/-- The actual exchange component: apply the five-bijection chain to the identity.
Equivalently this is unit of U, followed by V of the curry of the F-adjoint of
projection inverse followed by evaluation.
Source: latest blueprint fix-lem-tensor-adjunction.proof.md, Step 1.
(blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
def map {U : Y ⥤ X} {V : X ⥤ Y} {F : X ⥤ Y} {R : Y ⥤ X}
    (adjU : U ⊣ V) (adjF : F ⊣ R) (π : Projection U F) (M : X) (N : Y) :
    (ihom (F.obj M)).obj N ⟶ V.obj ((ihom M).obj (R.obj N)) :=
  adjU.unit.app _ ≫ V.map (curry (adjF.homEquiv _ _
    (((π.app M).app ((ihom (F.obj M)).obj N)).inv ≫ (ihom.ev (F.obj M)).app N)))

/-- Explicit unit and counit preservation for a pair of commuting functors.
Source: latest blueprint lem-fix-weil-operations.proof.md, adjunction paragraph.
(blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
structure PreservesAdjunction (P : X ⥤ X) (Q : Y ⥤ Y)
    {J : X ⥤ Y} {K : Y ⥤ X} (adj : J ⊣ K)
    (eJ : J ⋙ Q ≅ P ⋙ J) (eK : K ⋙ P ≅ Q ⋙ K) : Prop where
  unit (A : X) :
    P.map (adj.unit.app A) ≫ (eK.hom.app (J.obj A)) ≫ K.map (eJ.hom.app A) =
      adj.unit.app (P.obj A)
  counit (B : Y) :
    (eJ.hom.app (K.obj B)) ≫ J.map (eK.hom.app B) ≫ adj.counit.app (Q.obj B) =
      Q.map (adj.counit.app B)

/-- The four commuting functor isomorphisms, with actual unit, counit and projection
compatibility equations. Strong symmetric monoidal structures on P and Q are
parameters of the equivariance theorem, not arbitrary proposition fields.
Source: latest blueprint lem-fix-weil-operations.proof.md, adjunction and projection
paragraphs. (blueprint: lem-pod-normalized-closed-adjunction-exchange). -/
structure Compatible (P : X ⥤ X) (Q : Y ⥤ Y) [P.Monoidal] [Q.Monoidal]
    {U : Y ⥤ X} {V : X ⥤ Y} {F : X ⥤ Y} {R : Y ⥤ X}
    (adjU : U ⊣ V) (adjF : F ⊣ R) (π : Projection U F) where
  eU : U ⋙ P ≅ Q ⋙ U
  eV : V ⋙ Q ≅ P ⋙ V
  eF : F ⋙ Q ≅ P ⋙ F
  eR : R ⋙ P ≅ Q ⋙ R
  adjunctionU : PreservesAdjunction Q P adjU eU eV
  adjunctionF : PreservesAdjunction P Q adjF eF eR
  projection (M : X) (L : Y) :
    Q.map ((π.app M).app L).hom ≫ (eF.hom.app (M ⊗ U.obj L)) ≫
        F.map (Functor.OplaxMonoidal.δ P M (U.obj L)) ≫
        F.map (𝟙 (P.obj M) ⊗ₘ eU.hom.app L) =
      Functor.OplaxMonoidal.δ Q (F.obj M) L ≫
        (eF.hom.app M ⊗ₘ 𝟙 (Q.obj L)) ≫ ((π.app (P.obj M)).app (Q.obj L)).hom


section
omit sX sY

private theorem exchange_naturality_left {U : Y ⥤ X} {V : X ⥤ Y} {F : X ⥤ Y} {R : Y ⥤ X}
    (adjU : U ⊣ V) (adjF : F ⊣ R) (π : Projection U F)
    {M M' : X} (a : M' ⟶ M) (N : Y)
    [∀ B, IsIso ((π.hom.app M).app B)] [∀ B, IsIso ((π.hom.app M').app B)] :
    V.map ((pre a).app (R.obj N)) ≫ Verdier.exchange adjU adjF π.hom M' N =
      Verdier.exchange adjU adjF π.hom M N ≫ (pre (F.map a)).app N := by
  have hp : F.map a ▷ V.obj ((ihom M).obj (R.obj N)) ≫
      (π.hom.app M).app (V.obj ((ihom M).obj (R.obj N))) =
      (π.hom.app M').app (V.obj ((ihom M).obj (R.obj N))) ≫
        F.map (a ▷ U.obj (V.obj ((ihom M).obj (R.obj N)))) :=
    NatTrans.congr_app (π.hom.naturality a) _
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app, Verdier.uncurry_exchange,
    Verdier.uncurry_exchange]
  simp only [Verdier.exchangePairing]
  rw [Verdier.pf_naturality_right_assoc, reassoc_of% hp]
  have hi : M' ◁ U.map (V.map ((pre a).app (R.obj N))) ≫
      M' ◁ adjU.counit.app ((ihom M').obj (R.obj N)) ≫ (ihom.ev M').app (R.obj N) =
      a ▷ U.obj (V.obj ((ihom M).obj (R.obj N))) ≫
        M ◁ adjU.counit.app ((ihom M).obj (R.obj N)) ≫ (ihom.ev M).app (R.obj N) := by
    rw [← whiskerLeft_comp_assoc, (adjU.counit_naturality ((pre a).app (R.obj N)))]
    rw [whiskerLeft_comp_assoc, id_tensor_pre_app_comp_ev]
    rw [whisker_exchange_assoc]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ (π.hom.app M').app (V.obj ((ihom M).obj (R.obj N))) ≫
      F.map t ≫ adjF.counit.app N) hi

private theorem exchange_naturality_right {U : Y ⥤ X} {V : X ⥤ Y} {F : X ⥤ Y} {R : Y ⥤ X}
    (adjU : U ⊣ V) (adjF : F ⊣ R) (π : Projection U F)
    (M : X) {N N' : Y} (b : N ⟶ N')
    [∀ B, IsIso ((π.hom.app M).app B)] :
    V.map ((ihom M).map (R.map b)) ≫ Verdier.exchange adjU adjF π.hom M N' =
      Verdier.exchange adjU adjF π.hom M N ≫ (ihom (F.obj M)).map b := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right, Verdier.uncurry_exchange,
    Verdier.uncurry_exchange]
  simp only [Verdier.exchangePairing, Category.assoc]
  rw [Verdier.pf_naturality_right_assoc]
  have hi : M ◁ U.map (V.map ((ihom M).map (R.map b))) ≫
      M ◁ adjU.counit.app ((ihom M).obj (R.obj N')) ≫ (ihom.ev M).app (R.obj N') =
      M ◁ adjU.counit.app ((ihom M).obj (R.obj N)) ≫
        (ihom.ev M).app (R.obj N) ≫ R.map b := by
    rw [← whiskerLeft_comp_assoc, (adjU.counit_naturality ((ihom M).map (R.map b))),
      whiskerLeft_comp_assoc,
      ihom.ev_naturality]
  have h := congrArg (fun t ↦ (π.hom.app M).app (V.obj ((ihom M).obj (R.obj N))) ≫
    F.map t ≫ adjF.counit.app N') hi
  simpa only [Functor.map_comp, Category.assoc, adjF.counit_naturality b] using h

private theorem map_eq_inv_exchange {U : Y ⥤ X} {V : X ⥤ Y} {F : X ⥤ Y} {R : Y ⥤ X}
    (adjU : U ⊣ V) (adjF : F ⊣ R) (π : Projection U F) (M : X) (N : Y) :
    map adjU adjF π M N =
      @inv _ _ _ _ (Verdier.exchange adjU adjF π.hom M N)
        (Verdier.isIso_exchange_of_isIso adjU adjF π.hom M N) := by
  symm
  let E := Verdier.exchange adjU adjF π.hom M N
  let : ∀ B, IsIso ((π.hom.app M).app B) := fun B => inferInstance
  let : IsIso E := Verdier.isIso_exchange_of_isIso adjU adjF π.hom M N
  have e :
      (fun u : (ihom (F.obj M)).obj N ⟶ V.obj ((ihom M).obj (R.obj N)) ↦ u ≫ E) =
        curry ∘ (fun x ↦ (π.hom.app M).app _ ≫ x) ∘
          (adjF.homEquiv _ _).symm ∘ uncurry ∘ (adjU.homEquiv _ _).symm := by
    funext u
    simp only [Function.comp_apply, E, Verdier.exchange, ← curry_natural_left,
      Verdier.exchangePairing, Verdier.pf_naturality_right_assoc,
      Adjunction.homEquiv_counit, uncurry_eq,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, Functor.map_comp]
  apply (cancel_mono E).1
  have eh := congrFun e (map adjU adjF π M N)
  dsimp [E]
  simp only [IsIso.inv_hom_id]
  simpa [map, homChain, Function.comp_apply, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_counit, ← uncurry_id_eq_ev, curry_uncurry] using eh.symm

omit [MonoidalCategory X] [MonoidalClosed X]
  [MonoidalCategory Y] [MonoidalClosed Y] in
omit [MonoidalCategory X] [MonoidalClosed X]
  [MonoidalCategory Y] [MonoidalClosed Y] in
omit [MonoidalClosed X] [MonoidalClosed Y] in
omit [MonoidalCategory X] [MonoidalClosed X] in
end

-- Preserve the public symmetry parameters although the proof works without symmetry.
set_option linter.unusedSectionVars false in
include sX sY in
include sX sY in
end CategoryTheory.NormalizedClosedExchange

open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing.NormalizedClosedExchange
open CategoryTheory.NormalizedClosedExchange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

set_option maxHeartbeats 2000000 in
-- Elaborating both concrete six-operation expressions needs the larger heartbeat budget.
set_option synthInstance.maxHeartbeats 200000 in
end AlgebraicGeometry.ProEtale.CondensedRing.NormalizedClosedExchange
