/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.AlgebraicGeometry.ModuleDerivedCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
public import WeilConjectures.AlgebraicGeometry.ExchangeForgetCoefficients
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality
import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import all WeilConjectures.AlgebraicGeometry.Sites.Kummer
import all Mathlib.Algebra.Module.ZMod
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import WeilConjectures.AlgebraicGeometry.PurityFiniteKummerLevel
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison

/-! # Relative Kummer coefficients and scalar-forgetting normalization

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction,
prop-pur-gm-relative-kummer.proof.md, opening paragraph and Step 3;
Stacks Project, Tags 03PL, 03FD, 072W and 0D6J
(blueprint: lem-pur-relative-kummer-coefficient-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Etale

namespace WeilConjectures.PurityFiniteSetting

/-- Exactness of the coefficient forgetful functor used in the derived comparison.
Source: Stacks 03FD (blueprint: lem-pur-relative-kummer-coefficient-normalization).
Proof: restriction of scalars along Z to A has both scalar adjoints; the equivalence
between integer modules and abelian groups preserves colimits. Thus forgetting
preserves finite colimits, as required by proof steps 6 and 7 of the node. -/
theorem relativeScalarForgetFiniteColimits (P : PurityFiniteSetting.{u}) :
    PreservesFiniteColimits
      (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}) := by
  change PreservesFiniteColimits (ModuleCat.restrictScalars (Int.castRingHom P.Coefficient) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})
  infer_instance

attribute [instance] relativeScalarForgetFiniteColimits

/-- The prime-power exponent is nonzero, independently of the divisibility hypothesis.
Source: the finite coefficient conventions, ell prime
(blueprint: lem-pur-relative-kummer-coefficient-normalization). -/
instance relativeExponentNeZero (P : PurityFiniteSetting.{u}) : NeZero P.exponent :=
  ⟨pow_ne_zero _ (Fact.out : P.coefficients.l.Prime).ne_zero⟩

/-- The normalized positive twist comparison, specialized to the fixed coefficients.
Source: Stacks 03PK and 03Q1
(blueprint: lem-pur-relative-kummer-coefficient-normalization). -/
def relativeTwistPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T T' : Scheme.{u}}
    (v : T' ⟶ T) (a : T ⟶ Spec (.of P.field.k)) :
    (upperStar (ModuleCat.{u + 1} P.Coefficient) v).obj (P.twistEtale h T) ≅
      P.twistEtale h T' :=
  (Scheme.finiteEtaleTwistPullbackData P.Coefficient P.exponent
    (Nat.pos_of_ne_zero (NeZero.ne P.exponent)) (P.exponent_coefficient_eq_zero h)).c
      v (P.exponent_isUnit T a) (P.exponent_isUnit T' (v ≫ a)) 1

/-- The normalized root comparison, retaining its inclusion into the units sheaf.
Source: Stacks 03PK and 03Q1
(blueprint: lem-pur-relative-kummer-coefficient-normalization). -/
def relativeRootPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T T' : Scheme.{u}}
    (v : T' ⟶ T) (a : T ⟶ Spec (.of P.field.k)) :
    (upperStar AddCommGrpCat.{u + 1} v).obj (T.rootsOfUnitySheaf P.exponent) ≅
      T'.rootsOfUnitySheaf P.exponent :=
  (Scheme.finiteEtaleTwistPullbackData P.Coefficient P.exponent
    (Nat.pos_of_ne_zero (NeZero.ne P.exponent)) (P.exponent_coefficient_eq_zero h)).r
      v (P.exponent_isUnit T a)

/-- Evaluation at the terminal etale object commutes with scalar forgetting.
Source: Stacks 03FD (blueprint: lem-pur-relative-kummer-coefficient-normalization).
This uses the fixed evaluation comparisons, rather than choosing an automorphism
of cohomology. -/
def relativeGlobalSectionsForgetIso (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) ⋙
        forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1} ≅
      P.forgetEtale T ⋙ Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerRight
    (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
      (MorphismProperty.Over.mkIdTerminal @Etale T))
    (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}) ≪≫
  Functor.isoWhiskerLeft (P.forgetEtale T)
    (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology AddCommGrpCat.{u + 1}
      (MorphismProperty.Over.mkIdTerminal @Etale T)).symm

/-- Derive the fixed evaluation comparison, with its canonical right-derived units.
Source: Stacks 03FD and 0D6J
(blueprint: lem-pur-relative-kummer-coefficient-normalization). -/
@[irreducible]
def relativeDerivedGlobalForget (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)).rightDerivedFunctorPlus ⋙
        (forget₂ (ModuleCat.{u + 1} P.Coefficient)
          AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus ⟶
      (P.forgetEtale T).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (P.relativeGlobalSectionsForgetIso T).hom

/-- The global cohomology comparison in any integer degree, induced by the fixed
canonical derived comparison and exact forgetting of cohomology.
Source: Stacks 03FD (blueprint: lem-pur-relative-kummer-coefficient-normalization). -/
def relativeGlobalForgetMap (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (q : ℤ)
    (K : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :=
  ((forget₂ (ModuleCat.{u + 1} P.Coefficient)
    AddCommGrpCat.{u + 1}).mapDerivedCategoryPlusHomologyFunctorIso q).hom.app
      ((Sheaf.Γ T.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)).rightDerivedFunctorPlus.obj K) ≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).map
      ((P.relativeDerivedGlobalForget T).app K)

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.Etale
open Scheme

private theorem additiveConstantUnit_apply {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (M : AddCommGrpCat.{u + 1}) (V : Y.Etale) (m : M) :
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _
    ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app M))).hom.app (op V)
      ((CategoryTheory.toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
        M)).app
        (op V) m) =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj
        M)).app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V)) m := by
  let adjY := constantSheafAdj Y.smallEtaleTopology (AddCommGrpCat.{u + 1}) terminalIsTerminal
  let adjZ := constantSheafAdj Z.smallEtaleTopology (AddCommGrpCat.{u + 1}) terminalIsTerminal
  let e := Etale.lowerStarCompSheafSectionsTerminalIso (AddCommGrpCat.{u + 1}) g
  let adj := Etale.upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) g
  have key : (adjY.unit.app M ≫ ((sheafSections
    Y.smallEtaleTopology _).obj (op (⊤_ Y.Etale))).map
      (adj.unit.app ((constantSheaf Y.smallEtaleTopology _).obj M)) ≫ e.hom.app _) ≫
      ((sheafSections Z.smallEtaleTopology _).obj (op (⊤_ Z.Etale))).map
        ((upperStarConstantSheafIso (AddCommGrpCat.{u + 1}) g).hom.app M) = adjZ.unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app ((adjY.comp adj).ofNatIsoRight e) adjZ
      M
  have h := congr(($key).hom m)
  -- constant sections are compatible with restriction
  have hts {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) [HasWeakSheafify J
      (AddCommGrpCat.{u + 1})] {U W : C} (f : U ⟶ W) :
      (sheafify J ((Functor.const Cᵒᵖ).obj M)).map f.op
        ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op W) m) =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) m :=
    (congr(($((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).naturality
      f.op)).hom m)).symm
  let θ := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _
    ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app M))
  let F := MorphismProperty.Over.pullback @Etale ⊤ g
  let i := (PreservesTerminal.iso g.Etale)
  let G := (constantSheaf Z.smallEtaleTopology (AddCommGrpCat.{u + 1})).obj M
  let x := (CategoryTheory.toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
    M)).app
    (op (⊤_ Y.Etale)) m
  have h₁ : G.obj.map i.op.symm.hom (θ.hom.app (op (⊤_ Y.Etale)) x) =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj
        M)).app
        (op (⊤_ Z.Etale)) m :=
    (NatTrans.naturality_apply ((upperStarConstantSheafIso (AddCommGrpCat.{u + 1}) g).hom.app
      M).hom
      i.op.symm.hom _).symm.trans h
  have hT : θ.hom.app (op (⊤_ Y.Etale)) x =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj
        M)).app
        (op (F.obj (⊤_ Y.Etale))) m := by
    have h₂ := congrArg (G.obj.map i.op.hom) h₁
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.symm_hom, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.id_apply] at h₂
    exact h₂.trans (hts Z.smallEtaleTopology i.hom)
  have hn := NatTrans.naturality_apply θ.hom (terminal.from V).op x
  rw [← hts Y.smallEtaleTopology (terminal.from V)]
  refine hn.trans ?_
  change G.obj.map (F.map (terminal.from V)).op (θ.hom.app (op (⊤_ Y.Etale)) x) = _
  rw [hT]
  exact hts Z.smallEtaleTopology _

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

private noncomputable def constantsScalarEquiv (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))) ⟶
      F.obj ⋙ forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) ≃
    (((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A)) ⟶ F.obj) := by
  have hk (W : T.Etaleᵒᵖ) (x : F.obj.obj W) : N • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul A, hA, zero_smul]
  refine {
    toFun := fun f ↦ {
      app := fun W ↦ ModuleCat.ofHom
        (LinearMap.toSpanSingleton A _ ((f.app W).hom (ULift.up 1)))
      naturality := ?_ }
    invFun := fun f ↦ {
      app := fun W ↦
        (AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj W)) (hk W)).symm
          ((f.app W).hom (1 : A))
      naturality := ?_ }
    left_inv := ?_
    right_inv := ?_ }
  · rename_i f
    intro W V g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (show A from a) • (show F.obj.obj V from (f.app V).hom (ULift.up 1)) =
      (F.obj.map g).hom ((show A from a) •
        (show F.obj.obj W from (f.app W).hom (ULift.up 1)))
    rw [map_smul]
    congr 1
    exact (ConcreteCategory.congr_hom (f.naturality g) (ULift.up 1))
  · rename_i f
    intro W V g
    apply (AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj V)) (hk V)).injective
    change _ = (F.obj.map g).hom _
    change (AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj V)) (hk V))
      ((AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj V)) (hk V)).symm
        ((f.app V).hom (1 : A))) = _
    rw [Equiv.apply_symm_apply]
    change (f.app V).hom (1 : A) = (F.obj.map g).hom
      ((AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj W)) (hk W))
        ((AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj W)) (hk W)).symm
          ((f.app W).hom (1 : A))))
    rw [Equiv.apply_symm_apply]
    exact ConcreteCategory.congr_hom (f.naturality g) (1 : A)
  · intro f
    apply NatTrans.ext
    funext W
    apply (AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj W)) (hk W)).injective
    rw [Equiv.apply_symm_apply]
    change (1 : A) • (show F.obj.obj W from (f.app W).hom (ULift.up 1)) = _
    exact one_smul A _
  · intro f
    apply NatTrans.ext
    funext W
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (1 : A) • (show F.obj.obj W from
      ((AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj W)) (hk W)).symm
        ((f.app W).hom (1 : A))).hom (ULift.up 1)) = _
    rw [one_smul]
    exact (AddCommGrpCat.zmodHomEquiv
      (AddCommGrpCat.of (F.obj.obj W)) (hk W)).apply_symm_apply _


private noncomputable def normalizedLineHomEquiv (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (ρ : (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅ T.rootsOfUnitySheaf N)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleTateLine T N A hA ⟶ F) ≃
      ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A) ⟶ F) :=
  (lineHomEquiv T N A hA F).trans
    ((Iso.homCongr ρ.symm (Iso.refl _)).trans
      (((sheafificationAdjunction T.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
        _ _).trans ((constantsScalarEquiv T N A hA F).trans
          ((sheafificationAdjunction T.smallEtaleTopology
            (ModuleCat.{u + 1} A)).homEquiv _ _).symm)))

private theorem normalizedLineHomEquiv_generator (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (ρ : (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅ T.rootsOfUnitySheaf N)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : finiteEtaleTateLine T N A hA ⟶ F) (W : T.Etaleᵒᵖ) (a : A) :
    (normalizedLineHomEquiv T N A hA ρ F f).hom.app W
        ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app W a) =
      a • f.hom.app W (finiteEtaleTateOneGenerator A N T hA W 1
        (ρ.hom.hom.app W ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app W (ULift.up 1)))) := by
  have he := ((sheafificationAdjunction T.smallEtaleTopology
    (ModuleCat.{u + 1} A)).homEquiv _ _).apply_symm_apply
      ((constantsScalarEquiv T N A hA F)
        (((sheafificationAdjunction T.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
          _ _) (ρ.hom ≫ lineHomEquiv T N A hA F f)))
  have hw := ConcreteCategory.congr_hom (congr_app he W) a
  change (normalizedLineHomEquiv T N A hA ρ F f).hom.app W
    ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
      (ModuleCat.of A A))).app W a) = _ at hw
  rw [hw]
  change a • (show F.obj.obj W from (lineHomEquiv T N A hA F f).hom.app W _) = _
  rw [lineHomEquiv_generator]
  rfl


private theorem normalizedLineHomEquiv_comp (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (ρ : (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅ T.rootsOfUnitySheaf N)
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : finiteEtaleTateLine T N A hA ⟶ F) (g : F ⟶ G) :
    normalizedLineHomEquiv T N A hA ρ G (f ≫ g) =
      normalizedLineHomEquiv T N A hA ρ F f ≫ g := by
  apply ((sheafificationAdjunction T.smallEtaleTopology
    (ModuleCat.{u + 1} A)).homEquiv _ _).injective
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (normalizedLineHomEquiv T N A hA ρ G (f ≫ g)).hom.app W
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of A A))).app W a) =
    g.hom.app W ((normalizedLineHomEquiv T N A hA ρ F f).hom.app W
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of A A))).app W a))
  rw [normalizedLineHomEquiv_generator, normalizedLineHomEquiv_generator, map_smul]
  rfl

private noncomputable def normalizedLineIso (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (ρ : (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅ T.rootsOfUnitySheaf N) :
    (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ≅
      finiteEtaleTateLine T N A hA where
  hom := normalizedLineHomEquiv T N A hA ρ _ (𝟙 _)
  inv := (normalizedLineHomEquiv T N A hA ρ _).symm (𝟙 _)
  hom_inv_id := by
    rw [← normalizedLineHomEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]
  inv_hom_id := by
    apply (normalizedLineHomEquiv T N A hA ρ _).injective
    rw [normalizedLineHomEquiv_comp, Equiv.apply_symm_apply, Category.id_comp]

private theorem normalizedLineIso_generator (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (ρ : (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅ T.rootsOfUnitySheaf N)
    (W : T.Etaleᵒᵖ) (a : A) :
    (normalizedLineIso T N A hA ρ).hom.hom.app W
        ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app W a) =
      finiteEtaleTateOneGenerator A N T hA W a
        (ρ.hom.hom.app W ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app W (ULift.up 1))) := by
  change (normalizedLineHomEquiv T N A hA ρ _ (𝟙 _)).hom.app W _ = _
  rw [normalizedLineHomEquiv_generator]
  change a • finiteEtaleTateOneGenerator A N T hA W 1 _ = _
  exact (finiteEtaleGenerator_smul T N A hA W a _).symm


private theorem normalizedLineIso_natural (T T' : Scheme.{u}) (v : T' ⟶ T) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (ρ : (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅ T.rootsOfUnitySheaf N)
    (ρ' : (constantSheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅ T'.rootsOfUnitySheaf N)
    (r : (upperStar AddCommGrpCat.{u + 1} v).obj (T.rootsOfUnitySheaf N) ⟶
      T'.rootsOfUnitySheaf N)
    (c : (upperStar (ModuleCat.{u + 1} A) v).obj (finiteEtaleTateLine T N A hA) ⟶
      finiteEtaleTateLine T' N A hA)
    (hr : (upperStar AddCommGrpCat.{u + 1} v).map ρ.hom ≫ r =
      (upperStarConstantSheafIso AddCommGrpCat.{u + 1} v).hom.app _ ≫ ρ'.hom)
    (hc : ∀ W a z,
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _ c).hom.app W
          (finiteEtaleTateOneGenerator A N T hA W a z) =
        finiteEtaleTateOneGenerator A N T' hA
          ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W) a
          (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _ r).hom.app
            W z)) :
    (upperStar (ModuleCat.{u + 1} A) v).map (normalizedLineIso T N A hA ρ).hom ≫ c =
      (upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).hom.app _ ≫
        (normalizedLineIso T' N A hA ρ').hom := by
  have hr' := congrArg
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _) hr
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at hr'
  have hz (W : T.Etaleᵒᵖ) :
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _ r).hom.app W
          (ρ.hom.hom.app W ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app W (ULift.up 1))) =
        ρ'.hom.hom.app ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W)
          ((toSheafify T'.smallEtaleTopology ((Functor.const T'.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app
              ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W) (ULift.up 1)) := by
    have hw := ConcreteCategory.congr_hom (congr_app (congrArg (fun f ↦ f.hom) hr') W)
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app W (ULift.up 1))
    change _ = ρ'.hom.hom.app _
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
        ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} v).hom.app _)).hom.app W _) at hw
    rw [Etale.additiveConstantUnit_apply] at hw
    exact hw
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  apply ((sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv
    _ _).injective
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _ c).hom.app W
      ((normalizedLineIso T N A hA ρ).hom.hom.app W
        ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app W a)) =
    (normalizedLineIso T' N A hA ρ').hom.hom.app
      ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W)
      ((constantSheafUnit v (ModuleCat.of A A)).hom.app W
        ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app W a))
  rw [normalizedLineIso_generator, hc, hz, constantSheafUnit_app_toSheafify]
  exact (normalizedLineIso_generator T' N A hA ρ' _ a).symm

end AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting
attribute [local implicit_reducible] forgetEtale
private theorem globalForget_terminal (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    (P.relativeGlobalSectionsForgetIso T).hom.app F =
      (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).map
          ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology
            (ModuleCat.{u + 1} P.Coefficient) terminalIsTerminal).hom.app F) ≫
        (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology AddCommGrpCat.{u + 1}
          terminalIsTerminal).inv.app ((P.forgetEtale T).obj F) := by
  let U := forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}
  let ht := MorphismProperty.Over.mkIdTerminal @Etale T
  have hm : (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient) ht).hom.app F ≫
        F.obj.map (ht.from (⊤_ T.Etale)).op =
      (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient) terminalIsTerminal).hom.app F := by
    erw [← Sheaf.ΓNatIsoSheafSections_inv_app_comp_hom_app _ _ ht terminalIsTerminal]
    simp
  apply (cancel_mono ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal).hom.app ((P.forgetEtale T).obj F))).1
  change (U.map ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient) ht).hom.app F) ≫
      (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology AddCommGrpCat.{u + 1}
        ht).inv.app ((P.forgetEtale T).obj F)) ≫ _ =
    (U.map ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient) terminalIsTerminal).hom.app F) ≫
      (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).inv.app ((P.forgetEtale T).obj F)) ≫ _
  erw [Category.assoc, Sheaf.ΓNatIsoSheafSections_inv_app_comp_hom_app,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  change U.map _ ≫ U.map (F.obj.map _) = U.map _
  erw [← U.map_comp, hm]

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.Etale
universe u'
private noncomputable def sectionsPullbackNat (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [HasSmallSiteSheafify A] {T T' : Scheme.{u}} (v : T' ⟶ T) :
    Sheaf.Γ T.smallEtaleTopology A ⟶ upperStar A v ⋙ Sheaf.Γ T'.smallEtaleTopology A :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (upperStarLowerStarAdjunction A v).unit
      (Sheaf.Γ T.smallEtaleTopology A) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (upperStar A v) (lowerStarCompGlobalSectionsIso A v).hom
end AlgebraicGeometry.Etale

namespace WeilConjectures.PurityFiniteSetting
private theorem sectionsPullback_forget (P : PurityFiniteSetting.{u})
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).map
        ((sectionsPullbackNat (ModuleCat.{u + 1} P.Coefficient) v).app F) ≫
        (P.relativeGlobalSectionsForgetIso T').hom.app
          ((upperStar (ModuleCat.{u + 1} P.Coefficient) v).obj F) ≫
        (Sheaf.Γ T'.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((moduleAbelianUpperStarIso P.Coefficient v).inv.app F) =
      (P.relativeGlobalSectionsForgetIso T).hom.app F ≫
        (sectionsPullbackNat AddCommGrpCat.{u + 1} v).app ((P.forgetEtale T).obj F) := by
  rw [globalForget_terminal, globalForget_terminal]
  apply (cancel_mono ((Sheaf.ΓNatIsoSheafSections T'.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal).hom.app
      ((upperStar AddCommGrpCat.{u + 1} v).obj ((P.forgetEtale T).obj F)))).1
  simp only [sectionsPullbackNat, lowerStarCompGlobalSectionsIso,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.map_comp, Category.assoc]
  erw [(Sheaf.ΓNatIsoSheafSections T'.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal).hom.naturality]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  have hnM := (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology
    (ModuleCat.{u + 1} P.Coefficient) terminalIsTerminal).hom.naturality
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) v).unit.app F)
  have hnA := (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal).hom.naturality
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).unit.app
        ((P.forgetEtale T).obj F))
  erw [reassoc_of% hnM, reassoc_of% hnA]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  let σ := (moduleAbelianUpperStarIso P.Coefficient v).inv.app F
  have hunit : (P.forgetEtale T).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) v).unit.app F) ≫
        (lowerStar AddCommGrpCat.{u + 1} v).map σ =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).unit.app
        ((P.forgetEtale T).obj F) := by
    have hu := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv
      ((P.forgetEtale T).obj F)
      ((P.forgetEtale T').obj
        ((upperStar (ModuleCat.{u + 1} P.Coefficient) v).obj F))).apply_symm_apply
       ((P.forgetEtale T).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) v).unit.app F))
    change (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).unit.app
        ((P.forgetEtale T).obj F) ≫ (lowerStar AddCommGrpCat.{u + 1} v).map
        ((moduleAbelianUpperStarIso P.Coefficient v).hom.app F) = _ at hu
    rw [← hu, Category.assoc, ← Functor.map_comp]
    simp only [σ, Iso.hom_inv_id_app]
    change (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).unit.app
      ((moduleAbelianForget P.Coefficient T).obj F) ≫
      (lowerStar AddCommGrpCat.{u + 1} v).map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  apply (cancel_epi ((forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).map
    ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient) terminalIsTerminal).hom.app F))).2
  have hs := σ.hom.naturality (PreservesTerminal.iso v.Etale).inv.op
  have hx := congrArg (fun f ↦ f.hom.app (op (⊤_ T.Etale))) hunit
  change (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).map
      ((lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} P.Coefficient) v).hom.app
        ((upperStar (ModuleCat.{u + 1} P.Coefficient) v).obj F)) ≫
      ((sheafSections T'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (⊤_ T'.Etale))).map σ =
    ((lowerStar AddCommGrpCat.{u + 1} v).map σ).hom.app (op (⊤_ T.Etale)) ≫
      (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} v).hom.app
        ((upperStar AddCommGrpCat.{u + 1} v).obj ((P.forgetEtale T).obj F)) at hs
  erw [hs]
  change _ ≫ _ = _ at hx
  rw [← Category.assoc]
  exact congrArg (fun f ↦ f ≫
    (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} v).hom.app
      ((upperStar AddCommGrpCat.{u + 1} v).obj ((P.forgetEtale T).obj F))) hx

end WeilConjectures.PurityFiniteSetting

namespace CategoryTheory.Functor

section Pullback
variable {B B' C : Type*} [Category* B] [Category* B'] [Category* C]
  [Abelian B] [Abelian B'] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C]
  [EnoughInjectives B] [EnoughInjectives B']
  (F : B ⥤ C) (F' : B' ⥤ C) (L : B ⥤ B')
  [F.Additive] [F'.Additive] [L.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

private noncomputable def pullbackDerived (η : F ⟶ L ⋙ F') :
    F.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus :=
  Functor.rightDerivedDesc _ F.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso _)
    (L.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus)
    (Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus η) DerivedCategory.Plus.Qh ≫
      Functor.whiskerRight
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ F'))).inv
        DerivedCategory.Plus.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L.mapHomotopyCategoryPlus F'.rightDerivedFunctorPlusUnit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.inv F'.rightDerivedFunctorPlus ≫
      (Functor.associator _ _ _).hom)

private lemma pullbackDerived_fac (η : F ⟶ L ⋙ F') (K : HomotopyCategory.Plus B) :
    F.rightDerivedFunctorPlusUnit.app K ≫
        (pullbackDerived F F' L η).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus η).app K) ≫
        F'.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj K) ≫
        F'.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  have h := congr_app (Functor.rightDerived_fac _ F.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso B)
    (L.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus)
(Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus η) DerivedCategory.Plus.Qh ≫
      Functor.whiskerRight
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ F'))).inv
        DerivedCategory.Plus.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L.mapHomotopyCategoryPlus F'.rightDerivedFunctorPlusUnit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.inv F'.rightDerivedFunctorPlus ≫
      (Functor.associator _ _ _).hom)) K
  change _ ≫ (pullbackDerived F F' L η).app _ = _ at h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, Functor.map_id,
    Category.comp_id, Category.id_comp] at h
  erw [Category.id_comp] at h
  exact h

-- Stated by hand: generating it with `@[reassoc]` costs about 15 s.
private lemma pullbackDerived_fac_assoc (η : F ⟶ L ⋙ F') (K : HomotopyCategory.Plus B)
    {Z : DerivedCategory.Plus C}
    (g : F'.rightDerivedFunctorPlus.obj
      (L.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) ⟶ Z) :
    F.rightDerivedFunctorPlusUnit.app K ≫
        (pullbackDerived F F' L η).app (DerivedCategory.Plus.Qh.obj K) ≫ g =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus η).app K) ≫
        F'.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj K) ≫
        F'.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app K) ≫ g := by
  rw [← Category.assoc, pullbackDerived_fac]
  simp only [Category.assoc]

end Pullback

section Transport
variable {B B' D D' : Type*} [Category* B] [Category* B'] [Category* D] [Category* D']
  [Abelian B] [Abelian B'] [Abelian D] [Abelian D']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory D]
  [HasDerivedCategory D']
  (L : B ⥤ B') (S : B ⥤ D) (S' : B' ⥤ D') (L' : D ⥤ D')
  [L.Additive] [S.Additive] [S'.Additive] [L'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits S'] [PreservesFiniteColimits S']
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']

private noncomputable def derivedTransport (σ : L ⋙ S' ≅ S ⋙ L') :
    L.mapDerivedCategoryPlus ⋙ S'.mapDerivedCategoryPlus ≅
      S.mapDerivedCategoryPlus ⋙ L'.mapDerivedCategoryPlus :=
  (mapDerivedCategoryPlusCompIso L S').symm ≪≫
    mapDerivedCategoryPlusNatIso σ ≪≫ mapDerivedCategoryPlusCompIso S L'

set_option maxHeartbeats 1000000 in
-- The calculation unfolds the localization factorizations for four exact functors.
private lemma derivedTransport_fac (σ : L ⋙ S' ≅ S ⋙ L')
    (K : HomotopyCategory.Plus B) :
    S'.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app K) ≫
        (derivedTransport L S S' L' σ).hom.app (DerivedCategory.Plus.Qh.obj K) =
      S'.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ.hom).app K) ≫
        L'.mapDerivedCategoryPlusFactorsh.inv.app (S.mapHomotopyCategoryPlus.obj K) ≫
        L'.mapDerivedCategoryPlus.map (S.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  rw [← cancel_epi (S'.mapDerivedCategoryPlus.map
    (L.mapDerivedCategoryPlusFactorsh.hom.app K)),
    ← cancel_mono (L'.mapDerivedCategoryPlus.map (S.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      L'.mapDerivedCategoryPlusFactorsh.hom.app (S.mapHomotopyCategoryPlus.obj K))]
  simp only [derivedTransport, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  erw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  have h₁ := mapDerivedCategoryPlusCompIso_hom_app_factorsh L S' K
  have h₂ := mapDerivedCategoryPlusCompIso_hom_app_factorsh S L' K
  have h₃ := mapDerivedCategoryPlusNatIso_hom_app_factorsh σ K
  erw [h₂, h₃, ← h₁]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [Category.comp_id]


end Transport

section Compatibility
variable {B B' C D D' E : Type*}
  [Category* B] [Category* B'] [Category* C] [Category* D] [Category* D'] [Category* E]
  [Abelian B] [Abelian B'] [Abelian C] [Abelian D] [Abelian D'] [Abelian E]
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C]
  [HasDerivedCategory D] [HasDerivedCategory D'] [HasDerivedCategory E]
  [EnoughInjectives B] [EnoughInjectives B'] [EnoughInjectives D] [EnoughInjectives D']
  (F : B ⥤ C) (F' : B' ⥤ C) (G : D ⥤ E) (G' : D' ⥤ E)
  (L : B ⥤ B') (S : B ⥤ D) (S' : B' ⥤ D') (L' : D ⥤ D') (U : C ⥤ E)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [L.Additive] [S.Additive] [S'.Additive] [L'.Additive] [U.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits S'] [PreservesFiniteColimits S']
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

omit [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C]
  [HasDerivedCategory D] [HasDerivedCategory D'] [HasDerivedCategory E]
  [EnoughInjectives B] [EnoughInjectives B'] [EnoughInjectives D] [EnoughInjectives D']
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits S'] [PreservesFiniteColimits S']
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits U] [PreservesFiniteColimits U] in
private lemma homotopySquare
    (e : F ⋙ U ≅ S ⋙ G) (e' : F' ⋙ U ≅ S' ⋙ G')
    (σ : L ⋙ S' ≅ S ⋙ L') (η : F ⟶ L ⋙ F') (η' : G ⟶ L' ⋙ G')
    (h : ∀ X, U.map (η.app X) ≫ e'.hom.app (L.obj X) ≫ G'.map (σ.hom.app X) =
      e.hom.app X ≫ η'.app (S.obj X)) (K : HomotopyCategory.Plus B) :
    U.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus η).app K) ≫
        (NatTrans.mapHomotopyCategoryPlus e'.hom).app (L.mapHomotopyCategoryPlus.obj K) ≫
        G'.mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus σ.hom).app K) =
      (NatTrans.mapHomotopyCategoryPlus e.hom).app K ≫
        (NatTrans.mapHomotopyCategoryPlus η').app (S.mapHomotopyCategoryPlus.obj K) := by
  have hn : Functor.whiskerRight η U ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L e'.hom ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight σ.hom G' ≫ (Functor.associator _ _ _).hom =
      e.hom ≫ Functor.whiskerLeft S η' := by
    ext X
    simpa using h X
  have hk := congr_app (congrArg NatTrans.mapHomotopyCategoryPlus hn) K
  have h₁ := NatTrans.mapHomotopyCategoryPlusCompIso_whiskerRight_app η U K
  have h₂ := NatTrans.mapHomotopyCategoryPlusCompIso_whiskerLeft_app L e'.hom K
  have h₃ := NatTrans.mapHomotopyCategoryPlusCompIso_whiskerRight_app σ.hom G' K
  have h₄ := NatTrans.mapHomotopyCategoryPlusCompIso_whiskerLeft_app S η' K
  rw [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app] at h₁ h₂ h₃ h₄
  erw [Category.id_comp, Category.comp_id] at h₁ h₂ h₃ h₄
  simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app,
    NatTrans.mapHomotopyCategoryPlus_associator_hom_app,
    NatTrans.mapHomotopyCategoryPlus_associator_inv_app] at hk
  erw [Category.id_comp, Category.comp_id, Category.id_comp, h₁, h₂, h₃, h₄] at hk
  exact hk

private lemma pullbackDerived_compatibility
    (e : F ⋙ U ≅ S ⋙ G) (e' : F' ⋙ U ≅ S' ⋙ G')
    (σ : L ⋙ S' ≅ S ⋙ L') (η : F ⟶ L ⋙ F') (η' : G ⟶ L' ⋙ G')
    (h : ∀ K : HomotopyCategory.Plus B,
      U.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus η).app K) ≫
          (NatTrans.mapHomotopyCategoryPlus e'.hom).app (L.mapHomotopyCategoryPlus.obj K) ≫
          G'.mapHomotopyCategoryPlus.map
            ((NatTrans.mapHomotopyCategoryPlus σ.hom).app K) =
        (NatTrans.mapHomotopyCategoryPlus e.hom).app K ≫
          (NatTrans.mapHomotopyCategoryPlus η').app (S.mapHomotopyCategoryPlus.obj K))
    (K : DerivedCategory.Plus B) :
    U.mapDerivedCategoryPlus.map ((pullbackDerived F F' L η).app K) ≫
        (rightDerivedFunctorPlusBaseChange e'.hom).app (L.mapDerivedCategoryPlus.obj K) ≫
        G'.rightDerivedFunctorPlus.map ((derivedTransport L S S' L' σ).hom.app K) =
      (rightDerivedFunctorPlusBaseChange e.hom).app K ≫
        (pullbackDerived G G' L' η').app (S.mapDerivedCategoryPlus.obj K) := by
  suffices key :
      Functor.whiskerRight (pullbackDerived F F' L η) U.mapDerivedCategoryPlus ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft L.mapDerivedCategoryPlus
            (rightDerivedFunctorPlusBaseChange e'.hom) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedTransport L S S' L' σ).hom
            G'.rightDerivedFunctorPlus ≫
          (Functor.associator _ _ _).hom =
        rightDerivedFunctorPlusBaseChange e.hom ≫
          Functor.whiskerLeft S.mapDerivedCategoryPlus (pullbackDerived G G' L' η') by
    simpa using congr_app key K
  refine Functor.rightDerived_ext _
    (Functor.whiskerRight F.rightDerivedFunctorPlusUnit U.mapDerivedCategoryPlus ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.Plus.quasiIso B) _ _ _ (NatTrans.ext (funext fun X ↦ ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp, Functor.comp_obj]
  have hbc := (rightDerivedFunctorPlusBaseChange e'.hom).naturality
    (L.mapDerivedCategoryPlusFactorsh.inv.app X)
  have hpb := (pullbackDerived G G' L' η').naturality
    (S.mapDerivedCategoryPlusFactorsh.inv.app X)
  have hu := U.mapDerivedCategoryPlusFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategoryPlus η).app X)
  have hη := G'.rightDerivedFunctorPlusUnit.naturality
    ((NatTrans.mapHomotopyCategoryPlus σ.hom).app X)
  have hσ : S'.mapDerivedCategoryPlusFactorsh.inv.app
        (L.mapHomotopyCategoryPlus.obj X) ≫
        S'.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app X) ≫
        (derivedTransport L S S' L' σ).hom.app (DerivedCategory.Plus.Qh.obj X) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ.hom).app X) ≫
        L'.mapDerivedCategoryPlusFactorsh.inv.app (S.mapHomotopyCategoryPlus.obj X) ≫
        L'.mapDerivedCategoryPlus.map (S.mapDerivedCategoryPlusFactorsh.inv.app X) := by
    erw [derivedTransport_fac]
    simp only [Iso.inv_hom_id_app_assoc]
  simp only [Functor.comp_obj, Functor.comp_map] at hbc hpb hu hη
  rw [← Functor.map_comp_assoc, pullbackDerived_fac]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hbc, rightDerivedFunctorPlusBaseChange_fac_app_assoc]
  erw [rightDerivedFunctorPlusBaseChange_fac_app_assoc, hpb,
    pullbackDerived_fac_assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  erw [hσ]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hu, ← reassoc_of% hη]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  erw [h X]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end Compatibility
end CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
@[instance_reducible]
private noncomputable def abelianSmallDerived :
    HasDerivedCategory.{u + 1} AddCommGrpCat.{u + 1} :=
  HasDerivedCategory.ofIsGrothendieckAbelian _
attribute [local instance] abelianSmallDerived
private theorem derived_square (P : PurityFiniteSetting.{u})
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus.map
      (moduleDerivedCohomologyPullback P.Coefficient v K) ≫
        (P.relativeDerivedGlobalForget T').app
          ((upperStar (ModuleCat.{u + 1} P.Coefficient) v).mapDerivedCategoryPlus.obj K) ≫
        (Sheaf.Γ T'.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
          ((moduleAbelianDerivedUpperStarIso P.Coefficient v).symm.app K).hom =
      (P.relativeDerivedGlobalForget T).app K ≫ abelianDerivedCohomologyPullback v
        ((P.forgetEtale T).mapDerivedCategoryPlus.obj K) := by
  let : HasDerivedCategory.{u + 1} AddCommGrpCat.{u + 1} :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let F := Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
  let F' := Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
  let G := Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}
  let G' := Sheaf.Γ T'.smallEtaleTopology AddCommGrpCat.{u + 1}
  let L := upperStar (ModuleCat.{u + 1} P.Coefficient) v
  let S := P.forgetEtale T
  let S' := P.forgetEtale T'
  let L' := upperStar AddCommGrpCat.{u + 1} v
  let U := forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}
  have hs := Functor.homotopySquare F F' G G' L S S' L' U
    (P.relativeGlobalSectionsForgetIso T) (P.relativeGlobalSectionsForgetIso T')
    (moduleAbelianUpperStarIso P.Coefficient v).symm
    (sectionsPullbackNat (ModuleCat.{u + 1} P.Coefficient) v)
    (sectionsPullbackNat AddCommGrpCat.{u + 1} v) (sectionsPullback_forget P v)
  have hd := Functor.pullbackDerived_compatibility F F' G G' L S S' L' U
    (P.relativeGlobalSectionsForgetIso T) (P.relativeGlobalSectionsForgetIso T')
    (moduleAbelianUpperStarIso P.Coefficient v).symm
    (sectionsPullbackNat (ModuleCat.{u + 1} P.Coefficient) v)
    (sectionsPullbackNat AddCommGrpCat.{u + 1} v) hs K
  have hi : (Functor.derivedTransport L S S' L'
      (moduleAbelianUpperStarIso P.Coefficient v).symm).hom.app K =
      ((moduleAbelianDerivedUpperStarIso P.Coefficient v).symm.app K).hom := by
    simp only [L, S, S', L', forgetEtale, Functor.derivedTransport,
      moduleAbelianDerivedUpperStarIso, Functor.mapDerivedCategoryPlusNatIso,
      Functor.fullyFaithfulCancelRight_hom_app, Functor.fullyFaithfulCancelRight_inv_app,
      Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, Iso.trans_hom,
      NatTrans.comp_app, Iso.app_hom, Category.assoc]
    rfl
  rw [hi] at hd
  simpa only [Functor.pullbackDerived, sectionsPullbackNat,
    moduleDerivedCohomologyPullback, abelianDerivedCohomologyPullback,
    relativeDerivedGlobalForget] using hd
end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting

private theorem root_value (P : PurityFiniteSetting.{u})
    (T : Over (Spec (.of P.field.k))) (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.exponent) (W : T.left.Etaleᵒᵖ) (b : ℕ) :
    ((Additive.toMul ((kernel.ι (P.exponent • 𝟙 T.left.gmSheaf)).hom.app W
      ((T.left.constantZModIsoRootsOfUnitySheaf P.exponent T.hom hζ).hom.hom.app W
        ((toSheafify T.left.smallEtaleTopology
          ((Functor.const T.left.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod P.exponent))))).app W
              (ULift.up (b : ZMod P.exponent))))).down : Γ(W.unop.left, ⊤)ˣ) :
        Γ(W.unop.left, ⊤)) =
      W.unop.hom.appTop (((Scheme.ΓSpecIso (.of P.field.k)).inv ≫ T.hom.appTop) ζ) ^ b := by
  let hu := (hζ.isUnit (NeZero.ne P.exponent)).map
    (((Scheme.ΓSpecIso (.of P.field.k)).inv ≫ T.hom.appTop).hom)
  have hp : hu.unit ^ P.exponent = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_pow, hζ.pow_eq_one,
      map_one, Units.val_one]
  change ((Additive.toMul ((kernel.ι (P.exponent • 𝟙 T.left.gmSheaf)).hom.app W
    ((T.left.constantZModToRootsOfUnitySheaf P.exponent hu.unit hp).hom.app W _)).down :
      Γ(W.unop.left, ⊤)ˣ) : Γ(W.unop.left, ⊤)) = _
  have hk := congrArg (fun f ↦ f.hom.app W
    ((toSheafify T.left.smallEtaleTopology
      ((Functor.const T.left.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod P.exponent))))).app W
          (ULift.up (b : ZMod P.exponent))))
    (kernel.lift_ι (P.exponent • 𝟙 T.left.gmSheaf)
      (T.left.constantZModToGmSheaf P.exponent hu.unit hp)
      (T.left.constantZModToGmSheaf_comp_nsmul P.exponent hu.unit hp))
  change _ = (T.left.constantZModToGmSheaf P.exponent hu.unit hp).hom.app W _ at hk
  erw [hk]
  have ht := congrArg (fun f ↦ f.app W (ULift.up (b : ZMod P.exponent)))
    (T.left.toSheafify_constantZModToGmSheaf P.exponent hu.unit hp)
  change (T.left.constantZModToGmSheaf P.exponent hu.unit hp).hom.app W _ = _ at ht
  erw [ht]
  exact (T.left.zmodToGmPresheaf_app_natCast P.exponent hu.unit hp W b).trans
    (by rw [IsUnit.unit_spec])

private theorem root_canonical (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T T' : Scheme.{u}}
    (v : T' ⟶ T) (a : T ⟶ Spec (.of P.field.k)) :
    (P.relativeRootPullback h v a).hom =
      Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf P.exponent v := by
  apply (cancel_mono (kernel.ι (P.exponent • 𝟙 T'.gmSheaf))).1
  exact ((Scheme.finiteEtaleTwistPullbackData P.Coefficient P.exponent
    (Nat.pos_of_ne_zero (NeZero.ne P.exponent)) (P.exponent_coefficient_eq_zero h)).laws.2.1
      v (P.exponent_isUnit T a)).symm.trans
        (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι P.exponent v).symm

private theorem root_insertion_pullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T T' : Scheme.{u}}
    (v : T' ⟶ T) (a : T ⟶ Spec (.of P.field.k)) :
    (upperStar AddCommGrpCat.{u + 1} v).map
        (ordinaryFiniteRootMap P.Coefficient P.exponent
          (P.exponent_coefficient_eq_zero h) T) ≫
      (moduleAbelianUpperStarComparison P.Coefficient v).app (P.twistEtale h T) ≫
      (P.forgetEtale T').map (P.relativeTwistPullback h v a).hom =
    (P.relativeRootPullback h v a).hom ≫
      ordinaryFiniteRootMap P.Coefficient P.exponent
        (P.exponent_coefficient_eq_zero h) T' := by
  apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right]
  dsimp only [moduleAbelianUpperStarComparison]
  erw [Equiv.apply_symm_apply]
  ext W z
  exact (Scheme.finiteEtaleTwistPullbackData P.Coefficient P.exponent
    (Nat.pos_of_ne_zero (NeZero.ne P.exponent)) (P.exponent_coefficient_eq_zero h)).laws.2.2.1
      v (P.exponent_isUnit T a) (P.exponent_isUnit T' (v ≫ a)) W 1 z

attribute [local implicit_reducible] forgetEtale twistEtale
  Scheme.finiteEtaleTateSheaf Scheme.finiteEtaleTateTwist
attribute [local irreducible] ordinaryFiniteRootMap Sheaf.H.map
private theorem kummer_pullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T T' : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (v : T' ⟶ T) (w : Γ(T, ⊤)ˣ) :
    Sheaf.H.map ((moduleAbelianUpperStarComparison P.Coefficient v).app
        (P.twistEtale h T) ≫ (P.forgetEtale T').map (P.relativeTwistPullback h v a).hom) 1
      (cohomologyMap v ((P.forgetEtale T).obj (P.twistEtale h T)) 1
        (Sheaf.H.map (ordinaryFiniteRootMap P.Coefficient P.exponent
          (P.exponent_coefficient_eq_zero h) T) 1
          (T.kummerδ₀ P.exponent (P.exponent_isUnit T a) (Additive.ofMul w)))) =
      Sheaf.H.map (ordinaryFiniteRootMap P.Coefficient P.exponent
        (P.exponent_coefficient_eq_zero h) T') 1
          (T'.kummerδ₀ P.exponent (P.exponent_isUnit T' (v ≫ a))
            (Additive.ofMul (Units.map v.appTop.hom.toMonoidHom w))) := by
  let φ := ordinaryFiniteRootMap P.Coefficient P.exponent
    (P.exponent_coefficient_eq_zero h) T
  let ψ := (moduleAbelianUpperStarComparison P.Coefficient v).app (P.twistEtale h T) ≫
    (P.forgetEtale T').map (P.relativeTwistPullback h v a).hom
  have hn := cohomologyMap_map v 1 φ
    (T.kummerδ₀ P.exponent (P.exponent_isUnit T a) (Additive.ofMul w))
  refine (congrArg (Sheaf.H.map ψ 1) hn).trans ?_
  let x := cohomologyMap v (T.rootsOfUnitySheaf P.exponent) 1
    (T.kummerδ₀ P.exponent (P.exponent_isUnit T a) (Additive.ofMul w))
  refine (Sheaf.H.map_comp_apply ((upperStar AddCommGrpCat.{u + 1} v).map φ)
    ψ x).symm.trans ?_
  refine (congrArg (fun f ↦ Sheaf.H.map f 1 x)
    (root_insertion_pullback P h v a)).trans ?_
  refine (Sheaf.H.map_comp_apply (P.relativeRootPullback h v a).hom
    (ordinaryFiniteRootMap P.Coefficient P.exponent
      (P.exponent_coefficient_eq_zero h) T') x).trans ?_
  apply congrArg (Sheaf.H.map (ordinaryFiniteRootMap P.Coefficient P.exponent
    (P.exponent_coefficient_eq_zero h) T') 1)
  rw [root_canonical]
  exact Scheme.sheafH_map_cohomologyMap_kummerδ₀ v P.exponent
    (P.exponent_isUnit T a) (P.exponent_isUnit T' (v ≫ a)) w


private theorem root_natural (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.exponent)
    (T T' : Over (Spec (.of P.field.k))) (v : T' ⟶ T) :
    (upperStar AddCommGrpCat.{u + 1} v.left).map
        (T.left.constantZModIsoRootsOfUnitySheaf P.exponent T.hom hζ).hom ≫
        (P.relativeRootPullback h v.left T.hom).hom =
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} v.left).app
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod P.exponent)))).hom ≫
        (T'.left.constantZModIsoRootsOfUnitySheaf P.exponent T'.hom hζ).hom := by
  rw [root_canonical]
  simp only [Scheme.constantZModIsoRootsOfUnitySheaf, asIso_hom]
  rw [Scheme.upperStar_map_constantZModToRootsOfUnitySheaf_comp]
  congr 2
  apply Units.ext
  change v.left.appTop _ = _
  rw [IsUnit.unit_spec, IsUnit.unit_spec]
  change (((Scheme.ΓSpecIso (.of P.field.k)).inv ≫ T.hom.appTop) ≫ v.left.appTop) ζ = _
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, Over.w v]


/-- Finite Kummer coefficients, primitive-root trivializations and normalization of
scalar-forgetting maps on cohomology and actual derived exchange.
Source: latest blueprint prop-pur-gm-relative-kummer.proof.md, opening and Step 3;
Stacks 03PL, 03FD, 072W and 0D6J
(blueprint: lem-pur-relative-kummer-coefficient-normalization).

Proof:
1. Apply finiteKummerLevel. Transport its additive basis through ULift, identify
scalar multiplication using integer casts, and compute cardinalities of finite
function spaces. The exponent is invertible on every k-scheme.
2. Use the canonical constantZModIsoRootsOfUnitySheaf. Its kernel inclusion sends
constant b to zeta^b. Cancel that inclusion to identify the normalized root
pullback with the canonical one; its naturality proves the root square.
3. The universal property of scalar extension and sheafification identifies maps
out of the Tate line with maps out of the constant A-sheaf. Evaluation at 1
constructs the equivalence and its inverse. Its generator formula gives the
normalized trivialization. Adjunction, the root square, and the normalized twist
pullback generator law prove its naturality.
4. Use the proved ordinary Kummer boundary naturality theorem in
Sites.KummerNaturality. The twist generator law identifies the root insertion
under pullback; functoriality of cohomology then gives the scalar-extended formula.
5. The canonical constant sheafification comparison extends identity on constants.
6. The fixed derived global comparison is invertible because forgotten module
injectives are Gamma-acyclic. Its homology maps are consequently invertible.
7. The forgotten module adjunction unit agrees with the abelian unit after the
coefficient comparison. Evaluate at terminal etale objects to obtain the ordinary
global-sections square. Lift it to homotopy categories and apply rightDerived_ext:
rightDerived_fac and the exact-functor factorization identities reduce the
canonical derived pullback square to that ordinary square.
8. Use the fixed lower-star and exchange comparisons. Exact forgetting reflects
sheaf isomorphisms, and its homology comparison reflects derived isomorphisms.
-/
theorem relativeKummerCoefficientNormalization (P : PurityFiniteSetting.{u}) (h :
    P.ramificationIndex ∣ P.level) : (1 ≤ P.kummerLevel) ∧ ((P.exponent : P.Coefficient) = 0) ∧
    (∃ α : ZMod P.exponent →+* P.Coefficient, ∃ d : ℕ, ∃ b : P.Coefficient ≃+ (Fin d → ZMod
    P.exponent), ∀ (z : ZMod P.exponent) (x : P.Coefficient), b (α z * x) = z • b x) ∧ (∀ T :
    Over (Spec (.of P.field.k)), IsUnit (P.exponent : Γ(T.left, ⊤))) ∧ (∃ d : ℕ, Nat.card
    P.Coefficient = P.coefficients.l ^ d) ∧ (∀ (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ
    P.exponent), ∃ τ : ∀ T : Over (Spec (.of P.field.k)), P.constantEtale T.left ≅ P.twistEtale
    h T.left, (∀ (T : Over (Spec (.of P.field.k))) (W : T.left.Etaleᵒᵖ) (b : ℕ),
    ((Additive.toMul ((kernel.ι (P.exponent • 𝟙 T.left.gmSheaf)).hom.app W
    ((T.left.constantZModIsoRootsOfUnitySheaf P.exponent T.hom hζ).hom.hom.app W ((toSheafify
    T.left.smallEtaleTopology ((Functor.const T.left.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u +
    1} (ZMod P.exponent))))).app W (ULift.up (b : ZMod P.exponent))))).down : Γ(W.unop.left,
    ⊤)ˣ) : Γ(W.unop.left, ⊤)) = W.unop.hom.appTop (((Scheme.ΓSpecIso (.of P.field.k)).inv ≫
    T.hom.appTop) ζ) ^ b) ∧ (∀ (T : Over (Spec (.of P.field.k))) (W : T.left.Etaleᵒᵖ) (a :
    P.Coefficient), (τ T).hom.hom.app W ((toSheafify T.left.smallEtaleTopology ((Functor.const
    T.left.Etaleᵒᵖ).obj (ModuleCat.of P.Coefficient P.Coefficient))).app W a) =
    Scheme.finiteEtaleTateOneGenerator P.Coefficient P.exponent T.left
    (P.exponent_coefficient_eq_zero h) W a ((T.left.constantZModIsoRootsOfUnitySheaf P.exponent
    T.hom hζ).hom.hom.app W ((toSheafify T.left.smallEtaleTopology ((Functor.const
    T.left.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod P.exponent))))).app W (ULift.up
    1)))) ∧ (∀ (T T' : Over (Spec (.of P.field.k))) (v : T' ⟶ T), (upperStar AddCommGrpCat.{u +
    1} v.left).map (T.left.constantZModIsoRootsOfUnitySheaf P.exponent T.hom hζ).hom ≫
    (P.relativeRootPullback h v.left T.hom).hom = ((Scheme.upperStarConstantSheafIso
    AddCommGrpCat.{u + 1} v.left).app (AddCommGrpCat.of (ULift.{u + 1} (ZMod P.exponent)))).hom
    ≫ (T'.left.constantZModIsoRootsOfUnitySheaf P.exponent T'.hom hζ).hom) ∧ (∀ (T T' : Over
    (Spec (.of P.field.k))) (v : T' ⟶ T), (upperStar (ModuleCat.{u + 1} P.Coefficient)
    v.left).map (τ T).hom ≫ (P.relativeTwistPullback h v.left T.hom).hom =
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) v.left).app
    (ModuleCat.of P.Coefficient P.Coefficient)).hom ≫ (τ T').hom)) ∧ (∀ (T T' : Scheme.{u}) (a :
    T ⟶ Spec (.of P.field.k)) (v : T' ⟶ T) (w : Γ(T, ⊤)ˣ), Sheaf.H.map
    ((moduleAbelianUpperStarComparison P.Coefficient v).app (P.twistEtale h T) ≫ (P.forgetEtale
    T').map (P.relativeTwistPullback h v a).hom) 1 (cohomologyMap v ((P.forgetEtale T).obj
    (P.twistEtale h T)) 1 (Sheaf.H.map (ordinaryFiniteRootMap P.Coefficient P.exponent
    (P.exponent_coefficient_eq_zero h) T) 1 (T.kummerδ₀ P.exponent (P.exponent_isUnit T a)
    (Additive.ofMul w)))) = Sheaf.H.map (ordinaryFiniteRootMap P.Coefficient P.exponent
    (P.exponent_coefficient_eq_zero h) T') 1 (T'.kummerδ₀ P.exponent (P.exponent_isUnit T' (v ≫
    a)) (Additive.ofMul (Units.map v.appTop.hom.toMonoidHom w)))) ∧ (∀ (T : Scheme.{u}) (W :
    T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf P.exponent).obj.obj W), (ordinaryFiniteRootMap
    P.Coefficient P.exponent (P.exponent_coefficient_eq_zero h) T).hom.app W z =
    Scheme.finiteEtaleTateOneGenerator P.Coefficient P.exponent T
    (P.exponent_coefficient_eq_zero h) W 1 z) ∧ (∀ (T : Scheme.{u}) (W : T.Etaleᵒᵖ) (a :
    P.Coefficient), ((constantCommuteCompose T.smallEtaleTopology (forget₂ (ModuleCat.{u + 1}
    P.Coefficient) AddCommGrpCat.{u + 1})).hom.app (ModuleCat.of P.Coefficient
    P.Coefficient)).hom.app W ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
    (ModuleCat.of P.Coefficient P.Coefficient))).app W a) = (toSheafify T.smallEtaleTopology
    ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of P.Coefficient))).app W a) ∧ (∀ T :
    Scheme.{u}, IsIso (P.relativeDerivedGlobalForget T)) ∧ (∀ (T : Scheme.{u}) (q : ℤ) (K :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))), IsIso
    (P.relativeGlobalForgetMap T q K)) ∧ (∀ (T T' : Scheme.{u}) (v : T' ⟶ T) (K :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))),
    (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus.map
    (moduleDerivedCohomologyPullback P.Coefficient v K) ≫ (P.relativeDerivedGlobalForget T').app
    ((upperStar (ModuleCat.{u + 1} P.Coefficient) v).mapDerivedCategoryPlus.obj K) ≫ (Sheaf.Γ
    T'.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
    ((moduleAbelianDerivedUpperStarIso P.Coefficient v).symm.app K).hom =
    (P.relativeDerivedGlobalForget T).app K ≫ abelianDerivedCohomologyPullback v ((P.forgetEtale
    T).mapDerivedCategoryPlus.obj K)) ∧ (∀ (X B : Scheme.{u}) (a : X ⟶ B), IsIso
    (moduleAbelianDerivedLowerStarComparison P.Coefficient a)) ∧ (∀ (X X' B B' : Scheme.{u}) (f
    : X ⟶ B) (f' : X' ⟶ B') (g' : X' ⟶ X) (g : B' ⟶ B) (sq : ChosenCartesianSquare g' f' f g) (K
    : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))),
    ((P.forgetEtale B').mapDerivedCategoryPlus.map ((derivedBaseChangeMapPlus (ModuleCat.{u + 1}
    P.Coefficient) sq.toCommSq).app K) ≫ (moduleAbelianDerivedExchangeTargetIso P.Coefficient g'
    f' K).hom = (moduleAbelianDerivedExchangeSourceIso P.Coefficient f g K).hom ≫
    (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app ((P.forgetEtale
    X).mapDerivedCategoryPlus.obj K)) ∧ (IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1}
    P.Coefficient) sq.toCommSq).app K) ↔ IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
    sq.toCommSq).app ((P.forgetEtale X).mapDerivedCategoryPlus.obj K)))) ∧ (∀ (T : Scheme.{u})
    (F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) (b : F ⟶ G), IsIso
    ((P.forgetEtale T).map b) ↔ IsIso b) ∧ (∀ (T : Scheme.{u}) (K L : DerivedCategory.Plus
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) (b : K ⟶ L), IsIso
    ((P.forgetEtale T).mapDerivedCategoryPlus.map b) ↔ IsIso b) := by
  classical
  have hlevel := P.finiteKummerLevel h
  have hb : ∃ α : ZMod P.exponent →+* P.Coefficient, ∃ d : ℕ,
      ∃ b : P.Coefficient ≃+ (Fin d → ZMod P.exponent),
        ∀ z x, b (α z * x) = z • b x := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
      (show P.level ≠ 0 by have := P.level_pos; omega)
    obtain ⟨N, hN, α, f, hf, ⟨b, hb⟩, rest⟩ :=
      hlevel.2.2.2.2.2.2.2.2.2 n hn
    have he : P.exponent = P.coefficients.l ^ (N + 1) := by rw [exponent, hN]
    let b' : P.Ring ≃+ (Fin (P.ramificationIndex * f) → ZMod P.exponent) := by
      change Padic.coefficientExtensionRing P.coefficients.l P.extension P.level ≃+ _
      rw [hn, he]
      exact b
    let α' : ZMod P.exponent →+* P.Coefficient :=
      ZMod.castHom (ringChar.dvd (P.exponent_coefficient_eq_zero h)) _
    refine ⟨α', P.ramificationIndex * f, ULift.ringEquiv.toAddEquiv.trans b', ?_⟩
    intro z x
    obtain ⟨i, rfl⟩ := ZMod.intCast_surjective z
    simp only [map_intCast, ← zsmul_eq_mul, map_zsmul, Int.cast_smul_eq_zsmul]
  have hg (T : Scheme.{u}) : IsIso (P.relativeDerivedGlobalForget T) := by
    let : HasDerivedCategory.{u + 1} AddCommGrpCat.{u + 1} :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    unfold relativeDerivedGlobalForget
    apply Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic.{
      u + 1, u + 2, u + 1, u + 2, u + 1, u + 2, u + 1, u + 2,
          u + 1, u + 1, u + 1, u + 1}
      (G := Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
      (G' := Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (β := P.forgetEtale T)
      (γ := forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})
    intro I hI n
    exact Scheme.isZero_rightDerived_globalSections_forget_of_injective T P.Coefficient I n
  refine ⟨hlevel.1, P.exponent_coefficient_eq_zero h, hb,
    fun T ↦ P.exponent_isUnit T.left T.hom, ?_, ?_, ?_, ?_, ?_, hg, ?_, ?_,
    fun X B a ↦ inferInstance, ?_, ?_, ?_⟩
  · obtain ⟨α, d, b, hb⟩ := hb
    refine ⟨P.kummerLevel * d, ?_⟩
    rw [Nat.card_congr b.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin, exponent,
      pow_mul]
  · intro ζ hζ
    let τ (T : Over (Spec (.of P.field.k))) :=
      Scheme.normalizedLineIso T.left P.exponent P.Coefficient
        (P.exponent_coefficient_eq_zero h)
        (T.left.constantZModIsoRootsOfUnitySheaf P.exponent T.hom hζ)
    refine ⟨τ, ?_, ?_, ?_, ?_⟩
    · exact fun T W b ↦ root_value P T ζ hζ W b
    · exact fun T W a ↦ Scheme.normalizedLineIso_generator T.left P.exponent
        P.Coefficient (P.exponent_coefficient_eq_zero h) _ W a
    · exact fun T T' v ↦ root_natural P h ζ hζ T T' v
    · intro T T' v
      apply Scheme.normalizedLineIso_natural T.left T'.left v.left P.exponent
        P.Coefficient (P.exponent_coefficient_eq_zero h) _ _
        (P.relativeRootPullback h v.left T.hom).hom
        (P.relativeTwistPullback h v.left T.hom).hom
      · exact root_natural P h ζ hζ T T' v
      · exact (Scheme.finiteEtaleTwistPullbackData P.Coefficient P.exponent
          (Nat.pos_of_ne_zero (NeZero.ne P.exponent))
          (P.exponent_coefficient_eq_zero h)).laws.2.2.1 v.left
            (P.exponent_isUnit T.left T.hom)
            (P.exponent_isUnit T'.left (v.left ≫ T.hom))
  · intro T T' a v w
    exact kummer_pullback P h a v w
  · intro T W z
    unfold ordinaryFiniteRootMap
    rfl
  · intro T W a
    have hh : Functor.whiskerRight
        (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of P.Coefficient P.Coefficient)))
        (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}) ≫
        ((constantCommuteCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})).hom.app
            (ModuleCat.of P.Coefficient P.Coefficient)).hom =
        toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (AddCommGrpCat.of P.Coefficient)) := by
      rw [constantCommuteCompose_hom_app_hom, ← Category.assoc,
        sheafComposeIso_inv_fac, ← toSheafify_naturality]
      rfl
    exact ConcreteCategory.congr_hom (congr_app hh W) a
  · intro T q K
    have := hg T
    unfold relativeGlobalForgetMap
    infer_instance
  · intro T T' v K
    exact derived_square P v K
  · intro X X' B B' f f' g' g sq K
    exact (exchange_forget_coefficients P.Coefficient sq K).2.2.2.2.2.2.2.2
  · intro T F G b
    change IsIso ((moduleAbelianForget P.Coefficient T).map b) ↔ IsIso b
    constructor
    · intro h
      exact isIso_of_reflects_iso b (moduleAbelianForget P.Coefficient T)
    · intro h
      infer_instance
  · intro T K L b
    constructor
    · intro h
      apply (DerivedCategory.Plus.isIso_iff b).mpr
      intro i
      have h' := Functor.map_isIso
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) i)
        ((P.forgetEtale T).mapDerivedCategoryPlus.map b)
      have : IsIso ((P.forgetEtale T).map
          ((DerivedCategory.Plus.homologyFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) i).map b)) :=
        (NatIso.isIso_map_iff ((P.forgetEtale T).mapDerivedCategoryPlusHomologyFunctorIso i)
          b).2 h'
      change IsIso ((moduleAbelianForget P.Coefficient T).map
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) i).map b)) at this
      exact isIso_of_reflects_iso _ (moduleAbelianForget P.Coefficient T)
    · intro h
      infer_instance

end WeilConjectures.PurityFiniteSetting
