/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.AdicFibreComparisonCoherence
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Mathlib.Algebra.Category.ModuleCat.Descent
import Sheaf.Paper.ContinuousCoefficientRealizations
import Sheaf.Paper.LisseCompletedSystemComparison
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Sheaf.Paper.CommonStageCalculus
import Sheaf.Paper.PbcCommonStageCones
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.Paper.StratifiedLatticeRank
import Sheaf.Paper.LisseTensorScalarExtension

/-! # Normalized fibre comparisons, common stages and rank loci

Source: Bhatt--Scholze, Propositions 6.8.4 and 6.8.14, Definitions 6.8.3 and 6.8.6,
and Remark 6.8.15 (blueprint: lem-per-adic-normalized-fibre-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)

variable (E L : Type u) [Field E] [Field L] [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]

/-- The quotient tower of the finite integral scalar extension, indexed by positive powers.
Source: BS 6.8.4(1); Stacks 09B8 (blueprint: lem-per-adic-normalized-fibre-comparisons). -/
def scalarQuotients (i : E →ₐ[ℚ_[l]] L)
    (M : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) :
    ℕᵒᵖ ⥤ ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L) :=
  let D := Padic.coefficientExtensionIntegers l L
  let I := Padic.coefficientExtensionIdeal l L 1
  let V := (ModuleCat.extendScalars.{u, u, u + 1}
    (WeilConjectures.integralScalarIntegerInclusion l E L i)).obj M
  Functor.ofOpSequence
    (X := fun n : ℕ ↦ ModuleCat.of D (V ⧸ (I ^ (n + 1) • ⊤ : Submodule D V)))
    (fun n ↦ ModuleCat.ofHom (Submodule.factorPow I V (Nat.le_succ (n + 1))))

/-- The scalar-limit comparison is the map whose every component is reduction modulo
that target uniformizer power. It is constructed before its invertibility is asserted.
Source: BS 6.8.4(1) (blueprint: lem-per-adic-normalized-fibre-comparisons). -/
def scalarCompletionMap (i : E →ₐ[ℚ_[l]] L)
    (M : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) :
    (ModuleCat.extendScalars.{u, u, u + 1}
      (WeilConjectures.integralScalarIntegerInclusion l E L i)).obj M ⟶
      limit (scalarQuotients l E L i M) :=
  let D := Padic.coefficientExtensionIntegers l L
  let I := Padic.coefficientExtensionIdeal l L 1
  let V := (ModuleCat.extendScalars.{u, u, u + 1}
    (WeilConjectures.integralScalarIntegerInclusion l E L i)).obj M
  limit.lift (scalarQuotients l E L i M)
    { pt := V
      π := NatTrans.ofOpSequence
        (fun n ↦ ModuleCat.ofHom (I ^ (n + 1) • ⊤ : Submodule D V).mkQ)
        (fun n ↦ by
          simp only [Functor.const_obj_map,
            scalarQuotients, Functor.ofOpSequence_map_homOfLE_succ]
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro m
          rfl) }

/-- H⁰ of a specified derived degree-zero model, with the single/H⁰ unit removed.
Source: BS 6.8.14 (blueprint: lem-per-adic-normalized-fibre-comparisons). -/
def modelH0 {T : Scheme.{u}} {A : Type u} [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A]
    {K : DerivedCategory (pbcModules T (rationalCoefficientSheaf l T A))}
    {M : pbcModules T (rationalCoefficientSheaf l T A)}
    (e : K ≅ (DerivedCategory.singleFunctor _ 0).obj M) :=
  (DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M

/-- Transport a finite étale unit to the pro-étale site by the canonical comparison mate.
Source: BS 5.1.5, Stacks 03Q1
(blueprint: lem-per-adic-normalized-fibre-comparisons). -/
def finiteUnitMate {U V : Scheme.{u}} (f : V ⟶ U)
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
    (d : F ⟶ (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj G) :=
  (supportSiteProEtaleComparisonAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
    ((supportSiteComparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} f).inv.app F ≫
      (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} V).map
        ((supportSiteEtaleComparisonAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
          |>.symm d))

/-- The target finite quotient scalar sheaf. Using source level n+1 is a cofinal
presentation of the usual ramification-ceiling system: its further source powers
already vanish modulo the target power. No unramifiedness is imposed.
Source: Weil II (1.1.1)d), BS 6.8.4(1)
(blueprint: lem-per-adic-normalized-fibre-comparisons). -/
def finiteScalarLevel (i : E →ₐ[ℚ_[l]] L) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))) (n : ℕ) :=
  letI := smallCoefficientModuleGrothendieck (Padic.coefficientExtensionRing l L (n + 1))
  letI : HasSheafify T.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))) :=
    GrothendieckTopology.hasSheafify_smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))) T
  letI : HasWeakSheafify T.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))) :=
    HasSheafify.isRightAdjoint
  (sheafCompose T.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1}
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1))))).obj
      ((presheafToSheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l L (n + 1)))).obj
          (F.obj ⋙ ModuleCat.extendScalars.{u, u, u + 1}
            ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1))).comp
              (WeilConjectures.integralScalarIntegerInclusion l E L i))))

/-- The finite scalar unit is the actual tensor unit followed by sheafification.
Source: Stacks 008B, 03EL (blueprint: lem-per-adic-normalized-fibre-comparisons). -/
def finiteScalarUnit (i : E →ₐ[ℚ_[l]] L) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))) (n : ℕ) :
    (sheafCompose _ (forget₂ _ AddCommGrpCat.{u + 1})).obj F ⟶
      (sheafCompose _ (forget₂ _ AddCommGrpCat.{u + 1})).obj
        (finiteScalarLevel l E L i T F n) :=
  letI := smallCoefficientModuleGrothendieck (Padic.coefficientExtensionRing l L (n + 1))
  letI : HasSheafify T.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))) :=
    GrothendieckTopology.hasSheafify_smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))) T
  letI : HasWeakSheafify T.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))) :=
    HasSheafify.isRightAdjoint
  ⟨Functor.whiskerLeft F.obj (Functor.whiskerRight
      (ModuleCat.extendRestrictScalarsAdj.{u + 1}
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1))).comp
          (WeilConjectures.integralScalarIntegerInclusion l E L i))).unit
      (forget₂ _ AddCommGrpCat.{u + 1})) ≫
    Functor.whiskerRight (toSheafify T.smallEtaleTopology
      (F.obj ⋙ ModuleCat.extendScalars.{u, u, u + 1}
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1))).comp
          (WeilConjectures.integralScalarIntegerInclusion l E L i))))
      (forget₂ _ AddCommGrpCat.{u + 1})⟩

/-- A pulled lattice identification must agree with the finite pullback units on every
reduction, and its rationalization must send the same integral section to its image.
Thus the rational lattice isomorphism cannot absorb an independent scalar.
Source: BS 6.8.4(1),(4), 6.8.15; Stacks 03Q1
(blueprint: lem-per-adic-normalized-fibre-comparisons). -/
def IsPulledLattice {U V : Scheme.{u}} (f : V ⟶ U)
    (N : NormalizedFibre.Lattice l E U) (M : NormalizedFibre.Lattice l E V)
    (hs : M.system = N.system ⋙ Etale.upperStar
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) f)
    (η : (modulePull f (NormalizedFibre.coefficient l E f)).obj (N.rational l E) ≅
      M.rational l E) : Prop :=
  ∃ δ : (NormalizedFibre.forgetIntegral l E U).obj N.integral ⟶
      (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
        ((NormalizedFibre.forgetIntegral l E V).obj M.integral),
    (∀ n : ℕ, δ ≫ (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map
        (M.reduction.app (op n)) = N.reduction.app (op n) ≫
      finiteUnitMate f _ _
        ((sheafCompose _ (forget₂ _ AddCommGrpCat.{u + 1})).map
          ((supportSiteEtaleComparisonAdjunction
            (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) f).unit.app
              (N.system.obj (op n))) ≫
          (Etale.lowerStar AddCommGrpCat.{u + 1} f).map
            ((sheafCompose _ (forget₂ _ AddCommGrpCat.{u + 1})).map
              ((eqToIso hs).inv.app (op n))))) ∧
    ∀ (W : U.ProEt) (m : N.integral.val.obj (op W)),
      η.hom.val.app (op ((proEtaleBaseChange f).obj W))
        (moduleUnit f (NormalizedFibre.coefficient l E f) (N.rational l E) W
          (pbcTensorSection (integralRationalCoefficientMap l E U) N.integral
            (op W) 1 m)) =
        pbcTensorSection (integralRationalCoefficientMap l E V) M.integral
          (op ((proEtaleBaseChange f).obj W)) 1 (δ.hom.app (op W) m)

/-- The scalar lattice presentation and finite stalk map use the same finite tensor unit.
The reduction-cone equation fixes the integral section map; the rational section equation
fixes its balancing isomorphism. All identifications of the target lattice are therefore
shared by its finite tower and its rational presentation.
Source: BS 6.8.4(1),(4), 6.8.14; Stacks 008B, 03EL
(blueprint: lem-per-adic-normalized-fibre-comparisons). -/
def IsScalarLattice (i : E →ₐ[ℚ_[l]] L) (T : Scheme.{u})
    (N : NormalizedFibre.Lattice l E T) (M : NormalizedFibre.Lattice l L T)
    (r : rationalCoefficientSheaf l T E ⟶ rationalCoefficientSheaf l T L)
    (η : (pbcExtend r).obj (N.rational l E) ≅ M.rational l L)
    (τ : ∀ n : ℕ, finiteScalarLevel l E L i T (N.system.obj (op n)) n ≅
      M.system.obj (op n)) : Prop :=
  ∃ δ : (NormalizedFibre.forgetIntegral l E T).obj N.integral ⟶
      (NormalizedFibre.forgetIntegral l L T).obj M.integral,
    (∀ n : ℕ, δ ≫ M.reduction.app (op n) = N.reduction.app (op n) ≫
      (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} T).map
        (finiteScalarUnit l E L i T (N.system.obj (op n)) n ≫
          (sheafCompose _ (forget₂ _ AddCommGrpCat.{u + 1})).map (τ n).hom)) ∧
    ∀ (W : T.ProEt) (m : N.integral.val.obj (op W)),
      η.hom.val.app (op W)
        (pbcTensorSection r (N.rational l E) (op W) 1
          (pbcTensorSection (integralRationalCoefficientMap l E T) N.integral
            (op W) 1 m)) =
        pbcTensorSection (integralRationalCoefficientMap l L T) M.integral (op W) 1
          (δ.hom.app (op W) m)

/-- The chart pullback comparison is normalized by the actual global derived comparison,
its counit and the two ordinary pullback units. This fixes the chart presentation before
its inverse-limit formula is imposed.
Source: BS 6.8.15 (blueprint: lem-per-adic-normalized-fibre-comparisons). -/
def IsPullChartMap {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme)
    (F : NormalizedFibre.Heart l E (base l X))
    (C : NormalizedFibre.Chart l (base l X)) (D : NormalizedFibre.Chart l (base l Y))
    (f : D.scheme ⟶ C.scheme)
    (q : (D.restrict l E (R.realization E (base l Y))).obj ((heartPull l E R g).obj F) ≅
      (modulePull f (NormalizedFibre.coefficient l E f)).obj
        ((C.restrict l E (R.realization E (base l X))).obj F)) : Prop :=
  ∃ (e : (R.realization E (base l X)).J.obj F.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((NormalizedFibre.realize l E (base l X) (R.realization E (base l X))).obj F))
    (e' : (R.realization E (base l Y)).J.obj ((heartPull l E R g).obj F).obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((modulePull g (R.along E (X := base l Y) (Y := base l X) g).coefficient).obj
          ((NormalizedFibre.realize l E (base l X) (R.realization E (base l X))).obj F))),
    (modelH0 l e).hom = 𝟙 _ ∧ e'.hom = pullModelMap l R E g F _ e ∧
    ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ D.scheme)
      (W : X.scheme.ProEt)
      (a : ProEt.mk (𝟙 (Spec (.of κ))) ⟶ (proEtaleBaseChange t).obj
        ((proEtaleBaseChange D.map).obj ((proEtaleBaseChange g).obj W)))
      (b : ProEt.mk (𝟙 (Spec (.of κ))) ⟶ (proEtaleBaseChange t).obj
        ((proEtaleBaseChange f).obj ((proEtaleBaseChange C.map).obj W)))
      (_hab : a.left ≫ pullback.fst _ t ≫ pullback.fst _ D.map ≫ pullback.fst W.hom g =
        b.left ≫ pullback.fst _ t ≫ pullback.fst _ f ≫ pullback.fst W.hom C.map)
      (m : ((NormalizedFibre.realize l E (base l X)
        (R.realization E (base l X))).obj F).val.obj (op W)),
      (NormalizedFibre.ambient l E κ t).map q.hom
        (germ l E _ κ t _ a
          (moduleUnit D.map (NormalizedFibre.coefficient l E D.map) _ _
            ((modelH0 l e').inv.val.app (op ((proEtaleBaseChange g).obj W))
              (moduleUnit g (R.along E (X := base l Y) (Y := base l X) g).coefficient
                _ W m)))) =
        germ l E _ κ t _ b (moduleUnit f (NormalizedFibre.coefficient l E f) _ _
          (moduleUnit C.map (NormalizedFibre.coefficient l E C.map) _ W m))

/-- Scalar change on a chart uses the actual J/T comparison and derived counit.
Its tensor equation pins the chart comparison on generators of every geometric fibre.
Source: BS 6.8.14 (blueprint: lem-per-adic-normalized-fibre-comparisons). -/
def IsScalarChartMap (i : E →ₐ[ℚ_[l]] L) (X : FiniteTypeBase k)
    (F : NormalizedFibre.Heart l E (base l X)) (C : NormalizedFibre.Chart l (base l X))
    (r : rationalCoefficientSheaf l C.scheme E ⟶ rationalCoefficientSheaf l C.scheme L)
    (q : (C.restrict l L (R.realization L (base l X))).obj ((heartScalar l E L i X).obj F) ≅
      (pbcExtend r).obj ((C.restrict l E (R.realization E (base l X))).obj F)) : Prop :=
  (∀ (W : C.scheme.ProEtᵒᵖ) (s : (rationalCoefficientSheaf l C.scheme E).obj.obj W)
    (x : W.unop.left), rationalCoefficientValue l L C.scheme W (r.hom.app W s) x =
      i (rationalCoefficientValue l E C.scheme W s x)) ∧
  ∃ (e : (R.realization E (base l X)).J.obj F.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((NormalizedFibre.realize l E (base l X) (R.realization E (base l X))).obj F))
    (e' : (R.realization L (base l X)).J.obj ((heartScalar l E L i X).obj F).obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((pbcExtend (R.fieldChange E L i (base l X)).coefficient).obj
          ((NormalizedFibre.realize l E (base l X) (R.realization E (base l X))).obj F))),
    (modelH0 l e).hom = 𝟙 _ ∧ e'.hom = scalarModelMap l R E L i X F _ e ∧
    ∀ (W : X.scheme.ProEt)
      (m : ((NormalizedFibre.realize l E (base l X)
        (R.realization E (base l X))).obj F).val.obj (op W)),
      q.hom.val.app (op ((proEtaleBaseChange C.map).obj W))
        (moduleUnit C.map (NormalizedFibre.coefficient l L C.map) _ W
          ((modelH0 l e').inv.val.app (op W)
            (pbcTensorSection (R.fieldChange E L i (base l X)).coefficient _ (op W) 1 m))) =
        pbcTensorSection r _ (op ((proEtaleBaseChange C.map).obj W)) 1
          (moduleUnit C.map (NormalizedFibre.coefficient l E C.map) _ W m)

/-- The actual pullback comparison is the localized finite stalk-limit comparison,
conjugated by the prescribed adapted-chart normalization maps.
Source: BS 6.8.4 and 6.8.15 (blueprint: lem-per-adic-normalized-fibre-comparisons). -/
def IsPullLimitNormalized (ω : Fibres (k := k) l R) (c : AllComparisons l R ω) : Prop :=
  ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X Y : FiniteTypeBase k) (g : Y.scheme ⟶ X.scheme)
    (F : NormalizedFibre.Heart l A (base l X)) (C : NormalizedFibre.Chart l (base l X))
    (hC : C.Adapted l A (R.realization A (base l X)) F)
    (N : NormalizedFibre.Lattice l A C.scheme)
    (φ : (C.restrict l A (R.realization A (base l X))).obj F ≅ N.rational l A)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme)
    (s : Spec (.of κ) ⟶ C.scheme) (_hs : s ≫ C.map = y ≫ g),
    ∃ (D : NormalizedFibre.Chart l (base l Y)) (f : D.scheme ⟶ C.scheme)
      (t : Spec (.of κ) ⟶ D.scheme)
      (hD : D.Adapted l A (R.realization A (base l Y)) ((heartPull l A R g).obj F))
      (M : NormalizedFibre.Lattice l A D.scheme)
      (ψ : (D.restrict l A (R.realization A (base l Y))).obj
        ((heartPull l A R g).obj F) ≅ M.rational l A)
      (hsystem : M.system = N.system ⋙ Etale.upperStar
        (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l A)) f)
      (q : (D.restrict l A (R.realization A (base l Y))).obj
        ((heartPull l A R g).obj F) ≅
          (modulePull f (NormalizedFibre.coefficient l A f)).obj
            ((C.restrict l A (R.realization A (base l X))).obj F))
      (η : (modulePull f (NormalizedFibre.coefficient l A f)).obj
        (N.rational l A) ≅ M.rational l A)
      (P : PullLimit l A f N M κ t
        (pullTowerIso l A f N M (eqToIso hsystem) κ t)),
      D.map ≫ g = f ≫ C.map ∧ t ≫ D.map = y ∧ t ≫ f = s ∧
      IsPullChartMap l R A g F C D f q ∧ IsPulledLattice l A f N M hsystem η ∧
      ψ.hom = q.hom ≫ (modulePull f (NormalizedFibre.coefficient l A f)).map φ.hom ≫
        η.hom ∧
      HEq (((c A A).pull g κ y).hom.app F)
        (((ω A Y).normalization D ((heartPull l A R g).obj F) hD M ψ κ t).hom ≫
          (ModuleCat.extendScalars.{u, u, u + 1}
            (Padic.coefficientExtensionIntegers l A).subtype).map
            P.iso.hom ≫
          ((ω A X).normalization C F hC N φ κ (t ≫ f)).inv)

/-- The actual scalar comparison is the finite integral completion map followed by
localization and the tensor balancing associator, in normalized chart coordinates.
Source: BS 6.8.4 and 6.8.14 (blueprint: lem-per-adic-normalized-fibre-comparisons). -/
def IsScalarLimitNormalized (ω : Fibres (k := k) l R) (c : AllComparisons l R ω) : Prop :=
  ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X : FiniteTypeBase k)
    (F : NormalizedFibre.Heart l A (base l X)) (C : NormalizedFibre.Chart l (base l X))
    (hA : C.Adapted l A (R.realization A (base l X)) F)
    (N : NormalizedFibre.Lattice l A C.scheme)
    (φ : (C.restrict l A (R.realization A (base l X))).obj F ≅ N.rational l A),
    ∃ (hB : C.Adapted l B (R.realization B (base l X))
      ((heartScalar l A B i X).obj F))
      (M : NormalizedFibre.Lattice l B C.scheme)
      (ψ : (C.restrict l B (R.realization B (base l X))).obj
        ((heartScalar l A B i X).obj F) ≅ M.rational l B)
      (r : rationalCoefficientSheaf l C.scheme A ⟶ rationalCoefficientSheaf l C.scheme B)
      (q : (C.restrict l B (R.realization B (base l X))).obj
        ((heartScalar l A B i X).obj F) ≅
          (pbcExtend r).obj ((C.restrict l A (R.realization A (base l X))).obj F))
      (η : (pbcExtend r).obj (N.rational l A) ≅ M.rational l B)
      (τ : ∀ n : ℕ, finiteScalarLevel l A B i C.scheme (N.system.obj (op n)) n ≅
        M.system.obj (op n)),
      IsScalarChartMap l R A B i X F C r q ∧ IsScalarLattice l A B i C.scheme N M r η τ ∧
      ψ.hom = q.hom ≫ (pbcExtend r).map φ.hom ≫ η.hom ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ C.scheme),
      ∃ (e : scalarQuotients l A B i (N.fiber l A κ t) ≅
        M.system ⋙ (pointSmallEtale t).ulift.{u + 1}.sheafFiber
          (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l B)))
        (a : (ModuleCat.extendScalars.{u, u, u + 1}
          (WeilConjectures.integralScalarIntegerInclusion l A B i)).obj
            (N.fiber l A κ t) ≅ M.fiber l B κ t),
        (∀ (n : ℕ) (w : N.fiber l A κ t) (b : Padic.coefficientExtensionIntegers l B)
          (U : C.scheme.Etale) (x : (pointSmallEtale t).ulift.{u + 1}.fiber.obj U)
          (m : (N.system.obj (op n)).obj.obj (op U)),
          limit.π (N.system ⋙ (pointSmallEtale t).ulift.{u + 1}.sheafFiber
            (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l A))) (op n) w =
              (pointSmallEtale t).ulift.{u + 1}.toPresheafFiber U x
                (N.system.obj (op n)).obj m →
          (e.hom.app (op n))
            ((Padic.coefficientExtensionIdeal l B 1 ^ (n + 1) • ⊤ :
              Submodule (Padic.coefficientExtensionIntegers l B)
                ((ModuleCat.extendScalars.{u, u, u + 1}
                  (WeilConjectures.integralScalarIntegerInclusion l A B i)).obj
                    (N.fiber l A κ t))).mkQ
              (b ⊗ₜ[Padic.coefficientExtensionIntegers l A,
                WeilConjectures.integralScalarIntegerInclusion l A B i] w)) =
            b • (pointSmallEtale t).ulift.{u + 1}.toPresheafFiber U x
              (M.system.obj (op n)).obj
                ((τ n).hom.hom.app (op U)
                  ((finiteScalarUnit l A B i C.scheme (N.system.obj (op n)) n).hom.app
                    (op U) m))) ∧
        a.hom ≫ limMap (J := ℕᵒᵖ)
            (C := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l B)) e.inv =
          scalarCompletionMap l A B i (N.fiber l A κ t) ∧
        ∀ (b : B) (a₀ : A) (n : N.fiber l A κ t),
          ((ω B X).normalization C ((heartScalar l A B i X).obj F) hB M ψ κ t).hom
            ((((c A B).scalar i X κ (t ≫ C.map)).inv.app F)
              (b ⊗ₜ[A, i.toRingHom]
                ((ω A X).normalization C F hA N φ κ t).inv
                  (a₀ ⊗ₜ[Padic.coefficientExtensionIntegers l A,
                    (Padic.coefficientExtensionIntegers l A).subtype] n))) =
            (b * i a₀) •
              ((1 : B) ⊗ₜ[Padic.coefficientExtensionIntegers l B,
                (Padic.coefficientExtensionIntegers l B).subtype]
                (a.hom ((1 : Padic.coefficientExtensionIntegers l B) ⊗ₜ[
                  Padic.coefficientExtensionIntegers l A,
                  WeilConjectures.integralScalarIntegerInclusion l A B i] n)))

/-- Local computations of the actual comparison components through the dependency's
normalization maps. A source chart and its presentation are arbitrary. The target chart
is an affine refinement of its pullback through the given geometric lift; its system is
literally the pulled system. Scalar extension uses the positive quotient tower of the
finite integral tensor product, followed by the actual reduction-cone map and localization.
Source: BS 6.8.4(1),(4),(6), 6.8.14--6.8.15; Stacks 03Q1, 09B8
(blueprint: lem-per-adic-normalized-fibre-comparisons). -/
structure LocalLimits (ω : Fibres (k := k) l R) (c : AllComparisons l R ω) : Prop where
  pull : IsPullLimitNormalized l R ω c
  scalar : IsScalarLimitNormalized l R ω c

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- All normalized fibre comparisons, common-stage descent, detection and rank assertions.
Source: Bhatt--Scholze, Propositions 6.8.4 and 6.8.14, Definitions 6.8.3 and 6.8.6,
Remark 6.8.15; Stacks 03Q1, 09B8, 031D, 00MA
(blueprint: lem-per-adic-normalized-fibre-comparisons).

Proof plan:
1. Use the recorded continuous rational realizations and normalized finite-stage fibres.
An adapted affine etale lattice chart computes the fibre as E tensor_A the inverse limit
of its finite-free normalized etale stalks. A fractional integral map acts by the same
inverse uniformizer power times its inverse-limit map.
2. Finite etale pullback-stalk comparisons send a pulled section germ to the original germ.
They are linear and natural, hence commute with quotient transitions. Take their inverse
limit, characterized by every projection, then invert the uniformizer. The realization
comparison and its derived counit identify this with actual completed rational pullback.
The germ equation is precisely this calculation on generators. Pull a lattice chart to
the inverse-image stratum and replace it by an affine open neighbourhood of the chosen
lift; no nonemptiness or flatness is assumed away from that point.
3. For scalar extension A to D, the minimal source exponent at target level m is ceil(m/e).
The larger cofinal source exponent m used in finiteScalarLevel gives the identical target
quotient: t^ceil(m/e) is already zero modulo v^m, so the further source transition becomes
an isomorphism after tensoring. The tensor unit gives the same germ at either source level.
The finite scalar stalk map sends a tensor of a scalar and a germ to the germ of that tensor.
Finite-free reconstruction identifies its stalk tower with the quotients of D tensor_A M.
That finite free D-module is complete, so its actual reduction cone is limiting. Invert
both uniformizers. The two rational modules are both L tensor_A M; balancing gives beta.
The scalar germ equation characterizes its inverse and keeps the actual derived counit.
Use the finite-unit reduction-cone equation to identify the integral lattice map. Its
rationalization sends the same integral sections to their images; the presentation
therefore is exactly the composite of the J/T chart map, scalar phi and this rational map.
The pull presentation is pinned in the same way using the pulled system and its units.
4. Both routes in each identity, composition and mixed square have the same germ or
pure-tensor formula. Limit projections are jointly monic and localization preserves these
equalities. Thus these equations use the recorded raw associators. Naturality for integral
maps extends to fractional maps by division by the same uniformizer power. Equal fractions
have difference killed by a power, hence zero rational fibre map. Every presentation is
quantified in UnitNormalization; common refinements therefore eliminate chart, lattice,
stratification and denominator choices.
5. On a pair (A,F), extend its finite fibre to the algebraic closure. On a common-stage
arrow use beta, apply the fibre of its finite representative, and use inverse beta at the
other endpoint. The scalar composition equation makes this independent of enlarging the
stage. Common-stage heart truncations represent all heart objects by finite-stage hearts.
6. Kernels and cokernels of finite heart arrows are computed from their cone cohomology,
and common-stage cones and truncations preserve these computations. A finite diagram and
its vanishing obstructions descend after one enlargement. Finite fibres and field scalar
extension are exact, hence so are the descended fibres. Field scalar extension faithfully
reflects zero objects and zero maps by the basis description. Apply finite fibre detection
to kernels, cokernels and homology to obtain all common-stage detection assertions.
7. Tensor the finite pull comparison with the algebraic closure. The mixed equation makes
it independent of coefficient enlargement; the descent equation identifies it with the
actual common-stage pullback and retains naturality for every common-stage arrow.
8. The continuous realization has a finite lisse stratification. The clopen rank theorem on
each noetherian stratum gives locally constant ranks with finite image. Lattice reconstruction
identifies the normalized geometric fibre with E to that local rank. Thus the rank does
not depend on the geometric lift, and choosing bases gives an unspecified vector-space
isomorphism for two lifts of the same point. Refine by the finitely many rank loci; positive
rank is exactly a nonzero finite-dimensional fibre and gives constructible support. A basis
stays a basis under field extension. This proves scalar invariance and all common-stage
rank assertions. Empty schemes, empty strata, and the zero module are included throughout. -/
theorem normalizedFibreComparisons :
    ∃ (ω : Fibres (k := k) l R) (c : AllComparisons l R ω)
      (V : CommonAssertions l R Ω ω),
      Nonempty (Coherence l R ω c) ∧ Nonempty (UnitNormalization l R ω c) ∧
        Nonempty (Descent l R Ω ω c V) ∧ Nonempty (LocalLimits l R ω c) := by
  sorry

end AlgebraicGeometry.Scheme.AdicFibreComparison
