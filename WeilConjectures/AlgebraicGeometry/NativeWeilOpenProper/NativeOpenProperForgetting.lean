/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Native.NativeModuleConstructibilityComparison
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyFiniteCoefficientRingRealization
public import WeilConjectures.CategoryTheory.KInjectiveExactSquare.KInjectiveExactSquareComparison
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilComparisonStructure
import all WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus
import WeilConjectures.CategoryTheory.Endofunctor.FixedPairDerivedForgetComparison
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafIso
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Native coefficient hearts and normalized open/proper forgetting

Source: blueprint cor-coef-verdier-weil-equivariance, native refinement of Steps 1--2;
WeilSheaf/Category.lean, OpenImmersion.lean and LowerStar.lean; Stacks 03CY, 03EK, 03DJ
and 070I (blueprint: lem-sf-native-weil-open-proper-forgetting).

All derived categories are ordinary derived categories of the actual native hearts.
The comparisons below are assembled from the existing exact-localization and total-derived
comparisons, retaining their units. Constructibility is a condition on cohomology.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Endofunctor
open scoped AlgebraicGeometry.ProEtale CategoryTheory.Obj

namespace AlgebraicGeometry.NativeWeilOpenProper

/-- The native locally finite-span functions are precisely the continuous functions locally
valued in finite subextensions. Source: coefficient realization, Step 1; HRS Example 3.1
(blueprint: lem-sf-native-weil-open-proper-forgetting).
Proof: a finite-dimensional span has a finite basis of algebraic elements; the field they
 generate is a finite extension. Conversely a finite subextension is finite dimensional,
so any subset of it spans a finite-dimensional subspace. The argument is pointwise on
neighbourhoods; empty spaces and the zero span use the base field. -/
theorem coefficient_sections (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (V : T.ProEt) (s : C(V.left, PadicAlgCl l)) :
    s ∈ PadicAlgCl.locallyFiniteFunctions l V.left ↔
      ∀ x : V.left, ∃ N ∈ nhds x, ∃ E : PadicAlgCl.FiniteIntermediateField l,
        ∀ y ∈ N, s y ∈ E.1 := by
  rw [PadicAlgCl.mem_locallyFiniteFunctions_iff]
  constructor
  · intro hs x
    obtain ⟨W, hW, hxW, E, hE, hvalues⟩ :=
      PadicAlgCl.exists_isOpen_mem_finiteIntermediateField hs x
    refine ⟨W, hW.mem_nhds hxW, ⟨E, hE⟩, hvalues⟩
  · intro hs x
    obtain ⟨N, hN, E, hvalues⟩ := hs x
    haveI : FiniteDimensional ℚ_[l] E.1 := E.2
    refine ⟨N, hN, Submodule.finiteDimensional_of_le
      (S₂ := E.1.toSubalgebra.toSubmodule) ?_⟩
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hvalues y hy

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]

variable {k₀ l}
variable [Fact (ringChar k₀ ≠ l)]
variable {X Z Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

/-- The actual proper Frobenius transport comparison, not an independently chosen iso.
Source: LowerStar.lean and native comparison Step 7
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev properComparison (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))] :=
  letI : HasColimitsOfSize.{u + 1, u + 1}
      (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    IsGrothendieckAbelian.hasColimits _
  letI : HasColimitsOfSize.{0, 0}
      (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  letI : HasCoproducts.{0}
      (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    fun J ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  letI : AB5OfSize.{0, 0}
      (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    AB5OfSize_of_univLE.{0, 0, u + 1, u + 1} _
  letI : HasFiniteBiproducts
      (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  letI : AB4OfSize.{0}
      (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    AB4.of_AB5 _
  IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso
    (WeilSheaf.frobeniusPullback k₀ l Z)
    (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l p
      (comp_over p (Spec (CommRingCat.of k₀))))

/-- The native-unit arrow from the common sheaf-level representative.
Source: native comparison Step 8, Stacks 070I
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev properLeftUnit (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]
    (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) :=
  KInjectiveExactSquare.leftUnit
    (ProEtaleWeilSheaf.lowerStar k₀ l p)
    (ProEtale.adicLowerStar l (Scheme.Hom.geometricFiberMap p
      (comp_over p (Spec (CommRingCat.of k₀)))))
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)) rfl
    (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor
    (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctorUnit I

/-- The ordinary-unit arrow from the very same representative.
Source: native comparison Step 8, Stacks 070I
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev properRightUnit (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]
    (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) :=
  KInjectiveExactSquare.rightUnit
    (ProEtale.adicLowerStar l (Scheme.Hom.geometricFiberMap p
      (comp_over p (Spec (CommRingCat.of k₀)))))
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
    (ProEtale.adicLowerStar l (Scheme.Hom.geometricFiberMap p
      (comp_over p (Spec (CommRingCat.of k₀))))).rightDerivedFunctor
    (ProEtale.adicLowerStar l
      (Scheme.Hom.geometricFiberMap p
        (comp_over p (Spec (CommRingCat.of k₀))))).rightDerivedFunctorUnit I

-- Uniqueness of total right derivation supplies the unit equations of each factor.
-- The strict underlying square cancels the homotopy-composition comparisons.
section UnitNormalization

universe w w' v v' uC uD

variable {C : Type uC} [Category.{v} C] [Abelian C]
  {D : Type uD} [Category.{v'} D] [Abelian D]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{w} (IsoAlgebra F)] [HasDerivedCategory.{w'} (IsoAlgebra G)]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions C]

private theorem fixedPair_unit_normalization (I : CochainComplex (IsoAlgebra F) ℤ) :
    KInjectiveExactSquare.leftUnit (IsoAlgebra.mapOfNatIso e) L
      (IsoAlgebra.forget F) (IsoAlgebra.forget G) rfl
      (IsoAlgebra.mapOfNatIso e).rightDerivedFunctor
      (IsoAlgebra.mapOfNatIso e).rightDerivedFunctorUnit I ≫
        (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso F e).hom.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) =
      KInjectiveExactSquare.rightUnit L (IsoAlgebra.forget F) L.rightDerivedFunctor
        L.rightDerivedFunctorUnit I := by
  let P := IsoAlgebra.mapOfNatIso e
  let r := IsoAlgebra.forget F
  let s := IsoAlgebra.forget G
  let K := (HomotopyCategory.quotient (IsoAlgebra F) (.up ℤ)).obj I
  have h₁ : s.mapDerivedCategoryFactorsh.inv.app
        ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
      s.mapDerivedCategory.map (P.rightDerivedFunctorUnit.app K) ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso P s).inv.app
          (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (P ⋙ s)) (.up ℤ)).hom.app K) ≫
          (P ⋙ s).rightDerivedFunctorUnit.app K := by
    apply (cancel_mono ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso P s).hom.app
      (DerivedCategory.Qh.obj K))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    simp [Functor.rightDerivedFunctorCompMapDerivedCategoryIso,
      Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      Functor.rightDerivedFunctorCompMapDerivedCategoryUnit]
  have h₂ : (P ⋙ s).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorNatIso
        (IsoAlgebra.mapOfNatIsoCompForgetIso e)).hom.app (DerivedCategory.Qh.obj K) =
      (r ⋙ L).rightDerivedFunctorUnit.app K := by
    simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
      IsoAlgebra.mapOfNatIsoCompForgetIso, P, r, s]
  have h₃ : (r ⋙ L).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorCompIso r L).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (r ⋙ L)) (.up ℤ)).inv.app K) ≫
        L.rightDerivedFunctorUnit.app ((r.mapHomotopyCategory (.up ℤ)).obj K) ≫
          L.rightDerivedFunctor.map (r.rightDerivedFunctorUnit.app K) := by
    simp [Functor.rightDerivedFunctorCompIso, Functor.rightDerivedFunctorCompUnit]
  have h₄ : r.rightDerivedFunctorUnit.app K ≫
      r.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj K) =
      r.mapDerivedCategoryFactorsh.inv.app K := by
    exact congr_app (Functor.rightDerivedFunctorIsoMapDerivedCategory_hom_fac r) K
  have ha : (KInjectiveExactSquare.sourceIso P L r s rfl).hom.app K = 𝟙 _ := by
    change (𝟙 _) ≫ (𝟙 _) = _
    exact Category.id_comp _
  have hc₁ : (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (P ⋙ s)) (.up ℤ)).hom.app K = 𝟙 _ := rfl
  have hc₃ : (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (r ⋙ L)) (.up ℤ)).inv.app K = 𝟙 _ := rfl
  dsimp only [KInjectiveExactSquare.leftUnit, KInjectiveExactSquare.rightUnit]
  simp only [Category.assoc]
  change DerivedCategory.Qh.map ((KInjectiveExactSquare.sourceIso P L r s rfl).hom.app K) ≫
    s.mapDerivedCategoryFactorsh.inv.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
      s.mapDerivedCategory.map (P.rightDerivedFunctorUnit.app K) ≫
        (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso F e).hom.app
          (DerivedCategory.Qh.obj K) =
    L.rightDerivedFunctorUnit.app ((r.mapHomotopyCategory (.up ℤ)).obj K) ≫
      L.rightDerivedFunctor.map (r.mapDerivedCategoryFactorsh.inv.app K)
  simp only [IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  rw [reassoc_of% h₁, ha, hc₁]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rw [reassoc_of% h₂, reassoc_of% h₃, hc₃, CategoryTheory.Functor.map_id,
    Category.id_comp, ← L.rightDerivedFunctor.map_comp, h₄]

end UnitNormalization

-- Keep the existing characteristic binder for callers, although normalization is formal.
set_option linter.unusedSectionVars false in
/-- The total-derived comparison is induced by the equality of underlying sheaf functors
with their units. This equation makes it the identity after identifying both sides with
Q(p_* UI) by those units; it holds on every complex and in particular on K-injectives.
Source: native comparison Steps 7--8; Stacks 070Y and 070K
(blueprint: lem-sf-native-weil-open-proper-forgetting).
Proof: the lift is mapOfNatIso for the framework comparison. Its composite with forgetting
is literally forget followed by p_*. Use lem-sf-fixed-pair-derived-forget-comparison and
the unique unit-normalized exact-square comparison. Both units are invertible on a native
K-injective because forgetting preserves K-injectives. Their quotient is the identity
under the common representative identifications. Naturality extends the unit equality
along resolutions. This also proves uniqueness from normalization on K-injectives. -/
theorem proper_normalization (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]
    [IsProper p] :
    (∀ I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ,
      properLeftUnit p I ≫ (properComparison (k₀ := k₀) (l := l) p).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) =
          properRightUnit p I) ∧
      (∀ (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) [I.IsKInjective],
        IsIso (properLeftUnit p I) ∧ IsIso (properRightUnit p I)) := by
  let r := IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have : r.PreservesKInjectiveComplexes := inferInstance
  constructor
  · intro I
    exact fixedPair_unit_normalization (WeilSheaf.frobeniusPullback k₀ l Z)
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l p
        (comp_over p (Spec (CommRingCat.of k₀)))) I
  · intro I hI
    have : CochainComplex.IsKInjective ((r.mapHomologicalComplex (.up ℤ)).obj I) :=
      inferInstance
    have hu : IsIso ((ProEtale.adicLowerStar l (Scheme.Hom.geometricFiberMap p
        (comp_over p (Spec (CommRingCat.of k₀))))).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            ((r.mapHomologicalComplex (.up ℤ)).obj I))) := inferInstance
    constructor
    · dsimp only [properLeftUnit, KInjectiveExactSquare.leftUnit]
      infer_instance
    · dsimp only [properRightUnit, KInjectiveExactSquare.rightUnit]
      have : IsIso ((ProEtale.adicLowerStar l (Scheme.Hom.geometricFiberMap p
          (comp_over p (Spec (CommRingCat.of k₀))))).rightDerivedFunctorUnit.app
            ((r.mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) := hu
      infer_instance

omit [Fact (ringChar k₀ ≠ l)] in
/-- Exact open forgetting, descended termwise from the actual native lift.
Source: OpenImmersion.lean, native comparison Step 6
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev openComparison (j : X ⟶ Z) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ⋙
        (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)).mapDerivedCategory ≅
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory ⋙
        (ProEtale.adicOpenImmersionLowerShriek l
          (Scheme.Hom.geometricFiberMap j
            (comp_over j (Spec (CommRingCat.of k₀))))).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (IsoAlgebra.mapOfNatIsoCompForgetIso
        (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso
          l j (comp_over j (Spec (CommRingCat.of k₀))))) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The ordered open/proper comparison c^0, assembled by precomposing the canonical
proper comparison with native open extension and then using exact open forgetting.
Source: native comparison Step 9; LowerShriek.lean
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev comparison (j : X ⟶ Z) (p : Z ⟶ Y) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor ⋙
        (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategory ≅
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory ⋙
        (ProEtale.adicOpenImmersionLowerShriek l
          (Scheme.Hom.geometricFiberMap j
            (comp_over j (Spec (CommRingCat.of k₀))))).mapDerivedCategory ⋙
        (ProEtale.adicLowerStar l
          (Scheme.Hom.geometricFiberMap p
            (comp_over p (Spec (CommRingCat.of k₀))))).rightDerivedFunctor :=
  Functor.isoWhiskerLeft _ (properComparison (k₀ := k₀) (l := l) p) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openComparison (k₀ := k₀) (l := l) j) _ ≪≫
    Functor.associator _ _ _

omit [Fact (ringChar k₀ ≠ l)] in
/-- The ordinary ordered open/proper construction for the chosen compactification.
Source: LowerShriek.lean and native comparison Step 9
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev ordinaryCompactSupport (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    (c : Compactification f) :=
  letI := c.over (k₀ := k₀)
  (ProEtale.adicOpenImmersionLowerShriek l
      (Scheme.Hom.geometricFiberMap c.i
        (comp_over c.i (Spec (CommRingCat.of k₀))))).mapDerivedCategory ⋙
    (ProEtale.adicLowerStar l
      (Scheme.Hom.geometricFiberMap c.g
        (comp_over c.g (Spec (CommRingCat.of k₀))))).rightDerivedFunctor

/-- The canonical comparison c^0 for the actual compactification functor of the native
framework. Source: LowerShriek.lean and native comparison Step 9
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev compactificationComparison (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    (c : Compactification f) :
    ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c ⋙
        (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategory ≅
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory ⋙
        ordinaryCompactSupport (k₀ := k₀) (l := l) f c :=
  letI := c.over (k₀ := k₀)
  Functor.associator _ _ _ ≪≫ comparison (k₀ := k₀) (l := l) c.i c.g

set_option linter.unusedSectionVars false in
end AlgebraicGeometry.NativeWeilOpenProper
