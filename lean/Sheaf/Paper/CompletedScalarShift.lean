/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.IntegralScalarExtensionUniverses
import Sheaf.Paper.IntegralScalarExtensionWellDefined
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Completed scalar extension and cochain shifts

Source: the blueprint of the Weil conjectures, `def-weil-finite-coefficient-point`,
final equivalence display (blueprint: lem-weil-point-completed-scalar-shift).
The representative sign calculation uses Stacks Project Tags 011G, 014E and 08TC.
The coordinates below are mapping-cocone coordinates: the first is detected by
`mappingCocone.fst` and the second by `mappingCocone.snd`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 1024

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {L : Type u} [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})

/-- The canonical tensor reindexing at a finite level, followed by scalar restriction.
Both comparisons are the `mapCochainComplexShiftIso` comparisons of the underlying
additive module functors; no tower isomorphism is chosen.
Source: Stacks Tags 011G and 08TC (blueprint: lem-weil-point-completed-scalar-shift). -/
noncomputable def completedScalarShiftLevelIso
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) (n : ℕ) :
    (integralScalarLevel l E L ι Y n).obj (P⟦m⟧) ≅
      ((integralScalarLevel l E L ι Y n).obj P)⟦m⟧ :=
  (integralOperationsRestrict l L Y n).mapIso
      (((integralScalarReduction l E L ι Y n).mapCochainComplexShiftIso m).app P) ≪≫
    ((SheafOfModules.restrictScalars
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l L Y n))).mapCochainComplexShiftIso
            m).app
      ((integralScalarFiniteComplex l E L ι Y n).obj P)

/-- The canonical degreewise product reindexing, fixed at every quotient level.
Source: Stacks Tags 011G and 08TC (blueprint: lem-weil-point-completed-scalar-shift). -/
noncomputable def completedScalarShiftProductIso
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) :
    (∏ᶜ fun n : ℕ ↦ ((integralScalarTowerFunctor l E L ι Y).obj (P⟦m⟧)).obj (op n)) ≅
      (∏ᶜ fun n : ℕ ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))⟦m⟧ :=
  Limits.Pi.mapIso (fun n ↦ completedScalarShiftLevelIso ι Y P m n) ≪≫
    (PreservesProduct.iso (shiftFunctor (CochainComplex (integralTowerModules l L Y) ℤ) m)
      (fun n : ℕ ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))).symm

/-- The two coordinates of the actual Roos shift map. The first inclusion carries
coefficient one, and the second carries `(-1)^m`. These are inclusions in the
mapping *cocone*, rather than in the unshifted mapping cone.
Source: Stacks Tags 011G, 014E and 08TC
(blueprint: lem-weil-point-completed-scalar-shift). -/
def completedScalarShiftConeFormula
    (eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) : Prop :=
  (∀ j : ℤ,
    (CochainComplex.mappingCocone.inl
        (completedScalarRoosEndomorphism l E L ι Y (P⟦m⟧))).v j j (by omega) ≫
        ((Functor.commShiftIso (integralScalarComplexFunctor l E L ι Y)
          (self := eC) m).hom.app P).f j =
      (completedScalarShiftProductIso ι Y P m).hom.f j ≫
        (CochainComplex.mappingCocone.inl
          (completedScalarRoosEndomorphism l E L ι Y P)).v (j + m) (j + m) (by omega) ≫
        (CochainComplex.shiftFunctorObjXIso
          ((integralScalarComplexFunctor l E L ι Y).obj P)
          m j (j + m) rfl).inv) ∧
  (∀ (i j : ℤ) (h : i + 1 = j),
    (CochainComplex.mappingCocone.inr
        (completedScalarRoosEndomorphism l E L ι Y (P⟦m⟧))).1.v i j h ≫
        ((Functor.commShiftIso (integralScalarComplexFunctor l E L ι Y)
          (self := eC) m).hom.app P).f j =
      m.negOnePow • ((completedScalarShiftProductIso ι Y P m).hom.f i ≫
        (CochainComplex.mappingCocone.inr
          (completedScalarRoosEndomorphism l E L ι Y P)).1.v
            (i + m) (j + m) (by omega) ≫
        (CochainComplex.shiftFunctorObjXIso
          ((integralScalarComplexFunctor l E L ι Y).obj P)
          m j (j + m) rfl).inv))

/-- The chain equation, with the standard degreewise tensor identification.
Source: Stacks Tags 011G and 014E (blueprint: lem-weil-point-completed-scalar-shift). -/
def completedScalarShiftChainEquation
    (eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ) : Prop := by
  exact ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ),
    (((completedOrdinaryScalarExtension l E L ι Y).mapCochainComplexShiftIso m).hom.app P) ≫
        ((completedScalarChainComparison l E L ι Y).app P)⟦m⟧' =
      (completedScalarChainComparison l E L ι Y).app (P⟦m⟧) ≫
        (Functor.commShiftIso (integralScalarComplexFunctor l E L ι Y) (self := eC) m).hom.app P

/-- Normalization of ordinary derived shift by the universal counit on good complexes.
Source: Stacks Tags 011G, 06YT and 06YU
(blueprint: lem-weil-point-completed-scalar-shift). -/
def completedScalarShiftOrdinaryNormalization
    (eE : (completedDerivedScalarExtension l E L ι Y).CommShift ℤ) : Prop := by
  exact ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (m : ℤ),
    (Functor.commShiftIso (completedDerivedScalarExtension l E L ι Y) (self := eE) m).hom.app
          (DerivedCategory.Q.obj P.obj) ≫
        (completedScalarCounit l E L ι Y P.obj)⟦m⟧' =
      (completedDerivedScalarExtension l E L ι Y).map
          ((DerivedCategory.Q.commShiftIso m).inv.app P.obj) ≫
        completedScalarCounit l E L ι Y (P.obj⟦m⟧) ≫
        DerivedCategory.Q.map
          (((completedOrdinaryScalarExtension l E L ι Y).mapCochainComplexShiftIso m).hom.app
            P.obj) ≫
        (DerivedCategory.Q.commShiftIso m).hom.app
          ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)

/-- The strict derived shift is the descent of this same chain alpha, with the
retained localization comparison. Shifted representatives remain good.
Source: Stacks Tags 011G, 06YS and 08TC
(blueprint: lem-weil-point-completed-scalar-shift). -/
def completedScalarShiftIntegralNormalization
    (eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ)
    (eL : (integralScalarExtensionOfUniverses l E L ι Y).CommShift ℤ) : Prop := by
  exact ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (m : ℤ),
    ∃ hP : integralOperationsGoodComplex l E Y (P.obj⟦m⟧),
      (Functor.commShiftIso (integralScalarExtensionOfUniverses l E L ι Y) (self := eL) m).hom.app
            (DerivedCategory.Q.obj P.obj) ≫
          ((integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app P)⟦m⟧' =
        (integralScalarExtensionOfUniverses l E L ι Y).map
            ((DerivedCategory.Q.commShiftIso m).inv.app P.obj) ≫
          (integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app
            ⟨P.obj⟦m⟧, hP⟩ ≫
          DerivedCategory.Q.map
            ((Functor.commShiftIso (integralScalarComplexFunctor l E L ι Y)
              (self := eC) m).hom.app P.obj) ≫
          (DerivedCategory.Q.commShiftIso m).hom.app
            ((integralScalarComplexFunctor l E L ι Y).obj P.obj)

/-- The fixed cone formula, chain equation, and normalized descended shift square.
The chain CommShift supplies naturality and the standard zero/successive laws
for exactly the same alpha used in all these clauses.
Source: Stacks Tags 011G, 014E, 06YS, 06YT and 08TC
(blueprint: lem-weil-point-completed-scalar-shift). -/
def completedScalarShiftRepresentativeProperty
    (eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ)
    (eE : (completedDerivedScalarExtension l E L ι Y).CommShift ℤ)
    (eL : (integralScalarExtensionOfUniverses l E L ι Y).CommShift ℤ) : Prop := by
  exact
    (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ),
      completedScalarShiftConeFormula ι Y eC P m) ∧
    completedScalarShiftChainEquation ι Y eC ∧
    completedScalarShiftOrdinaryNormalization ι Y eE ∧
    completedScalarShiftIntegralNormalization ι Y eC eL ∧
    @NatTrans.CommShift _ _ _ _
      (completedDerivedScalarExtension l E L ι Y)
      (integralScalarExtensionOfUniverses l E L ι Y)
      (completedScalarComparison l E L ι Y) ℤ _ _ _ eE eL

/-- The canonical completed scalar comparison commutes with every integer shift,
with its ordinary tensor and strict Roos comparisons normalized on representatives.
In particular this applies to every derived-complete input K and every good
representative of K, independently of its chosen resolution. The strict chain
comparison alpha has coordinates `(x,y) ↦ (x,(-1)^m y)` in the mapping cocone.
Source: the final equivalence display of the Weil blueprint and Stacks Project
Tags 011G, 014E, 06YS, 06YT, 06YU and 08TC
(blueprint: lem-weil-point-completed-scalar-shift).
Proof: choose a flat-term K-flat resolution by lem-pc-kflat-resolution. Shift
preserves flat terms; the signed total-tensor reindexing preserves K-flatness.
The finite tensor and restriction shift maps are mapCochainComplexShiftIso, and
their product is completedScalarShiftProductIso. Quotient transitions commute
with this fixed reindexing. In mapping-cocone coordinates the source differential
is (e dx,-e dy-hx), the target differential is (e dx,-e dy-e hx), where e=(-1)^m.
The diagonal map (1,e) intertwines them and is its own inverse. Diagonal maps of
products show chain-level naturality. For zero shift its components are identities;
for successive shifts they multiply to (1,(-1)^(m+n)), giving the CommShift laws.
The quotient-map comparison has zero second component, so alpha chi_{P[m]} equals
chi_P[m] after the canonical tensor reindexing, as an equality of chain maps.
The equivalence of lem-weil-pbc-site-derived-tensor-descent and the quasi-isomorphism
invariance of lem-weil-integral-scalar-extension-well-defined descend these maps
and their coherences. Normalize ordinary derived shift by completedScalarCounit
and strict derived shift by integralScalarExtensionComparisonOfUniverses and
Q.map(alpha). The canonical-comparison uniqueness of
lem-weil-finite-free-completed-scalar-comparison identifies the descended chain
map with chi. The normalized chain equation then gives NatTrans.CommShift. -/
theorem completedScalarComparison_commutesWithShift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t}) :
    ∃ (eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ)
      (eE : (completedDerivedScalarExtension l E L ι Y).CommShift ℤ)
      (eL : (integralScalarExtensionOfUniverses l E L ι Y).CommShift ℤ),
      completedScalarShiftRepresentativeProperty ι Y eC eE eL := by
  sorry

end WeilConjectures
