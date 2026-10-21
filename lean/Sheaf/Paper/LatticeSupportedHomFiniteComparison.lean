module

public import Sheaf.Paper.DerivedNakayamaResolution
public import Sheaf.Paper.FormalClosedSupport
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
import Sheaf.Algebra.Homology.LocallyFreeDerivedScalars
import Sheaf.SixFunctors.IntTensorProjection
import Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.AlgebraicGeometry.ClosedSupportStratumHom

/-! # Finite-coefficient comparison for Hom from an extended lattice

Source: main-20261015, sec-six-functors-basics, uniform constructible Ext proof,
Lattices, Torsion targets and Integral targets
(blueprint: lem-sfb-lattice-supported-hom-finite-comparison).

Scalar extension is along the continuous quotient coefficient morphism; the target
category retains the quotient action. All derived categories are ordinary unbounded ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open DerivedNakayama

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
  {S Z V X : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) (v : S ⟶ Z)
  [IsClosedImmersion i] [IsOpenImmersion j] [IsOpenImmersion v]
  (L : FormalSupportModules (integerRing l E) S)

local notation "R" => integerRing l E
local notation "A" => quotientRing l E n
local notation "φ" Y => coefficientMap (reductionRing l E n) Y
local notation "Ext" Y => Mod.extendScalars (φ Y)
local notation "Res" Y => Mod.comap (φ Y)
local notation "Ln" => (Ext S).obj L
local notation "D" => (ihom L).obj (𝟙_ (FormalSupportModules R S))
local notation "Dn" => (Ext S).obj D
local notation "Q" => (lowerStar R i).obj ((openImmersionLowerShriek R v).obj L)
local notation "Qn" => (lowerStar A i).obj ((openImmersionLowerShriek A v).obj Ln)
local notation "sR" Y => DerivedCategory.singleFunctor (FormalSupportModules R Y) 0
local notation "sA" Y => DerivedCategory.singleFunctor (FormalSupportModules A Y) 0
local notation "TQ" => (Ext X).leftDerivedFunctor.obj ((sR X).obj Q)
local notation "F" => (formalClosedSupport A i j).rightDerivedFunctor ⋙
  (formalSupportPullback A v).mapDerivedCategory ⋙
  (derivedTensor A S).obj ((sA S).obj Dn) ⋙
  (formalClosedSupportSections A S).rightDerivedFunctor

set_option maxHeartbeats 600000 in
-- Elaborate the full natural-isomorphism package without unfolding closed derived structures.
/-- The full comparison package, including evaluation normalization of the reduced dual,
source reduction in D(A_n), derived global Hom, and all three natural abelian-group maps.
Source: main-20261015 uniform constructible Ext proof, Lattices/Torsion/Integral targets
(blueprint: lem-sfb-lattice-supported-hom-finite-comparison).

The evaluation equation is an equation of underlying abelian-sheaf morphisms. The two
adjunction units send x and a functional to their reductions; after the displayed dual
isomorphism, evaluating them is exactly evaluation over R followed by R → A. Thus the
isomorphism cannot be an arbitrary rescaling. The ordinary quotient module is scalar
extension along the quotient, so Ln and Dn mean L/pi^n and its reduced integral dual.
The natural transformations in `groups` have abelian-group morphism components. -/
structure LatticeSupportedHomFiniteComparison where
  finite : Finite (Padic.coefficientExtensionRing l E n)
  torsion : ∃ m : ℕ, ∀ x : Padic.coefficientExtensionRing l E n, (l ^ m) • x = 0
  reduced_lisse : IsLisseCoefficientModule A Ln
  dualReduction : Dn ≅ (ihom Ln).obj (𝟙_ (FormalSupportModules A S))
  evaluation :
    (((Mod.extendRestrictAdjunction (φ S)).unit.app L).hom ⊗ₘ
        (((Mod.extendRestrictAdjunction (φ S)).unit.app D).hom ≫ dualReduction.hom.hom)) ≫
      Mod.tensorObjπ Ln ((ihom Ln).obj (𝟙_ (FormalSupportModules A S))) ≫
        ((ihom.ev Ln).app (𝟙_ (FormalSupportModules A S))).hom =
      Mod.tensorObjπ L D ≫ ((ihom.ev L).app (𝟙_ (FormalSupportModules R S))).hom ≫ φ S
  sourceReduction : TQ ≅ (sA X).obj Qn
  derivedComparison : Nonempty
    ((Res X).mapDerivedCategory ⋙ (derivedHom R X).obj (op ((sR X).obj Q)) ⋙
        (formalClosedSupportSections R X).rightDerivedFunctor ≅ F)
  groups : ∀ q : ℤ,
    ∃ e₁ : shiftFunctor (DerivedCategory (FormalSupportModules A X)) q ⋙
        (Res X).mapDerivedCategory ⋙ preadditiveCoyoneda.obj (op ((sR X).obj Q)) ≅
      shiftFunctor (DerivedCategory (FormalSupportModules A X)) q ⋙
        preadditiveCoyoneda.obj (op TQ),
      (∀ (K : DerivedCategory (FormalSupportModules A X))
        (f : (sR X).obj Q ⟶ (Res X).mapDerivedCategory.obj (K⟦q⟧)),
        (e₁.hom.app K) f =
          ((Mod.derivedExtendMapDerivedCategoryAdjunction (φ X)).homEquiv _ _).symm f) ∧
      ∃ e₂ : shiftFunctor (DerivedCategory (FormalSupportModules A X)) q ⋙
          preadditiveCoyoneda.obj (op TQ) ≅
        shiftFunctor (DerivedCategory (FormalSupportModules A X)) q ⋙
          preadditiveCoyoneda.obj (op ((sA X).obj Qn)),
        (∀ (K : DerivedCategory (FormalSupportModules A X)) (f : TQ ⟶ K⟦q⟧),
          (e₂.hom.app K) f = sourceReduction.inv ≫ f) ∧
        Nonempty (shiftFunctor (DerivedCategory (FormalSupportModules A X)) q ⋙
            preadditiveCoyoneda.obj (op ((sA X).obj Qn)) ≅
          F ⋙ DerivedCategory.homologyFunctor Ab.{u + 1} q)
  termwise : ∃ h : PreservesFiniteLimits (tensorLeft Dn),
    letI := h
    Nonempty ((tensorLeft Dn).mapDerivedCategory ≅ (derivedTensor A S).obj ((sA S).obj Dn))

/-- Hom out of an integral lattice extended by zero is computed with finite coefficients
and the reduced-dual supported complex, naturally in every unbounded target.
Source: main-20261015 uniform constructible Ext proof, Integral targets and Torsion targets
(blueprint: lem-sfb-lattice-supported-hom-finite-comparison).

Proof:
1. The coefficient-extension DVR has finite residue field; the finite-quotient lemma
makes A_n finite. Since |l| = l^(-1) < 1, l lies in (pi), so l^n annihilates A_n.
2. The derived Nakayama exact quotient resolution identifies the continuous quotient
with R/pi^n. On every finite-free chart of L its scalar extension is A_n to the same
finite power. The locally-free-derived-scalars lemma computes reduction on this chart.
3. Reduce coordinate functionals: lambda-bar(x-bar) = lambda(x) mod pi^n. This is
well-defined, independent of the chart, invertible on each chart (including rank zero),
and satisfies exactly `evaluation`.
4. The integral tensor projection formula and cartesian coefficients give the underlying
integral source comparison. The slice scalar-Hom chain adjunction identifies underlying
scalar extension with the relative tensor, keeping the two coefficient categories distinct.
5. Take the scalar adjunct of Q → Res(a_!Ln). Its K-flat representative sends p tensor a
to a times p-bar. The two-term quotient resolution computes its underlying map as the
quotient augmentation. Exactness of i_*u_! and pi^n-torsion-freeness of L make this a
quasi-isomorphism. Exact restriction detects quasi-isomorphisms, proving sourceReduction
in D(A_n), without any flatness assumption on R → A_n.
6. Derived scalar adjunction gives the first additive Hom comparison; precomposition
with sourceReduction.inv gives the second. Their functoriality gives naturality in K.
7. Apply the formal closed-support stratum formula over the admissible finite ring A_n
and substitute the evaluation-compatible reduced dual. Its finite local freeness makes
it K-flat, so ordinary termwise tensor computes derived tensor on every complex. The
same K-injective Hom-complex comparisons give derivedComparison; taking degree-q
cohomology gives the final abelian-group comparison, for every integer q. -/
theorem latticeSupportedHomFiniteComparison
    (hn : 1 ≤ n) (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hpl : p ≠ l)
    [S.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [V.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [i.IsOver (Spec (.of k))] [j.IsOver (Spec (.of k))] [v.IsOver (Spec (.of k))]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hL : IsLisseCoefficientModule R L) :
    Nonempty (LatticeSupportedHomFiniteComparison l E n i j v L) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
