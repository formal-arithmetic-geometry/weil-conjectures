/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Sheaf.Paper.CompleteResidueCohomologyBounds
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-! # A lifted top residue cell and its complete cone

Source: Stacks Project, proetale.tex, Tags 09C2 and 09C3, final induction paragraph;
derived.tex, Tag 014E (blueprint: lem-sf-complete-top-residue-cell-cone).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

attribute [-instance] integralCoefficientAbLocallyBijective integralCoefficientAbSheafify
  GrothendieckTopology.hasSheafify_of_essentiallySmall

/-- The published locally bijective equivalences at the site's module universe.
Source: Stacks 00W1 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance topCellAbLocallyBijective (Y : Scheme.{u}) :
    (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} Y

/-- The published additive sheafification at the site's module universe.
Source: Stacks 00W1 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance topCellAbSheafify (Y : Scheme.{u}) :
    HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} Y

/-- The literal finite zero-differential sum of the indicated single-term complexes.
Source: Stacks 09C3, split residue model
(blueprint: lem-sf-complete-top-residue-cell-cone). -/
def topCellSplitComplex (C : Type v) [Category.{w} C] [Abelian C]
    (F : ℕ → C) (a b : ℤ) (r : ℤ → ℕ) : CochainComplex C ℤ :=
  ∐ fun q : Set.Icc a b ↦ (HomologicalComplex.single C (.up ℤ) q.val).obj (F (r q.val))

/-- Inclusion in the literal finite split complex, using its finite coproduct.
Source: Stacks 09C3 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
def topCellSplitInclusion (C : Type v) [Category.{w} C] [Abelian C]
    (F : ℕ → C) (a b : ℤ) (r : ℤ → ℕ) (q : Set.Icc a b) :
    (HomologicalComplex.single C (.up ℤ) q.val).obj (F (r q.val)) ⟶
      topCellSplitComplex C F a b r :=
  Sigma.ι (fun j : Set.Icc a b ↦
    (HomologicalComplex.single C (.up ℤ) j.val).obj (F (r j.val))) q

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Mathlib's abelian category at the explicit completed-coefficient sizes.
Source: Stacks 03DA (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance (priority := 3000) topCellSourceAbelian :
    Abelian (scalarReductionSource.{u, u} l E X) :=
  @SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
    (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
    (integralCoefficientAbSheafify.{u, u} X)
    (integralCoefficientAbLocallyBijective.{u, u} X)

/-- Mathlib's abelian category at the explicit residue-coefficient sizes.
Source: Stacks 03DA (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance (priority := 3000) topCellTargetAbelian :
    Abelian (scalarReductionTarget.{u, u} l E X 0) :=
  @SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
    (integralCoefficientSheaf.{u, u} l E X 0)
    (integralCoefficientAbSheafify.{u, u} X)
    (integralCoefficientAbLocallyBijective.{u, u} X)

/-- Standard localization at the explicit completed-coefficient sizes.
Source: Stacks 05RU (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance (priority := 2000) topCellSourceDerived :
    HasDerivedCategory (scalarReductionSource.{u, u} l E X) :=
  scalarReductionSourceDerived.{u, u} l E X

/-- Standard localization at the explicit residue-coefficient sizes.
Source: Stacks 05RU (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance (priority := 2000) topCellTargetDerived :
    HasDerivedCategory (scalarReductionTarget.{u, u} l E X 0) :=
  scalarReductionTargetDerived.{u, u} l E X 0

/-- Exact restriction, at the specified coefficient sizes.
Source: Stacks 03CZ (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance (priority := 3000) topCellRestrictionLimits :
    PreservesFiniteLimits (scalarReductionRestriction.{u, u} l E X 0) :=
  scalarReductionRestrictionLimits.{u, u} l E X 0

/-- Exact restriction, at the specified coefficient sizes.
Source: Stacks 03CZ (blueprint: lem-sf-complete-top-residue-cell-cone). -/
instance (priority := 3000) topCellRestrictionColimits :
    PreservesFiniteColimits (scalarReductionRestriction.{u, u} l E X 0) :=
  scalarReductionRestrictionColimits.{u, u} l E X 0

/-- The actual finite free module over the completed coefficient sheaf.
Source: Stacks 09C3 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
abbrev topCellIntegralFree (r : ℕ) : scalarReductionSource.{u, u} l E X :=
  @SheafOfModules.free X.ProEt inferInstance (ProEt.topology X)
    (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
    (inferInstanceAs (HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}))
    (integralCoefficientAbLocallyBijective.{u, u} X)
    (ULift.{u + 1} (Fin r))

/-- The actual finite free module over the constant residue ring sheaf.
Source: Stacks 09C3 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
abbrev topCellResidueFree (r : ℕ) : scalarReductionTarget.{u, u} l E X 0 :=
  @SheafOfModules.free X.ProEt inferInstance (ProEt.topology X)
    (integralCoefficientSheaf.{u, u} l E X 0)
    (inferInstanceAs (HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}))
    (integralCoefficientAbLocallyBijective.{u, u} X)
    (ULift.{u + 1} (Fin r))

/-- Coefficient reduction on finite free modules, fixed on every standard generator.
The restricted residue module has the same underlying global sections.
Source: Stacks 09C3, quotient of the completed coefficient sheaf
(blueprint: lem-sf-complete-top-residue-cell-cone). -/
def topCellFreeQuotient (r : ℕ) : topCellIntegralFree.{u} l E X r ⟶
    (scalarReductionRestriction.{u, u} l E X 0).obj (topCellResidueFree.{u} l E X r) :=
  (@SheafOfModules.freeHomEquiv X.ProEt inferInstance (ProEt.topology X)
    (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
    (inferInstanceAs (HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}))
    (integralCoefficientAbLocallyBijective.{u, u} X)
    ((scalarReductionRestriction.{u, u} l E X 0).obj (topCellResidueFree.{u} l E X r))
    (ULift.{u + 1} (Fin r))).symm
      (fun i ↦ PresheafOfModules.sectionsMk
        (fun U ↦ (@SheafOfModules.freeSection X.ProEt inferInstance (ProEt.topology X)
          (integralCoefficientSheaf.{u, u} l E X 0)
          (inferInstanceAs (HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}))
          (integralCoefficientAbLocallyBijective.{u, u} X) (ULift.{u + 1} (Fin r)) i).val U)
        (fun _ _ f ↦ PresheafOfModules.sections_property
          (@SheafOfModules.freeSection X.ProEt inferInstance (ProEt.topology X)
            (integralCoefficientSheaf.{u, u} l E X 0)
            (inferInstanceAs (HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}))
            (integralCoefficientAbLocallyBijective.{u, u} X) (ULift.{u + 1} (Fin r)) i) f))

/-- The canonical comparison from the derived reduction of a shifted finite free
module to its residue free module. It is the adjoint of coefficient reduction,
using the normalized scalar-extension adjunction and the exact-restriction comparison.
Source: Stacks 06YY, 09C3 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
def topCellReductionComparison (r : ℕ) (b : ℤ) :
    (scalarReductionDerivedExtension.{u, u} l E X 0).obj
      ((DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
        (topCellIntegralFree.{u} l E X r)) ⟶
    (DerivedCategory.singleFunctor (scalarReductionTarget.{u, u} l E X 0) b).obj
      (topCellResidueFree.{u} l E X r) :=
  ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E X 0).choose.homEquiv _ _).symm
    ((DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).map
        (topCellFreeQuotient.{u} l E X r) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (scalarReductionRestriction.{u, u} l E X 0) (.up ℤ) b).inv.app
            (topCellResidueFree.{u} l E X r)) ≫
      (scalarReductionRestriction.{u, u} l E X 0).mapDerivedCategoryFactors.inv.app
        ((HomologicalComplex.single (scalarReductionTarget.{u, u} l E X 0) (.up ℤ) b).obj
          (topCellResidueFree.{u} l E X r)))

/-- The split residue model over an integer interval, using the existing single-term
and coproduct constructions. Source: Stacks 09C3
(blueprint: lem-sf-complete-top-residue-cell-cone). -/
abbrev topCellResidueSplit (a b : ℤ) (r : ℤ → ℕ) :=
  @topCellSplitComplex (scalarReductionTarget.{u, u} l E X 0) inferInstance
    (topCellTargetAbelian.{u} l E X)
    (topCellResidueFree.{u} l E X) a b r

/-- Inclusion of one summand of the literal split residue complex.
Source: Stacks 09C3 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
def topCellResidueInclusion (a b : ℤ) (r : ℤ → ℕ) (q : Set.Icc a b) :
    (HomologicalComplex.single (scalarReductionTarget.{u, u} l E X 0)
      (.up ℤ) q.val).obj (topCellResidueFree.{u} l E X (r q.val)) ⟶
    topCellResidueSplit.{u} l E X a b r :=
  @topCellSplitInclusion (scalarReductionTarget.{u, u} l E X 0) inferInstance
    (topCellTargetAbelian.{u} l E X) (topCellResidueFree.{u} l E X) a b r q

/-- The reduced cell map after the specified free-generator comparison.
Source: Stacks 09C3 (blueprint: lem-sf-complete-top-residue-cell-cone). -/
def topCellReducedMap (r : ℕ) (b : ℤ)
    (M : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (e : (scalarReductionDerivedExtension.{u, u} l E X 0).obj
      ((DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
        (topCellIntegralFree.{u} l E X r)) ≅
      (DerivedCategory.singleFunctor (scalarReductionTarget.{u, u} l E X 0) b).obj
        (topCellResidueFree.{u} l E X r))
    (f : (DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
      (topCellIntegralFree.{u} l E X r) ⟶ M) :=
  e.inv ≫ (scalarReductionDerivedExtension.{u, u} l E X 0).map f

/-- Lift the prescribed top residue basis, with its complete cone, split residue
cone model, shortened Tor interval and the singleton-interval and rank-zero cases.
A single-term complex in degree b is the conventional P[-b]. The identity mapping
cone on that complex is the identity pair in degrees b-1 and b.

Source: Stacks Project, proetale.tex, Tags 09C2 and 09C3, final induction paragraph;
derived.tex, Tags 014E, 014A and 05QR
(blueprint: lem-sf-complete-top-residue-cell-cone).

Proof:
1. lem-sf-complete-residue-cohomology-bounds gives H^(b+1)(M)=0. The exponent-one
uniformizer triangle from lem-sf-completed-coefficient-free-resolution and
lem-sf-derived-homology-long-exact make H^b(M) to H^b(M_1) epic.
2. lem-weil-pbc-proetale-weakly-contractible-evaluation-exact makes this epic map
surjective on X-sections. Lift the finitely many prescribed basis sections.
The shifted-free Hom bijection of lem-sf-projective-cohomology-split-model gives f.
Naturality of coefficient reduction gives H^b(f_1)=theta_b. The empty tuple covers
rank zero. The normalized adjunction identifies its free source reduction with
k_X^r, giving the comparison e used below.
3. Complete f to a distinguished triangle. The source is complete by
lem-sf-completed-coefficient-free-resolution. Identify the completed ring sheaf
and its quotient projections by det-prop-sfb-qlbar-colimit-x-integral-limit with
the sk-def-pe-derived-completion convention. The cone-closure clause of
det-pe-derived-nakayama-first-reduction makes L quotient-tower complete.
4. lem-pur-derived-change-of-rings reduces this triangle exactly. Free cells are
K-flat (def-pc-kflat-complex). lem-sf-projective-cohomology-split-model splits M_1
with the given theta_q. For any such splitting phi, phi composed with the top
inclusion and f_1 have the same generator images. Injectivity of the shifted-free
Hom bijection proves the asserted equality for every phi.
5. Write the split model as W plus its top cell A. The cone of its top inclusion
is W plus Cone(id_A), by the literal cone formula. The latter has identity
differential between b-1 and b; the identity from degree b to b-1 contracts it.
TR3 and lem-sf-triangle-morphism-iso identify the reduced cone with this model,
and contraction identifies it with W in the derived category.
6. After any restriction W is a finite sum of free shifts, hence K-flat.
Its tensor with any degree-zero module N is the same split complex with terms
N^r_q. Thus it has Tor amplitude [a,b-1] and its cohomology has the stated ranks.
7. If a=b then W is the empty sum and L_1=0. Derived Nakayama gives L=0 and
lem-kun-distinguished-cone-zero makes f an isomorphism. Rank zero and the empty
scheme give zero free cells and the same formulas. -/
theorem complete_top_residue_cell_cone
    [CompactSpace X]
    (_hweak : ∀ (F G : Sheaf (ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 X)))))
    (M : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (_hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E X M)
    (a b : ℤ) (hab : a ≤ b) (r : ℤ → ℕ)
    (theta : ∀ q : Set.Icc a b, topCellResidueFree.{u} l E X (r q.val) ≅
      (DerivedCategory.homologyFunctor (scalarReductionTarget.{u, u} l E X 0) q.val).obj
        ((scalarReductionDerivedExtension.{u, u} l E X 0).obj M))
    (_hTor : ∀ V : X.ProEt,
      HasProEtaleTorAmplitude.{u} V.left (Padic.coefficientExtensionRing l E 1)
        ((proEtaleRingDerivedPullback.{u} V.hom
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E 1))
          (proEtaleConstantRing V.left (Padic.coefficientExtensionRing l E 1))
          (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso.{u}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1)) V.hom)).obj
            ((scalarReductionDerivedExtension.{u, u} l E X 0).obj M)) a b) :
    ∃ (e : (scalarReductionDerivedExtension.{u, u} l E X 0).obj
          ((DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
            (topCellIntegralFree.{u} l E X (r b))) ≅
        (DerivedCategory.singleFunctor (scalarReductionTarget.{u, u} l E X 0) b).obj
          (topCellResidueFree.{u} l E X (r b)))
      (f : (DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
        (topCellIntegralFree.{u} l E X (r b)) ⟶ M)
      (L : DerivedCategory (scalarReductionSource.{u, u} l E X))
      (g : M ⟶ L)
      (delta : L ⟶ ((DerivedCategory.singleFunctor
        (scalarReductionSource.{u, u} l E X) b).obj
          (topCellIntegralFree.{u} l E X (r b)))⟦(1 : ℤ)⟧),
      e.hom = topCellReductionComparison.{u} l E X (r b) b ∧
      Triangle.mk f g delta ∈ distTriang _ ∧
      IsDerivedCompleteUnrestricted.{u, u} l E X L ∧
      (DerivedCategory.homologyFunctor (scalarReductionTarget.{u, u} l E X 0) b).map
          (topCellReducedMap.{u} l E X (r b) b M e f) =
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (scalarReductionTarget.{u, u} l E X 0) b).hom.app
            (topCellResidueFree.{u} l E X (r b)) ≫ (theta ⟨b, hab, le_rfl⟩).hom ∧
      (∀ phi : DerivedCategory.Q.obj (topCellResidueSplit.{u} l E X a b r) ≅
          (scalarReductionDerivedExtension.{u, u} l E X 0).obj M,
        (∀ q : Set.Icc a b,
          (DerivedCategory.homologyFunctor (scalarReductionTarget.{u, u} l E X 0) q.val).map
              (DerivedCategory.Q.map (topCellResidueInclusion.{u} l E X a b r q) ≫ phi.hom) =
            (DerivedCategory.singleFunctorCompHomologyFunctorIso
              (scalarReductionTarget.{u, u} l E X 0) q.val).hom.app
                (topCellResidueFree.{u} l E X (r q.val)) ≫ (theta q).hom) →
        topCellReducedMap.{u} l E X (r b) b M e f =
          DerivedCategory.Q.map
            (topCellResidueInclusion.{u} l E X a b r ⟨b, hab, le_rfl⟩) ≫ phi.hom) ∧
      Nonempty ((scalarReductionDerivedExtension.{u, u} l E X 0).obj L ≅
        DerivedCategory.Q.obj (CochainComplex.mappingCone
          (topCellResidueInclusion.{u} l E X a b r ⟨b, hab, le_rfl⟩))) ∧
      Nonempty (CochainComplex.mappingCone
          (topCellResidueInclusion.{u} l E X a b r ⟨b, hab, le_rfl⟩) ≅
        topCellResidueSplit.{u} l E X a (b - 1) r ⨿
          CochainComplex.mappingCone (𝟙 ((HomologicalComplex.single
            (scalarReductionTarget.{u, u} l E X 0) (.up ℤ) b).obj
              (topCellResidueFree.{u} l E X (r b))))) ∧
      Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone
        (𝟙 ((HomologicalComplex.single (scalarReductionTarget.{u, u} l E X 0)
          (.up ℤ) b).obj (topCellResidueFree.{u} l E X (r b)))))) 0) ∧
      Nonempty ((scalarReductionDerivedExtension.{u, u} l E X 0).obj L ≅
        DerivedCategory.Q.obj (topCellResidueSplit.{u} l E X a (b - 1) r)) ∧
      (∀ q : Set.Icc a (b - 1), Nonempty (topCellResidueFree.{u} l E X (r q.val) ≅
        (DerivedCategory.homologyFunctor (scalarReductionTarget.{u, u} l E X 0) q.val).obj
          ((scalarReductionDerivedExtension.{u, u} l E X 0).obj L))) ∧
      (a < b → ∀ V : X.ProEt,
        HasProEtaleTorAmplitude.{u} V.left (Padic.coefficientExtensionRing l E 1)
          ((proEtaleRingDerivedPullback.{u} V.hom
            (proEtaleConstantRing X (Padic.coefficientExtensionRing l E 1))
            (proEtaleConstantRing V.left (Padic.coefficientExtensionRing l E 1))
            (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso.{u}
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1)) V.hom)).obj
                ((scalarReductionDerivedExtension.{u, u} l E X 0).obj L)) a (b - 1)) ∧
      (a = b → IsZero ((scalarReductionDerivedExtension.{u, u} l E X 0).obj L) ∧
        IsZero L ∧ IsIso f) ∧
      (r b = 0 → IsZero (topCellIntegralFree.{u} l E X (r b))) := by
  sorry

end WeilConjectures
