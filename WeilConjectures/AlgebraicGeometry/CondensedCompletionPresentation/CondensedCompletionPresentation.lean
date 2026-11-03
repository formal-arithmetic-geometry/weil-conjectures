/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralLimit.CondensedIntegralLimit
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings

/-! # Canonical completeness and coefficient relabelling

Source: current blueprint, integral-criterion-reductions, completeness hypothesis;
Stacks Project, Tags 0941 and 08TC
(blueprint: lem-pe-integral-completion-presentation).
Positive level n is indexed by n-1. All derived categories are unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCompletionPresentation

/-- Existence of a product and a Roos triangle with its specified first arrow.
Source: Stacks 08TC, Steps 3--5
(blueprint: lem-pe-integral-completion-presentation). -/
def RoosPresentation {D : Type v} [Category.{w} D] [HasZeroObject D]
    [HasShift D ℤ] [Preadditive D] [∀ i : ℤ, (shiftFunctor D i).Additive]
    [Pretriangulated D] (K : D) (V : ℕ → D) (t : ∀ n, V (n + 1) ⟶ V n)
    (c : ∀ n, K ⟶ V n) : Prop :=
  ∃ h : HasProduct V, letI := h
    ∃ δ : ∏ᶜ V ⟶ K⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (K := V) t K (Pi.lift (f := V) c) δ

attribute [local irreducible] upperStarFromPoint
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.modulesDerived AdicCompletion.finiteModulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

open CondensedIntegralLimit

/-- Modules over C, the actual inverse limit of the finite ring sheaves.
Source: coefficient identification, Step 1
(blueprint: lem-pe-integral-completion-presentation). -/
abbrev LimitModules := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (limitRing l E X).X

/-- The actual limit projection to positive level n+1.
Source: quotient action, Step 2
(blueprint: lem-pe-integral-completion-presentation). -/
abbrev projection (n : ℕ) : (limitRing l E X).X ⟶ AdicCompletion.finiteRing l E X n :=
  (limit.π (quotientTower l E X) (op n)).hom

/-- Derived extension along the projection, with its finite coefficient action retained.
Source: derived reduction, Step 2
(blueprint: lem-pe-integral-completion-presentation). -/
abbrev limitReduction (n : ℕ) : DerivedCategory (LimitModules l E X) ⥤
    AdicCompletion.FiniteDerived l E X n :=
  (Mod.extendScalars (projection l E X n)).leftDerivedFunctor

/-- Exact restriction from positive level n+1 to C.
Source: common coefficient category, Step 2
(blueprint: lem-pe-integral-completion-presentation). -/
abbrev limitRestrict (n : ℕ) : AdicCompletion.FiniteDerived l E X n ⥤
    DerivedCategory (LimitModules l E X) :=
  (Mod.comap (projection l E X n)).mapDerivedCategory

/-- Composition of restrictions along successive limit projections.
Source: compatibility of the quotient tower, Step 2
(blueprint: lem-pe-integral-completion-presentation). -/
def limitRestrictComp (n : ℕ) :
    AdicCompletion.finiteRestrict l E X n ⋙ limitRestrict l E X (n + 1) ≅
      limitRestrict l E X n :=
  Mod.mapDerivedCategoryComapCompIso (projection l E X (n + 1))
    (AdicCompletion.transition l E X n) (projection l E X n)
    (by
      simpa only [quotientTower, Functor.ofOpSequence_map_homOfLE_succ, Mon.comp_hom',
        projection] using
        congrArg Mon.Hom.hom
          (limit.w (quotientTower l E X) (homOfLE (Nat.le_succ n)).op))

/-- Canonical association of successive derived scalar extensions over C.
Source: K-flat change of rings, Step 2
(blueprint: lem-pe-integral-completion-presentation). -/
def limitReductionComp (n : ℕ) :
    limitReduction l E X (n + 1) ⋙ AdicCompletion.finiteExtend l E X n ≅
      limitReduction l E X n :=
  AdicCompletion.adjunctionAssociation
    (Mod.derivedExtendMapDerivedCategoryAdjunction (projection l E X (n + 1)))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.transition l E X n))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (projection l E X n))
    (limitRestrictComp l E X n)

/-- The quotient transition over C, defined by the tensor unit and canonical association.
Source: quotient transition, Step 2
(blueprint: lem-pe-integral-completion-presentation). -/
def limitStep (K : DerivedCategory (LimitModules l E X)) (n : ℕ) :
    (limitReduction l E X (n + 1)).obj K ⟶
      (AdicCompletion.finiteRestrict l E X n).obj ((limitReduction l E X n).obj K) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.transition l E X n)).unit.app
      ((limitReduction l E X (n + 1)).obj K) ≫
    (AdicCompletion.finiteRestrict l E X n).map ((limitReductionComp l E X n).hom.app K)

end AlgebraicGeometry.ProEtale.CondensedCompletionPresentation
