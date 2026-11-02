/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # The proper Čech step for a closed restriction of an injective

Source: the global matching-relations step in the proper boundary calculation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Positive Čech exactness on the proper scheme over a boundary test object.
Only the section complex of the given finite family is involved; no derived direct
image or injective resolution occurs in this statement.
Source: the proper matching-relations part of Step 2 of
`lem-sp-proetale-proper-closed-injective-cohomology`.
(blueprint: lem-sp-proetale-proper-closed-injective-cech).

Proof plan: on the closed fibre choose weakly contractible affine refinements of the
finite intersection diagrams. Lift them by henselization on affine charts of the
proper scheme. Properness lifts a specialization in W to the closure of each point
of the proper scheme. Flatness of pro-étale maps then shows that a lifted family
covering the closed fibre covers the whole proper scheme. Perform the principal-open
and closed-localization refinements simultaneously on the finite matching diagrams,
keeping all face equations. The augmented free-module resolution expresses those
equations as a kernel, and injectivity of the ambient sheaf extends a functional
from that kernel. Consequently a positive cocycle has a primitive compatible with
all faces. The closed evaluation formula identifies this primitive with one in the
displayed Čech complex. Refinement maps give the primitive for the original cover.
An intersection equal to the whole proper scheme is retained as a terminal factor;
its repeated factors have the usual degenerate contraction. Empty families and empty
closed fibres give zero complexes. No assertion that henselization preserves fibre
products is used: the finite matching diagrams are refined before applying Hom. -/
theorem exactAt_proper_closed_injective_cech
    (A : Type u) [CommRing A] [Finite A]
    {B D E : Scheme.{u}} (p : B ⟶ D) (i : E ⟶ D)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i]
    (W : D.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (hspecializes : ∀ x : W.left, ∃ z : ↥(pullback W.hom i.closedComplement),
      Specializes x ((pullback.fst W.hom i.closedComplement) z))
    (I : Sheaf (ProEt.topology B) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) [Injective I] :
    let P := (proEtaleBaseChange p).obj W
    let T : P.left.ProEt := ProEt.mk (𝟙 P.left)
    let F := (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) P.hom).obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (pullback.fst p i).closedComplement).obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (pullback.fst p i).closedComplement).obj I))
    ∀ {n : ℕ} (U : Fin n → Over T),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
        IsAffine (Presheaf.cechNerveObj U y).left.left ∨
          (Presheaf.cechNerveObj U y).left = T) →
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ ProEt.topology P.left T →
      ∀ q : ℕ, ((cechComplexFunctor U).obj ((Over.forget T).op ⋙ F.obj)).ExactAt (q + 1) :=
  by sorry

end AlgebraicGeometry.Scheme
