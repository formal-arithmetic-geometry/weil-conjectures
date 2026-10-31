/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived

import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedInjectiveAffineCech
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperClosedInjectiveCech
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAffineAndTerminalCechCriterion
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedEvaluationComparison

/-! # Closed-fibre inputs to the proper/open boundary calculation

Source: the local boundary calculation, Step 2 of
`lem-sp-proetale-proper-open-boundary-test-hypercohomology`.
(blueprint: lem-sp-proetale-proper-closed-injective-cohomology).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Positive cohomology of closed-fibre restrictions of ambient injectives.

Source: the positive-degree compatible-primitives part of Step 2 of
`lem-sp-proetale-proper-open-boundary-test-hypercohomology`.
(blueprint: lem-sp-proetale-proper-closed-injective-cohomology).

Proof: pull back to P over W, which is quasi-compact and separated. Apply the finite
Čech criterion to the class of affine objects of P together with its terminal
object. The affine closed-injective Čech calculation supplies exactness over affine
objects; the proper closed-injective Čech calculation supplies exactness over the
terminal object. Finite affine refinements give the covering-basis hypothesis.
This proves positive derived global-section vanishing on P. The exact localization
comparison identifies it with derived evaluation on the original site of B.
Finally, the coefficient-realization equivalence and exact evaluation at W compare
that fixed-scalar calculation with the displayed intrinsic higher direct image.
The two geometric Čech calculations retain the inherited matching-relations work;
the refinement, criterion, and coefficient-comparison helpers are proved separately. -/
theorem isZero_proper_closed_injective_higherDirectImage
    (A : Type u) [CommRing A] [Finite A]
    {B D E : Scheme.{u}} (p : B ⟶ D) (i : E ⟶ D)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i]
    [HasInjectiveResolutions (proEtaleRingModules B (proEtaleConstantRing B A))]
    (W : D.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (hspecializes : ∀ x : W.left, ∃ z : ↥(pullback W.hom i.closedComplement),
      Specializes x ((pullback.fst W.hom i.closedComplement) z)) :
    ∀ (I : Sheaf (ProEt.topology B)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) [Injective I] (n : ℕ),
      IsZero ((SheafOfModules.evaluation
        ((sheafCompose (ProEt.topology D)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing D A)) (op W)).obj
        (((proEtaleConstantModuleDirectImage p A).rightDerived (n + 1)).obj
          ((sfIntrinsicModuleEquivalence B A).functor.obj
            ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
              (pullback.fst p i).closedComplement).obj
              ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
                (pullback.fst p i).closedComplement).obj I))))) := by
  intro I hI n
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let P : B.ProEt := (proEtaleBaseChange p).obj W
  let T : P.left.ProEt := ProEt.mk (𝟙 P.left)
  let F : Sheaf (ProEt.topology B) C :=
    (ProEtale.lowerStar C (pullback.fst p i).closedComplement).obj
      ((ProEtale.upperStar C (pullback.fst p i).closedComplement).obj I)
  have : CompactSpace ((𝟭 Scheme).obj W.left) := inferInstanceAs (CompactSpace W.left)
  have : ((𝟭 Scheme).obj W.left).IsSeparated := inferInstanceAs W.left.IsSeparated
  have hcompact : CompactSpace P.left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst W.hom p)
  have hsep : P.left.IsSeparated := by
    constructor
    change IsSeparated (terminal.from (pullback W.hom p))
    rw [← terminal.comp_from (pullback.fst W.hom p)]
    infer_instance
  have : IsIso T.hom := inferInstanceAs (IsIso (𝟙 P.left))
  have : CompactSpace T.left := hcompact
  have : T.left.IsSeparated := hsep
  have hlocal : IsZero (((ProEtale.globalSectionsFunctor C P.left).rightDerived
      (n + 1)).obj ((ProEtale.upperStar C P.hom).obj F)) := by
    exact ProEt.isZero_sections_of_affine_and_terminal_cech (ULift.{u + 1, u} A) T
      ((ProEtale.upperStar C P.hom).obj F)
      (exactAt_closed_injective_affine_cech A (pullback.fst p i) P I)
      (exactAt_proper_closed_injective_cech A p i W hW hspecializes I) n
  have hfixed : IsZero (((ProEtale.sectionsFunctor C P).rightDerived (n + 1)).obj F) :=
    ProEtale.isZero_rightDerived_sectionsFunctor_of_upperStar C P F (n + 1) hlocal
  exact isZero_intrinsic_directImage_evaluation_of_fixed A p W hW F (n + 1) hfixed

end AlgebraicGeometry.Scheme
