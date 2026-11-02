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
public import WeilConjectures.CategoryTheory.SmoothPurity.ProEtaleClosedCechPresentation

import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedCechClosedExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperClosedCechOpenExact
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.CategoryTheory.Sites.CechComplexFunctorSection
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # The proper Čech step for a closed restriction of an injective

Source: the global matching-relations step in the proper boundary calculation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Over the proper scheme `P = B ×_D W` itself, the closed Čech presentation of a finite
cover with affine Čech intersections is exact.

Source: the proper matching-relations part of Step 2 of
`lem-sp-proetale-proper-closed-injective-cohomology`.

Proof: as in `closedAffineCech_corepresentingShortComplex_exact`. The restrictions to the
closed fibre (`closedCech_closed_restriction_exact`) and to the open complement
(`properClosedCech_open_restriction_exact`) are exact, the inverse images are exact, and
the two restrictions jointly detect zero objects. -/
theorem properClosedCech_corepresentingShortComplex_exact
    (A : Type u) [CommRing A] [Finite A]
    {B D E : Scheme.{u}} (p : B ⟶ D) (i : E ⟶ D)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i]
    (W : D.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (hspecializes : ∀ x : W.left, ∃ z : ↥(pullback W.hom i.closedComplement),
      Specializes x ((pullback.fst W.hom i.closedComplement) z))
    {n : ℕ} (U : Fin n → Over (ProEt.mk (𝟙 ((proEtaleBaseChange p).obj W).left)))
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      IsAffine (Presheaf.cechNerveObj U y).left.left)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      ProEt.topology ((proEtaleBaseChange p).obj W).left
        (ProEt.mk (𝟙 ((proEtaleBaseChange p).obj W).left)))
    (q : ℕ) (T : CochainCorepresentingShortComplex
      (closedCechCoefficientFunctor A (pullback.fst p i) ((proEtaleBaseChange p).obj W)
        (ProEt.mk (𝟙 ((proEtaleBaseChange p).obj W).left)) U) q) :
    T.complex.Exact := by
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let b := pullback.fst p i
  let z := b.closedComplement
  have hz := closedCech_closed_restriction_exact A b _ _ U q T
  have hb := properClosedCech_open_restriction_exact A p i W hW hspecializes U hU hcover q T
  have hpair : IsCompl (Set.range z.base) (Set.range b.base) := by
    change IsCompl (Set.range b.closedComplement) (Set.range b)
    rw [b.range_closedComplement]
    exact isCompl_compl.symm
  apply T.complex.exact_iff_isZero_homology.mpr
  apply ProEtale.isZero_of_isZero_upperStar_of_isCompl z b hpair
  · exact ((T.complex.map (ProEtale.upperStar C z)).exact_iff_isZero_homology.mp hz).of_iso
      (T.complex.mapHomologyIso (ProEtale.upperStar C z)).symm
  · exact ((T.complex.map (ProEtale.upperStar C b)).exact_iff_isZero_homology.mp hb).of_iso
      (T.complex.mapHomologyIso (ProEtale.upperStar C b)).symm

/-- The case of `exactAt_proper_closed_injective_cech` in which all Čech intersections
are affine.

Source: the proper matching-relations part of Step 2 of
`lem-sp-proetale-proper-closed-injective-cohomology`.

Proof: as in `exactAt_closed_injective_affine_cech`, using the corepresenting short
complex of `exists_closedCech_corepresentingShortComplex`, its exactness
`properClosedCech_corepresentingShortComplex_exact`, and injectivity of `I`. -/
theorem exactAt_proper_closed_injective_cech_of_isAffine
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
        IsAffine (Presheaf.cechNerveObj U y).left.left) →
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ ProEt.topology P.left T →
      ∀ q : ℕ, ((cechComplexFunctor U).obj ((Over.forget T).op ⋙ F.obj)).ExactAt (q + 1) := by
  dsimp only
  intro n U hU hcover q
  let H := closedCechCoefficientFunctor A (pullback.fst p i) ((proEtaleBaseChange p).obj W)
    (ProEt.mk (𝟙 ((proEtaleBaseChange p).obj W).left)) U
  obtain ⟨T⟩ := exists_closedCech_corepresentingShortComplex A (pullback.fst p i)
    ((proEtaleBaseChange p).obj W) (ProEt.mk (𝟙 ((proEtaleBaseChange p).obj W).left)) U q
  have hex := properClosedCech_corepresentingShortComplex_exact A p i W hW hspecializes U hU
    hcover q T
  change (H.obj I).ExactAt (q + 1)
  rw [HomologicalComplex.exactAt_iff' (H.obj I) q (q + 1) (q + 2)
    (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  intro c hc
  let f := (T.middle I).symm c
  have hf : T.complex.f ≫ f = 0 := by
    apply (T.first I).injective
    rw [map_zero, T.first_boundary]
    change (H.obj I).d (q + 1) (q + 2) ((T.middle I) ((T.middle I).symm c)) = 0
    rw [AddEquiv.apply_symm_apply]
    exact hc
  refine ⟨T.last I (hex.descToInjective f hf), ?_⟩
  change (H.obj I).d q (q + 1) _ = c
  rw [← T.last_boundary, hex.comp_descToInjective]
  exact (T.middle I).apply_symm_apply c

/-- Positive Čech exactness on the proper scheme over a boundary test object.
Only the section complex of the given finite family is involved; no derived direct
image or injective resolution occurs in this statement.
Source: the proper matching-relations part of Step 2 of
`lem-sp-proetale-proper-closed-injective-cohomology`.
(blueprint: lem-sp-proetale-proper-closed-injective-cech).

Proof: if some Čech intersection is the whole proper scheme, then the member `U (y 0)`
has a section over the terminal object, so the Čech complex of any presheaf is exact in
positive degrees (`cechComplexFunctor_exactAt_succ_of_hom`). Otherwise all Čech
intersections are affine, and `exactAt_proper_closed_injective_cech_of_isAffine` applies:
the Čech cochains of three adjacent degrees are corepresented by a short complex, which is
exact on the closed fibre (`closedCech_closed_restriction_exact`) and on the open
complement (`properClosedCech_open_restriction_exact`), and injectivity of `I` turns its
exactness into Čech exactness. -/
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
      ∀ q : ℕ, ((cechComplexFunctor U).obj ((Over.forget T).op ⋙ F.obj)).ExactAt (q + 1) := by
  dsimp only
  intro n U hU hcover q
  by_cases h : ∃ (k : ℕ) (y : Fin (k + 1) → Fin n),
      (Presheaf.cechNerveObj U y).left = ProEt.mk (𝟙 ((proEtaleBaseChange p).obj W).left)
  · obtain ⟨k, y, hy⟩ := h
    have hs : eqToHom hy.symm ≫ (Presheaf.cechNerveObj U y).hom = 𝟙 _ :=
      (ProEt.isTerminalMkId _).hom_ext _ _
    exact cechComplexFunctor_exactAt_succ_of_hom U Over.mkIdTerminal
      (Over.homMk (eqToHom hy.symm) hs ≫ Pi.π _ 0) _ q
  · simp only [not_exists] at h
    exact exactAt_proper_closed_injective_cech_of_isAffine A p i W hW hspecializes I U
      (fun k y ↦ (hU k y).resolve_right (h k y)) hcover q

end AlgebraicGeometry.Scheme
