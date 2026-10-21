/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.RingedTopoiDerivedPullback
public import Sheaf.Paper.SemilinearDerivedCalculus
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

/-! # Ringed-topos derived pullback with independent site universes

Source: Stacks Project, sites-cohomology.tex, Tag 06YY (lemma-derived-base-change).
(blueprint: lem-weil-pbc-ringed-topoi-derived-pullback).

This generalizes the existing interface to sites small relative to the coefficient
universe, keeping their object and morphism universes independent. The original
specialized declaration is retained by public import.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe uC vC uD vD r w
open CategoryTheory CategoryTheory.Limits
open WeilConjectures.SemilinearSections (Mod)
namespace SheafOfModules

/-- The resolution comparison witnesses of derived ringed pullback, with the explicit
computation formula and its naturality, identity and composition equations.
Source: Stacks Project, Tag 06YY (blueprint: lem-weil-pbc-ringed-topoi-derived-pullback).
This packages the resolution clauses of the existing node, without new assumptions. -/
structure RingedPullbackResolutionComparisons
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{r}} {S : Sheaf JD CommRingCat.{r}}
    [HasDerivedCategory.{w} (Mod JC R)] [HasDerivedCategory.{w} (Mod JD S)]
    (uStar : Mod JC R ⥤ Mod JD S) [uStar.Additive]
    (LF : DerivedCategory (Mod JC R) ⥤ DerivedCategory (Mod JD S))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) where
  comparison : ∀ {A P : CochainComplex (Mod JC R) ℤ} (p : P ⟶ A),
    P.IsKFlatIndependentCoefficients → (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
      QuasiIso p → (LF.obj (DerivedCategory.Q.obj A) ≅
        DerivedCategory.Q.obj ((uStar.mapHomologicalComplex (.up ℤ)).obj P))
  normalization : ∀ {A P : CochainComplex (Mod JC R) ℤ} (p : P ⟶ A)
    (hp : P.IsKFlatIndependentCoefficients) (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n))
    (hq : QuasiIso p),
    (comparison (A := A) (P := P) p hp hf hq).hom =
      inv (LF.map (DerivedCategory.Q.map p)) ≫
        epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  naturality : ∀ {A A' P P' : CochainComplex (Mod JC R) ℤ}
    (p : P ⟶ A) (p' : P' ⟶ A') (a : P ⟶ P') (b : A ⟶ A')
    (hp : P.IsKFlatIndependentCoefficients) (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n))
    (hq : QuasiIso p)
    (hp' : P'.IsKFlatIndependentCoefficients) (hf' : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R)
      (P'.X n))
    (hq' : QuasiIso p'), p ≫ b = a ≫ p' →
    LF.map (DerivedCategory.Q.map b) ≫ (comparison (A := A') (P := P') p' hp' hf' hq').hom =
      (comparison (A := A) (P := P) p hp hf hq).hom ≫
        DerivedCategory.Q.map ((uStar.mapHomologicalComplex (.up ℤ)).map a)
  map_comparison : ∀ {A P P' : CochainComplex (Mod JC R) ℤ}
    (p : P ⟶ A) (p' : P' ⟶ A) (a : P ⟶ P')
    (hp : P.IsKFlatIndependentCoefficients) (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n))
    (hq : QuasiIso p)
    (hp' : P'.IsKFlatIndependentCoefficients) (hf' : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R)
      (P'.X n))
    (hq' : QuasiIso p'), a ≫ p' = p →
    (comparison (A := A) (P := P) p hp hf hq).inv ≫
      (comparison (A := A) (P := P') p' hp' hf' hq').hom =
        DerivedCategory.Q.map ((uStar.mapHomologicalComplex (.up ℤ)).map a)
  identity : ∀ {A P : CochainComplex (Mod JC R) ℤ} (p : P ⟶ A)
    (hp : P.IsKFlatIndependentCoefficients) (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n))
    (hq : QuasiIso p),
    (comparison (A := A) (P := P) p hp hf hq).inv ≫
      (comparison (A := A) (P := P) p hp hf hq).hom =
        𝟙 (DerivedCategory.Q.obj ((uStar.mapHomologicalComplex (.up ℤ)).obj P))
  composition : ∀ {A P P' P'' : CochainComplex (Mod JC R) ℤ}
    (p : P ⟶ A) (p' : P' ⟶ A) (p'' : P'' ⟶ A)
    (hp : P.IsKFlatIndependentCoefficients) (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n))
    (hq : QuasiIso p)
    (hp' : P'.IsKFlatIndependentCoefficients) (hf' : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R)
      (P'.X n))
    (hq' : QuasiIso p')
    (hp'' : P''.IsKFlatIndependentCoefficients) (hf'' : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R)
      (P''.X n))
    (hq'' : QuasiIso p''),
    ((comparison (A := A) (P := P) p hp hf hq).inv ≫
      (comparison (A := A) (P := P') p' hp' hf' hq').hom) ≫
      ((comparison (A := A) (P := P') p' hp' hf' hq').inv ≫
        (comparison (A := A) (P := P'') p'' hp'' hf'' hq'').hom) =
      (comparison (A := A) (P := P) p hp hf hq).inv ≫
        (comparison (A := A) (P := P'') p'' hp'' hf'' hq'').hom

/-- The exact universal derived ringed pullback, its computation on flat-term K-flat
complexes, and natural resolution comparisons with their identity and composition laws.
Source: Stacks Project, Tag 06YY (blueprint: lem-weil-pbc-ringed-topoi-derived-pullback).
Proof: exact algebraic inverse image and extension of scalars preserve quasi-isomorphisms
between flat-term K-flat complexes, by the K-flat ringed pullback lemma. Flat-term K-flat
resolutions give a resolving class, so localization supplies the universal left derived
functor and its computation transformation. This transformation is invertible on that
class. For a resolution p define alpha(p) by the inverse of LF(Q(p)) followed by the
computation transformation. The resolution square and naturality of that transformation
prove naturality of alpha. For two resolutions use alpha(p) inverse followed by alpha(q);
a compatible chain map gives precisely this comparison. Cancellation proves its identity
and composition laws. These constructions require only relative smallness of the sites,
so the site object and morphism universes need not equal the coefficient universe. -/
theorem ringedTopoiDerivedPullbackIndependent
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{r}} {S RI : Sheaf JD CommRingCat.{r}}
    (uInv : Sheaf JC (Type r) ⥤ Sheaf JD (Type r))
    (uPush : Sheaf JD (Type r) ⥤ Sheaf JC (Type r))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : Mod JC R ⥤
      Mod JD S)
    (hobj : ∀ M : Mod JC R, uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : Mod JC R} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (Mod JC R)]
    [HasDerivedCategory.{w} (Mod JD S)] :
    ∃ (LF : DerivedCategory (Mod JC R) ⥤
        DerivedCategory (Mod JD S))
      (epsilon : DerivedCategory.Qh ⋙ LF ⟶
        uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor epsilon
        (HomotopyCategory.quasiIso (Mod JC R) (ComplexShape.up ℤ)) ∧
      (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
      (∀ {P Q : CochainComplex (Mod JC R) ℤ} (s : P ⟶ Q),
        P.IsKFlatIndependentCoefficients → (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
        Q.IsKFlatIndependentCoefficients → (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (Q.X n)) →
      QuasiIso s →
          QuasiIso ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) ∧
      (∀ (P : CochainComplex (Mod JC R) ℤ),
        P.IsKFlatIndependentCoefficients → (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
          IsIso (epsilon.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) ∧
      Nonempty (RingedPullbackResolutionComparisons uStar LF epsilon) := by
  sorry

end SheafOfModules
