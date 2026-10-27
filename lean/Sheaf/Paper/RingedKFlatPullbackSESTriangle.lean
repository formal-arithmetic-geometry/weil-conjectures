/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatQuotientTensorSES

/-! # Canonical SES triangles under derived ringed pullback

Source: Stacks Project, derived.tex, Tags 0152, 014F, 05SU and 05SC;
sites-modules.tex, Tag 0G6R; sites-cohomology.tex, Section 06YV and Tag 0G7E.
(blueprint: lem-sfb-ringed-kflat-pullback-ses-triangle).

The universal comparison is written on cochain complexes, as in this node's statement.
The existential shift is pinned by compatibility with that comparison; it is not an
arbitrary triangulated shift structure. The SES boundary is Mathlib's signed cone boundary.
-/

@[expose] public section
set_option autoImplicit false

universe uC vC uD vD r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open WeilConjectures.SemilinearSections (Mod)

namespace SheafOfModules

/-- Derived ringed pullback preserves the canonical triangles of short exact sequences
of flat-term K-flat complexes, including the canonical signed boundary.

Source: Stacks Project, Tags 0152, 014F, 05SU, 05SC, 0G6R and 0G7E.
(blueprint: lem-sfb-ringed-kflat-pullback-ses-triangle).

Proof:
1. Termwise pullback T is additive: geometric inverse image is exact and scalar
extension is additive and preserves finite coproducts. It descends to homotopy
categories and carries the cone matrix (d_B,f;0,-d_A) to the corresponding cone
matrix. Its shift comparison identifies the differential -T(d) on both sides.
Thus Q_S T is triangulated (geometric-inverse-image-exact, sheaf-tensor-product,
independent-sheaf-tensor-colimits and abstract-derived-category).
2. Flat-term K-flat resolutions form a resolving class (kflat-resolution), and
ringed-topoi-derived-pullback inverts quasi-isomorphisms between its objects.
The resolving-class left-derived criterion identifies the universal derived pair.
The coherent-shift theorem for right Kan extensions gives the canonical shifts
and compatibility of epsilon on every complex, without a K-flatness restriction.
3. In each degree inverse image preserves the SES. Its quotient stays flat by
ringed-topos-flat-module-pullback. Flat-quotient-tensor-ses applied with S then
preserves that SES under scalar extension. This needs no flatness of S over RI.
4. For the original and pulled-back SES, cone-short-exact-quasi-iso makes the
canonical cone projections q and q' quasi-isomorphisms. The termwise cone
identification h satisfies q' h = Tq and p' h = Tp. Both canonical boundaries
are -Q(p) Q(q) inverse, by abstract-derived-category and the SES triangle.
5. Naturality at p and q, followed by the shift compatibility from step 2,
gives epsilon_A[1] sigma LF(delta) = delta' epsilon_C: cancel Q_S(h) in the
signed cone formulas. Naturality at f and g gives the other two squares.
The comparison is invertible on each of A, B and C by ringed-topoi-derived-pullback.
These three components give the required triangle isomorphism. The derived
functor is exact for these canonical shifts. No inverse of epsilon on the cone,
boundedness of complexes, or flatness of the ringed morphism is used.
-/
theorem ringedKFlatPullbackSESTriangle
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{r}} {S RI : Sheaf JD CommRingCat.{r}}
    (uInv : Sheaf JC (Type r) ⥤ Sheaf JD (Type r))
    (uPush : Sheaf JD (Type r) ⥤ Sheaf JC (Type r))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : Mod JC R ⥤ Mod JD S)
    (hobj : ∀ M : Mod JC R, uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : Mod JC R} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (Mod JC R)] [HasDerivedCategory.{w} (Mod JD S)]
    (LF : DerivedCategory (Mod JC R) ⥤ DerivedCategory (Mod JD S))
    (epsilon : DerivedCategory.Q ⋙ LF ⟶
      uStar.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (Mod JC R) (.up ℤ))) :
    ∃ (_ : LF.CommShift ℤ),
      (∀ P : CochainComplex (Mod JC R) ℤ,
        epsilon.app (P⟦(1 : ℤ)⟧) ≫
            ((uStar.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).commShiftIso
              (1 : ℤ)).hom.app P =
          ((DerivedCategory.Q ⋙ LF).commShiftIso (1 : ℤ)).hom.app P ≫
            (epsilon.app P)⟦(1 : ℤ)⟧') ∧
      LF.IsTriangulated ∧
      ∀ (E : ShortComplex (CochainComplex (Mod JC R) ℤ)) (hE : E.ShortExact),
        E.X₁.IsKFlatIndependentCoefficients →
        (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (E.X₁.X n)) →
        E.X₂.IsKFlatIndependentCoefficients →
        (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (E.X₂.X n)) →
        E.X₃.IsKFlatIndependentCoefficients →
        (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (E.X₃.X n)) →
        ∃ (hT : (E.map (uStar.mapHomologicalComplex (.up ℤ))).ShortExact),
          ∃ (e : LF.mapTriangle.obj (DerivedCategory.triangleOfSES hE) ≅
            DerivedCategory.triangleOfSES hT),
            e.hom.hom₁ = epsilon.app E.X₁ ∧
            e.hom.hom₂ = epsilon.app E.X₂ ∧
            e.hom.hom₃ = epsilon.app E.X₃ ∧
            LF.map (DerivedCategory.triangleOfSESδ hE) ≫
                (LF.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj E.X₁) ≫
                (epsilon.app E.X₁)⟦(1 : ℤ)⟧' =
              epsilon.app E.X₃ ≫ DerivedCategory.triangleOfSESδ hT := by
  sorry

end SheafOfModules
