/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Sheaf.CategoryTheory.StrictTowerArithmeticRestriction
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.CategoryTheory.FiniteFreeScalarCoordinates
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.CategoryTheory.StrictRoosAdditiveComparison
import Sheaf.Algebra.Homology.KFlatRoosRepresentativeInvariance
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Finite free scalar extension and strict quotient completion

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YT and 0941;
the finite-free and arithmetic comparison extracted in the DAG proof.
(blueprint: lem-pur-finite-free-completion-exchange).

The comparison is specified on K-flat representatives by its two product coordinates.
No basis occurs in its specification.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r wR wS a b va vb
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic

namespace CategoryTheory.PrincipalQuotientCompletion

/-- The two coordinates of scalar extension of the actual Roos cone, formed from
its product comparison. This uses only the given functor and canonical cone projections.
Source: Stacks 0941, additive cone comparison in DAG proof step 4
(blueprint: lem-pur-finite-free-completion-exchange). -/
noncomputable def scalarRoosCoordinates
    {A : Type a} [Category.{va} A] [Abelian A] [HasCountableProducts A]
    {B : Type b} [Category.{vb} B] [Abelian B] [HasCountableProducts B]
    (E : A ⥤ B) [E.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (c : (E.mapHomologicalComplex (.up ℤ)).obj (roosP X) ⟶ roosP Y) (p : ℤ) :
    E.obj ((roosF.obj X).X (p + 1)) ⟶ (roosP Y).X p ⊞ (roosP Y).X (p + 1) :=
  biprod.lift
    (E.map ((roosχ X p).hom ≫ biprod.fst) ≫ c.f p)
    (E.map ((roosχ X p).hom ≫ biprod.snd) ≫ c.f (p + 1))

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} {φ : R ⟶ S}
  [HasDerivedCategory.{wR}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]

/-- Termwise application of the recorded ordinary scalar extension.
Source: Stacks 06YT (blueprint: lem-pur-finite-free-completion-exchange). -/
noncomputable abbrev extendedComplex (F : SheafOfModules.DerivedChangeOfRingsCochainModel φ) :=
  F.E.mapHomologicalComplex (.up ℤ)

/-- The source quotient tower of a representative.
Source: Stacks 0941 (blueprint: lem-pur-finite-free-completion-exchange). -/
noncomputable abbrev sourceTower
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) :=
  (quotientTower R t).obj P

/-- The target quotient tower, before arithmetic restriction.
Source: Stacks 0941 (blueprint: lem-pur-finite-free-completion-exchange). -/
noncomputable abbrev targetTower (F : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (P : CochainComplex
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) :=
  (quotientTower S vS).obj ((extendedComplex F).obj P)

/-- The actual Roos comparison data for scalar extension and arithmetic restriction.
Product projections and the two signed cone coordinates specify all maps without a basis.
Source: Stacks 0941 and 0H9K, DAG proof steps 3--6
(blueprint: lem-pur-finite-free-completion-exchange). -/
structure RepresentativeRoosComparison
    {A : Type a} [Category.{va} A] [Abelian A] [HasCountableProducts A]
    {B : Type b} [Category.{vb} B] [Abelian B] [HasCountableProducts B]
    (E : A ⥤ B) [E.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (e : ℕ) where
  /-- The balanced finite-stage isomorphisms, as one strict tower isomorphism. -/
  β : X.asFunctor ⋙ E.mapHomologicalComplex (.up ℤ) ≅ index e ⋙ Y.asFunctor
  /-- The canonical tensor/product comparison after the quotient identifications. -/
  c : (E.mapHomologicalComplex (.up ℤ)).obj (roosP X) ⟶
    roosP ((complexRestriction B e).obj Y)
  /-- Every product projection is prescribed. -/
  product_formula : ∀ n : ℕ,
    c ≫ Pi.π _ n =
      (E.mapHomologicalComplex (.up ℤ)).map
        (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n) ≫ β.hom.app (op n)
  /-- The comparison of actual signed Roos cones. -/
  δ : (E.mapHomologicalComplex (.up ℤ)).obj (roosF.obj X) ≅
    roosF.obj ((complexRestriction B e).obj Y)
  /-- Both coordinates are induced by that same product map. -/
  cone_formula : ∀ p : ℤ,
    δ.hom.f (p + 1) ≫ (roosχ ((complexRestriction B e).obj Y) p).hom =
      scalarRoosCoordinates E X ((complexRestriction B e).obj Y) c p
  /-- The arithmetic comparison before localization. -/
  a : roosF.obj Y ⟶ roosF.obj ((complexRestriction B e).obj Y)
  /-- The arithmetic comparison becomes invertible after localization. -/
  arithmetic_quasiIso : QuasiIso a
  /-- The block sum and selection prescribe both arithmetic coordinates. -/
  arithmetic_formula : ∀ p : ℤ,
    a.f (p + 1) ≫ (roosχ ((complexRestriction B e).obj Y) p).hom =
      (roosχ Y p).hom ≫
        biprod.map ((block e Y.asFunctor).f p) ((selection e Y.asFunctor).f (p + 1))

/-- The prescribed representative formula for the completion exchange.
The quotient maps are degreewise epimorphisms, so their equation pins the balanced
finite-stage formula. The final equation specifies inverse arithmetic restriction
following the canonical tensor/product comparison, using the fixed cochain counits.
Source: Stacks 06YT, 0941 and 0H9K, DAG proof steps 3--6
(blueprint: lem-pur-finite-free-completion-exchange). -/
def RepresentativeComparison
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (e : ℕ) (CR : Model R t) (CS : Model S vS)
    (ε : CR.completion ⋙ F.T ≅ F.T ⋙ CS.completion)
    (P : CochainComplex
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
    :=
  { roos : RepresentativeRoosComparison F.E (sourceTower t P) (targetTower F vS P) e //
    (∀ n : ℕ,
    (extendedComplex F).map (quotientMap R t P n) ≫
        roos.β.hom.app (op n) =
      quotientMap S vS ((extendedComplex F).obj P) (e * (n + 1) - 1)) ∧
    ε.hom.app (DerivedCategory.Q.obj P) ≫
      CS.completion.map (F.ε.app P) ≫ CS.counit.app ((extendedComplex F).obj P) ≫
        DerivedCategory.Q.map roos.a =
      F.T.map (CR.counit.app P) ≫ F.ε.app (roosF.obj (sourceTower t P)) ≫
        DerivedCategory.Q.map roos.δ.hom }

/-- Finite free scalar extension exchanges strict quotient completion on every unbounded
complex, preserves its specified unit, and has the prescribed basis-independent formula.

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YT and 0941;
DAG proof of this node (blueprint: lem-pur-finite-free-completion-exchange).

Proof:
1. Use lem-sfb-finite-free-scalar-coordinates and
lem-weil-pbc-module-sheaves-colimits-forgetful to identify ordinary extension with a finite
power after restriction of scalars. Thus extension is exact and the canonical product
map is an isomorphism, including rank zero.
2. By lem-sf-exact-functor-derived-triangulated it computes derived extension on every
complex. Take K-flat resolutions with flat terms using lem-pc-kflat-resolution;
lem-pur-kflat-change-of-rings makes their scalar extensions K-flat over S.
3. The equality φ(t)^n = u^n v^(en) identifies the two quotient ideals. Balancing gives
β by (p tensor rbar) tensor s maps to (p tensor s) tensor φ(r)bar. The inverse uses
local lifts; the equal ideals make it independent of those lifts. The quotient maps
characterize this formula and it commutes with transitions and augmentations.
4. Apply lem-pur-roos-additive-comparison to the canonical product map and then β.
lem-weil-strict-roos-comparison identifies the resulting actual cones with total derived
limits, with their normalized quotient augmentations.
5. lem-sp-strict-tower-arithmetic-restriction gives the selection/block cone map a.
Invert its localized class after δ to define ε.
6. Both composites on the quotient unit have the same quotient product coordinates
and zero shifted-product coordinate, proving the unit equation.
7. lem-pe-kflat-roos-representative-invariance makes the constructions invert all
quasi-isomorphisms between K-flat representatives; tensor homotopies give homotopies.
8. lem-weil-pbc-site-derived-tensor-descent identifies their localization with D(R).
lem-weil-pbc-localization-universal-property descends the natural isomorphism and its
unit equation, independently of resolutions.
9. A basis was used only to check invertibility: the projection, quotient and block
formulas specify the maps without it. At rank zero the target is zero; at e=1 the
arithmetic comparison is the identity. No truncation or completeness is used. -/
theorem finiteFreeCompletionExchange
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (_hfree : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)).obj
          (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
        ∐ (fun _ : Fin d ↦ SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R))))
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (_ht : Mono (globalSectionMultiplication R t))
    (_hv : Mono (globalSectionMultiplication S vS))
    (uS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (_hu : ∀ U : Cᵒᵖ, IsUnit (@id (S.obj.obj U) (uS.val U)))
    (e : ℕ) (_he : 1 ≤ e)
    (_hrelation : ∀ U : Cᵒᵖ,
      φ.hom.app U (@id (R.obj.obj U) (t.val U)) =
        (@id (S.obj.obj U) (uS.val U)) * (@id (S.obj.obj U) (vS.val U)) ^ e)
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    [HasExactLimitsOfShape (Discrete ℕ) (Sheaf J AddCommGrpCat.{r})] :
    ∃ (CR : Model R t) (CS : Model S vS)
      (ε : CR.completion ⋙ F.T ≅ F.T ⋙ CS.completion),
      (∀ Q, F.T.map (CR.unit.app Q) ≫ ε.hom.app Q = CS.unit.app (F.T.obj Q)) ∧
      (∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        Nonempty (RepresentativeComparison F t vS e CR CS ε P)) := by
  sorry

end CategoryTheory.PrincipalQuotientCompletion
