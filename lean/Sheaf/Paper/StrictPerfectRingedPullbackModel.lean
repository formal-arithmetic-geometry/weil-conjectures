/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.RingedTopoiDerivedPullback
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses

/-! # Specified strict-perfect models for derived ringed-topos pullback

Source: Stacks Project, Cohomology on Sites, Tag 08H3, lemma-strictly-perfect-pullback;
Tag 06YQ and Section derived-pullback, Tag 06YY
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model).

The finite-free comparison is characterized on all local pure tensors, so its choice
is uniquely determined. The transported splittings are degreewise, with no assertion
that they commute with the differentials.

## Main definitions and statements

- `ringedPullbackFiniteFreeIso`: the uniquely characterized finite-free comparison.
- `ringedPullbackStrictPerfectPackage`: the specified transported degreewise splittings.
- `ringedPullbackComplexComparison`: the given comparison on cochain complexes.
- `strictPerfectRingedPullbackModel`: flatness, K-flatness, bounds and natural comparison.
-/

@[expose] public section
set_option autoImplicit false

-- Avoid repeated multicospan searches: first use size-bounded limits, then the small model.
attribute [local instance 12000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
attribute [local instance 11000] CategoryTheory.hasSheafComposeEssentiallySmallSite

universe uC vC uD vD r w
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  {R : Sheaf JC CommRingCat.{r}} {RI S : Sheaf JD CommRingCat.{r}}
  (uInv : Sheaf JC (Type r) ⥤ Sheaf JD (Type r))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (uStar : ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    ringedSiteModules.{r} ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
  (hobj : ∀ M : ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R),
    uStar.obj M = changeOfRings c (I.modules.obj M))

/-- The local pure tensor `s ⊗ x` in ordinary ringed-topos pullback, followed by the
module-sheafification unit. This is real tensor and sheafification data.
Source: Stacks Project, Modules on Sites, Tag 03DF, lemma-global-pullback
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model). -/
noncomputable def ringedPullbackTensorSection
    (M : ringedSiteModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (V : Dᵒᵖ) (s : S.obj.obj V)
    (x : (uInv.obj ((toSheaf _ ⋙
      sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{r})).obj M)).obj.obj V) :
    (uStar.obj M).val.obj V :=
  (eqToHom (hobj M).symm).val.app V
    (((PresheafOfModules.sheafificationAdjunction.{r, vD, r, uD}
      (R := (sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
      (𝟙 ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)).unit.app
        (changeOfRingsPresheaf.{vD, uD, r} (J := JD) c (I.modules.obj M))).app V
      (s ⊗ₜ[RI.obj.obj V, (c.hom.app V).hom]
        (@id ((I.modules.obj M).val.obj V)
          ((I.moduleUnderlying.inv.app M).hom.app V x))))

/-- The coordinate formula specifying the canonical finite-free pullback comparison.
It tests arbitrary local sections of the inverse image, not just global sections.
Source: Stacks Project, Modules on Sites, Tag 03DF, lemma-global-pullback
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model). -/
def IsRingedPullbackFiniteFreeComparison (n : ℕ)
    (gamma : uStar.obj (∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ≅
      ∏ᶜ fun _ : Fin n ↦
        unit ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) : Prop :=
  ∀ (V : Dᵒᵖ) (s : S.obj.obj V)
    (x : (uInv.obj ((toSheaf _ ⋙
      sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{r})).obj
        (∏ᶜ fun _ : Fin n ↦
          unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))).obj.obj V)
    (k : Fin n),
    ((gamma.hom ≫ Pi.π _ k).val.app V)
      (ringedPullbackTensorSection (uInv := uInv) (I := I) (c := c)
        (uStar := uStar) (hobj := hobj) _ V s x) =
        s * c.hom.app V (I.ringUnderlying.hom.hom.app V
          ((uInv.map ((toSheaf _ ⋙
            sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{r})).map
              (Pi.π (fun _ : Fin n ↦
            unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) k))).hom.app V x))

variable (uPush : Sheaf JD (Type r) ⥤ Sheaf JC (Type r))
  (adj : uInv ⊣ uPush) [hlim : PreservesFiniteLimits uInv]
  (hmap : ∀ {M N : ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)} (a : M ⟶ N),
    uStar.map a = eqToHom (hobj M) ≫
      changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm)
  [hadd : uStar.Additive]

include adj hmap hlim hadd

/-- The canonical finite-free comparison exists uniquely, including rank zero.
Source: Stacks Project, Tag 08H3 and Modules on Sites, Tag 03DF
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model).

Proof: finite-limit preservation identifies inverse image of the finite tuple sheaf
with tuples over the inverse-image ring, respecting the coordinate projections.
Send `s ⊗ (a_j)` to `(s c(a_j))`. The inverse sends `(s_j)` to the finite sum of
`s_j ⊗ e_j`. The balanced tensor relations prove both inverse equations. These maps
respect restrictions and pass through sheafification. Pure tensors locally generate
the sheafified module, so the coordinate formula determines the map uniquely.
The empty tuple gives the unique isomorphism of zero objects. -/
theorem existsUnique_ringedPullbackFiniteFreeIso (n : ℕ) :
    ∃! gamma : uStar.obj (∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ≅
      ∏ᶜ fun _ : Fin n ↦
        unit ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S),
      IsRingedPullbackFiniteFreeComparison (uInv := uInv) (I := I) (c := c)
        (uStar := uStar) (hobj := hobj) n gamma := sorry

/-- The unique finite-free comparison fixed by the local pure-tensor coordinate formula.
The named theorem determines this object up to equality, so the choice carries no
unspecified mathematical data. Source: Stacks Project, Tag 08H3 and Tag 03DF
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model). -/
noncomputable def ringedPullbackFiniteFreeIso (n : ℕ) :
    uStar.obj (∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ≅
      ∏ᶜ fun _ : Fin n ↦
        unit ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S) :=
  Classical.choose (existsUnique_ringedPullbackFiniteFreeIso
    (uInv := uInv) (I := I) (c := c) (uStar := uStar) (hobj := hobj)
    (uPush := uPush) (adj := adj) (hmap := hmap) n)

/-- The transported degreewise splittings still split after canonical finite-free
identification. Source: Stacks Project, Tag 08H3
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model).

Proof: cancel gamma followed by its inverse, combine the two images by functoriality,
then use the given splitting and preservation of identity morphisms. No splitting
is required to commute with the differentials. -/
theorem ringedPullback_strictPerfect_splitting
    (F : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (package : StrictPerfectCoefficientPackageOnSite _ F) (n : ℤ) :
    (uStar.map (package.i n) ≫
      (ringedPullbackFiniteFreeIso uInv I c uStar hobj uPush adj hmap (package.N n)).hom) ≫
      ((ringedPullbackFiniteFreeIso uInv I c uStar hobj uPush adj hmap (package.N n)).inv ≫
        uStar.map (package.p n)) = 𝟙 (uStar.obj (F.X n)) := sorry

/-- The specified termwise strict-perfect package after ordinary pullback, with the
same finite ranks and the canonically transported inclusion and retraction maps.
Source: Stacks Project, Tag 08H3
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model). -/
noncomputable def ringedPullbackStrictPerfectPackage
    (F : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (package : StrictPerfectCoefficientPackageOnSite _ F) :
    StrictPerfectCoefficientPackageOnSite
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
      ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) where
  N := package.N
  i n := uStar.map (package.i n) ≫
    (ringedPullbackFiniteFreeIso uInv I c uStar hobj uPush adj hmap (package.N n)).hom
  p n := (ringedPullbackFiniteFreeIso uInv I c uStar hobj uPush adj hmap (package.N n)).inv ≫
    uStar.map (package.p n)
  splitting n := ringedPullback_strictPerfect_splitting
    uInv I c uStar hobj uPush adj hmap F package n

variable [HasDerivedCategory.{w} (ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
  [HasDerivedCategory.{w} (ringedSiteModules.{r}
    ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S))]
  (LF : DerivedCategory (ringedSiteModules.{r}
    ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤
    DerivedCategory (ringedSiteModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S)))
  (epsilon : DerivedCategory.Qh ⋙ LF ⟶
    uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)

/-- The given homotopy-category comparison, transported along the canonical quotient
factorizations to cochain complexes. No comparison map is chosen anew.
Source: Stacks Project, Tag 06YY, lemma-derived-base-change
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model). -/
noncomputable def ringedPullbackComplexComparison :
    DerivedCategory.Q ⋙ LF ⟶
      uStar.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv LF ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) epsilon ≫
    Functor.whiskerRight (uStar.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (uStar.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso _).hom

/-- Every bounded specified strict-perfect complex computes derived ringed-topos
pullback, with its specified termwise package and canonical natural comparison.
Source: Stacks Project, Tag 08H3; Tag 06YQ; Tag 06YY
(blueprint: lem-weil-pbc-strict-perfect-ringed-pullback-model).

Proof:
1. For each degree use the specified finite-free retraction. The coordinate tensor
   isomorphism identifies tensor with the finite free sheaf with a finite direct sum.
   Finite sums are exact and exactness passes to retracts, so every term is flat.
   This includes rank zero; projectivity as a categorical sheaf object is not used.
2. Boundedness above and lem-weil-pbc-independent-bounded-flat-kflat give K-flatness.
3. Ordinary pullback preserves zero objects. The finite-free comparison is fixed by
   its pure-tensor coordinate formula; functoriality transports each splitting to
   the maps in ringedPullbackStrictPerfectPackage, with exactly the original ranks.
4. The same retract argument over S gives flat terms in the pulled complex, and
   its unchanged upper bound and the bounded-flat theorem give its K-flatness.
5. The canonical comparison of lem-weil-pbc-ringed-topoi-derived-pullback is invertible
   on these K-flat flat-term complexes. Uniqueness of a left derived functor identifies
   it with the supplied LF and epsilon, respecting epsilon. The quotient isomorphisms
   give exactly ringedPullbackComplexComparison. Composing with LF(e inverse) gives
   the model of LF(P). Naturality of epsilon gives the displayed chain-map equation.
   Neither coefficient-map flatness nor exactness of ordinary pullback is needed. -/
theorem strictPerfectRingedPullbackModel
    [LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (ringedSiteModules.{r}
        ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (ComplexShape.up ℤ))]
    (F : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (package : StrictPerfectCoefficientPackageOnSite _ F)
    (a b : ℤ) (hbounded : ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) :
    (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (F.X n)) ∧
    F.IsKFlatIndependentCoefficients ∧
    (∀ n : ℤ, n < a ∨ b < n →
      IsZero (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X n)) ∧
    (∀ n : ℤ, IsFlatOnSite (J := JD) (R := S)
      (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X n)) ∧
    CochainComplex.IsKFlatIndependentCoefficients
      ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) ∧
    IsIso ((ringedPullbackComplexComparison uStar LF epsilon).app F) ∧
    (∀ (P : DerivedCategory (ringedSiteModules.{r}
        ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
      (e : DerivedCategory.Q.obj F ≅ P),
      IsIso (LF.map e.inv ≫ (ringedPullbackComplexComparison uStar LF epsilon).app F)) ∧
    (∀ (G : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
      (_ : StrictPerfectCoefficientPackageOnSite _ G) (a' b' : ℤ)
      (_ : ∀ n : ℤ, n < a' ∨ b' < n → IsZero (G.X n)) (v : F ⟶ G),
      (ringedPullbackComplexComparison uStar LF epsilon).app F ≫
          DerivedCategory.Q.map ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).map v) =
        LF.map (DerivedCategory.Q.map v) ≫
          (ringedPullbackComplexComparison uStar LF epsilon).app G) := sorry

end SheafOfModules
