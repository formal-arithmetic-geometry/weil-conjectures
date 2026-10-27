/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Algebra.Homology.RoosConeCalculus
import Sheaf.CategoryTheory.StrictRoosDerivation
import Sheaf.CategoryTheory.StrictRoosNormalization
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Localization.Predicate

/-! # The regular principal completion fibre triangle

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.4.9 and
Lemma 3.4.12, proof of (1) iff (2), printed pp.22--23; Stacks Tag 0941.
(blueprint: lem-sfb-regular-principal-completion-fiber).

The existing quotient-completion model fixes the strict quotient tensor tower and
both coordinates of its augmentation. Level `n : ℕ` means exponent `n+1`.
The repeated-scalar functor uses the existing strict Roos construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w t u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory.PrincipalCompletionFiber

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})

/-- The module category is exactly the recorded ringed-site module category.
Source: Bhatt--Scholze, Lemma 3.4.12, pp.22--23
(blueprint: lem-sfb-regular-principal-completion-fiber). -/
abbrev Modules := ringedSiteModules.{r}
  (SheafOfModules.derivedChangeRingIndependentCoefficients J R)

/-- Multiplication by the given global section, naturally on all module sheaves.
This lifts the existing section multiplication on the underlying module presheaf.
Source: Bhatt--Scholze, Lemma 3.4.12, source transition in its proof
(blueprint: lem-sfb-regular-principal-completion-fiber). -/
def scalar
    (a : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) :
    𝟭 (Modules R) ⟶ 𝟭 (Modules R) where
  app M := ⟨PresheafOfModules.sectionsSMul M.val ⟨a.val, a.property⟩⟩
  naturality {_M _N} f := SheafOfModules.hom_ext
    (PresheafOfModules.sectionsSMul_naturality f.val ⟨a.val, a.property⟩)

/-- Termwise multiplication on a cochain complex, with its naturality on chain maps.
Source: Bhatt--Scholze, Lemma 3.4.12, pp.22--23
(blueprint: lem-sfb-regular-principal-completion-fiber). -/
def scalarComplex
    (a : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) :
    𝟭 (CochainComplex (Modules R) ℤ) ⟶ 𝟭 (CochainComplex (Modules R) ℤ) :=
  (Functor.mapHomologicalComplexIdIso (Modules R) (.up ℤ)).inv ≫
    NatTrans.mapHomologicalComplex (scalar R a) (.up ℤ) ≫
      (Functor.mapHomologicalComplexIdIso (Modules R) (.up ℤ)).hom

/-- The strict repeated-multiplication tower, functorially in its representative.
Source: Bhatt--Scholze, Lemma 3.4.12, source transition in its proof
(blueprint: lem-sfb-regular-principal-completion-fiber). -/
def scalarTower
    (a : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) :
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ :=
  (Functor.ofOpSequence
    (X := fun _ : ℕ ↦ 𝟭 (CochainComplex (Modules R) ℤ))
    (fun _ ↦ scalarComplex R a)).flip ⋙ PrincipalQuotientCompletion.transpose R

/-- The actual shifted Roos cone of the repeated-scalar tower before localization.
Source: Bhatt--Scholze, Lemmas 3.4.9 and 3.4.12; Stacks Tag 0941
(blueprint: lem-sfb-regular-principal-completion-fiber). -/
def scalarRoos
    (a : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) :=
  scalarTower R a ⋙ roosF

/-- First evaluation of the actual repeated-scalar Roos complex.
Source: Bhatt--Scholze, Lemma 3.4.12, positive indexing convention
(blueprint: lem-sfb-regular-principal-completion-fiber). -/
def firstEvaluation
    (a : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (Modules R) ℤ) : (scalarRoos R a).obj P ⟶ P :=
  roosEval ((scalarTower R a).obj P) 0

/-- The natural fibre triangle with its specified Roos descent, first evaluation,
scalar action, and the existing universal quotient-completion unit. This transparent
predicate only collects the conclusion of the theorem, without choosing any data.
Source: Bhatt--Scholze, Lemmas 3.4.9 and 3.4.12, printed pp.22--23
(blueprint: lem-sfb-regular-principal-completion-fiber). -/
def FiberTriangle [HasDerivedCategory.{w} (Modules R)]
    (a : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections) : Prop :=
  ∃ (F : PrincipalQuotientCompletion.Model.{c, v, r, w} R a)
      (T : DerivedCategory.{w} (Modules R) ⥤
        DerivedCategory.{w} (Modules R))
      (φ : scalarRoos R a ⋙ DerivedCategory.Q.{w} ≅
        DerivedCategory.Q.{w} ⋙ T)
      (e : T ⟶ 𝟭 (DerivedCategory.{w} (Modules R)))
      (μ : 𝟭 (DerivedCategory.{w} (Modules R)) ⟶
        𝟭 (DerivedCategory.{w} (Modules R)))
      (δ : F.completion ⟶ T ⋙ shiftFunctor _ (1 : ℤ)),
      (∀ P : CochainComplex (Modules R) ℤ,
        φ.hom.app P ≫ e.app (DerivedCategory.Q.obj P) =
          DerivedCategory.Q.map (firstEvaluation R a P)) ∧
      (∀ P : CochainComplex (Modules R) ℤ,
        μ.app (DerivedCategory.Q.obj P) =
          DerivedCategory.Q.map ((scalarComplex R a).app P)) ∧
      ∀ K : DerivedCategory.{w} (Modules R),
        Triangle.mk (e.app K ≫ μ.app K) (F.unit.app K) (δ.app K) ∈
          distTriang (DerivedCategory.{w} (Modules R))

end CategoryTheory.PrincipalCompletionFiber

namespace CategoryTheory

/-- Regular principal quotient completion has the repeated-scalar fibre, with its
specified reduction unit and first arrow `a` times first evaluation, naturally in K.

Source: Bhatt--Scholze, Lemma 3.4.9 and Lemma 3.4.12, proof of (1) iff (2),
printed pp.22--23; normalized total inverse limit: Stacks Tag 0941
(blueprint: lem-sfb-regular-principal-completion-fiber).

Proof:
1. Countable products are exact by lem-weil-proetale-countable-products-exact.
   Apply lem-pe-roos-cone-calculus to strict towers. Its cone and shift comparisons
   preserve inclusions and boundaries. The descent of lem-weil-strict-roos-derivation
   and lem-weil-strict-roos-normalization identifies this with total right-derived
   inverse limit, respecting evaluations and zero-shifted-coordinate augmentations.
2. Choose a K-flat resolution by lem-pc-kflat-resolution. For each positive n,
   multiplication by a^n is monic by induction. Thus [R --a^n--> R] maps
   quasi-isomorphically to R/a^n. Tensor with the resolution, using
   lem-pur-kflat-tensor-quasiiso-independent. These maps form the augmented strict
   comparison of def-pur-principal-koszul-quotient-towers.
3. The tensor Koszul tower is the cone tower of f_n=a^n from the repeated-a tower
   to the constant identity-transition tower: its coordinates have differential
   (db+a^n c,-dc), transition (b,c) ↦ (b,ac), and augmentation x ↦ (x,0).
4. Apply the Roos cone comparison and localize its cone triangle. The quotient
   comparison identifies the third vertex with quotient completion. The normalized
   total-limit comparison identifies its particular zero-coordinate map with the unit.
5. For the constant tower put S=1-shift, j(x)=((x)_n,0), e(v,z)=v_1.
   Set r(w)_1=0 and r(w)_n=-sum_{i<n} w_i. Then Sr=1 and rSv=v-j(ev).
   The homotopy h(v,z)=(-rz,0) gives dh+hd=1-je. Hence evaluation and j are
   mutually inverse after localization, naturally in the representative.
6. Replacing the middle vertex by the representative makes the first arrow
   eH(f)(v,z)=a v_1. The second arrow is exactly x ↦ ((x mod a^n)_n,0),
   rather than a lift chosen from its product coordinates. Transport the boundary.
7. Every construction commutes with chain maps. Roos inverts levelwise quasi-isos;
   K-flat tensor and the quotient comparison identify all K-flat computations.
   Resolve the middle complex of a derived roof. The fraction calculus of
   lem-pur-quasi-isos-saturated-triangulated gives common refinements, so these
   natural transformations descend to every derived morphism. Uniqueness follows
   from lem-weil-pbc-localization-universal-property. The completion universal
   pair is the existing PrincipalQuotientCompletion.Model, not arbitrary data. -/
theorem regularPrincipalCompletionFiber
    (X : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (PrincipalCompletionFiber.Modules.{t + 1, t, max u (t + 1)} R)]
    (a : (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology X) R)).sections)
    (_ha : Mono (globalSectionMultiplication R a)) :
    PrincipalCompletionFiber.FiberTriangle.{t + 1, t, max u (t + 1), w} R a := by
  sorry

end CategoryTheory
