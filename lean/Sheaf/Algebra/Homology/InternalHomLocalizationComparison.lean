/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.CategoryTheory.RingedSiteLocalization
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.CategoryTheory.ScalarLocalizationSheafExact
import Sheaf.CategoryTheory.ScalarLocalizationTelescopeCore
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Internal Hom and localization under sequential continuity

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62,
conditional internal-sheaf localization argument (not the global Hom assertion);
Stacks Project, Tags 03CY, 03DB, 03ET, 06YY, 07A6 and 08J9
(blueprint: lem-sfb-internal-hom-localization-comparison).

All derived operations are the recorded, evaluation-normalized operations.
Sequential colimits are formed in complexes of module sheaves, before applying Q.
The functorial Hom representatives are the same ones as in the recorded internal Hom.
Exact filtered colimits are supplied by the Grothendieck-abelian module-sheaf theorem
on this small site; no independent exactness witness or stronger coefficient condition is needed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

/-- Fixed functorial complex representatives of internal Hom from K. The source is
Q's chosen representative and the target uses exactly the existing K-injective functor.
Source: Stacks 08J7, 0A95; Bhatt--Scholze 6.8.12, conditional internal-sheaf version
(blueprint: lem-sfb-internal-hom-localization-comparison). -/
def localizationHomComplex (R : Sheaf J CommRingCat.{max c v r})
    (K : DerivedCategory (scalarModules J R)) :
    CochainComplex (scalarModules J R) ℤ ⥤ CochainComplex (scalarModules J R) ℤ :=
  coefficientHomResolution.{r, c, v} J R ⋙
    (homComplexFunctor (R := R)).obj (op (DerivedCategory.Q.objPreimage K))

/-- The canonical continuity comparison is induced by the Hom images of the colimit legs.
Taking Q afterwards means that being an isomorphism means being a quasi-isomorphism,
not an isomorphism of complexes. Source: Stacks 03DB and 08J9; Bhatt--Scholze 6.8.12
(blueprint: lem-sfb-internal-hom-localization-comparison). -/
def localizationHomContinuityMap (R : Sheaf J CommRingCat.{max c v r})
    (K : DerivedCategory (scalarModules J R))
    (D : ℕ ⥤ CochainComplex (scalarModules J R) ℤ) :
    DerivedCategory.Q.obj (colimit (D ⋙ localizationHomComplex.{c, v, r, w} J R K)) ⟶
      DerivedCategory.Q.obj ((localizationHomComplex.{c, v, r, w} J R K).obj (colimit D)) :=
  DerivedCategory.Q.map
    (colimit.post D (localizationHomComplex.{c, v, r, w} J R K))

/-- The displayed hypothesis: all sequential diagrams with a common termwise lower
bound have invertible evaluation-induced internal-Hom colimit comparison.
Source: Bhatt--Scholze 6.8.12, conditional internal-sheaf formulation
(blueprint: lem-sfb-internal-hom-localization-comparison). -/
def HasLocalizationHomContinuity (R : Sheaf J CommRingCat.{max c v r})
    (K : DerivedCategory (scalarModules J R)) : Prop :=
  ∀ D : ℕ ⥤ CochainComplex (scalarModules J R) ℤ,
    (∃ a : ℤ, ∀ n : ℕ, (D.obj n).IsStrictlyGE a) →
      IsIso (localizationHomContinuityMap.{c, v, r, w} J R K D)

variable {J}
  (M : ScalarHomModels.{c, v, r, w} J)
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

/-- The actual canonical comparison: extend evaluation, use the inverse strong tensor
comparison, and transpose over S. No comparison arrow is supplied as a hypothesis.
Source: Stacks 07A4, 07A6 and 08J9; Bhatt--Scholze 6.8.14(2), conditional argument
(blueprint: lem-sfb-internal-hom-localization-comparison). -/
def localizationHomComparison (μ : ScalarHomTensorComparison M a)
    (K L : DerivedCategory (scalarModules J R)) :
    (M.scalar a).derived.obj ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op K, L)) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J S).obj
        (op ((M.scalar a).derived.obj K), (M.scalar a).derived.obj L) :=
  (M.closed S).transpose _ ((M.scalar a).derived.obj K) ((M.scalar a).derived.obj L)
    (μ.iso.inv.app
      ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L), K) ≫
      (M.scalar a).derived.map ((M.closed R).evaluation K L))

/-- Restrict the actual comparison and apply the evaluation-normalized scalar-Hom
adjunction. This is the map identified with sequential continuity by the theorem.
Source: Stacks 07A6 and 08J9; Bhatt--Scholze 6.8.14(2), conditional argument
(blueprint: lem-sfb-internal-hom-localization-comparison). -/
def localizationHomRestrictedComparison
    (μ : ∀ {A B : Sheaf J CommRingCat.{max c v r}} (b : A ⟶ B),
      ScalarHomTensorComparison M b)
    (α : ScalarInternalHomAdjunction M μ)
    (K L : DerivedCategory (scalarModules J R)) :
    (scalarDerivedRestriction a).obj
        ((M.scalar a).derived.obj
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L))) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op K, (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj L)) :=
  (scalarDerivedRestriction a).map (localizationHomComparison.{c, v, r, w} M a (μ a) K L) ≫
    (α.iso a).hom.app (op K, (M.scalar a).derived.obj L)

variable (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J CommRingCat.{max c v r}]
  (s : (R.obj ⋙ forget CommRingCat).sections)

/-- Under precisely the displayed sequential continuity assumption, scalar localization
commutes with ambient derived internal Hom for a bounded-below second input.
The restricted isomorphism is characterized by its zeroth telescope leg (the scalar
unit); uniqueness records the identification of the actual derived map, rather than
only a selection of an isomorphism between its endpoints. Naturality is in both inputs.
All auxiliary presentations are the already existing normalized models, which exist
by scalarInternalHomAdjunction_exists and impose no extra mathematical hypothesis.

Source: Bhatt--Scholze 6.8.12 and 6.8.14(2), pp. 61--62, conditional internal-sheaf
argument; Stacks 03CY, 03DB, 03ET, 06YY, 07A6 and 08J9
(blueprint: lem-sfb-internal-hom-localization-comparison).

Proof (the node's seven steps):
1. Replace L by the good quotient truncation at a cohomological lower bound. Its
scalar sequence has a common termwise lower bound.
2. Scalar localization and restriction are exact (scalar-localization-sheaf-exact,
ordinary coefficient adjunction). The K-flat formula identifies their termwise
functors with derived extension and restriction; the normalized derived adjunction
identifies the unit with x mapped to 1 tensor x.
3. Multiplication S tensor_R U(N) → N is inverse to the unit, by balancing local
fractions. Thus the derived counit is invertible. The triangle identities show
that precomposition with the scalar unit bijects maps UF(A) → U(N) with maps A → U(N).
4. The complex-colimit telescope theorem identifies scalar sequential colimits with
UF, compatibly with every fraction leg, even for unbounded Hom complexes. Exact
filtered colimits preserve quasi-isomorphisms.
5. Apply the continuity hypothesis to the bounded-below scalar input tower. In the
Hom representative the transition I(s) is homotopic to multiplication by s, since
both coincide in the derived category and the target is K-injective. The two
colimits are cokernels of 1 minus shift on the direct sum. A homotopy gives a
leg-compatible cone isomorphism, and each cone maps quasi-isomorphically to its
cokernel (kernel the contractible cone of the identity). This gives an invertible
beta with beta after the zeroth unit equal to Hom(K, eta_L).
6. The scalar-Hom adjunction and extended evaluation give the same unit equation
for the actual restricted comparison. The uniqueness in step 3 identifies it with beta.
7. Conservativity of scalar restriction gives invertibility over S. Functorial
scalar extension, evaluation, transposition and the scalar-Hom adjunction give
naturality contravariantly in K and covariantly in L. -/
theorem internalHom_localization_comparison
    (μ : ∀ {A B : Sheaf J CommRingCat.{max c v r}} (b : A ⟶ B),
      ScalarHomTensorComparison M b)
    (α : ScalarInternalHomAdjunction M μ)
    (K L : DerivedCategory (scalarModules J R))
    (hK : HasLocalizationHomContinuity.{c, v, r, w} J R K)
    (hL : ∃ n : ℤ, L.IsGE n) :
    IsIso (localizationHomComparison.{c, v, r, w} M (ringedLocalizationRingUnitOfUniverses R s)
      (μ (ringedLocalizationRingUnitOfUniverses R s)) K L) ∧
    IsIso (localizationHomRestrictedComparison.{c, v, r, w} M
      (ringedLocalizationRingUnitOfUniverses R s) μ α K L) ∧
    (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).adjunction.unit.app
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ≫
      localizationHomRestrictedComparison.{c, v, r, w} M
          (ringedLocalizationRingUnitOfUniverses R s) μ α K L =
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op K))
            ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).adjunction.unit.app L)) ∧
    (∀ b :
        (scalarDerivedRestriction (ringedLocalizationRingUnitOfUniverses R s)).obj
          ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).derived.obj
            ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L))) ⟶
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
          (op K, (scalarDerivedRestriction (ringedLocalizationRingUnitOfUniverses R s)).obj
            ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).derived.obj L)),
      (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).adjunction.unit.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ≫ b =
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op K))
            ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).adjunction.unit.app L)) →
      b = localizationHomRestrictedComparison.{c, v, r, w} M
        (ringedLocalizationRingUnitOfUniverses R s) μ α K L) ∧
    ∀ (K' L' : DerivedCategory (scalarModules J R))
      (_hK' : HasLocalizationHomContinuity.{c, v, r, w} J R K') (_hL' : ∃ n : ℤ, L'.IsGE n)
      (f : K' ⟶ K) (g : L ⟶ L'),
      (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).derived.map
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map (Prod.mkHom f.op g)) ≫
        localizationHomComparison.{c, v, r, w} M (ringedLocalizationRingUnitOfUniverses R s)
          (μ (ringedLocalizationRingUnitOfUniverses R s)) K' L' =
      localizationHomComparison.{c, v, r, w} M (ringedLocalizationRingUnitOfUniverses R s)
          (μ (ringedLocalizationRingUnitOfUniverses R s)) K L ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J
          (ringedLocalizationRingOfUniverses R s)).map
            (Prod.mkHom
              ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).derived.map f).op
              ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).derived.map g)) := by
  sorry

end CategoryTheory
