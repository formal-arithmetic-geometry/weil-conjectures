/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.CompletedPullbackAdjunction
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Strict quotient systems and the completion unit

Source: Stacks Project, sites-cohomology.tex, Tags 0940 and 0941;
proetale.tex, Tags 099M and 099N; the strict quotient auxiliary
(blueprint: lem-pur-strict-quotient-diagonal-normalization).

The existing sequence site, ring sheaves, scalar extension, quotient transitions,
ordinary derived categories and completion reflector are used throughout.

## Main definitions

* `strictDiagonalRing`, `strictQuotientRing`: the published ringed sequence-site models.
* `StrictQuotientDiagonalPresentation`: section-normalized ordinary comparison data.
* `StrictQuotientDiagonalPresentation.representative`: the canonical cochain comparison.

## Main statement

* `strictQuotientDiagonalNormalization`: all four clauses, with the unit equation.

Index n means the positive exponent n+1. The presentation below fixes every
ordinary comparison on sections, and every derived comparison on representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [CommRing A] (I : Ideal A)

/-- Standard localization for constant-coefficient module towers.
This is the standard derived-category instance, without a global-sections construction.
Source: Stacks 05RU, 0940 (blueprint: lem-pur-strict-quotient-diagonal-normalization). -/
instance strictQuotientTowerHasDerived (O : Sheaf J CommRingCat.{u}) :
    HasDerivedCategory (ℕᵒᵖ ⥤ Mod O) :=
  HasDerivedCategory.standard _

/-- The published constant ring on the vertical sequence site.
Source: Stacks 0940 (blueprint: lem-pur-strict-quotient-diagonal-normalization). -/
abbrev strictDiagonalRing : Sheaf (WeilConjectures.coefficientSequenceTopology J)
    CommRingCat.{u} :=
  SheafOfModules.systemSequenceRing.{u, u, u} (J := J)
    ((Functor.const ℕᵒᵖ).obj (constant J A))

/-- The published quotient ring on that site, with the actual quotient transitions.
Source: Stacks 0940, 099M (blueprint: lem-pur-strict-quotient-diagonal-normalization). -/
abbrev strictQuotientRing : Sheaf (WeilConjectures.coefficientSequenceTopology J)
    CommRingCat.{u} :=
  SheafOfModules.systemSequenceRing.{u, u, u} (J := J) (finiteSystem J A I)

/-- Section-normalized ordinary data for the strict quotient realization.
All categories and scalar operations are existing constructions. The fields fix the
coefficient map, the constant-tower equivalence, the diagonal and the scalar insertion;
they do not assume any derived comparison or completion assertion.
Source: Stacks 0940 and 03CZ; strict quotient auxiliary
(blueprint: lem-pur-strict-quotient-diagonal-normalization). -/
structure StrictQuotientDiagonalPresentation where
  /-- The structural map Delta A to the quotient coefficient sheaf. -/
  ringMap : strictDiagonalRing J A ⟶ strictQuotientRing J A I
  /-- Its sections are the actual maps A to A/I^(n+1). -/
  ringMap_sections : ∀ (n : ℕ) (U : Cᵒᵖ),
    HEq (ringMap.hom.app (op (n, U.unop))) ((quotient J A I n).hom.app U)
  /-- Constant-ring sequence modules are ordinary strict A-module towers. -/
  towers : Mod (strictDiagonalRing J A) ≌ (ℕᵒᵖ ⥤ Mod (constant J A))
  /-- The equivalence is additive. -/
  [towers_additive : towers.functor.Additive]
  /-- Its component modules are the literal vertical restrictions. -/
  towers_objects : ∀ (M : Mod (strictDiagonalRing J A)) (n : ℕ) (U : Cᵒᵖ),
    HEq (((towers.functor.obj M).obj (op n)).val.obj U) (M.val.obj (op (n, U.unop)))
  /-- Its vertical arrows are the original vertical restrictions. -/
  towers_restrictions : ∀ (M : Mod (strictDiagonalRing J A)) (n : ℕ)
    {U V : Cᵒᵖ} (f : U ⟶ V),
    HEq (((towers.functor.obj M).obj (op n)).val.map f)
      (M.val.map (Prod.mkHom (𝟙 n) f.unop).op)
  /-- Its horizontal arrows are the original horizontal restrictions. -/
  towers_transitions : ∀ (M : Mod (strictDiagonalRing J A)) {m n : ℕ}
    (h : m ≤ n) (U : Cᵒᵖ),
    HEq (((towers.functor.obj M).map (homOfLE h).op).val.app U)
      (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
  /-- It leaves every component of a module morphism unchanged. -/
  towers_maps : ∀ {M N : Mod (strictDiagonalRing J A)} (f : M ⟶ N)
    (n : ℕ) (U : Cᵒᵖ),
    HEq (((towers.functor.map f).app (op n)).val.app U) (f.val.app (op (n, U.unop)))
  /-- The ordinary diagonal on the ringed sequence site. -/
  diagonal : Mod (constant J A) ⥤ Mod (strictDiagonalRing J A)
  /-- The diagonal is additive. -/
  [diagonal_additive : diagonal.Additive]
  /-- The diagonal is exact on kernels. -/
  [diagonal_limits : PreservesFiniteLimits diagonal]
  /-- The diagonal is exact on cokernels. -/
  [diagonal_colimits : PreservesFiniteColimits diagonal]
  /-- Diagonal sections retain the entire module structure. -/
  diagonal_objects : ∀ (M : Mod (constant J A)) (n : ℕ) (U : Cᵒᵖ),
    HEq ((diagonal.obj M).val.obj (op (n, U.unop))) (M.val.obj U)
  /-- All diagonal restrictions are the vertical restrictions of M. -/
  diagonal_restrictions : ∀ (M : Mod (constant J A))
    {X Y : (ℕ × C)ᵒᵖ} (f : X ⟶ Y),
    HEq ((diagonal.obj M).val.map f) (M.val.map f.unop.2.op)
  /-- Diagonal maps are unchanged on sections. -/
  diagonal_maps : ∀ {M N : Mod (constant J A)} (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ),
    HEq ((diagonal.map f).val.app (op (n, U.unop))) (f.val.app U)
  /-- The ordinary scalar-insertion map before localization. -/
  insertion : diagonal ⟶ diagonal ⋙ change ringMap ⋙ res ringMap
  /-- Scalar insertion is x mapped to 1 tensor x, followed by sheafification. -/
  insertion_sections : ∀ (M : Mod (constant J A)) (X : (ℕ × C)ᵒᵖ)
    (x : (diagonal.obj M).val.obj X),
    (insertion.app M).val.app X x = tensorSection ringMap (diagonal.obj M) X 1 x
  /-- Scalar restriction of the whole tensor diagram is the published quotient tower. -/
  reductionIso : diagonal ⋙ change ringMap ⋙ res ringMap ⋙ towers.functor ≅
    reductionTower J A I false
  /-- This comparison is the identity on the local pure tensors at every level. -/
  reductionIso_sections : ∀ (M : Mod (constant J A)) (n : ℕ) (U : Cᵒᵖ)
    (s : (finite J A I n).obj.obj U)
    (x : (diagonal.obj M).val.obj (op (n, U.unop))) (m : M.val.obj U)
    (z : ((towers.functor.obj ((res ringMap).obj
      ((change ringMap).obj (diagonal.obj M)))).obj (op n)).val.obj U),
    HEq x m → HEq z (tensorSection ringMap (diagonal.obj M) (op (n, U.unop)) s x) →
      (((reductionIso.hom.app M).app (op n)).val.app U) z =
        tensorSection (quotient J A I n) M U s m

attribute [instance] StrictQuotientDiagonalPresentation.towers_additive
  StrictQuotientDiagonalPresentation.diagonal_additive
  StrictQuotientDiagonalPresentation.diagonal_limits
  StrictQuotientDiagonalPresentation.diagonal_colimits

namespace StrictQuotientDiagonalPresentation

variable {J A I} (d : StrictQuotientDiagonalPresentation J A I)

/-- The actual exact restriction from quotient systems to constant-A towers.
Source: Stacks 03CZ, 0940 (blueprint: lem-pur-strict-quotient-diagonal-normalization). -/
abbrev restriction := res d.ringMap ⋙ d.towers.functor

/-- The exact diagonal on ordinary derived categories.
Source: Stacks 0940 (blueprint: lem-pur-strict-quotient-diagonal-normalization). -/
def diagonalD : D (constant J A) ⥤ D (strictDiagonalRing J A) :=
  d.diagonal.mapDerivedCategory

/-- Derived scalar restriction, followed by the existing constant-tower realization.
Source: Stacks 03CZ, 0940 (blueprint: lem-pur-strict-quotient-diagonal-normalization). -/
def restrictionD : D (strictQuotientRing J A I) ⥤ TD (constant J A) :=
  dres d.ringMap ⋙ d.towers.functor.mapDerivedCategory

/-- Derived quotient reduction is S Delta, with S the existing universal scalar extension.
Source: Stacks 06YY, 099M (blueprint: lem-pur-strict-quotient-diagonal-normalization). -/
def reductionD : D (constant J A) ⥤ D (strictQuotientRing J A I) :=
  d.diagonalD ⋙ extend d.ringMap

/-- The canonical comparison to the strict quotient complex on one representative.
It is built from the exact diagonal, universal scalar-extension counit, exact scalar
restriction, exact tower equivalence, and the section-normalized ordinary tensor comparison.
Source: Stacks 06YY, 0940 (blueprint: lem-pur-strict-quotient-diagonal-normalization). -/
def representative (P : Cx (constant J A)) :
    (d.reductionD ⋙ d.restrictionD).obj ((Q (constant J A)).obj P) ⟶
      (TQ (constant J A)).obj (reductionComplex J A I false P) :=
  letI : (reductionTower J A I false).Additive := reductionTower_additive J A I false
  d.restrictionD.map
    ((extend d.ringMap).map (d.diagonal.mapDerivedCategoryFactors.hom.app P) ≫
      (extendComparison d.ringMap).app
        ((d.diagonal.mapHomologicalComplex (.up ℤ)).obj P)) ≫
    d.towers.functor.mapDerivedCategory.map
      ((res d.ringMap).mapDerivedCategoryFactors.hom.app
        (((change d.ringMap).mapHomologicalComplex (.up ℤ)).obj
          ((d.diagonal.mapHomologicalComplex (.up ℤ)).obj P))) ≫
    d.towers.functor.mapDerivedCategoryFactors.hom.app
      (((res d.ringMap).mapHomologicalComplex (.up ℤ)).obj
        (((change d.ringMap).mapHomologicalComplex (.up ℤ)).obj
          ((d.diagonal.mapHomologicalComplex (.up ℤ)).obj P))) ≫
    (TQ (constant J A)).map
      ((Functor.mapHomologicalComplexCompIso
        (F := d.diagonal ⋙ change d.ringMap ⋙ res d.ringMap)
        (G := d.towers.functor) (H := reductionTower J A I false)
        d.reductionIso (.up ℤ)).hom.app P)

end StrictQuotientDiagonalPresentation

/-- The strict quotient realization, common diagonal K-flat model, constant K-injective
normalization, and completion-unit equation, natural in every derived input.

Source: Stacks Project, sites-cohomology.tex, Tags 0940 and 0941;
proetale.tex, Tags 099M and 099N; agent strict quotient auxiliary
(blueprint: lem-pur-strict-quotient-diagonal-normalization).

Proof:
1. Use the diagram-site equivalence (lem-weil-pbc-diagram-site-realization).
The coefficient ring is the actual quotient sequence. Vertical module restrictions
and horizontal semilinear transitions give inverse constructions on objects and maps.
Restriction of scalars leaves all underlying groups and transitions unchanged.
2. Sheafification is vertical and componentwise: sheafify each slice and extend the
transitions uniquely. Tensor and direct-sum total tensor are therefore componentwise,
with the identity on pure tensors (def-pur-sheaf-tensor-product).
3. Kernels, cokernels and cohomology are componentwise. Scalar restriction is exact
and reflects isomorphisms. Exact functors descend termwise to the derived categories
(lem-weil-pbc-exact-functor-derived-factorization).
4. Write a derived map as a localization fraction. If restriction makes it invertible,
its cohomology maps are invertible after restriction and hence before restriction.
The numerator is then a quasi-isomorphism, proving derived conservativity
(lem-pc-quasi-isomorphisms-multiplicative-system,
lem-pc-left-localization-fraction-representation).
5. Choose one flat-term K-flat resolution (lem-pc-kflat-resolution). Its diagonal is
K-flat because every evaluated tensor with an acyclic tower is acyclic; its terms are
flat by componentwise exactness. This uses def-pc-kflat-complex.
6. Apply lem-pur-derived-change-of-rings to this diagonal. Its tensor complex is the
strict quotient complex with the actual quotient transitions. Scalar insertion is
x mapped to 1 tensor x and is a strict map since quotient maps preserve 1.
7. For an acyclic tower E and f:E to Delta J with J K-injective, write f_n=f_0 p_n0.
Choose a null homotopy h of f_0 using def-pur-kinjective-complex. Then h p_n0 is a
compatible tower null homotopy. Thus the constant functor preserves K-injectives.
8. The constant complex with identity projections is itself a limit cone. On a
K-injective representative the total derived limit computes this ordinary limit
(lem-weil-pbc-ringed-strict-tower-homotopy-limit). Hom into K-injectives gives the
natural isomorphism ell (prop-pur-kinjective-resolutions-exist,
lem-weil-pbc-kinjective-hom-derived).
9. Both L U R and the completion reflector use the same strict quotient complex and
the same total derived inverse limit (lem-sp-completed-pullback-adjunction).
10. Resolve the quotient tower by a K-injective tower. The insertion map induces the
map into its literal limit. Comparing with a K-injective representative of the input
shows that this whole derived map is L(i) composed with ell inverse, not just an
equality of its evaluated projections (lem-weil-pbc-kinjective-hom-derived).
11. Noetherianness gives finitely many ideal generators. The unit-preserving Koszul/
quotient comparison (lem-weil-pbc-constant-completion-equivalence) identifies this map
with the reflector unit. Scalar insertion commutes with every chain map; the
localization universal property descends the equality and all comparisons to natural
transformations (lem-weil-pbc-localization-universal-property). -/
theorem strictQuotientDiagonalNormalization [IsNoetherianRing A] :
    ∃ (d : StrictQuotientDiagonalPresentation J A I)
      (i : (constantTower J (constant J A)).mapDerivedCategory ⟶
        d.reductionD ⋙ d.restrictionD)
      (ell : (constantTower J (constant J A)).mapDerivedCategory ⋙
        rlim (constant J A) ≅ 𝟭 (D (constant J A)))
      (c : d.reductionD ⋙ d.restrictionD ⋙ rlim (constant J A) ≅ completion J A I false)
      (literalLimit : ∀ P : Cx (constant J A),
        (ordinaryLimit (constant J A)).obj
          (((constantTower J (constant J A)).mapHomologicalComplex (.up ℤ)).obj P) ≅ P),
      (∀ n : ℕ, PreservesFiniteLimits
        (SheafOfModules.systemSequenceEvaluation (finiteSystem J A I) n) ∧
        PreservesFiniteColimits
          (SheafOfModules.systemSequenceEvaluation (finiteSystem J A I) n)) ∧
      PreservesFiniteLimits d.restriction ∧ PreservesFiniteColimits d.restriction ∧
      (∀ {V W : D (strictQuotientRing J A I)} (f : V ⟶ W),
        IsIso (d.restrictionD.map f) → IsIso f) ∧
      (∀ P : Cx (constant J A),
        CochainComplex.IsKFlatIndependentCoefficients (R := constant J A) P →
        (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := constant J A) (P.X q)) →
        (CochainComplex.IsKFlatIndependentCoefficients (R := strictDiagonalRing J A)
          ((d.diagonal.mapHomologicalComplex (.up ℤ)).obj P) ∧
          (∀ q : ℤ, SheafOfModules.IsFlatOnSite
            (J := WeilConjectures.coefficientSequenceTopology J)
            (R := strictDiagonalRing J A) (d.diagonal.obj (P.X q))) ∧
          IsIso (d.representative P) ∧
          i.app ((Q (constant J A)).obj P) ≫ d.representative P =
            (constantTower J (constant J A)).mapDerivedCategoryFactors.hom.app P ≫
              (TQ (constant J A)).map
                ((NatTrans.mapHomologicalComplex (reductionUnit J A I false) (.up ℤ)).app P))) ∧
      (∀ V : D (constant J A), ∃ (P : Cx (constant J A))
        (_e : (Q (constant J A)).obj P ≅ V),
        CochainComplex.IsKFlatIndependentCoefficients (R := constant J A) P ∧
          (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := constant J A) (P.X q))) ∧
      (∀ P : Cx (constant J A), P.IsKInjective →
        CochainComplex.IsKInjective
          (((constantTower J (constant J A)).mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (∀ (P : Cx (constant J A)) (q : ℤ), (literalLimit P).hom.f q =
        limit.π ((constantTower J (constant J A)).obj (P.X q)) (op 0)) ∧
      (∀ P : Cx (constant J A), P.IsKInjective →
        (limitComparison (constant J A)).app
            (((constantTower J (constant J A)).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (rlim (constant J A)).map
            ((constantTower J (constant J A)).mapDerivedCategoryFactors.inv.app P) ≫
          ell.hom.app ((Q (constant J A)).obj P) =
            (Q (constant J A)).map (literalLimit P).hom) ∧
      (∀ P : Cx (constant J A),
        CochainComplex.IsKFlatIndependentCoefficients (R := constant J A) P →
        (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := constant J A) (P.X q)) →
        c.hom.app ((Q (constant J A)).obj P) ≫
          (rlim (constant J A)).map ((quotientPresentation J A I false).comparison.app P) =
            (rlim (constant J A)).map (d.representative P)) ∧
      ell.inv ≫ Functor.whiskerRight i (rlim (constant J A)) ≫ c.hom =
        completionUnit J A I false := by
  sorry

end CategoryTheory.ConstantCompletion
