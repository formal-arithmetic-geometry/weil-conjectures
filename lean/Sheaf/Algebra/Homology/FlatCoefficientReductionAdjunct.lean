/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellation
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Flat coefficient comparison and derived reduction adjuncts

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E, 0D6D and 07A6;
sites-modules.tex, Tag 05V4
(blueprint: lem-weil-pbc-flat-coefficient-reduction-adjunct).

The presentations and their normalization are the existing K-flat derived scalar
extensions, not new choices of tensor products or adjunctions. Tensor formulas below
use the scalar-first convention: the paper's `x ⊗ s` is `sectionTensor ... s x`.
The ordinary and derived comparisons are specified together, including their descent
through the universal counits, so the assertion fixes the canonical balanced maps.

## Main definitions

- `flatCoefficientMultiplication`: the normalized multiplication map.
- `flatCoefficientChange`: the canonical coefficient-change arrow.
- `flatCoefficientUnit`: the canonical scalar-extension unit identification.
- `FlatCoefficientReductionComparison`: the fully normalized comparison interface.

## Main statements

- `flat_coefficient_reduction_adjunct`: the comparison and all its compatibilities.
-/

@[expose] public section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false

universe u v r w

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.SuccessiveDerivedQuotient

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [hD : ∀ A : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules A)]
  (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
  (N : Normalization p)
  {R B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)

/-- The multiplication `B ⊗_R S → S`, as a morphism of B-module sheaves.
The normalized ordinary counit sends `b ⊗ s` to `ψ(b)s`.
Source: Stacks 05V4 and 07A6
(blueprint: lem-weil-pbc-flat-coefficient-reduction-adjunct). -/
noncomputable def flatCoefficientMultiplication {S : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S) :
    (p φ).ordinary.obj ((restriction φ).obj
      ((restriction ψ).obj (unit (derivedChangeRingIndependentCoefficients J S)))) ⟶
      (restriction ψ).obj (unit (derivedChangeRingIndependentCoefficients J S)) :=
  (N.ordinaryAdjunction φ).counit.app
    ((restriction ψ).obj (unit (derivedChangeRingIndependentCoefficients J S)))

/-- Coefficient change `X ⊗^L_A S → Res(X ⊗^L_A T)` for `S → T`.
This is the normalized extension unit followed by the canonical associator.
Source: Stacks 0D6D and 07A6
(blueprint: lem-weil-pbc-flat-coefficient-reduction-adjunct). -/
noncomputable def flatCoefficientChange {A S T : Sheaf J CommRingCat.{r}}
    (a : A ⟶ S) (τ : S ⟶ T) (X : DerivedCategory (Modules A)) :
    (p a).derived.obj X ⟶ (N.right τ).obj ((p (a ≫ τ)).derived.obj X) :=
  (N.adjunction τ).unit.app ((p a).derived.obj X) ≫
    (N.right τ).map ((N.derived a τ).hom.app X)

/-- The scalar-extension unit identification on `X ⊗^L_A S`.
Its flat-model formula is `(x ⊗ s) ⊗ t ↦ x ⊗ st`, since the associator
is normalized by that formula and `a ≫ 𝟙 S = a`.
Source: Stacks 0D6D, identity-map case
(blueprint: lem-weil-pbc-flat-coefficient-reduction-adjunct). -/
noncomputable def flatCoefficientUnit {A S : Sheaf J CommRingCat.{r}}
    (a : A ⟶ S) (X : DerivedCategory (Modules A)) :
    (p (𝟙 S)).derived.obj ((p a).derived.obj X) ⟶ (p a).derived.obj X :=
  (N.derived a (𝟙 S)).hom.app X ≫
    eqToHom (congrArg (fun b ↦ (p b).derived.obj X) (Category.comp_id a))

/-- The canonical balanced comparison, with its K-flat representative, all derived
adjuncts, coefficient naturality, and successive-extension and unit normalizations.
All maps in the coherence clauses are the existing normalized scalar maps.
Source: Stacks 0G7E, 0D6D, 07A6 and 05V4
(blueprint: lem-weil-pbc-flat-coefficient-reduction-adjunct). -/
structure FlatCoefficientReductionComparison where
  /-- The ordinary balanced comparison, natural in the B-module. -/
  ordinary : ∀ {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (_hμ : IsIso (flatCoefficientMultiplication p N φ ψ)),
    restriction φ ⋙ (p (φ ≫ ψ)).ordinary ≅ (p ψ).ordinary
  /-- Its actual formula on sheafified pure tensors. -/
  ordinary_pure : ∀ {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (hμ : IsIso (flatCoefficientMultiplication p N φ ψ))
    (M : Modules B) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
    ((ordinary ψ hμ).hom.app M).val.app U
        (sectionTensor (p (φ ≫ ψ)) ((restriction φ).obj M) U s x) =
      sectionTensor (p ψ) M U s x
  /-- The comparison in D(S), natural in every derived B-module. -/
  derived : ∀ {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (_hμ : IsIso (flatCoefficientMultiplication p N φ ψ)),
    N.right φ ⋙ (p (φ ≫ ψ)).derived ≅ (p ψ).derived
  /-- The restricted flat-term K-flat model computes the R-side. -/
  restricted_computed : ∀ {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (P : CochainComplex (Modules B) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B) P →
    (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) →
    IsIso ((p (φ ≫ ψ)).counit.app
      (((restriction φ).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)))
  /-- The derived map is represented by the displayed ordinary balanced map. -/
  representative : ∀ {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (hμ : IsIso (flatCoefficientMultiplication p N φ ψ))
    (P : CochainComplex (Modules B) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B) P →
    (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) →
    (derived ψ hμ).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p ψ).counit.app ((HomotopyCategory.quotient _ _).obj P) =
    (p (φ ≫ ψ)).derived.map
        ((N.right_factors φ).hom.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p (φ ≫ ψ)).counit.app
        (((restriction φ).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (ordinary ψ hμ) (.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ _).obj P))
  /-- Adjuncts of arbitrary derived morphisms agree under the comparison. -/
  adjunct : ∀ {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (hμ : IsIso (flatCoefficientMultiplication p N φ ψ))
    (M : DerivedCategory (Modules B)) (Q : DerivedCategory (Modules S))
    (f : M ⟶ (N.right ψ).obj Q),
    ((N.adjunction (φ ≫ ψ)).homEquiv _ _).symm
        ((N.right φ).map f ≫ (N.rightComp φ ψ).hom.app Q) =
      (derived ψ hμ).hom.app M ≫ ((N.adjunction ψ).homEquiv M Q).symm f
  /-- Naturality for a morphism S → S', with the arrows restricted to D(S). -/
  coefficient_naturality : ∀ {S S' : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S) (τ : S ⟶ S')
    (hμ : IsIso (flatCoefficientMultiplication p N φ ψ))
    (hμ' : IsIso (flatCoefficientMultiplication p N φ (ψ ≫ τ)))
    (M : DerivedCategory (Modules B)),
    flatCoefficientChange p N (φ ≫ ψ) τ ((N.right φ).obj M) ≫
        (N.right τ).map
          (eqToHom (congrArg (fun a ↦ (p a).derived.obj ((N.right φ).obj M))
            (Category.assoc φ ψ τ)) ≫ (derived (ψ ≫ τ) hμ').hom.app M) =
      (derived ψ hμ).hom.app M ≫ flatCoefficientChange p N ψ τ M
  /-- Compatibility with successive derived extension under the canonical associators.
  Together with N.associative, this includes every finite iteration. -/
  successive : ∀ {S S' : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S) (τ : S ⟶ S')
    (hμ : IsIso (flatCoefficientMultiplication p N φ ψ))
    (hμ' : IsIso (flatCoefficientMultiplication p N φ (ψ ≫ τ)))
    (M : DerivedCategory (Modules B)),
    (p τ).derived.map ((derived ψ hμ).hom.app M) ≫ (N.derived ψ τ).hom.app M =
      (N.derived (φ ≫ ψ) τ).hom.app ((N.right φ).obj M) ≫
        eqToHom (congrArg (fun a ↦ (p a).derived.obj ((N.right φ).obj M))
          (Category.assoc φ ψ τ)) ≫ (derived (ψ ≫ τ) hμ').hom.app M
  /-- The equal-index case uses the canonical scalar-extension unit identification. -/
  equal_index : ∀ {S : Sheaf J CommRingCat.{r}} (ψ : B ⟶ S)
    (hμ : IsIso (flatCoefficientMultiplication p N φ ψ))
    (M : DerivedCategory (Modules B)),
    (p (𝟙 S)).derived.map ((derived ψ hμ).hom.app M) ≫ flatCoefficientUnit p N ψ M =
      flatCoefficientUnit p N (φ ≫ ψ) ((N.right φ).obj M) ≫ (derived ψ hμ).hom.app M

/-- Flat scalar restriction preserves reduction adjuncts, naturally and coherently.
The `Normalization` parameter supplies the canonical adjunctions and associators of
the existing derived scalar extensions. `exactFunctor` states exactly flatness of B/R;
the multiplication-isomorphism hypothesis is imposed at each coefficient S in the result.

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E, 0D6D and 07A6;
sites-modules.tex, Tag 05V4
(blueprint: lem-weil-pbc-flat-coefficient-reduction-adjunct).

Proof:
1. Resolve a B-complex by a K-flat B-complex P with flat terms (06YS).
Restriction is exact and leaves the underlying abelian sheaf unchanged (07A6).
2. For an acyclic R-complex A, flatness makes B tensor_R A acyclic. Tensor
cancellation (05V4) identifies Tot(Res P tensor_R A) with the restriction of
Tot(P tensor_B (B tensor_R A)). Restriction commutes with direct sums and detects
acyclicity. K-flatness of P proves K-flatness of Res P. The same cancellation
shows each restricted term is flat, so its derived counit is invertible.
3. Cancellation followed by the assumed multiplication isomorphism gives the
ordinary balanced isomorphism, sending x tensor s to x tensor s. Its naturality
on complexes descends through K-flat localization (06YY and site tensor descent),
giving the natural derived isomorphism and its universal-counit representative.
4. Both normalized derived units are x maps to x tensor 1 (07A6). The balanced
map preserves these elements, hence carries the R-unit to the restricted B-unit.
Naturality extends this equality from P to every derived B-object.
5. Transpose the composite of the B-adjunct with the comparison using the R-unit.
Step 4 identifies its transpose with Res(f). Injectivity of the adjunction Hom
bijection gives the asserted equation for every derived morphism f.
6. For S to S', the two ordinary coefficient-change routes send x tensor s to
x tensor tau(s). Localization proves coefficient naturality with the specified
unit-and-associator coefficient arrows.
7. Extension preserves flat-term K-flat complexes (0G7E). Both successive routes
send (x tensor s) tensor t to x tensor tau(s)t, giving the associator equation.
For further extensions all parenthesizations agree by the normalized associativity
law (0D6D). The identity extension sends (x tensor s) tensor t to x tensor st,
which is precisely the specified scalar unit, giving the equal-index equation.
No flatness of S/B or S'/S, boundedness, or chain representative of f is needed. -/
theorem flat_coefficient_reduction_adjunct
    (hflat : exactFunctor (Modules R) (Modules B) (p φ).ordinary) :
    Nonempty (FlatCoefficientReductionComparison p N φ) := by
  sorry

end SheafOfModules
