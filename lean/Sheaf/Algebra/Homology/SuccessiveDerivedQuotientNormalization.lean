/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.Paper.RingedTopoiTensorSections
import Mathlib.CategoryTheory.Localization.Predicate

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
/-!
# Normalized composition of derived coefficient extensions

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E, 06YY and 07A6
(blueprint: lem-sfb-successive-derived-quotient-normalization).

The scalar-first tensor convention of `changeOfRings` writes the paper's
`(x ⊗ s) ⊗ t` as `t ⊗ (s ⊗ x)`. All the comparison maps below refer to the
existing sheafified extension, its universal left derived pair, and its
localization counit. The auxiliary presentations only bundle these interfaces.
-/

@[expose] public section

set_option autoImplicit false

universe u v r w

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules.SuccessiveDerivedQuotient

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- The existing module-sheaf category, with no new objects or morphisms.
Source: Stacks 03D7 (blueprint: lem-sfb-successive-derived-quotient-normalization). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)

/-- The existing restriction-of-scalars functor.
Source: Stacks 03D7 (blueprint: lem-sfb-successive-derived-quotient-normalization). -/
noncomputable abbrev restriction {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    Modules S ⥤ Modules R :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a)

/-- The sheafification image of a sectionwise scalar-first pure tensor.
Source: Stacks 03EK (blueprint: lem-sfb-successive-derived-quotient-normalization). -/
noncomputable def pure {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : Modules R) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (changeOfRings a M).val.obj U :=
  (CategoryTheory.toSheafify J (changeOfRingsPresheaf a M).presheaf).app U
    (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x)

variable [hD : ∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules R)]

/-- A presentation of the already defined derived coefficient extension. The object and
map equations fix the ordinary functor, and the universal counit fixes the derived pair
up to its unique compatible isomorphism. This bundles the interfaces of 06YY and 07A6;
it introduces no alternative tensor product or derived-category construction.
Source: Stacks 06YY, 07A6 (blueprint: lem-sfb-successive-derived-quotient-normalization). -/
structure Presentation {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) where
  /-- The ordinary, sheafified scalar-extension functor. -/
  ordinary : Modules R ⥤ Modules S
  /-- Its objects are the recorded change-of-rings objects. -/
  obj_eq : ∀ M : Modules R, ordinary.obj M = changeOfRings a M
  /-- Its maps are the recorded sheafified tensor maps. -/
  map_eq : ∀ {M N : Modules R} (f : M ⟶ N), ordinary.map f =
    eqToHom (obj_eq M) ≫ changeOfRingsHom a M f ≫ eqToHom (obj_eq N).symm
  /-- Additivity needed for passage to homotopy categories. -/
  additive : ordinary.Additive
  /-- The unbounded left derived functor. -/
  derived : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S)
  /-- The universal left-derived computation morphism. -/
  counit : DerivedCategory.Qh ⋙ derived ⟶
    @Functor.mapHomotopyCategory _ _ _ _ _ _ _ ordinary additive (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh
  /-- The universal property, rather than a freely chosen computation map. -/
  universal : derived.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (Modules R) (ComplexShape.up ℤ))

attribute [instance] Presentation.additive

/-- A pure section of the presented ordinary extension, transported only by `obj_eq`.
Source: Stacks 03EK (blueprint: lem-sfb-successive-derived-quotient-normalization). -/
noncomputable def sectionTensor {R S : Sheaf J CommRingCat.{r}} {a : R ⟶ S}
    (p : Presentation a) (M : Modules R) (U : Cᵒᵖ) (s : S.obj.obj U)
    (x : M.val.obj U) : (p.ordinary.obj M).val.obj U :=
  (eqToHom (p.obj_eq M).symm).val.app U (pure a M U s x)


/-- The canonical coefficient-change square made from two composition comparisons.
The equality is the commuting square of ring maps, not a chosen module comparison.
Source: Stacks 0D6D (blueprint: lem-sfb-successive-derived-quotient-normalization). -/
noncomputable def squareComparison
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (δ : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
      (p a).derived ⋙ (p b).derived ≅ (p (a ≫ b)).derived)
    {R S R' S' : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (a' : R' ⟶ S')
    (α : R ⟶ R') (β : S ⟶ S') (h : a ≫ β = α ≫ a') :
    (p a).derived ⋙ (p β).derived ≅ (p α).derived ⋙ (p a').derived :=
  δ a β ≪≫ eqToIso (congrArg (fun f ↦ (p f).derived) h) ≪≫ (δ α a').symm

/-- The complete normalized, coherent family of successive extensions. The fields
spell out the tensor formulas, their descent through the universal counits, the
restriction identifications, the scalar-extension units, and coefficient naturality.
Source: Stacks 0D6D, 0G7E, 06YY and 07A6
(blueprint: lem-sfb-successive-derived-quotient-normalization). -/
structure Normalization
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a) where
  /-- The actual ordinary scalar-extension comparison, natural in the module. -/
  ordinary : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    (p a).ordinary ⋙ (p b).ordinary ≅ (p (a ≫ b)).ordinary
  /-- The forward tensor formula, in the scalar-first convention. -/
  ordinary_hom : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) (t : T.obj.obj U),
    ((ordinary a b).hom.app M).val.app U
      (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
      sectionTensor (p (a ≫ b)) M U ((b.hom.app U).hom s * t) x
  /-- The inverse tensor formula. -/
  ordinary_inv : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (t : T.obj.obj U),
    ((ordinary a b).inv.app M).val.app U (sectionTensor (p (a ≫ b)) M U t x) =
      sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U 1 x)
  /-- The derived comparison is a natural isomorphism, not just objectwise existence. -/
  derived : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    (p a).derived ⋙ (p b).derived ≅ (p (a ≫ b)).derived
  /-- Canonical computation is invertible on each flat-term K-flat representative. -/
  computed : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    IsIso ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P))
  /-- The second computation is also invertible on the extended representative. -/
  intermediate_computed : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    IsIso ((p b).counit.app
      (((p a).ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)))
  /-- The derived comparison is represented by the displayed termwise tensor comparison. -/
  representative : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    (derived a b).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p (a ≫ b)).counit.app ((HomotopyCategory.quotient _ _).obj P) =
    (p b).derived.map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p b).counit.app (((p a).ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (ordinary a b) (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ _).obj P))
  /-- Ordinary extension/restriction adjunctions. -/
  ordinaryAdjunction : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    (p a).ordinary ⊣ restriction a
  /-- The units are the specified scalar-extension units. -/
  ordinary_unit : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Modules R)
    (U : Cᵒᵖ) (x : M.val.obj U),
    ((ordinaryAdjunction a).unit.app M).val.app U x = sectionTensor (p a) M U 1 x
  /-- Termwise restriction on unbounded derived categories. -/
  right : ∀ {R S : Sheaf J CommRingCat.{r}} (_a : R ⟶ S),
    DerivedCategory (Modules S) ⥤ DerivedCategory (Modules R)
  /-- Its canonical localization factorization. -/
  right_factors : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    DerivedCategory.Qh ⋙ right a ≅
      (restriction a).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  /-- The normalized derived coefficient adjunction. -/
  adjunction : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), (p a).derived ⊣ right a
  /-- Normalization of its unit through the universal derived computation. -/
  adjunction_normalization : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    (adjunction a).unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (right a).map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (right_factors a).hom.app
        (((p a).ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) =
    DerivedCategory.Qh.map
      (((ordinaryAdjunction a).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj P))
  /-- Ordinary composite restriction leaves every underlying section unchanged. -/
  restrictionComp : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    restriction b ⋙ restriction a ≅ restriction (a ≫ b)
  /-- It is the identity on underlying sheaves, not an arbitrary comparison. -/
  restrictionComp_sections : ∀ {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (N : Modules T) (U : Cᵒᵖ) (x : N.val.obj U),
    ((restrictionComp a b).hom.app N).val.app U x = x
  /-- The induced comparison between derived restrictions. -/
  rightComp : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    right b ⋙ right a ≅ right (a ≫ b)
  /-- The comparison is the localization of the ordinary identity on sections. -/
  rightComp_normalization : ∀ {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T)
    (H : HomotopyCategory (Modules T) (ComplexShape.up ℤ)),
    (rightComp a b).hom.app (DerivedCategory.Qh.obj H) ≫
      (right_factors (a ≫ b)).hom.app H =
    (right a).map ((right_factors b).hom.app H) ≫
      (right_factors a).hom.app
        (((restriction b).mapHomotopyCategory (ComplexShape.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (restrictionComp a b)
          (ComplexShape.up ℤ)).hom.app H)
  /-- The composite scalar-extension unit is the unit for the composite ring map. -/
  unit_comp : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (X : DerivedCategory (Modules R)),
    (adjunction a).unit.app X ≫
      (right a).map ((adjunction b).unit.app ((p a).derived.obj X)) ≫
      (rightComp a b).hom.app ((p b).derived.obj ((p a).derived.obj X)) ≫
      (right (a ≫ b)).map ((derived a b).hom.app X) = (adjunction (a ≫ b)).unit.app X
  /-- All parenthesizations of three successive extensions agree. This gives agreement
  for every finite iteration by the usual induction on parenthesizations. -/
  associative : ∀ {R S T V : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ V) (X : DerivedCategory (Modules R)),
    (p c).derived.map ((derived a b).hom.app X) ≫ (derived (a ≫ b) c).hom.app X =
      (derived b c).hom.app ((p a).derived.obj X) ≫ (derived a (b ≫ c)).hom.app X ≫
        eqToHom (congrArg (fun f ↦ (p f).derived.obj X) (Category.assoc a b c).symm)
  /-- Naturality in a commuting diagram of composable coefficient maps: pasting its
  two squares gives the outer square, compatibly with the composition comparison.
  The outer equality merely records the composite of the two commuting squares. -/
  coefficient_naturality : ∀ {R S T R' S' T' : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R' ⟶ S') (b' : S' ⟶ T')
    (α : R ⟶ R') (β : S ⟶ S') (γ : T ⟶ T')
    (ha : a ≫ β = α ≫ a') (hb : b ≫ γ = β ≫ b')
    (hab : (a ≫ b) ≫ γ = α ≫ (a' ≫ b')) (X : DerivedCategory (Modules R)),
    (p γ).derived.map ((derived a b).hom.app X) ≫
      (squareComparison p derived (a ≫ b) (a' ≫ b') α γ hab).hom.app X =
    (squareComparison p derived b b' β γ hb).hom.app ((p a).derived.obj X) ≫
      (p b').derived.map ((squareComparison p derived a a' α β ha).hom.app X) ≫
      (derived a' b').hom.app ((p α).derived.obj X)

/-- Successive derived scalar extensions have their canonical tensor comparison, inverse,
unit normalization, coefficient naturality and coherent finite iteration. This is a
family statement, so naturality concerns arbitrary derived morphisms as well as changing
coefficient rings. No ring map is required to be flat or surjective, and no complex is
required to be bounded. Ordinary rings are the specialization to the singleton category
with the bottom (identity-cover) topology.

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E, 06YS, 06YY and 07A6
(blueprint: lem-sfb-successive-derived-quotient-normalization).

Proof:
1. Use lem-pur-derived-change-of-rings to present each ordinary extension and its
universal unbounded left-derived pair. Resolve each input by a flat-term K-flat complex
using lem-pc-kflat-resolution (06YS), without assuming functorial resolutions.
2. By lem-weil-pbc-ringed-topos-kflat-pullback (0G7E), applied to identity inverse image,
the first and successive ordinary extensions remain flat-term K-flat; 06YY computes the
derived extensions by these complexes and preserves quasi-isomorphisms between them.
3. On sections define the two maps by the formulas in ordinary_hom and ordinary_inv.
Balancing over R uses b(a(r)s)=b(a(r))b(s); balancing over S uses multiplicativity of b.
The inverse moves the middle scalar across the outer tensor. Restrictions commute with
these formulas. The section calculus of def-weil-pbc-ringed-tensor-section-calculus
and the actual sheafification construction of def-pur-sheaf-tensor-product show that
they are mutually inverse sheaf morphisms. They commute with the complex differential.
4. These maps are natural for termwise morphisms, hence also homotopies. Apply the
flat-term K-flat localization equivalence of lem-weil-pbc-site-derived-tensor-descent
and clauses (2),(3) of lem-weil-pbc-localization-universal-property to descend the
comparison and its inverse. The universal 06YY counits give representative exactly;
uniqueness makes this independent of the resolution and all comparison choices.
5. Use lem-pur-sheaf-ring-derived-coefficient-adjunction (07A6) to normalize ordinary
and derived units. The composite sends x to 1 tensor (1 tensor x), which the comparison
sends to 1 tensor x. Exact restriction leaves underlying sheaves unchanged. Descent and
naturality give unit_comp at every derived input.
6. On triple tensors both collapses multiply the images of all scalars in the final
ring, in order. Multiplicativity and associativity give associative; induction on
parenthesizations gives every finite iteration, including identity ring maps.
7. In a commuting coefficient diagram the two formulas agree because b' beta=gamma b
and all vertical maps preserve one. Compute derived coefficient change using the
flat-term K-flat complex P tensor_R R'. Localization preserves these identities;
associative gives the displayed coefficient_naturality pasting equation.
8. On the singleton identity-cover site sheafification is identity and module sheaves
are ordinary modules. Thus the same statement includes ordinary, possibly nonflat,
quotient maps, zero coefficients and unbounded complexes. -/
theorem successive_derived_quotient_normalization :
    ∃ p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a,
      Nonempty (Normalization p) := by
  sorry

end SheafOfModules.SuccessiveDerivedQuotient
