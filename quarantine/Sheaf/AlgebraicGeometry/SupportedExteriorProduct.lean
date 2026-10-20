/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSupportedSections
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-!
# The supported exterior product

Source: blueprint, sec-smooth-purity/sk-prop-a1-kummer,
`def-pur-supported-exterior-product`, pulling back supported sections and tensoring them
(blueprint: def-pur-supported-exterior-product).

Supported coefficients are closed direct images of constant modules. The ordinary
adjunction is normalized by the quotient from constant coefficients. Its derived
adjunction and the coefficient tensor comparison specify the supported pairing.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

/-- Use the existing monoidal sheafification instance at the fixed coefficient ring.
Source: blueprint `def-pur-supported-exterior-product`, tensor construction
(blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedSheaf_isMonoidal (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) : (X.smallEtaleTopology.W (A := ModuleCat.{u + 1} A)).IsMonoidal :=
  GrothendieckTopology.W.monoidal

/-- Use the existing preadditive tensor structure without reopening sheafification
instance search under each tensor-complex binder.
Source: blueprint `def-pur-supported-exterior-product`, tensor construction
(blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedSheaf_monoidalPreadditive (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) : MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  Sheaf.monoidalPreadditive

section TensorWrappers

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

/-- The existing monoidal sheafification property, with generic coefficients.
Source: blueprint tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedSheaf_isMonoidalGeneric (X : Scheme.{u}) :
    (X.smallEtaleTopology.W (A := C)).IsMonoidal := GrothendieckTopology.W.monoidal

/-- The existing preadditive tensor structure, with generic coefficients.
Source: blueprint tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedSheaf_monoidalPreadditiveGeneric (X : Scheme.{u}) :
    MonoidalPreadditive (Sheaf X.smallEtaleTopology C) := Sheaf.monoidalPreadditive

/-- The existing sheaf tensor bifunctor at a variable scheme.
Source: blueprint constant tensor pairing (blueprint: def-pur-supported-exterior-product). -/
@[implicit_reducible]
noncomputable def supportedSheafTensorGeneric (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology C :=
      curriedTensor _

/-- Additivity of the upstream sheaf tensor in its first variable.
Source: blueprint tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedSheafTensorGeneric_additive (X : Scheme.{u}) :
    (supportedSheafTensorGeneric C X).Additive :=
  inferInstanceAs (curriedTensor (Sheaf X.smallEtaleTopology C)).Additive

/-- Additivity of the upstream sheaf tensor in its second variable.
Source: blueprint tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedSheafTensorGeneric_obj_additive (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology C) : ((supportedSheafTensorGeneric C X).obj M).Additive :=
  inferInstanceAs (tensorLeft M).Additive

/-- The signed complex tensor at a variable scheme, using the upstream structure.
Source: blueprint signed tensor pairing (blueprint: def-pur-supported-exterior-product). -/
@[implicit_reducible]
noncomputable def supportedComplexTensorGeneric (X : Scheme.{u}) :
    CochainComplex (Sheaf X.smallEtaleTopology C) ℤ ⥤
      CochainComplex (Sheaf X.smallEtaleTopology C) ℤ ⥤
        CochainComplex (Sheaf X.smallEtaleTopology C) ℤ := curriedTensor _

/-- The signed total tensor object, using the existing total complex construction.
Source: blueprint signed tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedTotalTensorGeneric (X : Scheme.{u})
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) :=
  HomologicalComplex.tensorObj (C := Sheaf X.smallEtaleTopology C) (c := .up ℤ) P Q

/-- The upstream complex tensor has the signed total complex as its object.
Source: blueprint signed total construction (blueprint: def-pur-supported-exterior-product).
Proof: unfold the upstream cochain monoidal structure and its curried tensor functor.
Its object field is precisely HomologicalComplex.tensorObj with the same direct sums
and Koszul differential; colimit-existence proofs are equal by proof irrelevance. -/
theorem supportedComplexTensorGeneric_eq (X : Scheme.{u})
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) :
    ((supportedComplexTensorGeneric C X).obj P).obj Q =
      supportedTotalTensorGeneric C X P Q := by
  sorry

/-- Localization comparison, retaining its canonical identification with the signed
total tensor. Source: blueprint K-flat derivation
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedDerivedTensorLocalizationGeneric (X : Scheme.{u})
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) :
    ((derivedTensor C X).obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q) ⟶
      DerivedCategory.Q.obj (supportedTotalTensorGeneric C X P Q) :=
  Functor.LaxMonoidal.μ DerivedCategory.Q P Q ≫
    DerivedCategory.Q.map (eqToHom (supportedComplexTensorGeneric_eq C X P Q))

/-- Canonical inclusion of a tensor bidegree in the signed total complex.
Source: blueprint signed tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedTensorInclusionGeneric (X : Scheme.{u})
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (r s n : ℤ) (h : r + s = n) :=
  HomologicalComplex.ιTensorObj (C := Sheaf X.smallEtaleTopology C) (c := .up ℤ) P Q r s n h

/-- Tensor two sheaf morphisms using the upstream bifunctor.
Source: blueprint constant tensor pairing (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedSheafTensorMapGeneric (X : Scheme.{u})
    {M M' N N' : Sheaf X.smallEtaleTopology C} (a : M ⟶ M') (b : N ⟶ N') :
    ((supportedSheafTensorGeneric C X).obj M).obj N ⟶
      ((supportedSheafTensorGeneric C X).obj M').obj N' :=
  ((supportedSheafTensorGeneric C X).map a).app N ≫
    ((supportedSheafTensorGeneric C X).obj M').map b

end TensorWrappers

/-- Sheaf tensor with the specified coefficient ring.
Source: blueprint tensor convention (blueprint: def-pur-supported-exterior-product). -/
noncomputable abbrev supportedSheafTensor (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) := supportedSheafTensorGeneric (ModuleCat.{u + 1} A) X

/-- Complex tensor with the specified coefficient ring.
Source: blueprint tensor convention (blueprint: def-pur-supported-exterior-product). -/
noncomputable abbrev supportedComplexTensor (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) := supportedTotalTensorGeneric (ModuleCat.{u + 1} A) X

/-- Closed supported constant coefficients. Source: blueprint
`def-pur-supported-exterior-product`, supported-section construction
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficients (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    ModuleCat.{u + 1} A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    lowerStar (ModuleCat.{u + 1} A) i

/-- The quotient from constant coefficients to closed supported coefficients.
Source: blueprint `def-pur-supported-exterior-product`, open-closed coefficient sequence
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientQuotient (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) (M : ModuleCat.{u + 1} A) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⟶
      (supportedCoefficients A i).obj M :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).hom.app M)

/-- Additivity of closed supported coefficients. Source: blueprint
`def-pur-supported-exterior-product` (blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedCoefficients_additive
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (supportedCoefficients A i).Additive :=
  inferInstanceAs ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    lowerStar (ModuleCat.{u + 1} A) i).Additive)

/-- Exactness of closed supported coefficients.
Source: blueprint `def-pur-supported-exterior-product`, closed-support construction
(blueprint: def-pur-supported-exterior-product).
Proof: at a geometric point the closed direct image of a constant module has stalk
that module on the closed subset and zero outside. Both functors on modules are exact.
Exact and conservative geometric stalks detect finite limits and finite colimits.
The same argument handles the empty closed subscheme. -/
theorem supportedCoefficients_exact (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteLimits (supportedCoefficients A i) ∧
      PreservesFiniteColimits (supportedCoefficients A i) := by
  sorry

/-- The finite-limit instance from closed-support exactness. Source: blueprint
`def-pur-supported-exterior-product` (blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedCoefficients_preservesFiniteLimits
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteLimits (supportedCoefficients A i) := (supportedCoefficients_exact A i).1

/-- The finite-colimit instance from closed-support exactness. Source: blueprint
`def-pur-supported-exterior-product` (blueprint: def-pur-supported-exterior-product). -/
noncomputable instance supportedCoefficients_preservesFiniteColimits
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteColimits (supportedCoefficients A i) := (supportedCoefficients_exact A i).2

/-- The ordinary adjunction, uniquely normalized by inclusion of the support kernel.
Source: blueprint `def-pur-supported-exterior-product`, supported-section construction
(blueprint: def-pur-supported-exterior-product).
Proof: apply Hom into F to the open-closed sequence of constant M. The kernel of
restriction is Hom from M into the kernel defining supported sections. The quotient
is epic, so precomposition determines the Hom equivalence uniquely. Naturality of
restriction gives naturality in both variables and hence the adjunction. -/
theorem exists_unique_supportedCoefficientAdjunction
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃! a : supportedCoefficients A i ⊣ supportedEtaleSections A X i.openComplement,
      ∀ (M : ModuleCat.{u + 1} A)
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
        (f : M ⟶ (supportedEtaleSections A X i.openComplement).obj F),
      supportedCoefficientQuotient A i M ≫ (a.homEquiv M F).symm f =
        ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv M F).symm
          (f ≫ (supportedEtaleSectionsι A X i.openComplement).app F) := by
  sorry

/-- Canonical ordinary supported-coefficient adjunction, selected from its unique
normalization. Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientAdjunction
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    supportedCoefficients A i ⊣ supportedEtaleSections A X i.openComplement :=
  (exists_unique_supportedCoefficientAdjunction A i).choose

/-- The unbounded support functor, extending the bounded-below injective construction.
Source: blueprint `def-pur-supported-exterior-product`, derived support resolutions
(blueprint: def-pur-supported-exterior-product). -/
noncomputable abbrev supportedSectionsDerived
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :=
  (supportedEtaleSections A X i.openComplement).rightDerivedFunctor

/-- Derive the normalized ordinary adjunction with its exact left adjoint.
Source: blueprint `def-pur-supported-exterior-product`, K-flat and injective derivation
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientDerivedAdjunction
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (supportedCoefficients A i).mapDerivedCategory ⊣ supportedSectionsDerived A i :=
  (supportedCoefficientAdjunction A i).mapDerivedCategoryRightDerivedAdjunction

/-- The closed immersion of the product of the two supports.
Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedProductImmersion {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y) :
    pullback (i ≫ f) (j ≫ g) ⟶ pullback f g :=
  pullback.map (i ≫ f) (j ≫ g) f g i j (𝟙 B) (by simp) (by simp)

/-- Closedness of the product support. Source: blueprint
`def-pur-supported-exterior-product` (blueprint: def-pur-supported-exterior-product).
Proof: the product map is the composite of the two base changes of the closed
immersions. Closed immersions are stable under base change and composition. -/
@[instance]
theorem supportedProductImmersion_isClosedImmersion {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsClosedImmersion (supportedProductImmersion f g i j) := by
  sorry

/-- The pointwise constant-presheaf tensor comparison.
Source: blueprint `def-pur-supported-exterior-product`, constant section tensor
(blueprint: def-pur-supported-exterior-product). -/
def constantPresheafTensor (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (M N : ModuleCat.{u + 1} A) :
    (Functor.const T.Etaleᵒᵖ).obj (M ⊗ N) ⟶
      (Functor.const T.Etaleᵒᵖ).obj M ⊗ (Functor.const T.Etaleᵒᵖ).obj N where
  app _ := 𝟙 _
  naturality _ _ _ := by simp

/-- Constant coefficient tensor comparison before pulling back either factor.
Source: blueprint constant section pairing (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedConstantTensor (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (M N : ModuleCat.{u + 1} A) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (M ⊗ N) ⟶
      ((supportedSheafTensor A X).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N) :=
  (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
      (constantPresheafTensor A X M N) ≫
    (Functor.Monoidal.μIso (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      ((Functor.const _).obj M) ((Functor.const _).obj N)).inv

/-- Tensor comparison for constant coefficients and the two projection pullbacks.
Source: blueprint `def-pur-supported-exterior-product`, constant section pairing
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def constantExteriorTensor (A : Type (u + 1)) [CommRing A]
    {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (M N : ModuleCat.{u + 1} A) :
    (constantSheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)).obj (M ⊗ N) ⟶
      ((supportedSheafTensor A (pullback f g)).obj
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M))).obj
      ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N)) :=
  supportedConstantTensor A (pullback f g) M N ≫
    supportedSheafTensorMapGeneric (ModuleCat.{u + 1} A) (pullback f g)
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (pullback.fst f g)).inv.app M)
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (pullback.snd f g)).inv.app N)

/-- Supported coefficients pulled back along the first projection.
Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product). -/
noncomputable abbrev supportedFirstCoefficients (A : Type (u + 1)) [CommRing A]
    {B X Y Z : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) :=
  supportedCoefficients A i ⋙ upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)

/-- Supported coefficients pulled back along the second projection.
Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product). -/
noncomputable abbrev supportedSecondCoefficients (A : Type (u + 1)) [CommRing A]
    {B X Y W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (j : W ⟶ Y) :=
  supportedCoefficients A j ⋙ upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)

/-- The supported coefficient tensor comparison is uniquely fixed by the quotient
of constant sections. Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product).
Proof: the target is zero off the intersection of the two inverse-image supports,
so the constant section pairing factors through the open-closed coefficient quotient.
That quotient is epic, giving uniqueness. On the intersection all maps are the
identity on M tensor N; elsewhere both supported coefficients are zero. Geometric
stalks detect that the resulting comparison is an isomorphism. -/
theorem exists_unique_supportedCoefficientTensor
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (M N : ModuleCat.{u + 1} A) :
    ∃! t : (supportedCoefficients A (supportedProductImmersion f g i j)).obj (M ⊗ N) ⟶
        ((supportedSheafTensor A (pullback f g)).obj
          ((supportedFirstCoefficients A f g i).obj M)).obj
          ((supportedSecondCoefficients A f g j).obj N),
      supportedCoefficientQuotient A (supportedProductImmersion f g i j) (M ⊗ N) ≫ t =
        constantExteriorTensor A f g M N ≫
          supportedSheafTensorMapGeneric (ModuleCat.{u + 1} A) (pullback f g)
            ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).map
              (supportedCoefficientQuotient A i M))
            ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).map
              (supportedCoefficientQuotient A j N)) := by
  sorry

/-- The uniquely normalized supported coefficient tensor comparison.
Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientTensor
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (M N : ModuleCat.{u + 1} A) :=
  (exists_unique_supportedCoefficientTensor A f g i j M N).choose


/-- The morphism type for the signed complex coefficient comparison.
Source: blueprint supported tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientTensorComplexHom
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (P Q : CochainComplex (ModuleCat.{u + 1} A) ℤ) : Type (u + 1) :=
    ((supportedCoefficients A (supportedProductImmersion f g i j)).mapHomologicalComplex
        (.up ℤ)).obj (P ⊗ Q) ⟶
      supportedComplexTensor A (pullback f g)
        (((supportedFirstCoefficients A f g i).mapHomologicalComplex (.up ℤ)).obj P)
        (((supportedSecondCoefficients A f g j).mapHomologicalComplex (.up ℤ)).obj Q)

/-- The complete normalization of the signed complex coefficient comparison.
Source: blueprint supported tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientTensorComplexCondition
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (P Q : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (t : supportedCoefficientTensorComplexHom A f g i j P Q) : Prop :=
      ∀ (r s n : ℤ) (h : r + s = n),
        (supportedCoefficients A (supportedProductImmersion f g i j)).map
            (HomologicalComplex.ιTensorObj P Q r s n h) ≫ t.f n =
          supportedCoefficientTensor A f g i j (P.X r) (Q.X s) ≫
            supportedTensorInclusionGeneric (ModuleCat.{u + 1} A) (pullback f g)
              (((supportedFirstCoefficients A f g i).mapHomologicalComplex (.up ℤ)).obj P)
              (((supportedSecondCoefficients A f g j).mapHomologicalComplex (.up ℤ)).obj Q)
              r s n h

/-- Totalization of the supported coefficient tensor map, characterized on every
bidegree summand, with the usual cochain signs.
Source: blueprint `def-pur-supported-exterior-product`, K-flat construction
(blueprint: def-pur-supported-exterior-product).
Proof: closed supported coefficients preserve direct sums, being a left adjoint.
Use their canonical coproduct comparison and the coefficient tensor comparison on
each summand. Naturality commutes with the two differentials, including the sign
(-1)^r in the second differential. The coproduct universal property gives uniqueness. -/
theorem exists_unique_supportedCoefficientTensorComplex
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (P Q : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    ∃! t : supportedCoefficientTensorComplexHom A f g i j P Q,
      supportedCoefficientTensorComplexCondition A f g i j P Q t := by
  sorry

/-- The signed total complex coefficient map, selected by its summand characterization.
Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientTensorComplex
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (P Q : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    supportedCoefficientTensorComplexHom A f g i j P Q :=
  (exists_unique_supportedCoefficientTensorComplex A f g i j P Q).choose

/-- Tensor morphisms through the existing derived bifunctor at a variable scheme.
Source: blueprint supported pairing (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedDerivedTensorMap (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u})
    {M M' N N' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (a : M ⟶ M') (b : N ⟶ N') :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj N ⟶
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj M').obj N' :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).map a).app N ≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj M').map b

/-- The canonical tensor localization comparison with the specified ring.
Source: blueprint K-flat derivation (blueprint: def-pur-supported-exterior-product). -/
noncomputable abbrev supportedDerivedTensorLocalization (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :=
  supportedDerivedTensorLocalizationGeneric (ModuleCat.{u + 1} A) X

/-- The morphism type for the signed derived coefficient comparison.
Source: blueprint supported tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientTensorDerivedHom
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] : Type (u + 2) :=
    ∀ M N : DerivedCategory (ModuleCat.{u + 1} A),
      (supportedCoefficients A (supportedProductImmersion f g i j)).mapDerivedCategory.obj
          (M ⊗ N) ⟶
        ((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).obj
          ((supportedFirstCoefficients A f g i).mapDerivedCategory.obj M)).obj
          ((supportedSecondCoefficients A f g j).mapDerivedCategory.obj N)

/-- The complete normalization of the signed derived coefficient comparison.
Source: blueprint supported tensor construction (blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientTensorDerivedCondition
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (t : supportedCoefficientTensorDerivedHom A f g i j) : Prop :=
      (∀ (M M' N N' : DerivedCategory (ModuleCat.{u + 1} A))
        (a : M ⟶ M') (b : N ⟶ N'),
        (supportedCoefficients A (supportedProductImmersion f g i j)).mapDerivedCategory.map
            (a ⊗ₘ b) ≫ t M' N' = t M N ≫
          supportedDerivedTensorMap A (pullback f g)
            ((supportedFirstCoefficients A f g i).mapDerivedCategory.map a)
            ((supportedSecondCoefficients A f g j).mapDerivedCategory.map b)) ∧
      (∀ P Q : CochainComplex (ModuleCat.{u + 1} A) ℤ,
        (supportedCoefficients A (supportedProductImmersion f g i j)).mapDerivedCategory.map
            (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          (supportedCoefficients A
            (supportedProductImmersion f g i j)).mapDerivedCategoryFactors.hom.app
            (P ⊗ Q) ≫
          DerivedCategory.Q.map (supportedCoefficientTensorComplex A f g i j P Q) =
        t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
          supportedDerivedTensorMap A (pullback f g)
            ((supportedFirstCoefficients A f g i).mapDerivedCategoryFactors.hom.app P)
            ((supportedSecondCoefficients A f g j).mapDerivedCategoryFactors.hom.app Q) ≫
          supportedDerivedTensorLocalization A (pullback f g)
            (((supportedFirstCoefficients A f g i).mapHomologicalComplex (.up ℤ)).obj P)
            (((supportedSecondCoefficients A f g j).mapHomologicalComplex (.up ℤ)).obj Q))

/-- The coefficient comparison after localization, with its full complex-model
normalization and naturality, rather than an unspecified isomorphism.
Source: blueprint `def-pur-supported-exterior-product`, K-flat tensor derivation
(blueprint: def-pur-supported-exterior-product).
Proof: choose K-flat module complexes with flat terms. Closed supported coefficients
and their projection inverse images preserve these properties: on a stalk their
coefficient sheaves are A or zero, and tensor with each is exact. The signed total
comparison above is an isomorphism on each stalk. Localize it and use the K-flat
localization equivalence to descend it naturally in both variables. Its compatibility
with the tensor localization counits is the displayed equation, also for other
complexes by naturality. Every derived object is isomorphic to the localization of
a K-flat model, and the localization tensor counits are isomorphisms on such models;
therefore that equation and naturality determine the family uniquely. -/
theorem exists_unique_supportedCoefficientTensorDerived
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    ∃! t : supportedCoefficientTensorDerivedHom A f g i j,
      supportedCoefficientTensorDerivedCondition A f g i j t := by
  sorry

/-- The derived coefficient comparison with its uniquely specified model normalization.
Source: blueprint `def-pur-supported-exterior-product`
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedCoefficientTensorDerived
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
      (supportedCoefficients A (supportedProductImmersion f g i j)).mapDerivedCategory.obj
          (M ⊗ N) ⟶
        ((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).obj
          ((supportedFirstCoefficients A f g i).mapDerivedCategory.obj M)).obj
          ((supportedSecondCoefficients A f g j).mapDerivedCategory.obj N) :=
  (exists_unique_supportedCoefficientTensorDerived A f g i j).choose M N

/-- Pull back the supported evaluation counit along the first projection, retaining
all exact-functor and total-derived pullback comparisons.
Source: blueprint `def-pur-supported-exterior-product`, evaluation construction
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedFirstEvaluation
    (A : Type (u + 1)) [CommRing A] {B X Y Z : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) [IsClosedImmersion i]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (Functor.mapDerivedCategoryCompIso (supportedCoefficients A i)
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g))).hom.app
        ((supportedSectionsDerived A i).obj K) ≫
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).mapDerivedCategory.map
      ((supportedCoefficientDerivedAdjunction A i).counit.app K) ≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
      (pullback.fst f g)).inv.app K

/-- Pull back the supported evaluation counit along the second projection.
Source: blueprint `def-pur-supported-exterior-product`, evaluation construction
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def supportedSecondEvaluation
    (A : Type (u + 1)) [CommRing A] {B X Y W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (j : W ⟶ Y) [IsClosedImmersion j]
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (Functor.mapDerivedCategoryCompIso (supportedCoefficients A j)
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g))).hom.app
        ((supportedSectionsDerived A j).obj L) ≫
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).mapDerivedCategory.map
      ((supportedCoefficientDerivedAdjunction A j).counit.app L) ≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
      (pullback.snd f g)).inv.app L

/-- The supported exterior product: the adjoint of the coefficient tensor comparison
followed by the tensor of the two supported evaluation counits.
Source: blueprint `def-pur-supported-exterior-product`, supported-section construction
(blueprint: def-pur-supported-exterior-product). The comparison is normalized on every
cochain bidegree, so this is the actual supported section pairing. In the bounded-below
case the total support functor agrees with injective support resolutions. -/
noncomputable def supportedExteriorProduct
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (supportedSectionsDerived A i).obj K ⊗ (supportedSectionsDerived A j).obj L ⟶
      (supportedSectionsDerived A (supportedProductImmersion f g i j)).obj
        (externalProduct (ModuleCat.{u + 1} A) f g K L) :=
  (supportedCoefficientDerivedAdjunction A (supportedProductImmersion f g i j)).homEquiv _ _
    (supportedCoefficientTensorDerived A f g i j
        ((supportedSectionsDerived A i).obj K) ((supportedSectionsDerived A j).obj L) ≫
      supportedDerivedTensorMap A (pullback f g)
        (supportedFirstEvaluation A f g i K) (supportedSecondEvaluation A f g j L))

end AlgebraicGeometry.Etale
