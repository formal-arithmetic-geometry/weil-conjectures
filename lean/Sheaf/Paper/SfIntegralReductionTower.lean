/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Canonical reduction towers without a finite-field datum

Source: Bhatt--Scholze, Definition 3.5.2, p. 24; Stacks Tags 03EK and 06YY
(blueprint: def-weil-integral-reduction-tower).
The index n means the positive exponent n+1. All scalar extensions are the published
universal derived scalar extensions, with their specified K-flat comparisons.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{u})

/-- The specified abelian sheafification at the coefficient size of this small site.
Source: Stacks Tag 03DA (blueprint: def-weil-integral-reduction-tower). -/
noncomputable instance (priority := 3000) sfAbSheafify (Y : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} Y

/-- The corresponding locally bijective criterion in the same coefficient size.
Source: Stacks Tag 03DA (blueprint: def-weil-integral-reduction-tower). -/
noncomputable instance (priority := 3000) sfAbBijective (Y : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} Y

/-- Ordinary reduction read as a completed-coefficient module.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable abbrev sfReductionRestricted (n : ℕ) :=
  scalarReductionExtension.{u, u} l E X n ⋙ scalarReductionRestriction.{u, u} l E X n

/-- Exact restriction retains its finite-limit structure with all coefficients specified.
Source: Stacks Tag 03CZ (blueprint: def-weil-integral-reduction-tower). -/
noncomputable instance sfRestrictionLimits (n : ℕ) :
    PreservesFiniteLimits (scalarReductionRestriction.{u, u} l E X n) :=
  scalarReductionRestrictionLimits.{u, u} l E X n

/-- Exact restriction retains its finite-colimit structure with all coefficients specified.
Source: Stacks Tag 03CZ (blueprint: def-weil-integral-reduction-tower). -/
noncomputable instance sfRestrictionColimits (n : ℕ) :
    PreservesFiniteColimits (scalarReductionRestriction.{u, u} l E X n) :=
  scalarReductionRestrictionColimits.{u, u} l E X n

/-- Additivity of the fixed scalar-extension functor, with explicit coefficients.
Source: Stacks Tag 03CZ (blueprint: def-weil-integral-reduction-tower). -/
noncomputable instance sfExtensionAdditive (n : ℕ) :
    (scalarReductionExtension.{u, u} l E X n).Additive :=
  scalarReductionExtensionAdditive.{u, u} l E X n

/-- The ordinary reduction followed by restriction is additive.
Source: Stacks Tag 03CZ (blueprint: def-weil-integral-reduction-tower). -/
noncomputable instance sfReductionRestrictedAdditive (n : ℕ) :
    (sfReductionRestricted l E X n).Additive :=
  letI := scalarReductionExtensionAdditive.{u, u} l E X n
  letI := sfRestrictionLimits l E X n
  Functor.additive_of_preserves_binary_products _

/-- Derived reduction read as a completed-coefficient complex.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable abbrev sfDerivedReductionRestricted (n : ℕ) :=
  scalarReductionDerivedExtension.{u, u} l E X n ⋙ scalarReductionDerivedRestriction.{u, u} l E X n

/-- The sheafified pure tensor in the actual scalar-extension construction.
Source: Stacks Tag 03EK (blueprint: def-weil-integral-reduction-tower). -/
noncomputable def sfReductionTensor (n : ℕ) (M : scalarReductionSource.{u, u} l E X)
    (U : X.ProEtᵒᵖ) (s : (integralCoefficientCommRingSheaf l E X n).obj.obj U)
    (x : M.val.obj U) : ((scalarReductionExtension.{u, u} l E X n).obj M).val.obj U :=
  (eqToHom ((scalarReductionExistence.{u, u} l E X n).choose_spec.choose M).symm).val.app U
    ((CategoryTheory.toSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      (SheafOfModules.changeOfRingsPresheaf
        (completedIntegralCommRingProjectionUnrestricted l E X n) M).presheaf).app U
        (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E X).obj.obj U,
          ((completedIntegralCommRingProjectionUnrestricted l E X n).hom.app U).hom] x))

/-- The unique ordinary transition sends s tensor x to rho(s) tensor x.
Source: Stacks Tag 03EK; Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-integral-reduction-tower).
Proof: the quotient projections commute, so the displayed formula is balanced over
completed coefficients. It commutes with restrictions and defines a sheafified tensor
map. Naturality follows on pure tensors. Tensor generation and sheafification give
uniqueness on each module, and hence uniqueness of the natural transformation. -/
theorem sfReductionTransition_existsUnique (n : ℕ) :
    ∃! τ : sfReductionRestricted l E X (n + 1) ⟶ sfReductionRestricted l E X n,
      ∀ (M : scalarReductionSource.{u, u} l E X) (U : X.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf l E X (n + 1)).obj.obj U)
        (x : M.val.obj U),
        (τ.app M).val.app U (sfReductionTensor l E X (n + 1) M U s x) =
          sfReductionTensor l E X n M U
            ((integralCoefficientSheafTransition l E X n).hom.app U s) x := by
  sorry

/-- The transition selected by its unique pure-tensor characterization.
Source: Stacks Tag 03EK (blueprint: def-weil-integral-reduction-tower). -/
noncomputable def sfReductionTransition (n : ℕ) :
    sfReductionRestricted l E X (n + 1) ⟶ sfReductionRestricted l E X n :=
  (sfReductionTransition_existsUnique l E X n).exists.choose

/-- The fixed derived comparison to termwise reduction, invertible on K-flat complexes.
Source: Stacks Tag 06YY (blueprint: def-weil-integral-reduction-tower). -/
noncomputable def sfReductionRepresentativeComparison (n : ℕ)
    (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ) :
    (sfDerivedReductionRestricted l E X n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((sfReductionRestricted l E X n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (scalarReductionDerivedRestriction.{u, u} l E X n).map
      ((scalarReductionCounit.{u, u} l E X n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
    (scalarReductionRestriction.{u, u} l E X n).mapDerivedCategoryFactorsh.hom.app
      (((scalarReductionExtension.{u, u} l E X n).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- The derived transition is uniquely determined by termwise quotient maps on K-flat
representatives. Source: Bhatt--Scholze, Definition 3.5.2; Stacks Tag 06YY
(blueprint: def-weil-integral-reduction-tower).
Proof: compute both derived reductions on a K-flat resolution. The ordinary transition
commutes with differentials and homotopies. A comparison of K-flat resolutions is a
quasi-isomorphism preserved by both reductions, so conjugation by the derived counits
is independent of the resolution and natural in roofs. These conjugates give the
transformation. Every derived object has a K-flat representative, where the counits
are invertible; the displayed equation therefore proves uniqueness. -/
theorem sfDerivedReductionTransition_existsUnique (n : ℕ) :
    ∃! τ : sfDerivedReductionRestricted l E X (n + 1) ⟶
        sfDerivedReductionRestricted l E X n,
      ∀ (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ),
        CochainComplex.IsAcyclicTensorKFlat
          (J := AlgebraicGeometry.Scheme.ProEt.topology X)
          (R := completedIntegralCommRingSheafUnrestricted l E X) P →
        τ.app (DerivedCategory.Q.obj P) ≫ sfReductionRepresentativeComparison l E X n P =
          sfReductionRepresentativeComparison l E X (n + 1) P ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex (sfReductionTransition l E X n) (.up ℤ)).app P) := by
  sorry

/-- The canonical derived quotient transition, with its representative normalization.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def sfDerivedReductionTransition (n : ℕ) :
    sfDerivedReductionRestricted l E X (n + 1) ⟶ sfDerivedReductionRestricted l E X n :=
  (sfDerivedReductionTransition_existsUnique l E X n).exists.choose

/-- The reduction unit, normalized by the published tensor/restriction adjunction.
Source: Stacks Tags 03CZ and 06YY
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def sfDerivedReductionUnit (n : ℕ) :
    𝟭 (DerivedCategory (scalarReductionSource.{u, u} l E X)) ⟶
      sfDerivedReductionRestricted l E X n :=
  (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.unit

/-- The canonical derived reduction tower at all positive coefficient levels.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def sfIntegralReductionTower
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    ℕᵒᵖ ⥤ DerivedCategory (scalarReductionSource.{u, u} l E X) :=
  Functor.ofOpSequence (X := fun n ↦ (sfDerivedReductionRestricted l E X n).obj K)
    (fun n ↦ (sfDerivedReductionTransition l E X n).app K)

/-- The reduction units form a cone over the actual derived quotient transitions.
Source: Bhatt--Scholze, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-integral-reduction-tower).
Proof: on a K-flat representative, the tensor/restriction adjunction unit is the
sheafified map x ↦ 1 tensor x. The quotient transition sends 1 tensor x to
1 tensor x. Thus adjacent transitions commute with the units on representatives,
and hence after localization. Every arrow in the opposite natural-number category
is a composite of consecutive arrows, so induction gives the displayed equation. -/
theorem sfIntegralReductionUnit_naturality
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (i j : ℕᵒᵖ) (g : i ⟶ j) :
    ((Functor.const ℕᵒᵖ).obj K).map g ≫
        (sfDerivedReductionUnit l E X j.unop).app K =
      (sfDerivedReductionUnit l E X i.unop).app K ≫
        (sfIntegralReductionTower l E X K).map g := by
  sorry

/-- The reduction tower together with its canonical compatible maps from K.
Source: Bhatt--Scholze, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def sfIntegralReductionCone
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    Cone (sfIntegralReductionTower l E X K) where
  pt := K
  π :=
    { app := fun n ↦ (sfDerivedReductionUnit l E X n.unop).app K
      naturality := sfIntegralReductionUnit_naturality l E X K }

end WeilConjectures
