/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.FiniteRestrictionDiagramModels
import Sheaf.Paper.FiniteRestrictionStrictTransport
import Sheaf.Paper.FiniteRestrictionConstructibleVertices
import Sheaf.Paper.PodReindexingCompletionUnitTensor
import Sheaf.Paper.FiniteTorStability

/-! # Semilinear naturality of finite-fibre restriction diagrams -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard WeilConjectures.scalarReductionExistence
  WeilConjectures.scalarReductionDerivedExistence SheafOfModules.monoidalCategory

universe u d e d' e'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.FiniteRestrictionNaturality
open FiniteCounitTowers

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {k : Type u} [Field k] (G : Diagram k)

private theorem square_image_commutes {A : Type d} [Category.{e} A]
    {A' : Type d'} [Category.{e'} A'] (S : Square A) (h : S.Commutes) (F : A ⥤ A') :
    (S.image F).Commutes :=
  Functor.map_commSq F h

private theorem square_restrict_commutes {A : Type d} [Category.{e} A]
    (S : Square A) (P : ObjectProperty A) (h : S.Vertices P) (hS : S.Commutes) :
    (S.restrict P h).Commutes := by
  constructor
  apply ObjectProperty.hom_ext
  exact hS.w

/-- Strict semilinear diagram naturality and its completed, rational and point images.

Source: blueprint sec-deligne-laumon-a1/sk-thm-dl-a1-upper,
lem-zl-finite-pushforward.proof.md, finite-stalk and permutation sentences;
Stacks Tags 0959, 03QP, 09A5 and 0941
(blueprint: lem-zl-finite-restriction-diagram-naturality).

Proof, following the eight DAG steps:
1. geometry and point_paths compute the fibre isomorphism and point permutation.
No equation involving the original finite subfield is used.
2. Reindex the sites along u,w,t,c. Constant sections and every quotient projection
fix the coefficient action. Relabelling preserves termwise flatness and K-flatness;
use lem-pod-isomorphism-field-transport to identify the prescribed integral input.
3. Under these identifications the adjunct of exchange is v* of the f-counit.
The primed adjunct is the same word, by the two geometric path equations.
The adjunction bijection gives exchangeSquare.Commutes, for entire system complexes.
4. A component of restriction is pullback of the h-counit. The equation t i_x=i_x' c
identifies its germ with the same restricted section. A module morphism commutes
with restriction, as does every quotient map. Product projections give exactly
sum, so restrictionSquare.Commutes, with the specified permutation and stalk maps.
Use lem-zl-finite-counit-restriction-towers for independence of representatives.
5. The strict squares commute with the system transitions. The coordinate product
transport therefore commutes with 1-s. Apply the same transport to both coordinates
of Cone(1-s)[-1]; the signed differential and every projection agree. The laws of
lem-pod-reindexing-completion-unit-tensor give this normalized whole-cone map.
The empty point product is zero, and its map is unique.
6. Apply the functorial total limit to the commuting localized system squares.
lem-zl-finite-integral-fibre-reconstruction identifies these with the prescribed
completed exchange and restriction. lem-pur-completed-operation-tower-substitution
normalizes their composition comparisons by the same finite-level maps.
Naturality extends through roofs because it already holds on strict complexes.
7. Raw rationalization sends each integral map to its tensor with one. Linearity
extends input naturality to every rational arrow. Exact point sections preserve
the equations, without introducing any action of sigma on the coefficient field.
8. lem-zl-finite-restriction-coefficient-descent and
lem-pod-pullback-identities-scalar-extension identify these actual maps under all
finite coefficient extensions, including ramified extensions. The isomorphism
transport theorem identifies u,w,t,c and their inverse comparisons at each stage.
Apply the common-stage inclusion after representing a finite diagram at one stage;
its image is independent of further extension. The common-stage clause
below uses this inclusion and the prescribed rational point-fibre functor.
Specialization to sigma=id gives the ordinary diagram case.
-/
theorem finiteRestrictionDiagramNaturality
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (G : Diagram F.k)
    [IsSeparated G.aX] [LocallyOfFiniteType G.aX] [QuasiCompact G.aX]
    [IsSeparated G.aY] [LocallyOfFiniteType G.aY] [QuasiCompact G.aY]
    [IsSeparated G.aX'] [LocallyOfFiniteType G.aX'] [QuasiCompact G.aX']
    [IsSeparated G.aY'] [LocallyOfFiniteType G.aY'] [QuasiCompact G.aY']
    [IsFinite G.f] [IsFinite G.f'] :
    Finite (Points G.f G.y) ∧ Finite (Points G.f' (y' G)) ∧
    IsIso (source l E G) ∧ IsIso (middle l E G) ∧ IsIso (sum l E G) ∧
    (∀ T : CochainComplex (coefficientSequenceModules l E G.X') ℤ,
      (exchangeSquare l E G T).Commutes ∧ (restrictionSquare l E G T).Commutes ∧
      (∀ n : ℕ,
        ((exchangeSquare l E G T).image (level l E (Spec (.of F.k)) n)).Commutes ∧
        ((restrictionSquare l E G T).image (level l E (Spec (.of F.k)) n)).Commutes) ∧
      (roos l E (exchangeSquare l E G T)).Commutes ∧
      (roos l E (restrictionSquare l E G T)).Commutes ∧
      (completed l E (exchangeSquare l E G T)).Commutes ∧
      (completed l E (restrictionSquare l E G T)).Commutes) ∧
    (∃ R : PodCompletionReindex l E (c G).hom,
      PodCompletionReindex.Laws l E (c G).hom R) ∧
    (∃ R : PodCompletionReindex l E G.u.hom,
      PodCompletionReindex.Laws l E G.u.hom R) ∧
    (∃ R : PodCompletionReindex l E G.w.hom,
      PodCompletionReindex.Laws l E G.w.hom R) ∧
    (∃ R : PodCompletionReindex l E (fibreIso G).hom,
      PodCompletionReindex.Laws l E (fibreIso G).hom R) ∧
    (∀ (K : sfIntegralConstructibleCategory l E G.X')
      (Q : CochainComplex (scalarReductionSource.{u, u} l E G.X') ℤ)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology G.X')
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E G.X') Q)
      (_hflat : ∀ j : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := Scheme.ProEt.topology G.X')
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E G.X') (Q.X j))
      (_eQ : DerivedCategory.Q.obj Q ≅ K.obj)
      (T : CochainComplex (coefficientSequenceModules l E G.X') ℤ)
      (κ : ∀ n : ℕ, (level l E G.X' n).obj T ≅
        ((scalarReductionExtension.{u, u} l E G.X' n).mapHomologicalComplex (.up ℤ)).obj Q)
      (eT : (coefficientDerivedSystemEvaluationCalculus.{u, u} l E G.X').choose.reduction.obj
        (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj T),
      CoefficientReductionPresentation.{u, u} l E G.X'
        (CoefficientDerivedSystemFibers.toCoefficientDerivedSystemReduction.{u, u}
          (CoefficientDerivedSystemCalculus.toCoefficientDerivedSystemFibers.{u, u}
            (coefficientDerivedSystemEvaluationCalculus.{u, u} l E G.X').choose)) Q hQ T eT κ →
      ∃ (hB : (completed l E (exchangeSquare l E G T)).Vertices
          (sfIntegralConstructible l E (Spec (.of F.k))))
        (hR : (completed l E (restrictionSquare l E G T)).Vertices
          (sfIntegralConstructible l E (Spec (.of F.k)))),
        (((completed l E (exchangeSquare l E G T)).restrict
            (sfIntegralConstructible l E (Spec (.of F.k))) hB).image
          (sfRationalConstructibleLocalization l E (Spec (.of F.k)))).Commutes ∧
        (((completed l E (restrictionSquare l E G T)).restrict
            (sfIntegralConstructible l E (Spec (.of F.k))) hR).image
          (sfRationalConstructibleLocalization l E (Spec (.of F.k)))).Commutes ∧
        ((((completed l E (exchangeSquare l E G T)).restrict
            (sfIntegralConstructible l E (Spec (.of F.k))) hB).image
          (sfRationalConstructibleLocalization l E (Spec (.of F.k)))).image
            (pointRationalFibre F l hl E)).Commutes ∧
        ((((completed l E (restrictionSquare l E G T)).restrict
            (sfIntegralConstructible l E (Spec (.of F.k))) hR).image
          (sfRationalConstructibleLocalization l E (Spec (.of F.k)))).image
            (pointRationalFibre F l hl E)).Commutes) := by
  obtain ⟨hs, hm, hsum, hstrict⟩ := finiteRestrictionStrictTransport l E G
  have hcompleted : ∀ T : CochainComplex (coefficientSequenceModules l E G.X') ℤ,
      (completed l E (exchangeSquare l E G T)).Commutes ∧
      (completed l E (restrictionSquare l E G T)).Commutes := by
    intro T
    exact ⟨square_image_commutes _
        (square_image_commutes _ (hstrict T).1 DerivedCategory.Q)
          (coefficientSequenceLimit l E (Spec (.of F.k))),
      square_image_commutes _
        (square_image_commutes _ (hstrict T).2 DerivedCategory.Q)
          (coefficientSequenceLimit l E (Spec (.of F.k)))⟩
  have reindex : ∀ (W V : Scheme.{u}) (aW : W ⟶ Spec (.of F.k))
      (aV : V ⟶ Spec (.of F.k)) (g : W ⟶ V) [IsIso g],
      ∃ R : PodCompletionReindex l E g, PodCompletionReindex.Laws l E g R := by
    intro W V aW aV g _
    let : W.Over (Spec (.of F.k)) := ⟨aW⟩
    let : V.Over (Spec (.of F.k)) := ⟨aV⟩
    let : ∀ x : W, Invertible (l : W.residueField x) :=
      sfStabilityResidueInvertible F l hl W
    let : ∀ x : V, Invertible (l : V.residueField x) :=
      sfStabilityResidueInvertible F l hl V
    obtain ⟨R, hR, _⟩ := podReindexingCompletionUnit l E g
    exact ⟨R, hR⟩
  refine ⟨finitePoints F.k G.f G.y, finitePoints F.k G.f' (y' G), hs, hm, hsum,
    ?_, reindex _ _ (𝟙 _) (𝟙 _) (c G).hom,
    reindex _ _ G.aX G.aX' G.u.hom, reindex _ _ G.aY G.aY' G.w.hom,
    reindex _ _ (pullback.snd G.f G.y) (pullback.snd G.f' (y' G)) (fibreIso G).hom,
    ?_⟩
  · intro T
    rcases hstrict T with ⟨hb, hr⟩
    refine ⟨hb, hr, ?_, ?_, ?_, (hcompleted T).1, (hcompleted T).2⟩
    · intro n
      exact ⟨square_image_commutes _ hb _, square_image_commutes _ hr _⟩
    · exact square_image_commutes _
        (square_image_commutes _ (square_image_commutes _ hb _) _) _
    · exact square_image_commutes _
        (square_image_commutes _ (square_image_commutes _ hr _) _) _
  · intro K Q hQ hflat eQ T κ eT hT
    obtain ⟨hB, hR⟩ :=
      finiteRestrictionConstructibleVertices F l hl E G K Q hQ hflat eQ T κ eT hT
    have hb := square_image_commutes _
      (square_restrict_commutes _ _ hB (hcompleted T).1)
      (sfRationalConstructibleLocalization l E (Spec (.of F.k)))
    have hr := square_image_commutes _
      (square_restrict_commutes _ _ hR (hcompleted T).2)
      (sfRationalConstructibleLocalization l E (Spec (.of F.k)))
    exact ⟨hB, hR, hb, hr, square_image_commutes _ hb (pointRationalFibre F l hl E),
      square_image_commutes _ hr (pointRationalFibre F l hl E)⟩

/-- Naturality in every input chain map, including each transported germ.
The equality is on whole quotient-system complexes, hence on every section and level.
Source: blueprint finite-stalk permutation sentence, a(m restricted to i_x) formula
(blueprint: lem-zl-finite-restriction-diagram-naturality).

Proof: b and r are the termwise maps of the published natural transformations.
Their naturality equations give the first two clauses. The component map is
itself a natural transformation, which gives the last clause. Evaluation on a section
is the equation a(m restricted to i_x) = a(m) restricted to i_x. Localization
carries these equations through roofs, and linear extension carries them through
raw rationalization; a common-stage arrow is represented at one finite stage. -/
theorem inputNaturality
    (T T' : CochainComplex (coefficientSequenceModules l E G.X') ℤ) (a : T ⟶ T') :
    (B l E G.f' (y' G)).map a ≫ (b l E G.f' (y' G)).app T' =
      (b l E G.f' (y' G)).app T ≫ (C l E G.f' (y' G)).map a ∧
    (C l E G.f' (y' G)).map a ≫ (r l E G.f' (y' G)).app T' =
      (r l E G.f' (y' G)).app T ≫ (D l E G.f' (y' G)).map a ∧
    (∀ x : Points G.f' (y' G),
      (C l E G.f' (y' G)).map a ≫
        (NatTrans.mapHomologicalComplex
          (component l E G.f' (y' G) x) (.up ℤ)).app T' =
      (NatTrans.mapHomologicalComplex
        (component l E G.f' (y' G) x) (.up ℤ)).app T ≫
          ((pull l E x.val).mapHomologicalComplex (.up ℤ)).map a) := by
  refine ⟨(b l E G.f' (y' G)).naturality a, (r l E G.f' (y' G)).naturality a, ?_⟩
  intro x
  exact (NatTrans.mapHomologicalComplex
    (component l E G.f' (y' G) x) (.up ℤ)).naturality a

/-- Common-stage classes of the specified rationalized strict squares, before and after
point sections. Every stage uses the same construction. Equality is in the quotient
Hom groups, so it includes every further finite extension used to represent a diagram.

Source: blueprint finite-stalk permutation sentence and common-stage final paragraph
(blueprint: lem-zl-finite-restriction-diagram-naturality).

Proof: apply finiteRestrictionDiagramNaturality at the coefficient model of A.
The actual inclusion maps the two equal composites to their common-stage classes.
The quotient relation identifies these with their images at any larger field.
Coefficient-descent and pullback-scalar composition coherence identify those images
with the prescribed exchange, restriction, and geometric transport at that field.
A common-stage input arrow has a representative at one common field, where strict
naturality and localization give the square; the same compatibility preserves it
under another enlargement. Apply pointQbarFibre, whose arrow formula is the specified
point-section map of that common-stage representative. -/
theorem finiteRestrictionDiagramNaturality_commonStage
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (A : AlgebraicallyClosedCoefficients.Index l Ω) (G : Diagram F.k)
    [IsSeparated G.aX] [LocallyOfFiniteType G.aX] [QuasiCompact G.aX]
    [IsSeparated G.aY] [LocallyOfFiniteType G.aY] [QuasiCompact G.aY]
    [IsSeparated G.aX'] [LocallyOfFiniteType G.aX'] [QuasiCompact G.aX']
    [IsSeparated G.aY'] [LocallyOfFiniteType G.aY'] [QuasiCompact G.aY']
    [IsFinite G.f] [IsFinite G.f']
    (T : CochainComplex (coefficientSequenceModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) G.X') ℤ)
    (hB : (completed l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
      (exchangeSquare l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) G T)).Vertices
      (sfIntegralConstructible l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
        (Spec (.of F.k))))
    (hR : (completed l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
      (restrictionSquare l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) G T)).Vertices
      (sfIntegralConstructible l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
        (Spec (.of F.k)))) :
    ∀ S : Square (sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) (Spec (.of F.k))),
      (S = (completed l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
          (exchangeSquare l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) G T)).restrict
          (sfIntegralConstructible l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
            (Spec (.of F.k))) hB ∨
       S = (completed l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
          (restrictionSquare l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) G T)).restrict
          (sfIntegralConstructible l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
            (Spec (.of F.k))) hR) →
      ((S.image (sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) (Spec (.of F.k)))).image
            (GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := l) (Ω := Ω) (Y := Spec (.of F.k)) A)).Commutes ∧
      (((S.image (sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) (Spec (.of F.k)))).image
            (GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := l) (Ω := Ω) (Y := Spec (.of F.k)) A)).image
                (pointQbarFibre F l hl Ω)).Commutes := by
  intro S hS
  have strict := (finiteRestrictionDiagramNaturality F l hl
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) G).2.2.2.2.2.1 T
  have hrestrict : S.Commutes := by
    rcases hS with rfl | rfl
    · exact square_restrict_commutes _ _ _ strict.2.2.2.2.2.1
    · exact square_restrict_commutes _ _ _ strict.2.2.2.2.2.2
  have h := square_image_commutes _
    (square_image_commutes _ hrestrict (sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) (Spec (.of F.k))))
    (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := Ω) (Y := Spec (.of F.k)) A)
  exact ⟨h, square_image_commutes _ h (pointQbarFibre F l hl Ω)⟩

end WeilConjectures.FiniteRestrictionNaturality
