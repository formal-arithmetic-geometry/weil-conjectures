module

public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Sheaf.CategoryTheory.CondensedProductActionInflation
public import Sheaf.CategoryTheory.CondensedInflationNativeSiteData
public import Sheaf.CategoryTheory.ActionToposGeometricRestriction
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.CategoryTheory.InflationShiftUnitComparisons
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import Sheaf.Paper.ExactDerivedResolvingIdentification
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.PullbackTensorCanonicalShiftUnit

/-! # Canonical monoidal inflation and invariant-adjunction normalization

Source: the internal-action infrastructure associated with paragraph (3) of the current
blueprint's direct-image stability proof; Stacks 015F, 06YY, 07A4, 07A6, 09T5, 0FPT, 0FNH.
The auxiliary normalization is agent-formulated, with an exact external reference wanted.
(blueprint: lem-sfb-derived-inflation-monoidal-normalization).

The tensor, its unit, its Koszul symmetry, the invariant inclusion and the adjunction
are the existing constructions, rather than existential replacements for those data.
The ordered shifted-unit comparison below allows every integer, including negative ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CondensedBar
open CategoryTheory.CondensedDerivedRestriction
open Profinite.CondensedAction (trivial)

namespace CategoryTheory.CondensedInflationNormalization

variable (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Exact derived inflation identifies every universal left-derived pair with its existing
termwise localization, with equality on all representatives and equality of the actual
adjunction units and counits. This applies to the canonical ringed-site pullback after
identifying the ordinary pullback with trivial inflation by its coefficient-tensor identity.
Source: Stacks 015F, 06YY, 07A6, 09T5
(blueprint: lem-sfb-derived-inflation-monoidal-normalization). -/
def PullbackIdentification : Prop :=
  ∀ (L : DerivedCategory.{u + 1} (Modules A) ⥤
        DerivedCategory.{u + 1} (Equivariant A G))
    (epsilon : DerivedCategory.Qh ⋙ L ⟶
      (trivial (R := A.toMon) (P := G)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
    L.IsLeftDerivedFunctor epsilon (HomotopyCategory.quasiIso (Modules A) (.up ℤ)) →
    ∃ e : L ≅ trivialDerived A G,
      (∀ K : HomotopyCategory (Modules A) (.up ℤ),
        e.hom.app (DerivedCategory.Qh.obj K) ≫
          (trivial (R := A.toMon) (P := G)).mapDerivedCategoryFactorsh.hom.app K =
            epsilon.app K) ∧
      (∀ e' : L ≅ trivialDerived A G,
        (∀ K : HomotopyCategory (Modules A) (.up ℤ),
          e'.hom.app (DerivedCategory.Qh.obj K) ≫
            (trivial (R := A.toMon) (P := G)).mapDerivedCategoryFactorsh.hom.app K =
              epsilon.app K) → e' = e) ∧
      ∃ d : L ⊣ derived A G,
        (∀ M, d.unit.app M ≫ (derived A G).map (e.hom.app M) =
          (adjunction A G).unit.app M) ∧
        (∀ N, d.counit.app N = e.hom.app ((derived A G).obj N) ≫
          (adjunction A G).counit.app N)

/-- The representative-normalized pullback identification respects the canonical shifts.
The shift structure on the universal pair is fixed by requiring its computation map
to commute with the signed shifts, just as in the recorded derived-pullback construction.
Source: Stacks 015F and 06YY
(blueprint: lem-sfb-derived-inflation-monoidal-normalization). -/
def PullbackShiftIdentification : Prop :=
  ∀ (L : DerivedCategory.{u + 1} (Modules A) ⥤
        DerivedCategory.{u + 1} (Equivariant A G))
    (epsilon : DerivedCategory.Qh ⋙ L ⟶
      (trivial (R := A.toMon) (P := G)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (_ : L.CommShift ℤ),
    L.IsLeftDerivedFunctor epsilon (HomotopyCategory.quasiIso (Modules A) (.up ℤ)) →
    NatTrans.CommShift epsilon ℤ →
    ∀ e : L ≅ trivialDerived A G,
      (∀ K : HomotopyCategory (Modules A) (.up ℤ),
        e.hom.app (DerivedCategory.Qh.obj K) ≫
          (trivial (R := A.toMon) (P := G)).mapDerivedCategoryFactorsh.hom.app K =
            epsilon.app K) → NatTrans.CommShift e.hom ℤ

/-- Exact forgetting preserves kernels, as in the recorded restriction calculus.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-derived-inflation-monoidal-normalization). -/
instance forgetLimits :
    PreservesFiniteLimits (CondensedBar.forgetAction (A := A) (G := G)) :=
  (forgetExact A G).1

/-- Exact forgetting preserves cokernels, as in the recorded restriction calculus.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-derived-inflation-monoidal-normalization). -/
instance forgetColimits :
    PreservesFiniteColimits (CondensedBar.forgetAction (A := A) (G := G)) :=
  (forgetExact A G).2.1

/-- Trivial inflation followed by forgetting is the literal identity on internal modules.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-derived-inflation-monoidal-normalization). -/
def trivialForget : trivial (R := A.toMon) (P := G) ⋙
    CondensedBar.forgetAction (A := A) (G := G) ≅ 𝟭 (Modules A) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- The canonical identity comparison is obtained from the literal ordinary identity.
Source: Stacks 015F (blueprint: lem-sfb-derived-inflation-monoidal-normalization). -/
def trivialForgetDerived : trivialDerived A G ⋙
    (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory ≅
      𝟭 (DerivedCategory.{u + 1} (Modules A)) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (trivialForget A G) ≪≫
      Functor.mapDerivedCategoryIdIso (Modules A)

/-- For the terminal group the given adjunction becomes the identity adjunction under
forgetting the uniquely trivial action. The two comparison equations specify its actual
unit and counit; the forward equivalence is the fixed trivialDerived functor.
Source: blueprint paragraph (3), identity normalization, Stacks 07A6
(blueprint: lem-sfb-derived-inflation-monoidal-normalization). -/
def TerminalIdentity : Prop :=
  ∀ _ : Subsingleton G,
    ∃ (i : trivialDerived A G ⋙
        (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory ≅
          𝟭 (DerivedCategory.{u + 1} (Modules A)))
      (j : (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory ⋙
        trivialDerived A G ≅ 𝟭 (DerivedCategory.{u + 1} (Equivariant A G)))
      (r : derived A G ≅
        (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory),
      i = trivialForgetDerived A G ∧
      (∀ M, (adjunction A G).unit.app M ≫ r.hom.app ((trivialDerived A G).obj M) ≫
        i.hom.app M = 𝟙 M) ∧
      (∀ N, (adjunction A G).counit.app N =
        (trivialDerived A G).map (r.hom.app N) ≫ j.hom.app N)

/-- All normalization assertions on the fixed internal categories and their native tensors.
No nonzero-coefficient or nontrivial-group condition is imposed.
Source: blueprint paragraph (3); Stacks 015F, 06YY, 07A4, 07A6, 09T5, 0FPT, 0FNH
(blueprint: lem-sfb-derived-inflation-monoidal-normalization). -/
structure Normalization : Prop where
  /-- The canonical left-derived pullback is termwise exact inflation. -/
  pullback : PullbackIdentification A G
  /-- The identification preserves the fixed signed shifts. -/
  pullback_shift : PullbackShiftIdentification A G
  /-- The site is the small action site, with its identity structural ring map. -/
  presentation : ∃ P : ActionSitePresentation A G,
    ∃ h : HasDerivedCategory.{u + 1} (siteModules A G P),
      @NativeTensorIdentification.{u} A G _ _ _ P h
  /-- The terminal-group specialization identifies the actual adjunction with identity. -/
  terminal_identity : TerminalIdentity A G
  /-- Exact inflation is triangulated with the specified termwise shifts. -/
  triangulated : (trivialDerived A G).IsTriangulated
  /-- The existing core is normalized on K-flat representatives. -/
  tensor_model : TrivialTensorModel (A := A) (G := G) (derivedTrivialTensor A G)
  /-- The existing unit comparison is the regular-coefficient identity. -/
  unit_model : TrivialUnitModel (A := A) (G := G) (derivedTrivialTensor A G)
  /-- Symmetry is the signed cochain symmetry, independently fixed in both categories. -/
  symmetry : SymmetrySquare A G
  /-- The actual adjunction commutes with shifts, including its unit and counit. -/
  adjunction_shift : (adjunction A G).CommShift ℤ
  /-- First-variable compatibility with the specified shifts. -/
  first_shift : FirstShiftSquare A G
  /-- Second-variable compatibility with the specified shifts. -/
  second_shift : SecondShiftSquare A G
  /-- The derived transpose is localization of the ordinary fixed-section transpose. -/
  transpose (M : CochainComplex (Modules A) ℤ) (I : CochainComplex (Equivariant A G) ℤ)
      (f : ((trivial (R := A.toMon) (P := G)).mapHomologicalComplex (.up ℤ)).obj M ⟶ I) :
    (adjunction A G).homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
        ((trivial (R := A.toMon) (P := G)).mapDerivedCategoryFactors.hom.app M ≫
          DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
          (((invariants A G).adjunction.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫
        (invariants A G).functor.rightDerivedFunctorUnitQ I
  /-- Unbounded K-injective computation retains the canonical computation unit. -/
  kinjective (I : CochainComplex (Equivariant A G) ℤ) (hI : I.IsKInjective) :
    IsIso ((invariants A G).functor.rightDerivedFunctorUnitQ I)
  /-- The bounded-below computation uses equivariant injectives. -/
  bounded_below (I : CochainComplex (Equivariant A G) ℤ)
      (hb : ∃ n : ℤ, ∀ i < n, IsZero (I.X i)) (hi : ∀ i : ℤ, Injective (I.X i)) :
    IsIso ((invariants A G).functor.rightDerivedFunctorUnitQ I)
  /-- Inflation preserves the prescribed ordered comparison for every pair of integers. -/
  ordered (p q : ℤ) :
    (trivialDerived A G).map (baseComparison A p q).hom ≫
        ((derivedTrivialTensor A G).μIso _ _).inv ≫
        ((shiftedCoefficientIso A G p).hom ⊗ₘ (shiftedCoefficientIso A G q).hom) =
      (shiftedCoefficientIso A G (p + q)).hom ≫ (actionComparison A G p q).hom
  /-- Inflation preserves the actual multiplication of the regular coefficient unit. -/
  multiplication :
    (trivialDerived A G).map
        ((baseCoefficient A ◁ (baseUnitIso A).inv) ≫ (ρ_ (baseCoefficient A)).hom) ≫
        (coefficientIso A G).hom =
      ((derivedTrivialTensor A G).μIso _ _).inv ≫
        ((coefficientIso A G).hom ⊗ₘ (coefficientIso A G).hom) ≫
        coefficientMultiply (A := A) (G := G)

/-- Canonical monoidal inflation and invariant-adjunction normalization.
Source: current blueprint direct-images proof, paragraph (3), agent-written infrastructure;
Stacks 015F, 06YY, 07A4, 07A6, 09T5, 0FPT, 0FNH
(blueprint: lem-sfb-derived-inflation-monoidal-normalization).

Proof: (1) Present actions on the small action site by geometricRestriction. Its ordinary
module pullback is coefficient tensor with the identity ring map: r tensor m maps to rm,
and m maps back to 1 tensor m. The tensor and unit comparisons are the identities on
pure tensors and the regular ring. Fixed sections after every base change give exactly
invariants and its inclusion-normalized Hom transpose (product_action_inflation).
(2) Apply exactDerivedResolvingIdentification to identify the canonical left-derived
pullback with exact termwise localization on every complex, including its fixed shifts.
Flat terms, K-flat complexes and the direct sums in total tensors are preserved.
(3) Apply ringedDerivedMonoidalComparisons using the independently fixed native tensor
constraints of ringedDerived_closed_symmetric_monoidal. Representative normalization
identifies its core with derivedTrivialTensor, including the unit and Koszul symmetry.
(4) Apply derivedAdjunctionOfResolvingClass to the fixed ordinary adjunction and unbounded
K-injective resolutions. Its Hom formula is the displayed transpose; hence both units
and both counits agree. Bounded-below equivariant injective resolutions are K-injective.
The fixed signed shifts commute with this actual adjunction.
(5) Apply pullback_tensor_canonical_shift_unit in each variable and at the regular unit.
Expand orderedUnitComparison: first inverse multiplication, then first shift, then second
shift, and finally the canonical addition comparison. Applying the two shift squares and
the unit equation identifies every arrow, giving ordered for all integers.
(6) No step excludes the zero ring. For a terminal group the invariant inclusion and its
transposes are identities; exact localization and identity comparison normalization give
the identity functor, monoidal comparisons and adjunction under the action equivalence. -/
theorem derivedInflationMonoidalNormalization
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : Normalization A G := by
  sorry

end CategoryTheory.CondensedInflationNormalization
