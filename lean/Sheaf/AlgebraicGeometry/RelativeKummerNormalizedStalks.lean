module

public import Sheaf.AlgebraicGeometry.NormalizedKummerGeneratorArrows

import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.CategoryTheory.DerivedSectionsScalarCoherence
import Sheaf.Paper.FiniteDirectImageComposition
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula
import Sheaf.AlgebraicGeometry.ExactGlobalSectionsLeray
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Canonical normalized stalk comparison for the two line families
Source: blueprint latest, sk-prop-a1-kummer, prop-pur-gm-relative-kummer.proof.md,
Step 2; Stacks Project, Tags 03Q8, 03Q9 and 03PL
(blueprint: lem-pur-relative-kummer-normalized-stalks).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

section Geometry
variable (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
  {k : Type u} [Field k] (hmk : IsUnit (m : k)) {ζ : k} (hζ : IsPrimitiveRoot ζ m)
  {B : Scheme.{u}} (p : B ⟶ Spec (.of k)) (b : Bool)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B)

/-- The strict-local family, the actual pullback C_B times_B S.
Source: blueprint Step 2 (blueprint: lem-pur-relative-kummer-normalized-stalks). -/
abbrev normalizedKummerStrictFamily :=
  pullback (normalizedKummerProjection p b) (Scheme.strictHenselizationStructuralMap s)

/-- Projection v to C_B.
Source: blueprint Step 2 (blueprint: lem-pur-relative-kummer-normalized-stalks). -/
abbrev normalizedKummerStrictV :=
  pullback.fst (normalizedKummerProjection p b) (Scheme.strictHenselizationStructuralMap s)

/-- Projection h to C.
Source: blueprint Step 2 (blueprint: lem-pur-relative-kummer-normalized-stalks). -/
abbrev normalizedKummerStrictH :=
  normalizedKummerStrictV p b s ≫ pullback.fst (KummerLine.structureMap k b) p

/-- The strict-local family's k-structure.
Source: blueprint Step 2 (blueprint: lem-pur-relative-kummer-normalized-stalks). -/
abbrev normalizedKummerStrictStructure :=
  normalizedKummerStrictV p b s ≫ normalizedKummerStructure p b

/-- The canonical pullback h* with its normalized root-line coefficient comparison.
Source: blueprint Step 2 (blueprint: lem-pur-relative-kummer-normalized-stalks). -/
@[irreducible]
def normalizedKummerH :=
  relativeKummerGlobalPullback A m hm hA (normalizedKummerStrictH p b s)
    (relativeKummerExponentUnit m hmk _ (KummerLine.structureMap k b))
    (relativeKummerExponentUnit m hmk _ (normalizedKummerStrictStructure p b s))

/-- The canonical pullback v* on global cohomology.
Source: blueprint Step 2 (blueprint: lem-pur-relative-kummer-normalized-stalks). -/
@[irreducible]
def normalizedKummerV :=
  relativeKummerGlobalPullback A m hm hA (normalizedKummerStrictV p b s)
    (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p b))
    (relativeKummerExponentUnit m hmk _ (normalizedKummerStrictStructure p b s))

/-- The specified strict-local comparison: restriction, exchange and Leray.
Source: Stacks Tag 03Q9 (blueprint: lem-pur-relative-kummer-normalized-stalks). -/
@[irreducible]
def normalizedKummerTheta :=
  moduleStrictLocalTheta A (normalizedKummerProjection p b) s
    (relativeKummerLinePlus A m hA _) (relativeKummerLinePlus A m hA _)
    (relativeKummerLinePullback A m hm hA (normalizedKummerStrictV p b s)
      (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p b))
      (relativeKummerExponentUnit m hmk _ (normalizedKummerStrictStructure p b s)))

set_option linter.defProp false in
/-- The specified derived comparison, all edge classes and the unit normalization.
Source: blueprint Step 2 (blueprint: lem-pur-relative-kummer-normalized-stalks). -/
@[irreducible]
def RelativeKummerNormalizedStalk : Prop :=
  IsIso (normalizedKummerH A m hm hA hmk p b s) ∧
  ∃ Φ : ((Scheme.pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} A)).mapDerivedCategoryPlus.obj
        (normalizedKummerImage A m hA (normalizedKummerProjection p b)) ≅
        normalizedKummerGlobal A m hA (KummerLine.curve k b),
    Φ.hom ≫ normalizedKummerH A m hm hA hmk p b s =
      normalizedKummerTheta A m hm hA hmk p b s ∧
    (∀ q : ℕ,
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          (normalizedKummerEdgeGerm A m hA (normalizedKummerProjection p b) s) ≫
        (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map Φ.hom ≫
        (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          (normalizedKummerH A m hm hA hmk p b s) =
        (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          (normalizedKummerV A m hm hA hmk p b s)) ∧
    normalizedKummerUnitGerm A m hm hA hζ p (normalizedKummerProjection p b)
        (relativeKummerExponentUnit m hmk B p)
        (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p b)) s ≫ Φ.hom =
      normalizedKummerGlobalSection A m hA _
        (normalizedKummerConstantMap A m hm hA hζ _ (KummerLine.structureMap k b)) ∧
    (match b, Φ with
    | false, _ => True
    | true, Ψ =>
      normalizedKummerGeneratorPlusMap A m hA _
          (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p true))
          (Units.map (pullback.fst (KummerLine.structureMap k true) p).appTop.hom.toMonoidHom
            (KummerLine.coordinateUnit k)) ≫
        (DerivedCategory.Plus.homologyFunctor _ 1).map
          (normalizedKummerEdgeGerm A m hA (normalizedKummerProjection p true) s) ≫
        (DerivedCategory.Plus.homologyFunctor _ 1).map Ψ.hom =
      normalizedKummerGeneratorPlusMap A m hA _
        (relativeKummerExponentUnit m hmk _ (KummerLine.structureMap k true))
        (KummerLine.coordinateUnit k))

end Geometry

/-- The canonical normalized comparison for every geometric stalk of either line
family, including its conservative-stalk consequences and restriction of constants.
Source: blueprint latest, prop-pur-gm-relative-kummer.proof.md, Step 2; Stacks 03Q9
(blueprint: lem-pur-relative-kummer-normalized-stalks).

Proof plan: The projections are affine and hence qcqs. The small affine-neighbourhood
strict localization is strictly henselian, so its section functor is exact. Restriction
followed by exchange and Leray is the abelian strict-local stalk comparison after
forgetting scalars; scalar forgetting detects its invertibility. Strict-local Kummer
invariance makes the actual h-pullback invertible. Compose the first comparison with
its inverse to obtain Phi. Restriction of a global cocycle, exchange, and exact sections
carry its edge germ to v-pullback, proving the all-degree formula. The unit sends a to
zeta tensor a. Naturality of the ordinary abelian Kummer boundary, then the scalar
insertion, gives the coordinate formula. Conservative geometric stalks now detect the
asserted relative isomorphisms and vanishings. The connective derived criterion gives
both line units. Finally localization k[t] -> k[t,t^-1] fixes the constant root and its
scalar multiples. No geometric-fibre base-change theorem defines Phi.
-/
theorem relativeKummer_normalized_stalks (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ N : ℕ) (hℓ : ℓ.Prime) (_hN : 1 ≤ N) (hℓk : IsUnit (ℓ : k))
    (A : Type (u + 1)) [CommRing A] [Algebra (ZMod (ℓ ^ N)) A]
    [Module.Free (ZMod (ℓ ^ N)) A] [Module.Finite (ZMod (ℓ ^ N)) A]
    (ζ : k) (hζ : IsPrimitiveRoot ζ (ℓ ^ N))
    (B : Scheme.{u}) (p : B ⟶ Spec (.of k)) :
    let m := ℓ ^ N
    let hm := relativeKummerPositive ℓ N hℓ
    let hA := relativeKummerAnnihilator A m
    let hmk := relativeKummerFieldExponentUnit ℓ N hℓk
    let hB := relativeKummerExponentUnit m hmk B p
    let hC := fun b => relativeKummerExponentUnit m hmk _ (KummerLine.structureMap k b)
    let hCB := fun b => relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p b)
    let abs0 := fun b => (DerivedCategory.Plus.homologyFunctor _ 0).map
      (normalizedKummerGlobalSection A m hA _
        (normalizedKummerConstantMap A m hm hA hζ _ (KummerLine.structureMap k b)))
    let rel0 := fun b => (DerivedCategory.Plus.homologyFunctor _ 0).map
      (normalizedKummerUntwistedUnit A m hm hA hζ p
        (normalizedKummerProjection p b) hB (hCB b))
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B),
      ∀ b : Bool, RelativeKummerNormalizedStalk A m hm hA hmk hζ p b s) ∧
    ((IsIso (abs0 false) ∧
      (∀ q : ℕ, q ≠ 0 → IsZero ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (normalizedKummerGlobal A m hA (KummerLine.curve k false))))) →
      IsIso (relativeKummerUnit A m hm hA (normalizedKummerProjection p false)
        hB (hCB false)) ∧
      IsIso (normalizedKummerUntwistedUnit A m hm hA hζ p
        (normalizedKummerProjection p false) hB (hCB false)) ∧
      IsIso (rel0 false) ∧
      (∀ q : ℕ, q ≠ 0 → IsZero ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (normalizedKummerImage A m hA (normalizedKummerProjection p false))))) ∧
    ((IsIso (abs0 true) ∧
      IsIso (normalizedKummerGeneratorMap A m hA _ (hC true) (KummerLine.coordinateUnit k)) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 1 →
        IsZero ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          (normalizedKummerGlobal A m hA (KummerLine.curve k true))))) →
      IsIso (rel0 true) ∧
      IsIso (normalizedKummerRelativeGenerator A m hA p (hCB true)) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 1 →
        IsZero ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          (normalizedKummerImage A m hA (normalizedKummerProjection p true))))) ∧
    (∀ a : A,
      relativeKummerCohomologyPullback A m hm hA (normalizedKummerInclusion p)
        (hCB false) (hCB true) 0
        (relativeKummerConstant A m hm hA hζ _ (normalizedKummerStructure p false) a) =
      relativeKummerConstant A m hm hA hζ _ (normalizedKummerStructure p true) a) := by
  sorry

end AlgebraicGeometry.Etale
