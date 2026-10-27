module

public import Sheaf.CategoryTheory.FormalDiagramRestriction
public import Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAdicFlatnessNearClosedFibre
import Sheaf.AlgebraicGeometry.SpaceModuleBaseChangeFlatProperSupport
import Mathlib.RingTheory.FiniteStability

/-! # Adic effectiveness of proper-support flat coherent families

Source: Stacks Project, quot.tex, Situation 08KB and Tag 08W9,
lemma-coherent-existence (blueprint: lem-sfb-space-coherent-formal-effectivity).

The existing CoherentModuli category is used without changing its objects or arrows.
Level n means Spec(A/m^(n+1)); a formal diagram includes every transition and its laws.
Restriction is characterized by cartesian arrows to the original family, including
their naturality, and is therefore the tensor restriction rather than an arbitrary
equivalence between the two categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}
variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The specified closed infinitesimal S-scheme at positive level n+1.
Source: Stacks, 08W9 (blueprint: lem-sfb-space-coherent-formal-effectivity). -/
def coherentAdicBase (a : Spec (CommRingCat.of A) ⟶ S) (n : ℕ) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))) ≫ a)

/-- The ordinary quotient-spectrum inclusion, with no arbitrary model of the map.
Source: Stacks, 08W9 (blueprint: lem-sfb-space-coherent-formal-effectivity). -/
def coherentAdicInclusion (a : Spec (CommRingCat.of A) ⟶ S) (n : ℕ) :
    coherentAdicBase a n ⟶ Over.mk a :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1))))) rfl

/-- The scheme map induced by the actual quotient homomorphism for two powers.
Source: Stacks, 08W9 (blueprint: lem-sfb-space-coherent-formal-effectivity). -/
def coherentAdicTransitionMap {n m : ℕ} (h : n ≤ m) :
    Spec (CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1))) ⟶
      Spec (CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1))) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))))

/-- Quotient-spectrum maps commute with the canonical map to Spec A.
Source: Stacks, 08W9 (blueprint: lem-sfb-space-coherent-formal-effectivity).
Proof: the quotient factor followed on rings by the original quotient projection
is the smaller-power quotient projection (Ideal.Quotient.factor_comp_mk). Apply
the contravariant Spec functor to this equality. -/
theorem coherentAdicTransitionMap_inclusion {n m : ℕ} (h : n ≤ m) :
    coherentAdicTransitionMap (A := A) h ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (m + 1)))) =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))) := by
  sorry

/-- Every quotient transition is a morphism over the original base S.
Source: Stacks, 08W9 (blueprint: lem-sfb-space-coherent-formal-effectivity). -/
def coherentAdicTransition (a : Spec (CommRingCat.of A) ⟶ S)
    {n m : ℕ} (h : n ≤ m) : coherentAdicBase a n ⟶ coherentAdicBase a m :=
  Over.homMk (coherentAdicTransitionMap h)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun g ↦ g ≫ a) (coherentAdicTransitionMap_inclusion h)))

/-- All identity, composition and inclusion compatibilities of the adic tower.
Source: Stacks, 08W9 (blueprint: lem-sfb-space-coherent-formal-effectivity).
Proof: forget to scheme maps, using faithfulness of Over.forget. The corresponding
ring maps are the quotient factors. Ideal.Quotient.factor_eq and factor_comp give
the identity and composition laws, and factor_comp_mk gives compatibility with
the inclusions. Spec reverses composition. -/
theorem coherentAdicTransition_laws (a : Spec (CommRingCat.of A) ⟶ S) :
    (∀ n : ℕ, coherentAdicTransition a (le_refl n) = 𝟙 (coherentAdicBase a n)) ∧
    (∀ (n m k : ℕ) (h : n ≤ m) (h' : m ≤ k),
      coherentAdicTransition a h ≫ coherentAdicTransition a h' =
        coherentAdicTransition a (h.trans h')) ∧
    (∀ (n m : ℕ) (h : n ≤ m),
      coherentAdicTransition a h ≫ coherentAdicInclusion a m =
        coherentAdicInclusion a n) := by
  sorry

/-- The tower is covariant in n: Spec(A/m^(n+1)) maps to Spec(A/m^(m+1)) for n ≤ m.
Source: Stacks, 08W9 (blueprint: lem-sfb-space-coherent-formal-effectivity). -/
def coherentAdicTower (a : Spec (CommRingCat.of A) ⟶ S) : ℕ ⥤ Over S where
  obj n := coherentAdicBase a n
  map h := coherentAdicTransition a (leOfHom h)
  map_id n := (coherentAdicTransition_laws a).1 n
  map_comp h k := ((coherentAdicTransition_laws a).2.1 _ _ _ (leOfHom h) (leOfHom k)).symm

/-- The compatible inclusion of all infinitesimal bases into Spec A.
Source: Stacks, 08W9 (blueprint: lem-sfb-space-coherent-formal-effectivity). -/
def coherentAdicTowerInclusion (a : Spec (CommRingCat.of A) ⟶ S) :
    coherentAdicTower a ⟶ (Functor.const ℕ).obj (Over.mk a) where
  app n := coherentAdicInclusion a n
  naturality n m h := ((coherentAdicTransition_laws a).2.2 n m (leOfHom h)).trans
    (Category.comp_id _).symm

/-- Tensor restriction exists with its cartesian arrows and is uniquely determined
up to the natural isomorphism preserving every one of those arrows.
Source: Stacks, 08KB; artin.tex, equation-approximation
(blueprint: lem-sfb-space-coherent-formal-effectivity).
Proof: pull each (b,M) back along every closed quotient-spectrum inclusion. The
fibre-product universal property gives the pulled map b and the map of fibres.
Tensor pullback gives the module and its canonical arrow. The four admissibility
conditions persist by lem-sfb-space-module-base-change-flat-proper-support;
local finite type of each fibre follows from finite presentation of f by the
etale chart test. Tensor composition and unit comparisons give a functorial
diagram and cartesian arrows, natural also in (b,M). These are cartesian by
the pullback universal property, so the unique maps between any two choices
preserving the arrows are inverse isomorphisms. The same uniqueness gives
naturality in the family and level. This characterizes the restriction functor
with its arrows up to unique compatible natural isomorphism. -/
theorem coherentFormalRestrictionModel_exists (f : X ⟶ B)
    (hfp : ProperQuotFinitePresentation f) (a : Spec (CommRingCat.of A) ⟶ S) :
    ∃ P : FormalRestrictionModel (CoherentModuli.category f) (coherentAdicTower a)
        (Over.mk a) (coherentAdicTowerInclusion a),
      ∀ Q : FormalRestrictionModel (CoherentModuli.category f) (coherentAdicTower a)
          (Over.mk a) (coherentAdicTowerInclusion a),
        ∃! e : P.restriction ≅ Q.restriction,
          ∀ (x : Functor.Fiber (CoherentModuli.category f).p (Over.mk a)) (n : ℕ),
            ((e.hom.app x).val.app n) ≫ Q.arrow x n = P.arrow x n := by
  sorry

/-- The canonical tensor restriction, chosen by its full cartesian normalization
and uniqueness preserving all its arrows, rather than by mere Nonempty choice.
Source: Stacks, 08W9 and equation-approximation
(blueprint: lem-sfb-space-coherent-formal-effectivity). -/
def coherentFormalRestrictionModel (f : X ⟶ B) (hfp : ProperQuotFinitePresentation f)
    (a : Spec (CommRingCat.of A) ⟶ S) :
    FormalRestrictionModel (CoherentModuli.category f) (coherentAdicTower a)
      (Over.mk a) (coherentAdicTowerInclusion a) :=
  (coherentFormalRestrictionModel_exists f hfp a).choose

/-- Restriction of proper-support flat coherent families to the positive adic tower.
Source: Stacks, 08W9 (blueprint: lem-sfb-space-coherent-formal-effectivity). -/
def coherentFormalRestriction (f : X ⟶ B) (hfp : ProperQuotFinitePresentation f)
    (a : Spec (CommRingCat.of A) ⟶ S) :
    Functor.Fiber (CoherentModuli.category f).p (Over.mk a) ⥤
      FormalDiagram (CoherentModuli.category f) (coherentAdicTower a) :=
  (coherentFormalRestrictionModel f hfp a).restriction

/-- Adic restriction is an equivalence, hence every compatible formal family,
including all of its specified transitions, comes from a family over A.
Source: Stacks Project, quot.tex, Tag 08W9, lemma-coherent-existence
(blueprint: lem-sfb-space-coherent-formal-effectivity).
Proof:
1. lem-sfb-space-complete-local-map-effectivity uniquely algebraizes the compatible
   maps b_n to a map b : Spec A → B. Thus all modules lie on thickenings of the
   single fibre Y = X ×_B Spec A, retaining the prescribed transition isomorphisms.
2. Y → Spec A is separated by lem-sfb-space-separated-fp-composition and
   quasi-compact by lem-sfb-space-quasicompact-affine-tests. On surjective etale
   charts finite presentation persists under base change by
   lem-weil-pbc-finite-presentation-base-change-composition. Apply
   lem-sfb-space-local-properties-chart-test to deduce local finite presentation,
   hence finite type of Y over A and likewise of every infinitesimal fibre.
3. lem-sfb-space-supported-adic-existence gives a finitely presented quasi-coherent
   module M with proper support and compatible isomorphisms to the given M_n.
   It also gives full faithfulness for all module homomorphisms.
4. lem-sfb-space-adic-flatness-near-closed-fibre makes the flat locus open and
   containing the closed fibre. The complement is contained in a closed proper
   carrier of M because M is zero outside that carrier. Its image in Spec A
   is therefore closed. Every nonempty closed subset of a local spectrum contains
   the closed point, a contradiction. Thus M is flat everywhere.
5. Restriction is well-defined by
   lem-sfb-space-module-base-change-flat-proper-support. Different base maps admit
   no formal arrow by injectivity in complete-local map effectivity. For equal
   base maps, supported adic existence lifts a compatible module isomorphism
   and its inverse uniquely. Faithfulness makes the lifted composites identities.
   Thus restriction is fully faithful and essentially surjective, as required. -/
theorem coherentFormalRestriction_isEquivalence [IsLocallyNoetherian S]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f : X ⟶ B) (hfp : ProperQuotFinitePresentation f) (hsep : MapIsSeparated f)
    (a : Spec (CommRingCat.of A) ⟶ S)
    (hres : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ≫ a) ∧
      QuasiCompact
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ≫ a)) :
    (coherentFormalRestriction f hfp a).IsEquivalence := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
