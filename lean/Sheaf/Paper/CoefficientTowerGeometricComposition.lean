/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.Paper.CoefficientTowerShriekInterfaces
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.Paper.ProEtaleConstructibleSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
import Sheaf.Paper.SmoothPurityTowerShriekLevels
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleSumStalks
import WeilConjectures.Compactification.CategoryBaseChange
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.CompactificationRefinementCoherence
import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
import Sheaf.Paper.VaryingRingGraphSummand
import Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-! # Geometric composition and etale comparison

Source: blueprint Local pairs and Levels, coefficient tower shriek calculus.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Proper/open composition and exact etale sum-extension, normalized together.
Source: Stacks 0F7J and 03DI--03DJ, 03S5; blueprint Local pairs, steps 1--6.
Proof: first obtain finite etale origins from bounded constructible finite-Tor
levels. Construct the proper/open mate on strict systems using the clopen graph
projection and the semilinear geometric calculus. Horizontal and vertical mate
pasting give coherent comparisons before evaluation. Compatible compactification
towers then give the compositor; common refinements give independence and the
three-map staircase gives associativity and the identity laws. Evaluation gives
the already normalized finite compositor. For etale maps sheafify the sum over
lifts on every level, retaining the quotient transitions on each summand. The
summand inclusion and sum counit give the exact ordinary adjunction and descend
to the unbounded derived adjunction. The graph-summand map identifies this functor
with compact support. Exactness preserves cohomological intervals, the tensor
projection identity preserves Tor intervals, and the structural summand proves
the inverse-image Tor bound. The unique-lift formula for open immersions gives
the displayed open normalization. Preservation restricts these operations to C.
This construction does not assert coefficient-reduction compatibility.
(blueprint: lem-sp-tower-geometric-composition). -/
theorem geometric_calculus
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (x : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o x)
    (q : Coordinates l E b) (z : FiniteCoordinates l E) :
    ∃ finiteData : FiniteNormalization l E k b o q z,
    ∃ ops : CompositionOperations l E k b o q z,
    ∀ h : Preservation l E k b o q,
    ∃ et : EtaleCalculus l E k b o q z,
      Nonempty (CompositionCoherence l E k b o q z h finiteData ops) ∧
      (∀ {U X Y : Scheme.{u}}
    [U.Over (Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (a : Compactification j) (c : Compactification f) (K : C l E b q U),
    (ops.composition j f (j ≫ f) rfl a c (c.precomp j)).hom.app K =
      (F l E b o q c).map
        ((et.etale_shriek j a).hom.app K ≫
          (openEtaleCoordinates l E b o q z j (et.etale j)).hom.app K.obj) ≫
        (openComposition l E b o q j c).hom.app K.obj) := by
  sorry


end AlgebraicGeometry.ProEtale.SpTowerCalculus

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
