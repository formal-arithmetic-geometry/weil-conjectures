/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.Paper.GeometricHypotheses
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.CommonStageWeilShriek
public import Sheaf.Paper.ConstantWeilStructure
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.GlobalGeometricFrobenius
import Sheaf.Paper.PoincarePointFiniteness
import Sheaf.Paper.SfWeilSheafComplex
import WeilConjectures.WeilSheaf.FourierInversion.OtherSections

/-!
# The smooth proper hypotheses for purity

Source: blueprint main-20261015, sk-def-set, sk-thm-sf-package (1),
prop-weil-operations and sk-lem-finite
(blueprint: lem-weil-smooth-proper-purity-hypotheses).

The target point is the geometric fibre of Spec k₀, canonically Spec k. Compact
support is presented by the proper model's identity compactification. At field
coefficients finite Tor amplitude imposes no extra condition. The exceptional
adjoint and its Frobenius comparison are conclusions, with the latter normalized
by the actual compact-support exchange and adjunction counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom] [GeometricallyConnected X₀.hom]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The hypotheses required for smooth-proper purity, in the three clauses of the node.
The existential G is the constructible exceptional inverse image, right adjoint to
specified compact support. Its natural Frobenius comparison e is characterized by
F(e_K) followed by epsilon_(g*K) = Ex! inverse followed by g*(epsilon_K).
The Weil pair omega has exactly G applied to the constant point object as carrier;
its structure is e at that constant followed by G of its canonical Weil structure.
The last conjunct asserts finite-dimensionality of ordinary and compact cohomology
of the constant Weil complex in every integer degree. Their specified actions are
`globalGeometricFrobeniusQbarOnCohomology`, on precisely these coefficient modules.

Source: main-20261015, sk-def-set, sk-thm-sf-package (1),
prop-weil-operations, and sk-lem-finite
(blueprint: lem-weil-smooth-proper-purity-hypotheses).

Proof plan:
1. Properness gives separated finite type, and the fixed field datum makes l
invertible. Apply sk-def-set and sk-thm-sf-package (1) to obtain the constructible
exceptional adjunction on Dctf. At Ω this is the common-stage bounded constructible
category. No ambient exceptional-adjoint admissibility is assumed.
2. Apply prop-weil-operations to the structure morphism. The geometric-Frobenius
exchange is zlShriekFrobenius, the composite of its canonical proper/open mates.
Its right-adjoint mate is invertible, since Frobenius pullback is an equivalence.
The inverse-transpose formula gives the displayed counit identity and naturality.
Apply this comparison to the canonical constant point Weil object, then G to its
structure isomorphism. These give an invertible structure on the carrier G(Ω),
so the resulting fixed pair is the required dualizing Weil complex.
3. Apply sk-lem-finite to the constant bounded constructible finite-Tor object.
Its ordinary and compact point complexes have finite-dimensional cohomology at
field coefficients. The two canonical transports of prop-weil-operations followed
by cohomology of the constant Weil structure are exactly the displayed operators.
The common finite-stage scalar extension retains finite dimension over Ω. -/
theorem smoothProperPurityHypotheses (d : ℕ)
    (hsmooth : D.IsSmoothOfPureDimension X₀ d) :
    (∃ G : finiteTorFieldCoefficientCategory
        (generalAlgebraicallyClosedConstructibleCategory l Ω
          (D.geometricFiber (sfWeilCohomologyPoint D)).left) ⥤
        finiteTorFieldCoefficientCategory
          (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left),
      ∃ adj : zlCommonStageShriek D l hl Ω (frobeniusCohomologyModelMap D X₀)
          (Compactification.ofIsProper X₀.hom) ⊣ G,
      ∃ e : G ⋙ sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ≅
          sfCommonStageWeilFrobeniusPullback D l hl (sfWeilCohomologyPoint D) Ω ⋙ G,
        (∀ K,
          (zlCommonStageShriek D l hl Ω (frobeniusCohomologyModelMap D X₀)
            (Compactification.ofIsProper X₀.hom)).map (e.hom.app K) ≫
              adj.counit.app
                ((sfCommonStageWeilFrobeniusPullback D l hl (sfWeilCohomologyPoint D) Ω).obj K) =
          (zlShriekFrobenius D l hl Ω (frobeniusCohomologyModelMap D X₀)
            (Compactification.ofIsProper X₀.hom)).inv.app (G.obj K) ≫
              (sfCommonStageWeilFrobeniusPullback D l hl (sfWeilCohomologyPoint D) Ω).map
                (adj.counit.app K)) ∧
        ∃ omega : sfCommonStageWeilComplex D l hl X₀ Ω,
          omega.carrier = G.obj
            (constantWeilAlgebraicallyClosedComplex l D hl (sfWeilCohomologyPoint D) Ω).carrier ∧
          HEq omega.str
            (e.app
                (constantWeilAlgebraicallyClosedComplex l D hl
                  (sfWeilCohomologyPoint D) Ω).carrier ≪≫
              G.mapIso (constantWeilAlgebraicallyClosedComplex l D hl
                (sfWeilCohomologyPoint D) Ω).str)) ∧
    ∀ (compact : Bool) (i : ℤ),
      FiniteDimensional Ω
        (globalGeometricFrobeniusQbarCohomology D l hl X₀ Ω
          (Compactification.ofIsProper X₀.hom)
          (constantWeilAlgebraicallyClosedComplex l D hl X₀ Ω) compact i).a := by
  sorry

end WeilConjectures
