/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Inseparable

import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange
import Sheaf.AlgebraicGeometry.SectionComponentPullback
import Sheaf.AlgebraicGeometry.DescendFlatFinitePresentation
import WeilConjectures.AlgebraicGeometry.NoetherianSpecializationTrait
import WeilConjectures.AlgebraicGeometry.ConnectedGenericFibreTrait

/-!
# Generalization stability of a section component in a flat geometrically reduced family

Source: Stacks Project, More on Morphisms, Tag 055Q,
`lemma-connected-along-section-open-neighbourhood`, its specialization argument.
(blueprint: lem-trf-flat-reduced-section-component-generalization)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The fibrewise connected components through a section form a locus stable under
 generalization for a flat morphism of finite presentation with geometrically reduced fibres.
The topological fibre in the conclusion is the scheme-theoretic fibre through `g.fiberHomeo`.

Source: Stacks Project, Tag 055Q, `lemma-connected-along-section-open-neighbourhood`.

Proof:
1. Given `p` specializing to `q` in the locus, restrict the base to an affine neighbourhood
   of `g q`. It also contains `g p`. Flatness and finite presentation persist by
   `lem-weil-pbc-flat-morphism-base-change` and `lem-weil-pbc-qcqs-morphism-permanence`.
   Apply geometric reducedness to an algebraic closure of the residue field, then use
   `lem-trf-geometric-reduced-fibre-locus-base-change` for the restricted geometric fibre.
   The cartesian component identity `lem-sbc-section-component-cartesian` identifies the
   restricted component locus with the inverse image of the original one.
2. Express the affine base as a limit of finite-type integer algebras using
   `lemma-nagata-noetherian-inverse-system-affine`. The three clauses of
   `thm-pd-spreading-out` descend the family, its section, and the section identity.
   The stages are qcqs by `lem-weil-pbc-qcqs-morphism-permanence` and noetherian by
   `lem-weil-pbc-finite-type-over-noetherian`.
3. By `lem-weil-pbc-descend-flat-finite-presentation`, advance until the model is flat.
   Its distinguished geometric fibre is reduced by
   `lem-trf-geometric-reduced-fibre-locus-base-change`; no condition on other model fibres
   is needed. The cartesian component identity transfers membership of `q` to its model
   image and identifies the inverse image of the model locus. Continuity transfers the
   specialization. Equal model images settle the claim immediately.
4. Otherwise `lem-sbc-noetherian-specialization-trait` traces the specialization by a DVR.
   Pull back the model to this trait. Flatness and finite presentation persist, and the
   geometric closed fibre is reduced by the geometric-reduced-fibre base-change lemma.
   Its ordinary closed fibre is reduced: on affine charts the scalar extension to the
   algebraic closure is reduced, by `lem-weil-pbc-open-fibre-product`,
   `lem-weil-pbc-fibre-product-affine-spectra`, and `lem-weil-pbc-affine-scheme-reduced-iff`.
   The algebra map is injective by `lem-weil-pbc-field-extension-base-change-faithfully-flat`
   and `lem-weil-pbc-faithfully-flat-universally-injective`, so nilpotents already vanish
   before extension. This is reducedness in `def-pc-reduced-scheme`.
5. The trait family has the original section and a second section tracing the two points.
   The cartesian component identity places both closed section points in the same closed
   fibre component `D`. Scheme and topological fibres agree by `def-pc-scheme-fibre`.
   The DVR is noetherian (`def-sc-discrete-valuation-ring`), hence the total space and
   closed fibre are noetherian by `lem-weil-pbc-finite-type-over-noetherian`; their spaces
   are noetherian by `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`.
6. By `lem-sfb-noetherian-connected-components-open`, `D` is clopen in the closed fibre.
   Remove its complement from the total space. In the remaining noetherian open, take
   the open connected component `W` through the original closed section point. Connectedness
   of `D` implies `D` is contained in `W`, so the second closed section point lies there too.
7. Both sections factor through `W`: their inverse images are open in the local trait and
   contain its closed point, so are the entire trait. These are open-subscheme factorizations
   (`def-weil-open-immersion`). The restriction stays flat (`def-weil-flat-morphism`),
   with reduced closed fibre (`def-pc-reduced-scheme`). Now
   `lem-sbc-connected-generic-fibre-trait` makes its generic fibre connected and nonempty.
8. Its connected image in the generic topological fibre contains both generic section
   points, so the second lies in the component of the first. Use
   `lem-sbc-section-component-cartesian` to return this membership to the model general
   point and then to `p` in the original family. This includes the equality case of step 3.

(blueprint: lem-trf-flat-reduced-section-component-generalization) -/
theorem stableUnderGeneralization_section_component_of_flat_of_geometricallyReduced_fibers
    {P T : Scheme.{u}} (g : P ⟶ T) [Flat g] [LocallyOfFinitePresentation g]
    [QuasiCompact g] [QuasiSeparated g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T)
    (hred : ∀ t : T, GeometricallyReduced (g.fiberToSpecResidueField t)) :
    StableUnderGeneralization
      {p : P | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))} := by
  sorry

end AlgebraicGeometry
