## What changed

Replaced the item's hole by a proof combining eventual interpolation with Bertini for
a fixed finite linear system. The proof derives injectivity of coefficient combination
from uniqueness for the zero section, then derives vanishing of every combination.
It preserves the exact original theorem signature.

Extracted the seven unchanged constructions into PrescribedPointSystemData, publicly
reexported by the original module, to keep the lower lemmas independent of their consumer.
See coord/changes/S6-prescribed-point-interface-extraction.md.

Proved EffectiveCartierPureDimension: isolate a nonempty open of each component,
lift it to the ambient scheme, apply the existing Cartier dimension-drop theorem,
and compare with a nonempty open of the reduced integral component. The empty
Cartier divisor is handled vacuously. The component comparison is topological and
does not claim an equality of scheme structures.

Proved PrescribedPointSmoothMember from its smoothness/nonzero-jet open: regularity
and connectedness make X integral; a nonzero jet gives a nonzero section, hence an
effective Cartier divisor. The new purity theorem gives dimension d-1. A closed
subscheme of affine X is affine. The existing SectionNonvanishingZeroLocus theorem
identifies residue-fibre vanishing with membership in its support.

## Proved and sorry left

The original single hole, AlgebraicGeometry.exists_eventual_prescribedPoint_smoothSystem,
has a complete Lean proof from the two separate results below. This is a decomposition,
not a net hole reduction: one original hole is replaced by two genuinely separate holes
(net minus one under the stated closed-minus-added convention).

Complete new theorem bodies:

- AlgebraicGeometry.Scheme.IdealSheafData.isPureDimension_of_isInvertible
  (lem-zl-effective-cartier-pure-dimension), from the existing Cartier dimension-drop
  declaration and the nonempty-open dimension theorem.
- AlgebraicGeometry.exists_open_smooth_prescribedPoint_member
  (lem-zl-prescribed-point-smooth-member), from the Bertini open and the proved
  Cartier/affineness/containment argument.

Every sorry left in this packet (two):

- AlgebraicGeometry.exists_eventual_prescribedPoint_jetSystem
  (lem-zl-prescribed-point-eventual-jet-system): the high-degree interpolation result,
  without smoothness, dimension or smooth-member conclusions.
- AlgebraicGeometry.exists_open_prescribedPoint_bertini
  (lem-zl-prescribed-point-bertini-open): smoothness and nonzero jets for an already
  supplied finite system, without degree bounds, a kernel basis, affineness or purity.

Both statements are separate steps of the cited source argument, have full proofs in
words and matching DAG nodes, and are strictly parts of the original theorem. Their
combination with the proved geometric argument is actual Lean. No definition has a hole.
The existing imported Cartier dimension-drop theorem remains an existing dependency;
its hole is neither created nor hidden by this packet.

Edge cases checked: the empty divisor has vacuous pure dimension; d>=1 is necessary
for the Cartier result; the nonempty S hypothesis supplies a point detecting a nonzero
section; a zero section cannot satisfy the nonzero-jet conclusion. The interpolation
result does not use smoothness, connectedness or pure dimension. The Bertini-open
result also allows disconnected smooth X with all components of the specified dimension.

Validation: remote lcompile.py checks, exact source/signature comparison for the
relocation, and deliver3.py preflight. See delivery output for final compiler results.

## No longer needed

The root now privately imports only PrescribedPointEventualJetSystem and
PrescribedPointSmoothMember and publicly imports PrescribedPointSystemData. The
following former direct imports were removed:

- Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
- Sheaf.AlgebraicGeometry.PureDimension
- WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
- WeilConjectures.AlgebraicGeometry.BaseChangeConventions
- WeilConjectures.AlgebraicGeometry.EtaleTensorSections
- WeilConjectures.AlgebraicGeometry.InvertibleStalkLinearEquiv
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
- WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
- Mathlib.RingTheory.Ideal.Cotangent
- Mathlib.AlgebraicGeometry.Morphisms.Smooth
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace
- WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
- WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
- WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
- Sheaf.DeligneLaumon.BertiniSections
- WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
- WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealTensorSections
- WeilConjectures.AlgebraicGeometry.CoherentSerreVanishing
- WeilConjectures.AlgebraicGeometry.PQFCohomology
- Sheaf.RingTheory.SmoothOverFieldRegularLocal
- WeilConjectures.AlgebraicGeometry.Regular
- WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension
- WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
- WeilConjectures.AlgebraicGeometry.MaximalIdealDifferentialCotangentDimension
- Sheaf.AlgebraicGeometry.BertiniSmoothMember
- Sheaf.AlgebraicGeometry.HypersurfaceNonzeroRelativeDifferential
- WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
- Sheaf.AlgebraicGeometry.EffectiveCartierDimensionDrop
- Sheaf.AlgebraicGeometry.AmpleOfAffineGeneratingLoci
- Mathlib.AlgebraicGeometry.Noetherian
- Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
- Mathlib.AlgebraicGeometry.Morphisms.Proper
- Mathlib.AlgebraicGeometry.Morphisms.Finite
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
- Mathlib.AlgebraicGeometry.Morphisms.Separated
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType
- Mathlib.AlgebraicGeometry.Morphisms.Immersion
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
- Mathlib.Algebra.MvPolynomial.Basic
- Mathlib.RingTheory.Spectrum.Prime.Topology
- Mathlib.Topology.Baire.Lemmas
- Mathlib.AlgebraicGeometry.Morphisms.Integral
- Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
- Mathlib.Topology.NoetherianSpace

The old public imports remain available transitively through the extracted interface;
this is not an API withdrawal. Most old proof dependencies remain mathematical steps
of the two lower statements, and have been moved to their DAG plans instead of being
imported by a sorry proof. In particular the sections-vanishing theorem, Serre
vanishing, Bertini smoothness and the local differential criterion remain needed.

The node lem-pc-ample-affine-loci-criterion / module
Sheaf.AlgebraicGeometry.AmpleOfAffineGeneratingLoci is not needed on this route:
the specified projective closed immersion witnesses very ampleness directly, and
the first tensor power witnesses the required ample power. Its obsolete tool_uses
entry was removed. This does not withdraw that node or any adopted source declaration.
No module is withdrawn, and no claim is made that a module used elsewhere is globally
unreachable. The item's parent and the blueprint unit's realized route are preserved.

## Where the brief, the DAG or earlier work was wrong

The original twelve-step plan gives the mathematical argument but leaves substantial
interface glue unstated: finite-support first-order sections versus the concrete
stalk-frame jet, and complement Bertini versus the prescribed-point smoothness open.
The two remaining results isolate these independent source arguments rather than
renaming the original conclusion. Existing dependencies were read first and retained
in their plans. In particular, their existing sorry bodies are allowed dependencies.

The affine-loci ampleness detour is unnecessary for a specified closed projective
embedding. The purity step also needs componentwise reasoning; total dimension of a
Cartier divisor alone is not the purity assertion. This packet supplies that reasoning.

The compile server repeatedly returned exit 124 with 'no answer'; those checks were
retried while continuing proof work. No script, build timeout or launcher metadata
was modified, and no source-library signature, attribute, public import or definition
body was edited.

## New nodes

- def-zl-prescribed-point-system-data: identical concrete interfaces moved to an
  acyclic public module; no new mathematical assumption or construction.
- lem-zl-prescribed-point-eventual-jet-system: source interpolation/immersion and
  simultaneous jet separation, without any general-smooth-member conclusion.
- lem-zl-prescribed-point-bertini-open: source derivative open and Bertini smoothness
  for a fixed system, without the high-degree construction or dimension assertion.
- lem-zl-effective-cartier-pure-dimension: proved componentwise Cartier purity.
- lem-zl-prescribed-point-smooth-member: proved affineness, containment and purity
  around the smoothness/nonzero-jet open.

Change record: coord/changes/S6-prescribed-point-interface-extraction.md.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
