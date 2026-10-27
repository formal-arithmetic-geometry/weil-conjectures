## What changed

Replaced the hole in WeilConjectures.sfFiniteOpenPresentation by an assembly
from the finite restriction comparison and a coefficient calculation on one
extension generator. The proof constructs the left comparisons by composing
actual adjunctions and applying leftAdjointUniq. A private, completely proved
finiteExtension_hom_ext reduces equality of morphisms to the recorded
finiteExtensionSection generators, using the sheafification adjunction and
DirectSum.induction_on. The supplied e.sections then converts the generator
calculation into the required natural-isomorphism equality.

Added Sheaf.Paper.SfFiniteOpenRestrictionPresentation with explicit definitions
of the realization section map, slice recomposition isomorphism, finite open
adjunction, right-comparison normalization, and left comparison constructed from
a supplied right comparison. No definition chooses an arbitrary witness from
an unproved theorem. The sole remaining theorem in this module is the
single-coefficient section-normalized right restriction comparison.

Added Sheaf.Paper.SfFiniteOpenCoefficientGenerators for the adjacent coefficient
law on a single represented generator, with supplied normalized right
comparisons. Two explicit named isomorphisms package the intrinsic and lower
coefficient composites. Explicit, generically proved identity maps transport
section carriers under restriction. The section law is a literal pointwise
equality with those maps; a proved generic helper consumes e.sections (HEq).
It has no OpenData parameter and asserts no equality of natural
transformations. Moved the original proved restriction equality and its eqToIso
to this module with identical names, signatures and bodies, re-exporting them
publicly from the item. This is necessary to state the generator lemma without
an import cycle. Change record:
coord/changes/F7-finite-open-generator-assembly.md.

## Proved and sorry left

Closed the original hole in WeilConjectures.sfFiniteOpenPresentation, node
lem-sf-finite-open-presentation-coefficients, by a complete Lean assembly.
The item's module has zero remaining holes. The existing proved theorem
WeilConjectures.sfFiniteOpenPresentation_restriction_eq remains proved.

Added exactly two named holes:

- WeilConjectures.sfFiniteOpenRestriction_presentation,
  node lem-sf-finite-open-restriction-presentation: a unique section-normalized
  right comparison at one finite coefficient, without any coefficient square.
- WeilConjectures.sfFiniteOpenCoefficient_generator,
  node lem-sf-finite-open-coefficient-generators: the intrinsic scalar comparison
  applied to one generator and one adjacent quotient, with normalized right
  comparisons supplied, and without an ordinary slice comparison.

This is a decomposition: one original hole closed and two finer holes added,
net minus one. It is not a sorry-free proof of the target closure. Each lower
statement is a strict step of the original argument; the original ordinary
coefficient square and its natural-transformation extensionality are proved
in the item's module rather than repeated as another hole.

Validation: lcompile.py accepted the final restriction module (59.1 s),
generator module (5.1 s), item module (53.0 s), and original direct importer
SfSupportTransitionPresentation (44.6 s). All are below the 60 s limit.
The importer copy was byte-identical to the current shared source and was
removed after checking. No profiling or altered transparency options remain.
The delivery tool performs its own compile and preflight before pushing.

## No longer needed

No module is pruned and no existing public import is removed. The original
direct proof citation def-weil-integral-reduction-tower is not needed for the
successor restriction computation: the actual definition used is
normalizedDVRQuotient, recorded by def-coef-normalized-dvr-tower. The new generator
node records this corrected dependency. This does not withdraw the unrelated
canonical integral reduction tower or its module.
The main node's direct proof edges now name the two more precise obligations;
the original localization, intrinsic adjunction, coefficient coherence and
quotient-transition dependencies remain needed below those obligations.
No upstream declaration is changed or withdrawn, and the unit route is kept.

## Where the brief, the DAG or earlier work was wrong

The successor computation originally cited the canonical integral reduction
tower node, which does not own normalizedDVRQuotient; its actual normalized-DVR
tower definition node is now cited.

The original plan's instructions to identify the right restrictions and compare
represented sections were not declarations that directly instantiate the desired
presentation isomorphism. The current dependencies provide the site equivalence,
actual adjunctions, normalized coefficient square, and slice generator formulas,
but not the comparison between these two concrete module presentations. The new
statements expose precisely those two steps, with a literal section equation
rather than an unspecified choice of a compatible family. No mathematical
counterexample or statement weakening was found.

The naive section formula hit a kernel timeout because converting a module
section to its restricted carrier unfolds the actual normalized quotient. The
carrier identity is now defined for an arbitrary ring-sheaf map and specialized
to that quotient, so the constructed finite extension need not be unfolded.
The generic heterogeneous-function helper is proved from eq_of_heq and congrFun;
no shared definition or transparency option was changed. The generator module
then compiled in 5.9 s, with 210 ms of kernel checking in the profiler.

The normalization was checked on the empty open (only zero ambient sections
can contribute) and the identity open (the same realization unit and counit),
and includes the zero module and the initial finite coefficient n = 0. Neither
new statement adds a quasi-compactness, properness, constructibility or
completion hypothesis. The current blueprint's extension-by-zero construction
is the same direct-sum/Kan-extension and sheafification construction used here.

## New nodes

lem-sf-finite-open-restriction-presentation records the single-coefficient
right restriction identification with its concrete section normalization.
Its definitions construct all maps from supplied data; the theorem alone is
still sorry. Its proof in words identifies the sites and scalar actions,
transports through the specified equivalences, and establishes uniqueness by
bijectivity of the realization section maps.

lem-sf-finite-open-coefficient-generators records the adjacent intrinsic scalar
law on a represented extension generator. Its proof in words uses the
left-adjoint uniqueness unit equation and the published normalized open
coefficient comparison. Sheafification/direct-sum extensionality and the
arbitrary ordinary slice comparison are left to the fully written parent
proof, so this is strictly smaller than the parent's natural-isomorphism square.
The node also owns the two moved, already-proved restriction declarations.

Change record: coord/changes/F7-finite-open-generator-assembly.md.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
