## What changed

Preserved the signature and public import of exists_ordinaryFiniteP1Adjunction.
Its proof constructs the normalized twist transport, represents the actual Kummer
classes by the proved class comparison, equips the specified maps with their unique
inverses, builds an adjunction from component triangle identities, and fills every
field of OrdinaryFiniteP1Datum. The trace/Chern equation and trace base-change square
are proved by biproduct and isomorphism cancellation, not additional assumptions.

Added OrdinaryFiniteClassComparison: the specified integral generator corepresents
global sections, and ordinaryFiniteClass_bijective follows from the already proved
adopted-library universal Ext/cohomology comparison. This is a reusable comparison
lemma, with no new hole. Added OrdinaryFiniteTraceCounit: naturality of the ordered
projection, a tensor-trace natural transformation, its inverse-projection counit,
and both general and projective-line normalization equations are proved.

The geometric residue is two separate source results. OrdinaryFiniteP1KummerMaps
is the cohomological decomposition and its component square, with no adjunction.
OrdinaryFiniteP1DiagonalUnit assumes that splitting and supplies the supported-diagonal
unit, its two triangles, and the actual-counit square, with no decomposition conclusion.
These retain the original fibre/Kummer/scalar-extension and diagonal-kernel routes.
The geometric module also proves ordinaryFiniteP1_geometric_cohomology and
ordinaryFiniteP1_geometric_kummer_normalization: the root sheaf has only its two
cyclic fibre cohomology groups, and the degree-normalized trace takes the actual
Kummer boundary of O(1) to one. Its degree is computed from the existing two-chart
coherent cohomology as chi(O(1))-chi(O)=2-1.

No existing definition, theorem signature, attribute, public import or source-library
file changes. The conservative attribute-scan change record is
coord/changes/B2-ordinary-finite-p1-proof-attributes.md; it records the new private
constructor attribute and proof-local transparency controls, with all four textual
consumers checked. No consumer adaptation is needed. Chern representatives
are unique by the proved class bijection; splitting inverses are unique. The diagonal
unit is determined by its fixed counit and the two triangle identities; this is proved
explicitly by existsUnique_componentUnit using Adjunction.ext_counit before the
family is selected. No unconstrained witness is used as data.

All five delivered Lean modules compile cleanly through lcompile.py. The class
comparison, trace-counit API, both geometric statements and the assembled parent
were checked against the sandbox dependency artifacts. Explicit #print axioms checks
for existsUnique_componentUnit, trace_baseChange_of_decomposition and
trace_chern_of_decomposition show only propext, Classical.choice and Quot.sound.
The diagnostic commands were removed from the delivered source. Preflight compilation
also passed for all five modules. Its four per-module axiom probes timed out at
60 seconds; the tool explicitly defers these probes to the merge check.

## Proved and sorry left

Closed the item body's hole in
AlgebraicGeometry.Etale.exists_ordinaryFiniteP1Adjunction by a complete proof from the two
source statements below. This is a decomposition of one old hole into two simpler holes,
not a net reduction of the sorry ledger.

Proved without adding holes: ordinaryFiniteClass_bijective and its integral-generator
comparison; existsUnique_ordinaryFiniteP1Chern (used to choose the Chern family);
ordinaryFiniteP1_isUnit; ordinaryFiniteP1_geometric_cohomology;
ordinaryFiniteP1_geometric_kummer_normalization and its degree-one computation;
ordinaryFiniteProjection_naturality; ordinaryFiniteTensorTrace_app;
ordinaryFiniteTraceCounit_projection; ordinaryFiniteP1TraceCounit_projection; and the
item's private existsUnique_componentUnit, adjunctionOfComponentTriangles,
trace_chern_of_decomposition and trace_baseChange_of_decomposition.

Exactly two holes are added and left, each as a public theorem whose body is `by sorry`:

- AlgebraicGeometry.Etale.ordinaryFiniteP1_kummer_maps
  (lem-asd-ordinary-finite-p1-kummer-maps).
- AlgebraicGeometry.Etale.ordinaryFiniteP1_diagonal_unit
  (lem-asd-ordinary-finite-p1-diagonal-unit).

The item has zero remaining holes; the delivery has two. There are no holes in
definitions or private helpers. Each remaining theorem has its source, complete proof
in words and a matching DAG node. Edge cases checked in the statements: N=1, the zero
coefficient ring, the empty base, disconnected or nonreduced bases, and nonflat finite
coefficient extension. No new nonemptiness, connectedness, field or flatness hypothesis
is imposed on the base or on A.

## No longer needed

No mathematical node or module is withdrawn. The source-library boundary is preserved.
The original geometric dependencies remain in the new nodes
as the plans for the two remaining source arguments. Only imports used by the
currently written Lean proofs are retained; the unproved source arguments will
import their additional declarations when their proofs are written. The parent now imports the two smaller source interfaces
and the proved class and counit APIs.

The following original direct imports are no longer needed by the parent proof
and have been removed. The new geometric modules retain only their actual proof
imports. Their DAG plans still name the geometric facts needed for the remaining
arguments, so this is no mathematical withdrawal:

- Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
- Mathlib.Algebra.Homology.ShortComplex.ShortExact
- Mathlib.AlgebraicGeometry.Morphisms.Proper
- Mathlib.AlgebraicGeometry.Pullbacks
- Mathlib.AlgebraicGeometry.ZariskisMainTheorem
- Mathlib.CategoryTheory.Sites.Point.Basic
- Mathlib.CategoryTheory.Sites.Point.Skyscraper
- Sheaf.AlgebraicGeometry.ExactUnboundedExchange
- Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
- Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
- Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero
- Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
- Sheaf.AlgebraicGeometry.ProperProjectionFormula
- Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
- Sheaf.AlgebraicGeometry.SecondKummerDivisors
- Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
- Sheaf.Paper.RingedExchangeTensorCoherence
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
- WeilConjectures.AlgebraicGeometry.Curve
- WeilConjectures.AlgebraicGeometry.Curve.Estimate
- WeilConjectures.AlgebraicGeometry.Curve.PicProperNTorsion
- WeilConjectures.AlgebraicGeometry.Curve.PicardDecomposition
- WeilConjectures.AlgebraicGeometry.EffectiveCartier
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace
- WeilConjectures.AlgebraicGeometry.Sites.Kummer
- WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
- WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

The following original direct imports are redundant in the parent and were removed;
the definitions or general infrastructure they supplied remain available through the
retained public interfaces and/or the retained geometric dependency closure:

- Mathlib.AlgebraicGeometry.Morphisms.Smooth
- Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
- Mathlib.Topology.Defs.Filter
- Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
- Sheaf.Paper.ProjectionMateExact
- Sheaf.Paper.RingedTopoiCanonicalTensorPullback
- WeilConjectures.AlgebraicGeometry.DerivedCategories
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
- WeilConjectures.SixFunctors.Etale.Derived.Tensor
- WeilConjectures.SixFunctors.Etale.Derived.TensorStructure


After profiling module linting, OrdinaryFiniteP1KummerMaps retains exactly these
private proof imports:

- Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero
- WeilConjectures.AlgebraicGeometry.Curve.Estimate
- WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
- WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine

Its other private imports listed above, and its private import of
OrdinaryFiniteClassComparison, were removed. OrdinaryFiniteP1DiagonalUnit has no
private proof imports; its statement needs the two public interfaces it imports.
The DAG plans preserve all mathematical dependencies needed to finish those proofs.

No graph-pruning credit is claimed for removing these direct imports.

## Where the brief, the DAG or earlier work was wrong

No false statement was found and no target was changed. The original DAG combines
separate cohomological decomposition and supported-diagonal arguments in one item.
The packet records these separately and implements their formal combination in Lean.
The canonical Chern representative needed an explicit check of the specified integral
generator; the existing adopted-library comparison applies after that check.

Repeated normalization of the derived tensor structure was expensive. The counit API
constructs the unitor and tensor trace over an abstract coefficient category and then
specializes to ModuleCat A, preserving exactly the original ordered map and unitor.
The derived tensor stays locally irreducible during naturality as well as unitor
construction. Both new inverse-projection counit constructors are irreducible; their
proved projection equations supply the normalization API used by consumers.
Local irreducibility attributes keep proof elaboration from expanding the recorded
functor wrappers. The new private adjunction constructor is irreducible, with proved
unit and counit equations used by both normalization and base-change consumers; this
avoids repeatedly normalizing the derived-category constructor. No compiler limit
is raised and no existing definition is changed.

The existing OrdinaryFiniteP1Decomposition, ProjectiveLineTrace,
ProjectiveLineFullAdjunction and ProjectiveLineDiagonalIntegrals interfaces already
import this item, so importing them here would create a cycle. The new interfaces
state the two source components below that cycle; they do not replace or withdraw
any existing declaration. The normalized class comparison is not a duplicate of
lem-weil-pbc-etale-module-cohomology-forget: that node compares derived global sections,
whereas this result identifies the actual specified integral-generator Ext map.


The additional geometric normalization uses the adopted degree trace in
Curve.RootsOfUnityTop. The source plan identifies O(1) with a point divisor; the
proved Lean calculation instead computes its degree by the existing two-chart
cohomology, preserving the specified O(1) and its Kummer boundary. Roots and
projective twist definitions are locally irreducible to keep elaboration within
the existing compile limit. The degree proof uses the existing monomial basis
directly. ordinaryFiniteP1_isUnit names the projection transport once, replacing
repeated global-section casts in all three consumers. Diagnostic profiler and
heartbeat settings were removed. No existing definition or global reducibility changes.

## New nodes

lem-asd-ordinary-finite-class-comparison records the proved, normalized derived-Hom to
cohomology bijection, including its exact integral generator.

def-asd-ordinary-finite-trace-counit records the explicit natural inverse-projection
counit and its proved normalization API.

lem-asd-ordinary-finite-p1-kummer-maps is the strictly cohomological part of original
steps 1--4, with the normalized Chern arrows supplied as input. Its statement does not
assert a trace adjunction. Its source is the projective-line decomposition theorem.

lem-asd-ordinary-finite-p1-diagonal-unit is the remaining diagonal-kernel argument of
original steps 5--9, conditional on the splitting. Its source is the projective-line
adjunction proof and the diagonal-integral lemma. Its statement supplies no splitting.

The original node's proof and proof_deps follow the actual Lean assembly. Existing
statements, Lean attachments, unit routes and maintainer tool-use approvals are retained.
Change record: coord/changes/B2-ordinary-finite-p1-proof-attributes.md. It documents
the proof-local attributes and private constructor; existing signatures and
definitions are unchanged.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
