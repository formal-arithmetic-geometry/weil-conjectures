## What changed

Added CategoryTheory.brownHypothesesFor_coefficientIso_iff, a complete proof that the
Brown bundle is invariant under an isomorphism of commutative condensed coefficient
rings on any scheme. It imposes no field, finite-type, Noetherian or admissibility
hypothesis. The proof identifies the constructible finite-Tor property as the inverse
image under the exact derived scalar equivalence, pulls back its thickness, transports
essential smallness along the induced full-subcategory equivalence, and uses the
existing canonical Hom-map comparison to transfer compactness.

The integral branch of the supported finite-field assembly now transfers the whole
canonical integral Brown bundle through this theorem. Its separate thickness/size
calculation was moved into the other branch, where it remains needed. The new theorem
is used by this existing proof; it is not an unused additional specialization.

No imports are added: preservation for both directions of the coefficient isomorphism
and the unit of the exact derived equivalence supply reflection without a separate Tor
reflection or constructible-heart argument.
The scalar equivalence is constructed with the two maps of the given pulled-back
ring isomorphism as its functor and inverse. This avoids choosing another inverse
through IsIso and then comparing the corresponding derived functors. The general
implication clears its unused outer coefficient instances. Local irreducibility keeps
BrownHypothesesFor folded once its criterion API is used and coefficient admissibility
folded in the finite-field wrapper, which unfolds it explicitly to split its cases.
These attributes do not escape the namespace. The wrapper passes its supplied structure
morphism and morphism-property proofs directly to the finite-field assembly.
Every original declaration signature, visibility, public import, definition and
non-theorem body is unchanged. The private finite-field assembly and public finite-field
wrapper proofs change; the latter applies the assembly with explicit instance arguments. No consumer adaptation or target review is required.

Added one node and updated the main and supported finite-field proof routes.
Change record: coord/changes/A2-brown-coefficient-iso-invariance.md.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split-off holes: 0.
Proved CategoryTheory.brownHypothesesFor_coefficientIso_iff with no sorry, and used it
in CategoryTheory.brownHypotheses_finiteIntermediateField.
The sole remaining sorry is CategoryTheory.brownHypotheses,
node sk-lem-brown-hypotheses, retaining its original signature and
STATEMENT-DISPUTED diagnostic. This is a partial delivery of a proved transport step,
not a proof or decomposition of the disputed unconditional arbitrary-field theorem.

The project source parser confirms that all 23 original declarations retain their
signatures and visibility and all non-theorem bodies are unchanged. The only added
declaration is the proved invariance theorem. The final delivery gate performs the
single-file compilation, axiom and packet checks. No profiling options or temporary
probe declaration is delivered.

## No longer needed

The integral branch no longer invokes brownHypotheses_admissible_small for the original
coefficient, or separately combines thickness and size with transferred compactness.
It transfers those clauses with the whole Brown bundle. The smallness theorem and its
module remain used by the other coefficient branches and the existing public criteria.
The supported finite-field node now cites the invariance theorem instead of directly
repeating its coefficient-preservation and formal-criterion dependencies in the integral
step; those remain needed inside the invariance proof. No import, node or module is
withdrawn; none is claimed pruned from the target closure.

The new invariance proof itself needs no coefficient classification, finite-field datum,
Noetherian hypothesis, small skeletal representative family or geometric compactness
assertion. It transfers a supplied Brown bundle instead of asserting one unconditionally.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the remaining arbitrary-field theorem claims compactness without
cohomological finiteness. The available finite/rational compactness statement requires
a finite-field datum, while the integral statement requires explicit uniform Ext bounds.
The existing Kummer/infinite-transcendence diagnostic remains in the source unchanged;
this delivery does not claim a formal field-cohomology counterexample. Both current
callers continue to use the original arbitrary-field theorem, so replacing it by a
finite-field specialization would not preserve their route.

The existing coefficient helper transferred only compactness, although exact scalar
restriction transfers the entire Brown criterion. This delivery proves that larger
formal step and uses it in the supported integral branch. No field restriction is
silently changed, and no missing compactness assumption is renamed as a new hole.

Edge cases of the new theorem include the empty scheme, zero ring, identity ring
isomorphism, non-Noetherian schemes, and rings outside the admissible list. The proof
uses equivalences and preserves every Tor interval, the fixed coproduct universe, and
the canonical inherited shift. Both directions are obtained from the same implication
with inverse ring isomorphisms. No object is defined using arbitrary data chosen from
an unproved existence theorem.

## New nodes

lem-sfb-brown-coefficient-iso-invariance records the proved invariance theorem in the
item module. The source is the Brown unit's thickness/size/compactness assembly and
the coefficient identifications in its generation detail. The whole-blueprint search
for coefficient isomorphism found four unrelated nodes, none about Brown bundles.
LeanSearch found ordinary scalar-restriction equivalences, LeanFinder found triangulated
equivalence infrastructure, Loogle found no IsCompactObject theorem, and Mathlib grep
found the essentially-small equivalence APIs. Direct project search found and reused
the private compactness transport helper. The new node is fully proved, has no new
module, and introduces no hole. The unit route is retained.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
