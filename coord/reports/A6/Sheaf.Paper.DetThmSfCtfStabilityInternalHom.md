## What changed

Replaced the one proof hole in
`AlgebraicGeometry.ProEtale.CondensedRing.internalHom_stability` by an explicit
assembly of the blueprint's argument. All original declarations, definitions,
public imports and the entire theorem signature are unchanged.

Four new modules isolate strictly smaller obligations: bounded-constructibility
triangulated closure for arbitrary admissible representatives, finite generation
by locally closed scalar-perfect pieces, bounded constructibility and evaluation
for a locally constant perfect dual, and the ambient locally closed support model.
Each contains one public named theorem with its source, proof in words and matching
new node. They introduce no definitions or chosen data.

The parent proves the dual's finite Tor amplitude directly from the existing
`internalHom_dual_tor_amplitude`, using its vanishing conclusion and the standard
`isGE_iff`/`isLE_iff` criteria. It tensors the dual with the support adjoint object,
applies existing direct-image stability, and transports membership through the two
actual internal-Hom isomorphisms. It equips Hom(-,L) with coherent exactness using
`DerivedCategory.nativeInternalHom_contravariant_exact`, takes the inverse-image
triangulated property on the opposite category, and applies finite generation.
The same generation theorem proves the final arbitrary-Q clause, using identity
isomorphisms to recognize each extension as a generator. The locally closed
adjunction witnesses and both formulas are retained in the conclusion.

Validation: lcompile.py compiled all five modules. The four new statement modules
compiled without warnings in 24.7--27.5 seconds; the final focused parent compile
was clean in 51.9 seconds. Profiling the initial assembly showed most proof cost in
type checking. Local irreducibility of upperStarFromPoint, the recorded dual and
derivedTensor, with explicit curriedTensor_obj_obj simplification in the Tor test,
keeps large wrappers out of routine conversion. No profiler options, enlarged
limits or transparency-disabling options remain. These annotations are local to
the proof file; no imported definition or public interface is changed.

## Proved and sorry left

Original hole closed in the text:
`AlgebraicGeometry.ProEtale.CondensedRing.internalHom_stability`
(node `det-thm-sf-ctf-stability-internal-hom`). Its assembly contains no sorry.

Added and remaining holes, each the entire proof of its named theorem:

- `AlgebraicGeometry.ProEtale.CondensedRing.admissible_boundedConstructible_isTriangulated`
  (`lem-sfb-admissible-bounded-constructible-triangulated`).
- `AlgebraicGeometry.ProEtale.CondensedRing.ctf_locallyClosedPerfect_generation`
  (`lem-sfb-ctf-locally-closed-perfect-generation`).
- `AlgebraicGeometry.ProEtale.CondensedRing.locallyConstantPerfect_dual_constructible`
  (`lem-sfb-locally-constant-perfect-dual-ctf`).
- `AlgebraicGeometry.ProEtale.CondensedRing.locallyClosed_support_hom_model`
  (`lem-sfb-locally-closed-support-hom-model`).

This is a decomposition: one original hole replaced by four smaller holes,
net -3, not a complete axiom-free proof. The parent still depends on sorry through
these obligations and existing dependencies. No hole is inside a definition,
instance, private declaration or the parent's proof.

## No longer needed

No original public import is removed. No existing module is withdrawn, and no
whole module is claimed pruned from the targets' import closure.

The factorization theorem `lem-pqf-qc-immersion-open-closed-factor` is unnecessary
for this proof: the assigned statement already supplies j and i with a=j≫i.
It is removed from the direct proof route and is not needed by the support-model
obligation either. No corresponding original Lean import existed to remove.

The remaining original dependencies are retained in the four obligations or used
directly in the parent. The setting, admissibility and constructibility nodes
remain statement dependencies. All proof imports added to the parent are private.

The new modules publicly import only the interfaces needed to state their
conclusions. In particular, the closure module does not import scalar-perfect
complexes or exceptional-adjoint existence; the perfect-dual module does not
import exceptional-adjoint existence or extension by zero; the generation module
does not import exceptional-adjoint existence; the support module does not import
scalar-perfect complexes or Brown existence merely to state its conclusion.

## Where the brief, the DAG or earlier work was wrong

The high-level proof is mathematically useful, but its recorded dependencies have
several nontrivial encoding gaps. The generic bounded-constructible triangulated
theorem concerns arbitrary local ring presentations, while the assigned predicate
requires scalar-constant presentations. The dual constructible-model theorem
uses explicit scalar realizations and its algebraic-closure clause concerns the
ring of all continuous maps, whereas current admissibility uses the finite-
subextension-valued condensed ring. The general ringed-site perfect-duality and
pushforward-composition interfaces use sectionwise modules. These assertions do
not typecheck directly as the assigned native internal-module assertions.
The new obligations explicitly require the comparisons with the actual operations
and coefficient rings; they do not identify the two algebraic-closure rings.

The theorem supplies S and Z without pre-existing k-structures. The parent gives
S the induced structure through a, and uses immersion into Noetherian X for
quasi-compactness. The support obligation likewise constructs the induced
structures before invoking geometric stability. No additional hypothesis is added
to the original statement. The unit's generation, support, duality and finite
triangulated devissage steps all remain; no chapter or unit route is bypassed.

Edge cases were checked in formulating the obligations: empty schemes and strata,
identity immersions, zero complexes, zero coefficient rings, finite rings of
infinite global dimension, negative degree bounds and unbounded second arguments
in evaluation. Generation requires cones and shifts only, not retracts. The
parent tests Tor against every module sheaf and preserves the sign [-b,-a].

There is no second worker or independent-reader claim in this report. The
maintainer's review is independent of this delivery, as required by the brief.

## New nodes

`lem-sfb-admissible-bounded-constructible-triangulated` realizes only Step 2,
before any internal-Hom or generation conclusion. It retains the coefficient
transport and finite scalar model comparison omitted by a direct application of
the generic triangulated theorem.

`lem-sfb-ctf-locally-closed-perfect-generation` realizes Steps 3--5, for an arbitrary
replete triangulated property and explicit extension objects. It makes no
internal-Hom stability assertion; the parent must prove that its Hom property
is triangulated and contains those objects.

`lem-sfb-locally-constant-perfect-dual-ctf` realizes Step 6 only: its conclusion is
bounded constructibility of the specified dual and evaluation against any ambient
object. It does not assert finite Tor amplitude. That remaining requirement is
proved in the parent from the existing Step 7 theorem.

`lem-sfb-locally-closed-support-hom-model` realizes Steps 8--10: ambient internal-Hom
formula, genuine restricted adjunction and support preservation. It applies to
any first argument P and says nothing about constructibility of RHom(P,G(N)).
The parent uses scalar-perfect duality, tensor and direct image to establish that
missing membership, then performs the finite devissage.

The first preflight caught and corrected a metadata extraction error: the generation
node signature had started at a word inside its docstring. It now starts at the
actual theorem declaration, as do all four signature fields.

All four nodes inherit the chapter/unit and have precise current-blueprint proof
places, complete dependency lists and actual LeanSearch/LeanFinder/grep records.
Whole-blueprint searches found only the parent and the finite-coefficient smooth
stratum duality statement, not these four interfaces. Existing native Hom
exactness is reused through its existing node. The record
`coord/changes/A6-internal-hom-proof-local-annotations.md` documents the local
elaboration annotations flagged by the static interface advisory. No existing
signature, definition, public import or statement is altered.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
