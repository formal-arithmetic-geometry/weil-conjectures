## What changed

Reduced the unchanged existence theorem `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`
to two genuine intermediate assertions and proved the categorical assembly in Lean.

- Extracted the 65 existing declarations preceding the theorem, verbatim in signature,
  attributes, visibility and body, into `Sheaf.Paper.CoefficientDerivedSystemEvaluationData`.
  The original module publicly re-exports them and retains all original public imports.
  This separates the interface from its existence proof and avoids an import cycle.
  No existing module other than the assigned item is edited.
- Proved `coefficientClosedEnriched_isIso` and `coefficientClosedEnriched_naturality`.
  The private identification proof expands the five Hom bijections of
  `CategoryTheory.ClosedScalarHom.iso` and identifies its inverse with the actual
  evaluation-defined enriched adjunct. It cancels the tensor comparison and uses the
  two adjunction counit identities. This works for every tensor-preserving left adjoint.
- Added the real propositional definition `CoefficientDerivedSystemProjectionModels`.
  Its first clause concerns ordinary derived sections and total-limit projections,
  before internal Hom. Its second clause normalizes the finite scalar enriched adjunct
  on H-zero, before any system limit. Neither clause asserts a gamma identity or
  chooses data from existence.
- Split the remaining construction into `coefficientDerivedSystemResolutionModels`
  (normalized fibers, global comparison, resolution and these two model equations)
  and `coefficientDerivedSystemProjectionFormulas` (enriched gamma and Hom-zero
  projection identities for such models). Each has its own module, source, complete
  argument in words and DAG node. They are strictly different parts of the argument.
- The final proof explicitly constructs S from F and kappa, supplies enriched
  invertibility by the proved generic calculation, and combines the projection lemma
  with finite enriched invertibility. It proves gamma naturality by applying integral
  sections to enriched naturality and then naturality of kappa. A private, fully proved
  categorical calculation proves the tensor-parameter composition equation by
  adjunction naturality, tensor-comparison naturality and tensor functoriality.

Validation: all four delivery modules compile in import order with `lcompile.py`.
The extracted data file took 39.3 seconds, projection lemma 2.3 seconds, resolution
lemma 2.5 seconds, and final theorem 3.4 seconds. No transparency restriction or
compile-time limit was disabled. The server baseline item compiled in 36.9 seconds.
The 65 extracted declarations were compared against the current server source by
keyword, signature, body, visibility and attributes: no differences.
All 59 direct importers from the current server source were checked: 57 compile within
60 seconds against the delivered set.
Two unchanged consumers exceed 60 seconds in both the delivered set and isolated
compiles against the original item:

| Consumer | Delivery | Original item |
| --- | ---: | ---: |
| `Sheaf.Algebra.Homology.FlatScalarEvaluationModel` | 65.8 s | 65.7 s |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | 64.3 s | 65.8 s |

These are pre-existing timeouts, not forced adaptations; their sources are not
included in the packet. The independent reader must assess them. Every temporary
consumer source copy was verified unchanged and removed after these checks.
There are no consumer type errors and no adapted consumer files in the packet.

The node graph was checked with the delivered nodes overlaid: no new dependency
cycle or missing dependency. All delivered Lean lines have at most 100 characters.
The two existing definition-node owners now point to the extracted interface;
their mathematical statements are unchanged.

## Proved and sorry left

One original hole closed, by a decomposition:

- `WeilConjectures.coefficientDerivedSystemEvaluationCalculus` — its entire body is
  now a compiling Lean proof from the two intermediate declarations. Its signature,
  universes and conclusion are unchanged.

Two holes added and left, each as a whole named public theorem `:= by sorry`:

- `WeilConjectures.coefficientDerivedSystemResolutionModels` in
  `Sheaf.Paper.CoefficientDerivedSystemResolutionModels`.
- `WeilConjectures.coefficientDerivedSystemProjectionFormulas` in
  `Sheaf.Paper.CoefficientDerivedSystemProjectionFormulas`.

There are no other direct holes in the four delivered modules. In particular the
interface, new normalization predicate, generic enriched proofs, naturality assembly
and parameter-composition proof have none. This is a decomposition of one upper hole
into two lower holes, not a completed proof of the existence theorem from permitted
axioms: direct holes change 1 to 2, net minus one. Earlier auxiliary bodies in the
starting item were already proved and are not counted as new closures.

## No longer needed

The final proof does not need these three direct proof dependencies from the old plan:

- `lem-coef-closed-adjunction-enriched-isomorphism`, module
  `Sheaf.CategoryTheory.ClosedAdjunctionEnrichedIsomorphism`: use the already proved
  five-Hom-bijection comparison and identify the actual map with its inverse instead.
- `lem-coef-closed-adjunction-naturality`, module
  `Sheaf.CategoryTheory.ClosedAdjunctionComparison`: naturality is that of the inverse
  comparison itself and then of the sections/limit comparison.
- `lem-coef-monoidal-adjunction-parameter-composition`, module
  `Sheaf.CategoryTheory.TensorParameterComposition`: the elementary categorical
  calculation is proved locally, with no new assumption or hole.

They are removed from this node's proof route; they may remain needed by other
modules or by the generic projection theory. No module is withdrawn and no global
pruning claim is made. Other original construction dependencies remain on the two
split nodes. All original public imports are retained for compatibility; existing
private imports needed by representative proofs move with those proofs to the data
module. The final assembly has only the data public import and the two new proof
imports in addition to that preserved public interface. No upstream declaration,
public import or proof is removed.

## Where the brief, the DAG or earlier work was wrong

The old import-environment note describes an earlier state. A fresh compilation of
the current item succeeds and the HomComplex owner collision does not recur.
The current server item has one direct hole, not the four retained in that old note.
The initial sandbox had no retained proof or report; the accepted scalar-prefix
split was already part of the server source and was preserved.

A consumer-only compilation initially lacked an unpublished scalar-calculus object
while preparing an upstream dependency. Compiling the delivery and consumers in one
ordered set resolves that artifact issue; it is distinct from the timing issue above.

The local shared snapshot changed while this session was running and temporarily
showed an older item and no scalar-calculus module. Current source and importer
records were therefore read from the server. Its item still has the scalar-calculus
split and the single final hole. No archived module was withdrawn or restored.

An initial, undelivered draft of the projection lemma was too general: arbitrary
resolution data alone do not fix the sections-evaluation comparison or finite
closed Hom-zero normalization. Rescaling those unspecified comparisons can change
the asserted projection. The delivered version requires the two explicit
ProjectionModels equations, constructed by the first lemma from normalized units
and cocycle-class evaluation. These are genuine earlier steps, rather than the
gamma assertion restated as a premise. The original theorem is not weakened.

## New nodes

- `def-coef-derived-system-projection-models`: the two real normalization equations,
  declared in `Sheaf.Paper.CoefficientDerivedSystemEvaluationData`.
- `lem-coef-derived-system-resolution-models`: normalized model construction, declared
  in `Sheaf.Paper.CoefficientDerivedSystemResolutionModels`.
- `lem-coef-derived-system-projection-formulas`: enriched and degree-zero projection
  transport, declared in `Sheaf.Paper.CoefficientDerivedSystemProjectionFormulas`.

All three include source pointers, the current unit and blueprint ancestor, actual
Mathlib searches, and accurate Lean attachments. The two new theorem nodes include
complete numbered proofs in words. No unit statement or unit proof step is bypassed.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
