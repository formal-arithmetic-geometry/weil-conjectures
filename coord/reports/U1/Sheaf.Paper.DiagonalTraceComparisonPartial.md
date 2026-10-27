## What changed

The item theorem now obtains normalized Chern/twist data on S and X, obtains the
specified geometric model, constructs its derived-limit square, and combines this
with scalar-restriction comparisons. The public statement and PartialPresentation
record are unchanged. Imports added to the item are private proof imports; the
new modules publicly import what their statements need.

The private traceLimits proof applies the existing general
`diagonalDirectImage_of_preservesKInjective` argument (imported with `import all`)
to the actual constant-coefficient direct image. It supplies Grothendieck structures
on the two module-sheaf categories and tower categories, and proves that the exact
left-adjoint tower inverse image makes tower direct image preserve K-injectives.
Unlike the public geometric specialization, this argument needs no extraneous
finite-field structure on X or S. The resulting comparison retains the complete
common-unit normalization. Private generic limit and tower-adjunction helpers
keep kernel checking from repeatedly unfolding the concrete sheaf constructions.
In the isolated limit probe the concrete specialization checks in 1.9 seconds;
the complete probe including its generic helpers compiles in 15 seconds.

The scalar comparison supplies a full ExactSquareOfUniverses. The combining proof
specializes its normalization to a K-injective complex, rewrites the canonical
cochain unit as the inverse of rightDerivedFunctorObjQIso, and cancels the mapped
hom/inverse pair. This proves the precise varying_normalization field, rather
than assuming that field under another name.

Validation: `lcompile.py --all` compiled all four modules, including the complete
assembly proof. Its only warning was an overlong docstring line, corrected in the
final source. The isolated cancellation and limit proofs also compile.

## Proved and sorry left

This is a decomposition, not a completed proof of the underlying construction.
One upper hole is closed: exists_diagonalTraceComparisonPartial (node
new-sfb-diagonal-trace-comparison-partial-existence). No sorry remains in the item.
The derived-limit subargument and the normalization cancellation are complete.

Three holes are added, each the entire proof of a public theorem in its own module:

- exists_diagonalTraceChernTwist: lem-sfb-diagonal-trace-chern-twist-existence.
  This is a construction on one scheme; it has no morphism, model, scalar-restriction
  comparison or limit data.
- exists_diagonalTraceGeometricModel: lem-sfb-diagonal-trace-geometric-model-existence.
  This takes the already constructed normalized Chern and twist data and supplies
  the geometric model and invertible line-projection mate; it has no coefficient
  cones, constant-scalar derived comparisons or derived-limit fields.
- exists_diagonalTraceScalarComparisons: lem-sfb-diagonal-trace-scalar-comparisons.
  This concerns scalar restriction for general geometric direct image, taking
  normalized Chern data and the two specified right-derived models as inputs.
  It does not assert Chern/twist existence, a projective model, derived limits,
  Milnor invertibility, a splitting, or a trace.

Thus the delivery closes 1 hole and adds 3, for a net increase of 2 before any
independently landed dependencies. No definition contains sorry or selects data
from an arbitrary unproved existence theorem. The existential witnesses are
eliminated inside a theorem proof; no data definition is built by choice from them.

## No longer needed

None. No existing import, declaration, module or unit step is withdrawn. The
original six planned proof dependencies remain relevant through the three
construction obligations and the existing derived-limit argument. The finite
field and finite-type hypotheses of diagonalTower_directImage are not needed:
its already proved general private argument is the one used here.

## Where the brief, the DAG or earlier work was wrong

The previous node had a single construction step covering independent local
Chern/twist, geometric, scalar-restriction and derived-limit problems. The six
listed dependencies provide generic constructions, not an existing constructor
for this specialized record. The semilinear calculus supplies tensor and scalar
models, but not the positive integral Kummer source/target equations and their
finite evaluations. Grothendieck abelianness supplies resolutions, not the
section-normalized residue restriction or its coefficient/root cones. Generic
composition compares specified ringed morphisms; it does not construct these
ordinary chart squares. The existing fixedScalarRestrictionDirectImageMap_isIso
also requires finite coefficient rings; the discrete Z_l target here is infinite,
and its theorem does not identify the strict sequence-site category. Their
declarations were inspected and exact-name,
Loogle, semantic and source searches found no such constructor.

The three new statements are strictly smaller parts of that source construction,
not another partial presentation. The unit route is retained: simultaneous
Kummer reduction, line twisting and geometric adjunctions, scalar restriction,
and the normalized direct-image/derived-limit comparison are all present.

Edge cases checked mathematically: the empty scheme, l=2, level n=0 (exponent 1),
identity morphisms in the scalar construction, and replacing a universal derived
model by its uniquely unit-normalized equivalent model. Scalar restriction is
not asserted to preserve K-injectives. No target or shared definition changed.

## New nodes

lem-sfb-diagonal-trace-chern-twist-existence records the one-scheme simultaneous
Kummer reduction, finite-boundary normalization, and actual tensor/Hom twist.

lem-sfb-diagonal-trace-geometric-model-existence records geometric coefficient/root
pullback and the invertible line-projection mate on the specified model m.

lem-sfb-diagonal-trace-scalar-comparisons records exact constant-scalar restriction,
coefficient/root cones, and both full unit-normalized direct-image squares.

Each is in a separate new Sheaf.Paper module, with its source and proof in words.
The existing item node now records their combination, the proved limit argument,
and the canonical-unit cancellation. No change record is needed: no existing
public interface, statement or definition changed.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
