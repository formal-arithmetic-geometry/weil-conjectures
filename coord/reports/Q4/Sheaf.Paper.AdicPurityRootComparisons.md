## What changed

In `Sheaf.Paper.AdicPurityRootComparisons`, proved the integer shift-degree identity,
ordinary etale Tate-power flatness, and generic-power flatness. All existing signatures,
definitions, attributes and public imports are preserved. Added one proved private helper
identifying the ordinary power recursions and the proof import
`Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`. The flatness characterization is already
available through the existing public FlatModel import; no redundant direct import is added.
Updated the owning node's proof, proof dependencies and proof origin to describe the partial
proof and the unchanged obligations accurately.

## Proved and sorry left

Closed three of six original holes; added zero holes and zero split-off statements:

- `WeilConjectures.adicPurityDoubleSuccSucc`.
- `WeilConjectures.adicPurityEtalePower_flat`.
- `WeilConjectures.adicPurityEtaleGenericPower_flat`.

Three original named obligations remain unchanged, all attached to
`def-pur-adic-root-comparisons`:

- `WeilConjectures.adicPurityRootComparison_existsUnique`.
- `WeilConjectures.adicPurityEtaleDiagonal_existsUnique`.
- `WeilConjectures.adicPurityRootQuotients_existsUnique`.

The private ordinary-power recursion helper is fully proved. No hollow definitions,
axioms or changed theorem statements.

## No longer needed

None. No existing imports, nodes or modules are withdrawn. The existing public imports
remain needed by the retained statements and definitions. The unit's realized route is
preserved. No new primitive-root or flatness infrastructure is required: the already
proved `finite_etale_torsion_twist_line` supplies the needed exactness directly.

## Where the brief, the DAG or earlier work was wrong

The original node had no proof steps or proof dependencies despite six named obligations.
The updated record separates the three completed steps from the three unchanged obligations.
The existing proved node `lem-asd-finite-etale-twist-line` is used as a flatness tool from
unit `sk-prop-sf-cbc`; it replaces no realized step of `sk-thm-purity-transport`.
No maintainer `tool_uses` approval is edited.

Edge cases: the ordinary-power recursion equality handles zero and one before the two-step
induction. The finite-twist theorem includes power zero, empty schemes and the zero ring.
Primality gives positivity of the root exponent. The global unit is mapped to every stalk,
so exactly the invertibility hypothesis required by the existing flatness theorem is used.

The quotient-family theorem has no invertibility hypothesis on l on T. Its unchanged
obligation should use generation of scalar-extension sheaves and tensor powers, rather than
assuming a primitive-root trivialization is available on every scheme. No stronger
hypothesis was added.

A complete proof of the diagonal obligation was explored but incurred expensive kernel
comparisons between generic derived tensors and the ordinary etale tensor instance. One
profiled run of that larger attempt passed at 59.5 seconds; other versions timed out.
The final packet retains the original diagonal hole and only delivers the three proofs
above. No timeout is classified as a tool failure, no file was split to evade the limit,
and no compiler limit or launcher script was changed. All development profiling and local
attribute experiments were removed from the final file.

The current blueprint was read at
`latest/blueprint/sec-proetale-coefficients/sk-def-sp-tate-twist/def-coefficient-twists-detailed.md`
and `latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/sk-thm-purity-transport.proof.md`.
The node's historical reconstruction source path has no counterpart in `latest`; the
proof-origin field records the current coefficient definition and finite-twist compatibility
paragraph. No statement or unit route is altered.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
