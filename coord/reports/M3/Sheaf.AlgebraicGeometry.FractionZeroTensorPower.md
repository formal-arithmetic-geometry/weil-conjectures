## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_cohomology_eq_zero_of_subsingleton_fractions`
in `Sheaf.AlgebraicGeometry.FractionZeroTensorPower`, with its signature unchanged.
Added the proof-only import `Sheaf.Topology.ModuleCohomologyTopComparison`.
Mathlib's direct-limit declarations and monoidal tactics are already available
through the existing imports.

The proof establishes tensor transition coherence, maps the fraction quotient into
Mathlib's additive direct limit, applies its zero criterion, and transfers the result
through the already proved natural cohomology comparison. The first two private
coherence proofs reuse the corresponding private arguments in
`Sheaf.AlgebraicGeometry.InvertibleSectionRing`; their statements require no invertibility.
All other helpers are proved locally. Updated the existing DAG node's proof and proof
dependencies to record this argument and the comparison dependency.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_cohomology_eq_zero_of_subsingleton_fractions`
(node `lem-sc-section-affine-open-kills-cohomology-localization-step`).
No `sorry` remains in the item, and no hole or module is added elsewhere.
This is a complete proof of the item, not a decomposition into new holed statements.

Validation: `deliver3.py --no-push` compiled the module, checked the declarations'
axioms and unchanged signatures, and printed OK (with only the expected pending
second reading). An earlier standalone compile timed out under heavy machine load;
the delivery compile and axiom probe subsequently passed. The final dry run is
repeated after restoring the original theorem docstring and correcting this report.

## No longer needed

Removed the redundant proof-only import
`Sheaf.Topology.RingedSpaceModuleCohomology`: the new comparison import already
provides it transitively. No original dependency node or module leaves the target
closure, so this is import cleanup, not pruning of mathematical dependencies.
The original public import `Sheaf.AlgebraicGeometry.CohomologyFractionPresentation`
is needed by the theorem's statement, and the new comparison import is used.
Removed the redundant explicit imports `Mathlib.Algebra.Colimit.Module` and
`Mathlib.Tactic.CategoryTheory.Monoidal.Basic` from the working proof after verifying
that compilation succeeds without them. They were not present in the original file,
so this does not claim removal of modules from the target's import closure.
An isomorphism between the fraction presentation and the direct limit is unnecessary:
a homomorphism in one direction suffices for the zero criterion.

## Where the brief, the DAG or earlier work was wrong

The original DAG called the directed-system coherence and quotient zero criterion
steps elementary while leaving their Lean realization implicit. The coherence step
requires exponent transports and associativity induction; these are now proved in
private helpers. The top-open cohomology comparison was already available as a
proved declaration, and its node is now an explicit proof dependency.
No statement or definition was changed. The unit's statement and route are preserved.
The proof applies unchanged to degree zero, the empty scheme, the zero section,
and arbitrary (not necessarily invertible) L.

The first delivery dry run's source-inventory check rejected those two direct
Mathlib imports, despite their successful local compilation. Both were independently
verified redundant and removed; no tool or source outside the sandbox was edited.

## Second reading by M3

1. Compared the delivered module with the repository version. The theorem signature is byte-for-byte unchanged; the only interface change is the proof-only comparison import. The sandbox DAG node records the revised proof and dependencies, including the top-cohomology comparison.
2. Compiled the module with `lcompile.py`; it succeeds with no Lean errors. The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; its declarations use only permitted axioms. The sole split node is the existing item node, and no additional statements were introduced.
3. Checked the proof route against the imported declarations and searched for existing fraction/direct-limit denominator-clearing results. The private coherence lemmas are strictly intermediate and carry no public statement. The theorem remains valid for degree zero, the empty scheme, zero sections, and arbitrary modules L. The direct-limit zero criterion is applied to the quotient map, so no stronger or weaker theorem is substituted.
4. Verified pruning: the former `RingedSpaceModuleCohomology` import and redundant explicit Mathlib imports are absent; the comparison import is used. The unit route is preserved: comparison, directed-system coherence, quotient-to-direct-limit map, zero criterion, and naturality. No proof-dependency node is removed from the target closure.
5. The DAG proof steps, `proof_deps`, and `proof_origin` agree with the Lean proof. No target statement or definition changed, and no new node or change record is required.

Changed during second reading: added this review section only; no Lean code or DAG content was altered.
