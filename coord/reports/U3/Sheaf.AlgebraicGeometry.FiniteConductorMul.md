## What changed

Corrected and proved Subalgebra.exists_base_mul_mem_of_mem_map_jacobson_pow in
Sheaf.AlgebraicGeometry.FiniteConductorMul. Its original statement is false: it allowed
an arbitrary exponent. The added hconductor hypothesis is precisely the property supplied
by Subalgebra.exists_jacobson_pow_mul_mem_base at the caller.

Rewrote the ideal power using Ideal.map_pow, then used Submodule.span_induction with
an arbitrary multiplier. Generators use hconductor, zero uses witness 0, sums use c+d,
and scalar multiplication absorbs its scalar into the multiplier. No new lemmas or holes.

Adapted only the two forced proof lines in Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPower:
retain hconductor when obtaining r, and supply it to the changed helper. Its statement
and visibility are identical. Change record: coord/changes/finite-conductor-mul-exponent.md.

## Proved and sorry left

The corrected Subalgebra.exists_base_mul_mem_of_mem_map_jacobson_pow
(node semilocal-dim-one-conductor-power-mul) has a complete proof: one textual hole closed,
zero holes added, zero split off. The original false assertion is corrected, not proved;
this should not be counted as a proof of its original statement. No sorry remains in
either delivered module. The caller still depends on the pre-existing auxiliary theorem
exists_finite_adjoin_with_jacobson_power (semilocal-dim-one-conductor-power-aux); it is
not modified or added here.

## No longer needed

Removed the proof import Sheaf.RingTheory.FiniteIntegralConductor from FiniteConductorMul.
The local proof no longer uses node lem-sc-finite-integral-conductor directly: it uses
an explicit conductor hypothesis and Mathlib instead. The finite-conductor module and
node remain necessary at the caller, so no global pruning of that module is claimed.
Added the proof-only import Mathlib.RingTheory.Ideal.Maps. All public imports are retained.
No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original helper omitted the condition making r a conductor
exponent. At r=0, z=1, it would force every element of A into B. A counterexample is
B=Q[t^2,t^3]_(t^2,t^3), K=Q(t), A=B[t], a=t: A is finite and t is outside B.
The caller obtained and discarded the necessary property. Stacks 09N2 explicitly uses
a suitable exponent. The DAG statement and proof are corrected openly, with the only
citer recorded as still valid because it already has that property. The unit route is kept.

Searches: msearch leanfinder found Ideal.map and membership lemmas; msearch loogle found
Ideal.map_pow. Local rg found no duplicate helper and identified the only call. Read
Mathlib RingTheory/Ideal/Maps.lean and LinearAlgebra/Span/Defs.lean for span induction.
The local source mirror lacks literature/stacks-project/varieties.tex; the source was
read on the official Stacks page https://stacks.math.columbia.edu/tag/09N2.

## Forced adaptations

Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPower is unclaimed in this checkout.
Only line 60 (retain hconductor) and line 65 (pass it) are changed. Without these edits,
the old argument `(a ^ r)` occupies the new hconductor argument, causing a type mismatch.
The delivery tool verified the original against the changed helper fails and the
adapted copy compiles. The initial missing published auxiliary object was resolved by
the next library refresh. Both delivered modules now compile without warnings; the
axiom probes pass and deliver3.py --no-push printed OK (except for the second reading,
which is intentionally reserved for the second reader). No delivery was pushed.
The statement-change record passes node_fields.check_statement_change.

Original caller compiler error against the corrected dependency:

```text
/home/ubuntu/weil-sandbox/U3/Sheaf.AlgebraicGeometry.FiniteConductorMul/scratchpad/lean/Sheaf/AlgebraicGeometry/SemilocalDimOneConductorPower.lean:65:12: error: Type mismatch
  a ^ r
has type
  ↥A
of sort `Type v` but is expected to have type
  ∀ b ∈ ⊥.jacobson ^ ?m.221, ∀ (a : ↥A), ∃ c, (algebraMap B K) c = (algebraMap B K) b * ↑a
of sort `Prop`

(with the modules compiled into /home/ubuntu/weil-sandbox/U3/Sheaf.AlgebraicGeometry.FiniteConductorMul/scratchpad/.lbuild) [1.6 s]
[exit code 1: NOT compiled]
```

## Second reading by U3

1. Compared both delivered modules with the repository using diff. Verdict: the
only signature change is the declared addition of hconductor, recorded verbatim
in coord/changes/finite-conductor-mul-exponent.md and in the helper node's
statement_change. The old assertion is false: at r=0 and z=1 it implies A=image(B).
In the stated cusp counterexample, the t-adic valuation of a nonzero element of
B cannot be 1 (denominators have nonzero constant term), whereas t has valuation 1.
The caller's signature and visibility are byte-for-byte unchanged; its only
proof edits retain and pass the previously discarded conductor property.
No target or definition changed.

2. Compiled both modules in import order with lcompile.py --all: no errors or
warnings. Inspected the entire delivered Lean sources: no sorry, axiom, unsafe,
opaque, implemented_by, extern, or data definitions. Scratch-copy #print axioms
reports [propext, Classical.choice, Quot.sound] for the corrected helper and
[propext, sorryAx, Classical.choice, Quot.sound] for the unchanged caller,
whose auxiliary existence theorem remains open upstream. Independently compiled
the original caller against the corrected helper: it fails at the new argument,
confirming the adaptation is forced. The delivered caller compiles.
Verdict: the corrected statement has a complete proof; the original false
statement is corrected, not proved. One textual hole removed, zero holes added.

3. No statements are split off, no new nodes are introduced, and no new holes
need docstrings or duplication checks. Tested the corrected helper at r=0:
hconductor itself then forces A=image(B), so there is no longer a contradiction.
For z=0 or a=0, witness 0 works. The general proof handles arbitrary r and
mapped ideal generators, sums, and scalar multiples without extra assumptions.
Verdict: the conductor hypothesis is true at the actual caller and sufficient.

4. Rechecked the official Stacks 09N2 proof, which explicitly selects a suitable
exponent with J(B)^r A contained in B. Independently searched with msearch loogle
for Ideal.map_pow and inspected Ideal/Maps.lean for map membership, map/comap,
and span induction; local rg found the only actual call and no duplicate helper.
No shorter existing conductor assertion was found. The proof uses map_pow and
span induction directly; its statement imports and proof-only Maps import are
appropriate. The removed helper proof dependency lem-sc-finite-integral-conductor
is fully listed under No longer needed and remains used by the caller.
Read dag/units/sk-thm-curveestimate.json: its realized statement remains
thm-sc-proper-cohomology, with no steps bypassed or changed. Verdict: pass.

5. Compared the changed helper node with its Lean statement and proof: the explicit
hypothesis, empty proof_deps, and agent proof_origin match the direct Mathlib
argument. The statement-change record includes the old statement and proof and
the only DAG citer. Found an existing mismatch in the caller node: its proof
step uses lem-sc-finite-integral-conductor but proof_deps omitted it. Added that
dependency in the delivered copy; no statement or unit metadata changed.
Verdict: the delivered nodes now agree with the Lean proof.

Second-reader changes: removed three parser-output pseudo-rows from the change
record's Users table; added the missing finite-conductor proof dependency to
semilocal-dim-one-conductor-power; appended this independent reading. No Lean
proof needed repair. This delivery proves the corrected helper, not the old
false assertion, and claims no global pruning of the finite-conductor module.

## Forced adaptations

### Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPower
Original against changed dependencies failed:
```
/tmp/forced-adaptation-mkvcwbfc/lean/Sheaf/AlgebraicGeometry/SemilocalDimOneConductorPower.lean:65:12: error: Type mismatch
  a ^ r
has type
  ↥A
of sort `Type v` but is expected to have type
  ∀ b ∈ ⊥.jacobson ^ ?m.221, ∀ (a : ↥A), ∃ c, (algebraMap B K) c = (algebraMap B K) b * ↑a
of sort `Prop`

(with the modules compiled into /tmp/forced-adaptation-mkvcwbfc/.lbuild) [1.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
