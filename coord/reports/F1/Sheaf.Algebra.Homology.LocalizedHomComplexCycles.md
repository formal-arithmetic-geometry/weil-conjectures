## What changed

Kept the existing signature and all four existing public imports of
`Sheaf.Algebra.Homology.LocalizedHomComplexCycles` byte for byte. Replaced its
proof by a reduction to existence of the component-defined forward function,
then bijectivity of any function with those components, assembled using
`Equiv.ofBijective`. Both auxiliary imports are proof-only.

The first worker's undelivered Equiv and Formula modules and their new nodes
were removed: the formula theorem asserted a canonical formula for an arbitrary
equivalence, which is false. The replacement modules are
`LocalizedHomComplexCyclesForward` and `LocalizedHomComplexCyclesBijective`.
Their signatures use the same complexes, restriction, cycles and projections.

## Proved and sorry left

Closed the original hole in `CategoryTheory.localizedHomComplex_cycles_aux`
by a complete reduction. Added two holes:

- `CategoryTheory.localizedHomComplex_cycles_forward`, node
  `lem-pur-localized-hom-complex-cycles-forward`: the projection components of
  a cycle assemble to a chain map (no bijectivity asserted).
- `CategoryTheory.localizedHomComplex_cycles_bijective`, node
  `lem-pur-localized-hom-complex-cycles-bijective`: a function with those
  components is bijective (existence of the function not asserted).

This is a decomposition: one original hole closed, two holes added, net -1.
The target still depends on `sorryAx`; it is not an unconditional finished proof.
No hole was put in a definition. Both remaining holes have complete proof
arguments and sources in their docstrings and matching DAG nodes.

## No longer needed

No dependency of the original proof is pruned. Its only old `proof_deps` node,
`def-pur-hom-complex`, remains used by both new nodes and the target signature.
All four original public imports are used in signatures. The undelivered
`LocalizedHomComplexCyclesEquiv` and `LocalizedHomComplexCyclesFormula`
modules/nodes are removed from this proposed delivery; they were never library
dependencies, so this is not counted as pruning.

## Where the brief, the DAG or earlier work was wrong

The first worker's `localizedHomComplex_cycles_formula` is
STATEMENT-DISPUTED: it quantifies over every equivalence, not a component-defined
one. On a one-object site with constant rational coefficients and complexes
concentrated in degree zero, chain maps are rational scalars. Postcomposing any
equivalence with negation changes its values on nonzero maps; both equivalences
cannot satisfy the same fixed projection formula. Mere existence of an
equivalence cannot fix this. The associated docstring and node described a
canonical equivalence without asserting canonicity in the Lean hypothesis.
Neither invalid auxiliary is delivered.

The repaired reduction asserts the component formula before bijectivity. This
keeps forward construction and inverse/product-kernel arguments separate.
The source is the construction in Stacks 0A8X preceding Equation 0A8Y, checked
at https://stacks.math.columbia.edu/tag/0A8X. Equation 0A8Y itself concerns
homology modulo homotopy, so the cycle statements are the preceding construction's
intermediate steps, not a verbatim quotation of that equation.

## New nodes

`lem-pur-localized-hom-complex-cycles-forward` realizes the forward component
construction in the existing proof plan. `lem-pur-localized-hom-complex-cycles-bijective`
realizes its joint-injectivity and kernel/product inverse argument. Both are in
`sec-smooth-purity`, unit `sk-def-sf-operations`, and have verbatim Lean signatures,
complete proof arguments, source, origin, searches and creation records.
No statement or definition change record is required: existing signatures and
public imports are unchanged.

## Second reading by F1

1. Compared the delivered target with the repository using `diff`: its existing
   signature, visibility and docstring are unchanged; edits are two proof-only
   imports, a documented local 400000-heartbeat limit, and the proof body. No existing definition or target is altered.
2. Checked each delivered file for prohibited declarations and for hollow
   definitions. The target proof constructs an equivalence from a bijective
   function and keeps the formula definitionally; only the two named auxiliary
   theorems contain `sorry`. All modules are locally compiled and their axioms
   checked through launcher scratch probes and delivery preflight.
3. Rejected the arbitrary-equivalence formula with the rational-scalar example
   above. Reviewed the replacements on zero complexes (unique zero chain map),
   complexes concentrated in degree zero (the ordinary internal-Hom product),
   and unbounded complexes (full products, no finite support). Each replacement
   is a proper part of the original argument. Their docstrings give the forward
   differential check and the converse product/kernel construction. Repeated
   searches with `leanfinder`, `loogle` and grep, and searched both library roots:
   LeanSearch was also attempted and returned an internal server error; this
   unavailable search is recorded without a verdict. Mathlib's `Cocycle.homOf`/`equivHom` apply to ordinary categorical Hom groups
   and do not supply the evaluated sheaf-product comparison.
4. Kept all original signature imports; both added imports are proof-only and
   used. The only old proof dependency is still used via both auxiliaries.
   `sk-def-sf-operations.json` has empty realized statement/steps lists; no unit
   realization is bypassed or changed. This is the original forward/inverse route.
5. Checked that the existing node describes forward function, bijectivity and
   `Equiv.ofBijective` assembly, and its dependency list is exactly the two new
   nodes. Each new node uses `def-pur-hom-complex`, agrees with its Lean signature,
   and has all required fields. Restored the original existing node fields that
   stage 3 does not own, instead of reserializing its statement as a change.

The unchanged nested section-complex types exhaust the default deterministic
heartbeat budget when checked against both auxiliary statements. A documented
local budget of 400000 permits the reduction; the single-file wall-clock
compile remains below the 60-second limit. No wall-clock limit was increased.

Explicit scratch-copy `#print axioms` checks for all three declarations passed:
each uses only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`
from the two disclosed holes. Scratch copies were removed.

Second reading changed the invalid split, expanded the remaining-hole proof
arguments, corrected the DAG route and verbatim signature records, and rewrote
this report to count the result honestly as a decomposition.
