## What changed

Proved `AlgebraicGeometry.exists_perfect_generator` in
`Sheaf.AlgebraicGeometry.PerfectGeneratorExists`, preserving its signature and all public
imports. Added proof-only imports of `SupportedPerfectGenerator` and
`SupportedDerivedGeneratedPerfectCore`; retained `PerfectObjectCompact`.

Specialize the existing supported-generator theorem to support equal to the entire scheme.
Its empty complement is compact and every support condition is vacuous. This gives a single
perfect quasi-coherent weak generator P and triangulated closure. Apply the existing tower
core to the empty open, supplying compactness of this same P. For every candidate property Q,
induct on the tower from zero, using closure under shifts, coproducts and middle terms of
triangles. Reindex the countable sum by `ULift.{u} ℕ`, then use closure under third terms on
the telescope triangle. This proves the localizing clause without using retract closure.
No witness is chosen in a new definition; the existential witnesses are eliminated inside
the theorem proof.

Updated the existing DAG node `lem-pc-perfect-generator-exists` to record this route.
No definitions, signatures, instances or visibility changed; no adaptations are needed.
The unit `sk-thm-picard-duality` has empty realized statement and step lists: no unit-level
statement or realized proof step is bypassed. The source-supported theorem and tower core
are tools for this node's existence and closure argument.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.exists_perfect_generator`
(node `lem-pc-perfect-generator-exists`). Proved 1 of 1 original sorries; added 0 holes.
No sorry remains in the delivered module. The proof uses existing library theorems;
it does not claim to have closed all of their transitive proof dependencies.

The module compiled cleanly with `lcompile.py`, including both independent universe
parameters u and w. No new statement requires edge-case testing. In the specializations,
support is the whole space and the excluded open is empty, so the support premises are
vacuous even when X is empty. Empty attaching families and the initial zero stage are
covered by the supplied coproduct and triangulated closure assumptions.

## No longer needed

Removed the following proof-only imports and direct proof dependencies:

- `Sheaf.AlgebraicGeometry.PerfectGenerationAffineBase`
  (`lem-pc-perfect-generation-affine-base`): the supported generator supplies existence.
- `Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction`
  (`lem-pc-perfect-generation-open-induction-step`): no separate open-extension construction.
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction`
  (`lem-sc-invert-s-cohomology-induction`): no separate induction on opens in this proof.
- `Sheaf.AlgebraicGeometry.DerivedQCohDirectSums`
  (`lem-pc-derived-qcoh-direct-sums`): supplied through the compactness/core interfaces.
- `Sheaf.CategoryTheory.CompactGeneratorsBuildObjects`
  (`lem-pc-compact-generators-build-objects`): the scheme-specific tower core provides the
  required ambient triangles with Type u sums for the same generator.

`def-pc-generators` is no longer a direct proof dependency: the shifted-Hom equivalence is
supplied directly by the supported generator. Its public module import is retained to
preserve the exported environment. All other public imports are also retained.

These are direct dependency removals, not assertions that the named modules become globally
unreachable: several remain transitive dependencies of the supported-generator/tower route
or are used elsewhere. No existing module or node is deleted.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan remains mathematically valid, but it duplicates the existing supported
perfect generator theorem at full support. The existing supported tower core also resolves
the indexing-universe issue in applying the generic compact-generation theorem when the
localization's morphism universe w is independent of the scheme universe u. Reusing it avoids
new glue statements or changing the target's coproduct closure hypotheses.

Searches: `msearch.py` LeanFinder query “single perfect generator quasi coherent derived
category scheme” returned generic derived-category declarations, no matching theorem;
Loogle `IsWeakTriangulatedGenerator` reported unknown identifier/no hits; grep
`perfect.*generator` returned no Mathlib match. Local rg searches located the supported
generator and tower core, whose complete signatures and proofs were read before use.
Import-direction checks accepted both new imports.

The repository's cited literature files are absent on this machine. Read the source directly
at https://stacks.math.columbia.edu/tag/0A9A (supported generator),
https://stacks.math.columbia.edu/tag/09IS (perfect generation), and
https://stacks.math.columbia.edu/tag/09SN (compact-generator tower).
No mathematical error or statement dispute was found.

## Second reading by U1

1. **Interface: pass.** Compared the only delivered Lean module with the repository using
   `diff -u` and independently compared the text from `theorem exists_perfect_generator`
   through `:= by`: the existing signature is byte-for-byte identical. Both universes,
   compactness, quasi-separatedness, and the derived-category assumptions on X and every
   open are retained. The existential includes perfection, quasi-coherence, detection
   for every quasi-coherent object and every integer shift, and the full ambient
   localizing clause with exactly the original Type u coproduct closure and retract
   hypothesis. No definition, instance, visibility or public import changed. The changed
   declaration docstring accurately records the new proof; no change record is needed.
2. **Proof and axioms: pass relative to the existing open dependencies.** Independently
   compiled the delivered file using `lcompile.py` with no errors or warnings (3.3 s).
   Searched its source for sorry and forbidden declarations/attributes: none present.
   A scratch copy compiled with `#print axioms AlgebraicGeometry.exists_perfect_generator`
   reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The last
   comes from existing dependencies, not a new hole in this delivery. There are no new
   definitions choosing arbitrary witnesses: P and the tower are eliminated within a
   theorem proving a proposition. Read the complete supported-generator, supported-core
   and perfect-compactness interfaces and the two supported proofs. Full support makes
   every stalk premise vacuous; the core takes the same P that detects zero. In the
   transition triangle the previous stage is object 1, next stage object 2, and the
   attaching sum object 3, so `ext_of_isTriangulatedClosed₂` is the correct rule. In the
   telescope triangle both first objects are S.pt, so the final use of closure under
   object 3 proves the desired E.obj clause. `Equiv.ulift` transports the colimit cofan
   to Type u without restricting the independent morphism universe w.
3. **Split statements and edge cases: pass.** There are no split-off statements, new
   nodes, or added holes. Checked the empty scheme, zero initial stage and empty
   attaching family: full support and empty excluded open remain vacuous, and zero and
   empty coproducts are covered by the supplied triangulated and coproduct properties.
   The unused retract premise is retained in the signature; using stronger available
   closure consequences does not weaken the statement. This closes the one original
   hole and adds zero, rather than moving its statement into a new sorry.
4. **Shortest route and pruning: pass.** Read Stacks Tags
   [0A9A](https://stacks.math.columbia.edu/tag/0A9A),
   [09IS](https://stacks.math.columbia.edu/tag/09IS), and
   [09SN](https://stacks.math.columbia.edu/tag/09SN). Full-support specialization of the
   first supplies the existence and shifted-Hom criterion of the second; the core
   supplies the third's tower argument for the fixed generator. Independently searched
   local Sheaf and upstream WeilConjectures/AlgebraicGeometry, and Mathlib, including
   `msearch.py ... grep 'localizing.*generator|generator.*localizing'` (zero hits).
   Read the nearby `derivedQCohPerfectGeneration` and compact-generation statements:
   the former gives closure of all perfect objects, and the latter a generating family,
   so neither supplies this fixed single-generator closure more directly. All three
   direct proof-only imports are used. Existing public imports are retained as part of
   the exported environment; neither new proof dependency is public. Compared all old
   proof_deps: the report lists all six removed direct dependencies, including
   def-pc-generators, and distinguishes direct removals from global unreachability.
   Opened `dag/units/sk-thm-picard-duality.json`: realized.statement is empty and its
   one realized step is empty. The route replaces only this node's internal tools and
   does not bypass a recorded unit statement or step.
5. **DAG: pass.** The node changes only proof, proof_deps and proof_origin; its statement,
   statement dependencies and Lean record remain unchanged. Verified proof_deps equals
   the union of the steps' uses: supported perfect generator, perfect-object compactness,
   and supported derived generation core. The final elementary step is exactly the
   explicit shift/coproduct closure, natural-number induction, colimit reindexing and
   triangle closure in the Lean proof. The cited source tags describe the reused
   existence and tower results. Historical split_report/tool_uses fields are unchanged;
   current proof_deps records the new route.

Second reading changed only this report, adding the independent interface, edge-case,
source, search, proof, axiom and DAG checks above. No mathematical or Lean repair was
necessary. No new holes or adaptations were introduced.
