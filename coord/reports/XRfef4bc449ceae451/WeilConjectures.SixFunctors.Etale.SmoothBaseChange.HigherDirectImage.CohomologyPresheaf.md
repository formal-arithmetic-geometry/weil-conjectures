## What changed

Repaired the landed delivery at tip 47d97fea17ab96ef0bfe041d809f7fcf255197c6.
Only source change: in
Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackComposition, add
`set_option backward.isDefEq.respectTransparency false in` to the final application
of `rawTriangleMap_comp` in `higherDirectImageRawTrianglePullback_comp`.
This lets the elaborator identify the raw derived-category structures with the
ModuleSheaf specialization exported through `higherDirectImagePresheaf`.
The theorem's statement, visibility, docstring and categorical proof are unchanged.
No import, instance, definition or dependency is changed by this repair.
CohomologyPresheaf and the two node copies remain identical to the broken tip.

Updated coord/changes/H4-cohomology-presheaf-instance-sharing.md to document the
forced consumer adaptation and replace the earlier claim that no adaptation was needed.

Validation used only lcompile.py, one module per invocation, with the unchanged
60-second per-file limit and remote fallback disabled:

- CohomologyPresheaf: compiled cleanly, 43.7 seconds, into the sandbox .lbuild.
- Original HigherDirectImageRawTrianglePullbackComposition against that fresh artifact:
  reproduced the exact reported line-114 instance error, 21.8 seconds.
- Repaired HigherDirectImageRawTrianglePullbackComposition against the same artifact:
  compiled cleanly, 27.0 seconds.
- Axiom inspection of `higherDirectImageRawTrianglePullback_comp`: compiled cleanly
  in 35.9 seconds; only `propext`, `Classical.choice` and `Quot.sound`.
  The temporary `#print axioms` command was then removed.

To generate the dependency artifact using lcompile.py's existing CLI, its pathname
was supplied twice in that invocation. The helper deduplicates by module name before
compiling, so this compiles exactly one file once and saves it to .lbuild. The consumer
checks each used the ordinary single-path invocation and resolved that fresh artifact.
No multi-module build, server compile, delivery, push, configuration edit, .check file
or second-reading evidence was created.

## Proved and sorry left

This repair closes no additional mathematical hole and adds none.
`AlgebraicGeometry.Etale.higherDirectImageRawTrianglePullback_comp` retains its
complete existing proof. Neither sandbox Lean source contains a `sorry`.

The landed reduction of the original hole is retained:
`AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists`
(node lem-sbc-constant-module-higher-direct-image-local-vanishing) applies the two
existing open dependencies:

- `AlgebraicGeometry.Etale.isZero_cyclicHigherDirectImage_of_locally_zero`
  (node lem-sbc-cyclic-higher-direct-image-local-vanishing).
- `AlgebraicGeometry.Etale.isZero_constantModHigherDirectImage_of_cyclic`
  (node lem-sbc-constant-module-higher-direct-image-cyclic-reduction).

No new declaration, axiom or data chosen from an unproved theorem is introduced.
The existing dependence of the vanishing reduction on these open statements is unchanged.

## No longer needed

No further import, node or module is pruned by this repair. The landed removal of the
redundant direct FullyFaithful import remains; its declarations are still publicly
available through DerivabilityStructureInjectives. Both vanishing dependencies remain
needed. No blueprint unit or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier compatibility claim missed this consumer's strict elaboration setting.
The shared cached CohomologyPresheaf artifact predates the landing: against that cache,
the unchanged consumer compiled, which did not establish compatibility with the delivery.
Against the freshly compiled landed source it reproduces the reported failure. Allowing
alias unfolding locally in the final application fixes that failure without changing
any exported interface or mathematical statement.
The DAG route and dependencies already agree with the retained proofs.

## Forced adaptations

Adapted module: Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackComposition;
holder: unclaimed in the coordination snapshot.

Original error at line 114:

```text
failed to synthesize instance of type class
  D+((b)^*[ModuleCat Λ]).CommShift ℤ
```

Changed line 114 by inserting a local elaborator option immediately before the existing
`exact rawTriangleMap_comp` application. That line is necessary because the original
application fails against the fresh changed dependency; the adapted application compiles.
All existing signatures, visibility, docstrings, imports and proof arguments are unchanged.
The change record contains the old and new application prefixes and validation results.

## Second reading by XRfef4bc449ceae451

Independent second reader, 2026-10-14. Read request.json, delivery.diff, both complete
Lean files, both node records, the change record and report; followed check-brief3.md,
coord/brief-stage3.md, stages/3-proving-and-pruning.md, AGENTS.md sections 4–5 and
roles/lead.md section 3. No other agents were used.

1. Interfaces and mathematics: PASS. Compared each scoped file with the read-only
   repository and reconstructed the supplied original delivery in scratchpad. The
   repaired CohomologyPresheaf source is byte-for-byte the original broken delivery;
   both node records have exactly its JSON contents. The consumer differs from the
   repository by exactly one proof-local option at line 114. Its complete signature,
   visibility, imports, docstring and proof arguments are unchanged. All existing
   CohomologyPresheaf declaration kinds and visibility survive. Its earlier alias
   signature/definition changes are recorded in the change record: ModuleSheaf is
   the original sheaf category, its cached instances are the inferred original
   instances, and the functor/free-sheaf aliases unfold to the original constructions.
   The vanishing criterion retains its signature verbatim; no target is changed.

2. Compilation and trust: PASS. Used only lcompile.py, with remote fallback disabled
   and its unchanged 60-second limit. Independently rebuilt CohomologyPresheaf into
   .lbuild in 37.3 seconds (the repeated pathname is deduplicated to one compilation).
   Against that fresh artifact, the original consumer fails in 6.7 seconds with the
   exact reported line-114 D+((b)^*[ModuleCat Λ]).CommShift ℤ error. The repaired
   consumer compiles cleanly in 27.7 seconds. Its scratch #print axioms compilation
   passes in 27.2 seconds and shows only propext, Classical.choice and Quot.sound.
   A scratch copy of CohomologyPresheaf with 47 public-declaration axiom queries
   compiles cleanly in 39.0 seconds. All except the retained vanishing reduction use
   only the permitted three axioms. That reduction still uses sorryAx through its
   two explicitly reported pre-existing open dependencies; it is not claimed as an
   unconditional completed target. Neither delivered Lean file contains sorry,
   axiom, unsafe, opaque, implemented_by, extern, sorryAx or a kernel-check bypass.
   The new option affects elaboration transparency only; kernel checking stays on.
   This addresses every compiler failure listed in request.json.

3. Split statements: PASS. This repair adds no declaration, split-off statement,
   hollow definition or arbitrary witness. Read both existing cyclic-vanishing and
   coefficient-reduction dependencies and their natural-language proofs. Their
   conclusions are exactly the two steps used by the retained vanishing reduction;
   d = 0 includes ZMod 0 and all finite cyclic orders, d = 1 gives zero coefficients,
   and degree zero and empty schemes cause no changed hypothesis. No whole target
   is moved to a new admitted theorem. The earlier generic boundary homotopy and
   cycle helper are fully proved constructions; repository searches found no exact
   existing helper to replace them. Closing these open cohomological dependencies
   is beyond a small repair and is not claimed here.

4. Route and pruning: PASS. Read the categorical coherence proof: functoriality,
   sourceComp, shift naturality and composition yield precisely the displayed
   composite coefficient map. The same argument and all its inputs are retained;
   the one failing application needs unfolding of definitionally equal instances.
   The original-fails/repaired-passes comparison establishes necessity of that
   forced adaptation. No mathematical reproof or new dependency is needed. The
   retained FullyFaithful import removal is valid because
   DerivabilityStructureInjectives publicly imports it. Both proof-only vanishing
   imports remain needed; the report accurately claims no further pruning. Read
   dag/units/sk-lem-failure-field.json: its route and realized fields are untouched.

5. DAG and records: PASS. Matched both nodes' Lean statements and proof steps to
   their declarations: local bijectivity uses derived adjunction, local
   cycles/boundaries and the homology-shift isomorphism; the constant-module
   vanishing reduction applies precisely its two recorded proof dependencies.
   The ModuleSheaf spelling in the comparison node matches the delivered Lean.
   No node statement or dependency is changed by this repair. The change record
   documents the sole forced consumer edit, the original error and its holder.

Second-reader changes: appended this actual independent reading and wrote .check.
No further source or DAG repair was necessary. Scratch copies and axiom queries are
confined to scratchpad/second-reading and are excluded from delivery. The authorized
delivery is to the normal project server only; no server compilation or lake build
was run.

Delivery dry run: deliver3.py --no-push returned OK; compilation and stage-3
preflight passed. Its public-import warning comes from the retained multiline
`public import` of DerivabilityStructureInjectives: inspection confirms that the
import remains public and present. Review metadata from the old node copies is
correctly excluded by the delivery tool.
