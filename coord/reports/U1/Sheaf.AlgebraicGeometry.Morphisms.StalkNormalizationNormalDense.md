## What changed

The original theorem is obtained by conjunction introduction from its normality and density
components, in two new modules. Its existing signature and all public imports are unchanged.
The second reader proved `AlgebraicGeometry.Scheme.stalk_normalization_dense_part` using
Mathlib's zero-kernel normalization theorem and flat base change of schematic dominance.
Only normality is left open. The two components are strict parts of the original conclusion.

Proof-only imports `Sheaf.RingTheory.SmoothNormalRing` and `Sheaf.RingTheory.EtaleNormalRing`
were moved from the original module into the normality component, whose planned proof needs
them. The density component privately imports
`Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat`.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.stalk_normalization_normal_and_dense`.
Added one lower hole:
`AlgebraicGeometry.Scheme.stalk_normalization_normal_part`, node
`lem-sbc-stalk-normalization-normal-part`. This is the sole explicit `sorry` in the delivery.
Its docstring supplies the normal-component integral-closure and stalk-localization proof.

The new `AlgebraicGeometry.Scheme.stalk_normalization_dense_part`, node
`lem-sbc-stalk-normalization-dense-part`, is fully proved, with only `propext`,
`Classical.choice`, and `Quot.sound`. The original theorem and normality component also
show `sorryAx`, solely because normality remains open. All three files compile without warnings.

Relative to the repository this is a decomposition: one upper hole closed, one lower hole
added, net zero holes. Relative to the first worker's sandbox the second reader closed the
density hole and added none. No claim of a fully proved normality-and-density theorem is made.

## No longer needed

Removed the original module's direct proof-only imports
`Sheaf.RingTheory.SmoothNormalRing` and `Sheaf.RingTheory.EtaleNormalRing`.
Its old immediate proof dependencies
`lem-weil-pbc-smooth-over-normal-ring-normal`,
`lem-weil-pbc-etale-over-normal-ring-normal`, and
`lem-weil-pbc-relative-normalization` are replaced by the two component nodes.
The old dependencies remain needed in those components; the first two imports now belong
to the normality component. No whole module is pruned from the import closure.
The density component needs neither smooth-normal nor etale-normal ring lemmas.

## Where the brief, the DAG or earlier work was wrong

The first worker left both components open even though the density component has a short
proof from existing Mathlib tools. Its new node statements referred to the parent instead
of introducing their objects. Their proof explanations omitted the normal-source and
finite-component hypotheses of Tag 035L and the explicit local nature of the stalk base
change. Both new nodes incorrectly inherited the parent's old review and audit records.
These faults are repaired. The density proof only needs containment of the dense image in
the displayed open, not an identification of that image with the open.

No change to the target statement, definitions, or unit route was required. The unit
`sk-prop-input-spreading` has empty `realized.statement` and seven empty step arrays in the
repository; this delivery neither changes nor fills that pre-existing bookkeeping gap.
The localized relative-normalization step of the maximal-open extension argument is kept.

## New nodes

`lem-sbc-stalk-normalization-normal-part`, module
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart`, states exactly the
normal-stalk clause with the original hypotheses. Its proof plan preserves the original
smooth ascent, etale ascent, integral-closure charts, and localization route. The complete
proof in words covers finite disjoint components and components killed by localization.
It remains open. No change record is needed for a new declaration.

`lem-sbc-stalk-normalization-dense-part`, module
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDensePart`, states exactly the density
clause with the original hypotheses (the unused normal-base proof is named `_hS`). It is
proved. The node records relative normalization and
`lemma-nagata-dense-flat-pullback` as proof dependencies; the latter is a finished generic
tool, realized by Mathlib's `IsSchemeTheoreticallyDominant.pullbackSnd`, and does not replace
a step of the spreading unit. New searches are recorded from actual `msearch.py` runs.
LeanSearch returned an internal server error; Loogle, LeanFinder, and grep supplied tools
but no exact full component theorem. Upstream
`Scheme.Hom.isIntegrallyClosed_stalk_normalization` assumes an integral source, which the
possibly disconnected finite etale source here need not have.

## Second reading by U1

1. Compared the delivered original module with the repository using `diff`. Its signature,
   visibility, universe, hypotheses, let-instance data, and conclusion are byte-for-byte
   unchanged. Only its proof and private imports differ. Neither new module exists in the
   repository, and there are no adapted modules or definition changes. Verdict: pass.
2. Compiled every module in import order with `lcompile.py --all`, without warnings. A scratch
   module printed the axioms of all three declarations: the density component uses only the
   three permitted axioms; the normality component and original theorem additionally use
   `sorryAx`, as reported. Scanned for prohibited declarations and attributes; none occur.
   There is one named theorem hole and no definition or arbitrary-witness construction.
   Verdict: pass with the explicitly reported normality hole.
3. Checked both split statements clause by clause and considered empty P, empty U, U = top,
   disconnected covers, and arbitrary stalk points. Empty normalization makes both clauses
   vacuous; finite disjoint components are essential for the normality proof; localization
   either preserves a normal domain or kills the component. Both clauses are strictly
   smaller than the parent conjunction. Repeated searches with different words and inspected
   Mathlib, upstream, and Sheaf sources. Proved density from the existing tools; retained
   normality as a sourced theorem with a complete proof in words. Verdict: pass.
4. Checked the top-down conjunction proof, the shorter Mathlib route for density, and each
   import's role. Moved normality-only imports to its module and listed all three old immediate
   dependencies above. The original unit's relative-normalization route stays intact; the
   flat-base-change lemma is a generic finished tool. Verdict: pass; no whole-module pruning.
5. Compared the original node with its repository version, retaining every field except
   `proof`, `proof_deps`, and `proof_origin`. Checked both new nodes against their Lean
   signatures, self-contained statements, source citations, proof-dependency unions, creation
   records, chapter/unit, and blueprint ancestry. Removed inherited review/audit metadata
   and replaced unverified search records by actual searches. Verdict: pass.

Changes by this second reading: proved density; expanded both component proof docstrings;
made both node statements self-contained; corrected their proof plans, sources, ancestry,
searches, and copied metadata; moved the two normality-only imports; corrected the hole
accounting and pruning report. Existing statements and definitions are unchanged.
