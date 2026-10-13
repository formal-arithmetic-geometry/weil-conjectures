## What changed

Proved `AlgebraicGeometry.relativeDifferentials_affine_sections_map_injective` in
`Sheaf.AlgebraicGeometry.RelativeDifferentialsAffineSectionsMapInjective`, with its
signature and visibility unchanged. Imported the existing
`Sheaf.AlgebraicGeometry.RelativeDifferentialsAffineChartDerivation` for its inverse
formula on differential generators. Constructed the linear section transport, showed
that the resulting affine comparison agrees with the supplied map on generators,
and proved injectivity by cancellation of three injective factors.

The transport construction and generator computation reuse the landed proof of
`relativeDifferentials_affine_sections_map_surjective`; the final argument proves
injectivity of the section transport by restricting back, then cancels the Spec
comparison and the mapped chart isomorphism. Neither the surjectivity theorem nor
its module is imported. Updated the item's node proof, proof dependencies, and
proof origin to describe this argument. The unit's realized statement/steps are
empty, and no unit route is bypassed.

Validation: the single-file local compile passed without warnings. The required
delivery dry run is the final check. The source is Stacks Tag 01UT, read at
https://stacks.math.columbia.edu/tag/01UT because the literature TeX is not present
in this read-only clone.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.relativeDifferentials_affine_sections_map_injective`
(node `lem-sc-relative-differentials-affine-sections-map-injective`).
No `sorry` remains in the delivered module. No holes were added and none were
split off. This is a proof from an existing named dependency, rather than a new
decomposition. The current source of the imported theorem
`AlgebraicGeometry.relativeDifferentials_affine_chart_derivation`
(node `lem-sc-relative-differentials-affine-chart-derivation`) is proved.
The local compiled axiom probes for both it and the delivered theorem still list
`sorryAx`, alongside `propext`, `Classical.choice`, and `Quot.sound`. Thus this
delivery closes the item's explicit hole but does not claim an axiom-free proof
of its full import closure.

## No longer needed

Removed the redundant direct proof import
`WeilConjectures.AlgebraicGeometry.Modules.Differentials`; its declarations remain
available through the unchanged public statement import
`Sheaf.AlgebraicGeometry.RelativeDifferentialsAffineSectionsMap`.
No DAG dependency node or source-library module is pruned: both original definition
nodes remain used. The chart-derivation node is added as a proof dependency.
The earlier sandbox attempt's explicit `affineDifferentialsIso` and forward
`affineSectionsToSpec` helpers are replaced by inverse transport; its explicit
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde` import is unnecessary.
That latter import was only in the unfinished sandbox, not in the repository base.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox proof left the chart compatibility computation as a `sorry`
inside the main theorem. The landed chart-derivation theorem now supplies exactly
that step, so no new lemma is needed. The DAG's single sentence is expanded into
section transport, uniqueness on generators, and injectivity by cancellation.
The original statement is true and unchanged. No definition, statement, target,
or module owned by another group was adapted.


## Second reading by M4

1. PASS: diffed the only delivered Lean module against the repository version.
   The existing theorem signature is byte-for-byte unchanged, as are its visibility,
   universes and namespace variables. No definition, target, or extra declaration
   changes. Restored the original theorem docstring; the option is scoped to this
   theorem. The only new import is a plain proof import.
2. PASS: local compilation succeeds without warnings. The delivered module has no
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and adds no
   definition. A scratch copy printing the theorem's axioms reports exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the existing compiled
   chart-derivation theorem has the same list. Its source now has a complete proof,
   so the report's claim that its explicit hole remains was corrected. The witness
   T has an equality fixing it to an explicit composite; no arbitrary data is
   chosen from an undetermined existence statement.
3. PASS: no new statements or split-off holes exist. Read the chart-derivation
   statement and proof: its inverse formula supplies precisely the generator
   computation, while its equality fixes T. Read Stacks Tag 01UT at
   https://stacks.math.columbia.edu/tag/01UT: the affine opens and containment
   hypotheses match, and uniqueness of the compatible isomorphism implies this
   injectivity statement. No nonemptiness, smoothness, or finite-type assumptions
   enter; empty affine opens and zero differential modules cause no exception.
4. PASS: checked the Spec comparison and its IsIso instance in the source module,
   the landed surjectivity computation, and searched the upstream Differentials
   module, Mathlib AlgebraicGeometry/Modules, and Sheaf's relative-differential
   modules for affine comparisons and injectivity. No shorter noncircular existing
   theorem for this statement was found: the bijectivity/affine-sections theorems
   depend on this item. The proof agrees on generators by KaehlerDifferential.ext,
   proves L injective by restricting back, then cancels two section isomorphisms.
   Both imports are used; the redundant direct Differentials import is completely
   accounted for under No longer needed. Both old proof dependency nodes remain
   used, so no node is pruned. Read sk-thm-picard-duality.json: its realized
   statement and step lists are empty; this local affine argument bypasses none.
5. PASS: node diffs change only proof, proof_deps and proof_origin. The three steps
   describe the actual transport, generator equality and cancellation argument;
   their uses have exactly the recorded union. No new nodes need auditing.

Second reading changed only the restored original docstring and the stale report
claim about the chart-derivation hole, and added this review. The proof required
no repair.
