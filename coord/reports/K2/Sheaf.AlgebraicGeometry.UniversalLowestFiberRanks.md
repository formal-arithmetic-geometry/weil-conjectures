## What changed

Proved `AlgebraicGeometry.Scheme.universalLowest_fiber_ranks` in
`Sheaf.AlgebraicGeometry.UniversalLowestFiberRanks`, preserving its complete signature
and all public imports. Two proved private helpers convert the K-flat tensor witness
to derived homology vanishing and calculate sections of a finite locally free sheaf
on a field spectrum.

The lower-bound argument uses the existing generic bounded flat model theorem rather
than affine restrictions and projective representatives. Pulling that model back
termwise makes every term below `a` zero. The bottom-rank argument transports `hres`
through derived composition, calculates the sections of the resulting globally free
sheaf, and applies the existing fibre-cohomology base-change isomorphism and
`Module.finrank_baseChange`.

Added proof-only imports:
- `Sheaf.AlgebraicGeometry.DerivedFiberCohomologyBaseChange`
- `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`
- `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`
- `Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison`
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`
- `WeilConjectures.AlgebraicGeometry.Modules.FreeComplex`

Updated only `proof`, `proof_deps`, and `proof_origin` of the existing node
`lem-sc-universal-lowest-fiber-ranks`. No other module or interface was changed.
The cube unit's realized statement and steps are untouched; this is a shorter
argument below that level. The general flat-model node is an already proved source
tool; the fibre base-change node belongs to the same cube unit.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.universalLowest_fiber_ranks`
(node `lem-sc-universal-lowest-fiber-ranks`).

No `sorry` remains in the item's module. No holes or modules were added.
The private helpers `tensor_single_vanishes` and `finrank_sections_of_rank` are proved.
This closes one local hole, with zero split off; it is not a decomposition into
newly sorried statements. Imported declarations may retain transitive project holes.

The complete module compiled without errors or warnings through `lcompile.py`.
Every added import passed `tools/import_direction.py may`.

## No longer needed

Removed proof-only imports and their dependency edges:
- `Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion`
  (`lem-pc-affine-tor-amplitude-criterion`): the generic flat model supplies the
  required interval globally, so no affine module representative is needed.
- `Sheaf.AlgebraicGeometry.PerfectJumpLoci`
  (`lem-sc-perfect-jump-loci`): only fibre base change is needed; its standalone
  cohomology isomorphism avoids all upper-semicontinuity and constructibility work.

Also removed `def-pc-perfect-complex` and `def-pc-derived-pullback` from proof-dependency
edges because no proof step uses their definitions. Their modules remain reachable
through the unchanged public statement imports. Perfection and pseudo-coherence
conversion, affine open pushforward tests, enlargement to `max a b`, and affine
projective-model construction are unnecessary for this argument. The proof does
still use derived-pullback composition and the locally free rank definition.
These are pruned edges of this item, not a claim that the corresponding modules are
unreachable from every project target.

## Where the brief, the DAG or earlier work was wrong

The former proof plan was mathematically valid but unnecessarily indirect. The
existing generic source flat-model theorem works for all integers `a,b`; it does
not require `a <= b`. When `b < a`, its two support bounds force the entire model
to be zero. The source of the route was checked in Stacks Tags 09U8 and 08CI.

The former rank argument invoked the full jump-loci theorem and an unstated
perfect-to-pseudo-coherent conversion. The already available standalone
`derivedFiberCohomology_baseChange_iso` handles exactly the needed comparison,
without either assumption. The original `hE` binder is retained, with its unused
variable warning locally disabled; no target or intermediate statement was changed.

Edge cases checked in the actual proof: `r = 0` is covered by the free sections
formula, `b < a` by the generic support bounds, and empty `T` by introduction of
an arbitrary point without a nonemptiness assumption on `T`. The rank helper
chooses a point only on `Spec R` for a field, where nonemptiness is available.

Searches: launcher LeanFinder for Tor-amplitude/residue-fibre vanishing returned
t-structure vanishing characterizations; Loogle for zero finrank returned
`Module.finrank_zero_of_subsingleton`; repository `rg` found the proved source
flat-model theorem, flat derived pullback, field-spectrum free sections calculation,
and the standalone fibre base-change isomorphism. No new intermediate statement
was needed.

## Second reading by K2

1. **Repository comparison.** Compared the delivered module with the repository
version. The theorem signature and all public imports are unchanged byte for byte;
only the author line, proof-only imports, and proof body differ. The existing node's
statement is unchanged. Verdict: pass.

2. **Proof and trust.** Compiled the complete sandbox module with `lcompile.py --all`.
There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or
`debug.skipKernelTC` declarations in the delivered file. An axiom probe reports only
`propext`, `Classical.choice`, and `Quot.sound` for both private helpers; the target
also inherits `sorryAx` only from still-open imported declarations. Verdict: pass.

3. **Statements and split-offs.** No statement was added or weakened, and no split-off
theorem or new node was introduced. The two private helpers are fully proved and are
strictly internal reductions. Searches of the repository and the recorded Mathlib
searches found no duplicate declaration needed by this proof. Verdict: pass.

4. **Shortest route and pruning.** The proof uses the generic bounded flat model,
termwise derived pullback, and standalone fibre base change. The former affine
Tor-amplitude and perfect jump-locus dependencies are unused and are removed from the
node's proof route; all remaining imports and proof dependencies are used. The
unit's realized route is unaffected. Verdict: pass.

5. **DAG agreement.** The node proof steps, proof dependencies, and proof origin now
match the Lean proof, including the flat-model, pullback, sections, and base-change
steps. No new node or change record is required. Verdict: pass.

Changed during second reading: added this review section only; no Lean proof repair was
needed after compilation and the axiom probe.
