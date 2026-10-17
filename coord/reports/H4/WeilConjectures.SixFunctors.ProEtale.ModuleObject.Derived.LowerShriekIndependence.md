## What changed

Replaced all three original holes of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence`
with complete Lean proofs, preserving every existing signature, visibility and definition body.
All imports added to that module are proof-only imports.

Repair of the return at `f904489d4`: removed the duplicate private
`moduleUnitOfAbelian` theorem from `OpenClosedConservative.lean`. That file now uses
`import all Sheaf.Paper.CondensedOpenClosedRecollement` and applies its existing private
theorem. The same import supplies the existing `profinitePointModuleForgetPullbackIso`,
so the duplicate private `forgetPullbackIso` definition is also removed. The main module
uses the existing private `openUnitIsIso` from that module; its duplicate
`openUnitIsIsoForRefinement` proof is removed. The duplicate `openUnitIsIso` in
`OpenRefinementSupport.lean` is also replaced by that existing helper, and
`DisjointOpenExtension.lean` uses `profinitePointModuleForgetPullbackIso` instead of
its private copy. All added imports are proof-only.
The import-direction checks confirm no cycle, and `lcompile.py --all` compiles all four
delivered files without errors or warnings. No existing library signature or definition
body is changed; only newly introduced private duplicates are removed.

The cartesian restriction comparison is a composite of invertible factors. Its unit factor is
invertible because open extension is fully faithful. Its counit factor is invertible because
cartesian inverse image of an extension by zero is supported on the pulled-back open. The proof
transports this support through the scalar-change equivalence and exact derived functors, then
through the fully faithful inclusion of bounded constructible complexes.

For the pushforward comparisons, a private coefficient-independent argument proves invertibility
of the unit on an open extension. Its open inverse image is invertible by the adjunction/full
faithfulness lemma. For the closed complement and its scheme-theoretic pullback, both inverse
images vanish: the target vanishes by the existing proper-base-change comparison and disjoint
support. Open–closed conservativity detects invertibility. Both coefficient cases instantiate
this argument with the existing proper-base-change theorem in `BaseChangeTheorems.Proper`.
The pullback and closed complement are constructed explicitly, not selected from existence.

Three new, fully proved supporting modules are included:

- `Sheaf.SixFunctors.ProEtale.ModuleObject.OpenRefinementSupport`: underived module support.
- `Sheaf.SixFunctors.ProEtale.ModuleObject.OpenClosedConservative`: unbounded derived detection.
- `Sheaf.SixFunctors.ProEtale.ModuleObject.DisjointOpenExtension`: unbounded derived vanishing.

The proof uses the existing abelian open base-change theorem. A fourth new DAG record attaches
that already proved source-library theorem, whose generic abelian-coefficient statement had no
matching attachment. No source file for that attachment is changed. Object-instance scopes are local to the new
private helpers, and the original global commands are preserved. No change record is needed:
there is no definition, statement or visible-import change, and no consumer requires adaptation.

Verification: `lcompile.py --all` compiled all four delivered Lean modules. A separate scratch
`#print axioms` audit of the three original theorems and three new support theorems found only
`propext`, `Classical.choice`, `Quot.sound` and transitive `sorryAx` from existing imported inputs.
This delivery closes local proof holes; it does not claim the targets' entire import closure is
already axiom-clean. The earlier `deliver3.py --no-push` run printed `OK (dry run)` for commit `b144e59df2`:
the delivered modules compile and preflight passes except for the second reading, which the
independent reader writes. Nothing was pushed.

## Proved and sorry left

Holes closed: 3 of 3, all in namespace `AlgebraicGeometry.ProEtale.CondensedRing`:

- `isIso_boundedConstructibleOpenImmersionLowerShriekRefinement`.
- `isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward`.
- `isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl`.

Holes added: 0. Split off: 0. Holes left in every delivered Lean file: 0.
The support, conservativity and disjoint-vanishing theorems are proved, rather than new obligations.
The already existing proper-base-change and bounded-constructible preservation inputs are used as
stated. Empty opens, identity refinements, the zero complex, and empty closed complements require
no extra hypotheses or separate choices in the proofs.

## No longer needed

No original import, module, node or unit is pruned; all original public imports remain.
The direct proof import `Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport` in the new
conservativity module is replaced by the existing recollement module, which provides the
abelian support result and the reusable module-unit helper. Local duplicates
`moduleUnitOfAbelian`, both copies of `forgetPullbackIso`, and the two copies named
`openUnitIsIso` / `openUnitIsIsoForRefinement` are pruned;
their existing library declarations are used instead. No entire module becomes unused.
The three componentwise `_app` restatements rejected in the earlier attempt remain withdrawn
and are neither imported nor reintroduced. The present proofs also do not import the downstream
`BaseChangeTheorems.LowerShriek.MorphismDefs` module or its left/right inverse split modules.
Those results still serve other users; this delivery makes no global pruning claim for them.
The three invalid earlier node records and their change record stay outside the delivery set.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the private `moduleUnitOfAbelian` theorem already in
`Sheaf.Paper.CondensedOpenClosedRecollement`. Its private visibility is accessible by the
existing project convention `import all`; importing and reusing it resolves the return.
The prior second reading below predates this repair. This worker has not rewritten that
independent review; a second reader should recheck the changed imports and removed helpers.

The earlier attempt moved the full obligations to componentwise restatements. This delivery
instead supplies the geometric support, disjointness and open–closed calculations, with no new
holes. `BaseChangeTheorems.LowerShriek.MorphismDefs` imports the item and cannot be imported back;
the underived abelian base-change theorem gives a non-circular route. The import-direction tool
also confirms that the proof-only import of `BaseChangeTheorems.Proper` creates no cycle.

No DAG node currently attaches the item's three original declarations. Their statements and
proofs in words were read directly from the whole source module, together with the current
blueprint `det-sf-comp-coherence-refinement`, especially its open restriction and closed-complement
steps. No existing node's statement or unit route is changed or bypassed. Four new records
track the supporting results actually used; each introduces its own objects, records actual
LeanSearch/LeanFinder/Loogle/grep searches, and points to a real blueprint ancestor.

An earlier reader raised an arbitrary-witness concern in the two unchanged
`boundedConstructibleLowerShriekOfCompactificationIso` definitions, which use
`Compactification.exists_overRefinement`. In the repository read for this second reading,
that existence theorem now has a proof constructing `inf c₁ c₂` and its two projections;
it is no longer a theorem whose proof is `sorry`. None of the three new comparison proofs
uses that existential theorem or those definitions. This delivery makes no new coherence claim.

## New nodes

`lem-sfb-abelian-open-extension-base-change` attaches the already proved
`AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekBaseChangeMap`, with generic
Grothendieck abelian coefficients. The finite-constant-ring blueprint statement is not used as
a substitute for abelian coefficients. No new Lean declaration or hole is created by this record.

`lem-sfb-module-open-refinement-support` records
`openImmersionLowerShriek_refinement_support` in `OpenRefinementSupport.lean`. It proves the
underived support calculation needed to invert the specified counit. It is not the original
bounded-constructible comparison under another name: it has no derived functors, no restricted
categories, and constructs an existence of a support isomorphism without claiming the specified
comparison equals that isomorphism. The item's proof separately proves invertibility of that
specified comparison by its unit and counit factors.

`lem-sfb-module-open-closed-conservative` records
`isIso_of_isIso_module_derived_open_closed` in `OpenClosedConservative.lean`. It derives joint
detection from abelian closed support, the existing module-unit transport theorem,
kernels/cokernels and exact homology.

`lem-sfb-module-disjoint-open-extension` records
`isZero_module_derived_pullback_openExtension_of_disjoint` in `DisjointOpenExtension.lean`.
It proves vanishing for an arbitrary morphism disjoint from the open, by empty fibre-product
sections, two adjunctions and exact homology. It requires neither properness nor constructibility.

All four node files are under `dag/nodes/sec-six-functors-basics/`. Change records: none.

## Earlier second reading (a previous round; superseded)

1. **Existing interface — pass.** Read the complete main module and its diff against the
   read-only repository. Independently compared all 13 existing declaration headers through
   `:=`: byte-identical. Existing definition bodies, visibility, variables and global commands
   are unchanged. All five added main-module imports are proof-only. No target or other group's
   module is changed; no change record or forced adaptation is required.
2. **Proof and data — pass.** Independently ran `lcompile.py --all`: all four modules compile
   without errors or warnings. No delivered file contains `sorry`, `axiom`, `unsafe`, `opaque`,
   `extern`, `implemented_by` or a hollow definition. A scratch copy with `#print axioms` for
   the three original theorems and all three support theorems reports only `propext`,
   `Classical.choice`, `Quot.sound` and transitive `sorryAx` from existing inputs. Checked the
   two explicit closed-complement/pullback constructions and the scalar-change equivalences;
   no new data is selected from an unproved existence theorem. The unchanged common-refinement
   definitions were checked against the now-constructed upstream existence theorem, as above.
3. **New statements and holes — pass.** No statement is split off with `sorry`; no hole is
   added. Read all three support proofs and the existing generic abelian open-base-change
   theorem. Support is obtained through the actual adjunction counit, disjoint vanishing
   through empty fibre products and two Hom equivalences, and derived detection through exact
   inverse images and homology. Empty schemes, empty or identity opens, identity refinements
   and zero complexes introduce no extra assumptions. The support theorem is an underived
   geometric step, not a restatement of the bounded-constructible comparison. Fresh Loogle,
   LeanFinder and grep searches with different queries, plus `rg` over the pro-etale module
   and Sheaf six-functor sources, found no replacement for the three module-specific results.
   The existing generic exact-derived detection lemma is already used.
4. **Route and pruning — pass.** Followed the proof from the three original holes down.
   Each specified comparison is proved invertible, not replaced by an arbitrary isomorphism.
   Checked every import's use and the compactification-coherence unit's `realized` route:
   open restriction, proper base change on bounded constructible generators, and open–closed
   detection remain. The proper-base-change import does not import the item back. No old
   proof dependency or module becomes unused; `## No longer needed` is complete. The existing
   unit record needs no change.
5. **DAG — pass.** Read all four new records and their referenced existing declarations.
   Checked that every dependency and blueprint ancestor resolves, `proof_deps` is exactly
   the ordered union of the proof steps' `uses`, and each new Lean statement matches its
   record verbatim. The generic abelian base-change attachment matches its source context,
   including Grothendieck abelian coefficients. Sources, searches, creation metadata and
   module attachments are present. No existing node attaches the three original holes, so
   there is no existing item-node proof record to update. No unit statement or step is bypassed.

Second-reading changes: corrected the report's stale description of the upstream
common-refinement existence proof, and recorded this independent review. No Lean or DAG
repair was needed. Verified local count: three holes closed, zero added, zero split off;
no pruning claim beyond the report.

## Second reading by H4

1. **Existing interface — pass.** I compared the delivered main module against the
   repository version and checked every existing declaration signature and definition body.
   The three target statements are byte-for-byte unchanged. The added imports are proof-only;
   the three new support modules expose only their newly stated supporting theorems. No target
   or module held by another group was edited, and no change record or forced adaptation is
   needed.
2. **Proof and data — pass.** `lcompile.py --all` compiles all four delivered modules without
   errors or warnings. A source scan finds no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`,
   `implemented_by`, or hollow definition in the delivered files. The three target proofs and
   the three support theorems use only ordinary constructions and existing inputs; the explicit
   closed-complement and pullback objects are constructed in the proof. The remaining
   transitive `sorryAx` reported by the scratch axiom audit comes only from existing imported
   declarations.
3. **New statements and holes — pass.** The three support statements are true and strictly
   below the target: underived open-refinement support, unbounded disjoint vanishing, and
   derived open-closed detection. They add no hypotheses to or weaken any target, and all are
   fully proved with no new holes. Searches recorded in each node, together with repository
   searches, found no existing declaration that duplicates these module-specific results.
4. **Route and pruning — pass.** The proofs retain the unit's open restriction, proper
   base-change, and closed-complement detection route. The specified comparison morphisms are
   proved invertible directly, rather than replaced by an arbitrary isomorphism. Imports and
   local duplicate helpers removed by the worker are accurately described under `No longer
   needed`; no old proof dependency or unit step is pruned.
5. **DAG — pass.** I checked all four delivered node records: their Lean statements match the
   declarations, proof steps and `proof_deps` agree, sources and search records are present,
   and blueprint chapter/unit references resolve. The existing abelian base-change declaration
   is attached as an existing Lean result, while the other three records attach the new support
   modules. No target node or unit statement changes.

Second-reading changes: added this required independent review section. No Lean proof, statement,
definition, import, or DAG node required repair.
