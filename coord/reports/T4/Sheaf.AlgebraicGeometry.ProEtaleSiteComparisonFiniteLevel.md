## What changed

Proved `AlgebraicGeometry.ProEtale.siteComparison_finiteLevel` without changing its
signature, definitions, or public imports. The proof assembles existing upstream
comparison finite-limit and finite-colimit instances, the comparison-unit isomorphism,
and comparison acyclicity of pulled-back injectives. The unit in the statement is
definitionally the upstream comparison adjunction unit. Positive degree is converted
explicitly to successor degree. Updated the item's proof and dependencies accordingly.

Added an explicit proof import of
`WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful`.
The module compiles cleanly through `lcompile.py` after pruning. No other Lean module changes.
The unit's realized statement and steps are untouched: this item is below those nodes.

## Proved and sorry left

Closed the sole local hole:
`AlgebraicGeometry.ProEtale.siteComparison_finiteLevel`
(node `prop-weil-pbc-site-comparison-finite-level`). One hole closed, zero holes added,
zero split-off theorems. No `sorry` remains in the delivered Lean module.

The proof intentionally uses the already existing theorem
`AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective`
in `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`, whose own
proof is still `sorry`. This is an existing dependency, not a new hole or a claim
that the complete transitive proof is finished. Its new attachment is
`lem-weil-pbc-comparison-grothendieck-injective-acyclicity`.
The same Lean declaration already has an abelian-group specialization attachment
at `lem-cbc-abelian-comparison-injective-acyclicity`; the new attachment records the
finite-ring module clause required here without pretending the abelian-only statement
implies a module theorem. Both attachments share the original source declaration.

## No longer needed

Removed these seven proof imports from this module:

- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`
- `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonSections`
- `Sheaf.CategoryTheory.RingedSiteModules`

The parent no longer directly uses these previous planned proof dependencies:
`def-sp-left-exact-additive`, `def-weil-pbc-ind-etale-basis`,
`def-weil-sheaf-of-modules-category`, `lem-sp-grothendieck-enough-injectives`,
`lem-weil-pbc-affine-etale-site-topos`, `lem-weil-pbc-comparison-injective-acyclicity`,
`lem-weil-pbc-comparison-pullback`, `lem-weil-pbc-comparison-sections`,
`lem-weil-pbc-etale-restriction-injectives`,
`lem-weil-pbc-proetale-restriction-injectives`,
`lem-weil-pbc-ring-sheaves-grothendieck`.
Some still describe the argument of the existing downstream acyclicity theorem and
are retained on its new attachment. Many removed imports remain transitively imported
by the upstream acyclicity module; no claim is made that all seven modules leave the
whole targets' import closure. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG did not use the upstream generic comparison-unit and direct-image-acyclicity
API, although those declarations already give the last two clauses directly. In
particular the recorded affine injective theorem is unnecessary in this assembly.
The section-formula dependency accepts `CommRing Λ`, whereas this item's unchanged
statement assumes only `Ring Λ`; using the upstream Grothendieck abelian coefficient
API avoids that mismatch without adding commutativity. The formal coefficient
instances synthesize for the original universes and noncommutative ring hypothesis.

Searches actually run: LeanFinder for the complete comparison statement and for the
unit, Loogle for `rightAcyclic` and for `sheafPullback`/`IsIso`, Mathlib grep for
comparison and pro-etale names, and source-library `rg`. Mathlib had no exact match;
source-library search found the three required APIs. LeanSearch returned Internal
Server Error and is recorded as unavailable, not as a negative result.

## New nodes

`lem-weil-pbc-comparison-grothendieck-unit` attaches the already proved upstream
`AlgebraicGeometry.ProEtale.isIso_comparisonAdjunction_unit`, with its actual generic
signature, source proof, and search record. It introduces no Lean declaration.

`lem-weil-pbc-comparison-grothendieck-injective-acyclicity` attaches the existing
`AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective`
to the finite-ring module specialization required here. It introduces no Lean declaration
or new proof hole. Its remaining work is precisely the existing source theorem's proof:
affine vanishing followed by the higher-direct-image sheafification calculation.
No change record is needed: all exported interfaces are unchanged.

## Second reading by T4

1. **Signatures and definitions — pass.** I diffed the delivered module against the shared
version. The theorem statement and all existing declaration signatures are byte for byte
unchanged; only proof imports and the body changed. No definitions were altered.

2. **Compilation and proof hygiene — pass.** `lcompile.py` compiles the module with no
errors or warnings. The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by`; the proof uses only the existing comparison declarations and the
successor-degree rewrite. The imported acyclicity declaration remains an explicitly open
upstream theorem, as recorded in the report.

3. **Split statements and nodes — pass.** No new Lean theorem or proof hole was added.
The two unsplit node records attach the exact existing generic declarations used by the
proof and state the finite-ring specialization without changing those declarations. Their
sources and existing Lean records are recorded; no duplicate local theorem is introduced.

4. **Pruning and route — pass.** The proof uses the shortest available upstream route:
finite-limit and finite-colimit instances, the generic comparison-unit isomorphism, and
the generic injective right-acyclicity theorem. The seven obsolete proof-only imports and
the corresponding unused planned dependencies are listed under `No longer needed`.
The unit statement and realized route are untouched.

5. **DAG agreement — pass.** The target node's proof and `proof_deps` match the Lean proof:
its first two clauses are instance synthesis, the unit clause uses
`isIso_comparisonAdjunction_unit`, and the final clause uses
`rightAcyclic_comparisonUpperStar_obj_of_injective` after writing `q = n + 1`. The two
attachment nodes identify the exact imported declarations and preserve their source
provenance.

I changed only the proof imports/body and added this second-reading audit; no statement,
definition, or public interface required repair.
