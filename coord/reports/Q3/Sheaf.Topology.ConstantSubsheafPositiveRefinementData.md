## What changed

Proved `TopCat.Sheaf.positive_refinement_data` in the assigned module, retaining its
entire statement and the fields of `PositiveRefinementData` unchanged. The proof constructs
the original generator sections, finite compact-open fibres, zero pieces, parent indices,
positive absolute values and signs. It proves every partition and section equation.

The private proved helper `extension_integer_section` explicitly constructs the map from
extension by zero using integer multiplication, `sheafifyLift`, the extension functor and
the existing counit. Its canonical unit calculation is proved with both sheafification
unit identities and the direct-sum counit formula. Choices of component maps come from
this fully proved existence theorem, not from any unproved existence statement.

Added `Sheaf.Topology.ConstantSheafLocallyConstantUnitComparison`, with the fully proved
`TopCat.constantSheaf_locallyConstant_unit_comparison`. This imports the existing P3 comparison module with proof-only `import all`,
reuses its private proved helpers directly, and retains the `hconst` calculation in
the public conclusion. All six duplicate helper declarations have been removed. It adds no definition of a constant sheaf and no
unproved lemma. The existing comparison module and its public signature are untouched;
a separate strengthened theorem is needed because its existing public interface omits
unit compatibility. The private helpers are available through `import all`.

Replaced the proof import of `Sheaf.Topology.ConstantSheafLocallyConstantComparison` by
the new comparison module. The second reader removed the redundant proof imports of
`Mathlib.Data.Fintype.EquivFin` and `Mathlib.Algebra.Category.Grp.EpiMono`; their
APIs are already available through retained imports. Kept all original public imports. Updated the
assigned node's proof, proof dependencies and proof origin. A declaration-local unused
variable linter option preserves the existing named existential binder `d`, whose
predicate is `True`; it does not change the theorem statement.

Both modules compile without warnings through the prescribed local compiler. The
finite indexing includes empty families, empty opens and sections with only zero value;
no nonemptiness, separation or connectedness assumptions were added. The comparison
works for unrelated coefficient and space universes, including the zero coefficient
group. Sources read online: Stacks [0A38](https://stacks.math.columbia.edu/tag/0A38),
[006W](https://stacks.math.columbia.edu/tag/006W),
[007B](https://stacks.math.columbia.edu/tag/007B), and
[0081](https://stacks.math.columbia.edu/tag/0081).

## Proved and sorry left

Closed the sole original hole: `TopCat.Sheaf.positive_refinement_data`, node
`lem-sc-constant-subsheaf-positive-refinement-data`.

Also proved the new theorem `TopCat.constantSheaf_locallyConstant_unit_comparison`, node
`lem-sc-constant-sheaf-locally-constant-unit-comparison`, and the private helper
`TopCat.Sheaf.extension_integer_section`. The new comparison module declares no private helpers; it uses the existing ones. No `sorry` remains in either delivered module. No holes were added
or split off: this is a complete proof, not a decomposition into new unproved statements.

## No longer needed

Removed all six duplicate declarations from the new comparison module:
`abelian_underlying_isSheaf`, `abelian_section_ext`, `abelian_gluing`,
`skyscraper_abelian_isSheaf`, `unit_inj`, and `constantSheaf_unit_localSurj`.
Removed its direct proof imports `Mathlib.Topology.Sheaves.Skyscraper`,
`Mathlib.Algebra.Category.Grp.Limits`, and `Mathlib.Algebra.Category.Grp.Zero`.
The existing comparison module and node remain needed: the new theorem now imports
and reuses their proved helpers. The old direct proof dependency `lem-sc-constant-sheaf-locally-constant-comparison`
is replaced by the unit-compatible node; it remains a transitive dependency through
the new module, so no existing node or module is globally pruned.
The assigned module still imports the stronger comparison theorem.

## Where the brief, the DAG or earlier work was wrong

The planned restriction-compatible comparison alone does not identify canonical unit
values. An arbitrary additive equivalence with restriction compatibility need not send
the canonical value to itself. The assigned docstring and node correctly mention this
extra obligation, but their dependency's public statement does not expose it. The P3
proof already proves the missing equation locally as `hconst`. The new, completely
proved comparison theorem exposes precisely that equation and uses the same construction.
The returned delivery correctly identified six duplicate helper statements. This repair
removes them and reuses the originals with a proof-only `import all`; no existing module
or signature is modified. The earlier second reading did not detect that duplication,
and its review is removed pending a fresh independent reading.

The blueprint ancestor script returns `None` for this item because its `created.item`
is a Lean module name. Following the existing `blueprint.from` records leads from the
assigned node through positive refinement and positive presentation to
`lem-sc-pic-proper-ntorsion`; the new node records that existing ancestry explicitly.
No existing blueprint metadata was changed. The unit has no realized proof steps below
its statement, and no unit statement or route is bypassed.

## New nodes

`lem-sc-constant-sheaf-locally-constant-unit-comparison` records the natural additive
comparison with locally constant maps together with the prescribed sheafification-unit
values. Its new module contains the evaluation proof with `hconst` retained and directly
uses the existing comparison module's private helpers. Its sole proof dependency is
`lem-sc-constant-sheaf-locally-constant-comparison`. Mathlib searches were performed through
`msearch.py`: LeanSearch was unavailable (HTTP Internal Server Error), Loogle found
sheafification APIs, and grep found constant-sheaf construction and adjunction APIs.
None provided this topological unit-compatible comparison. Searches of the existing
library and the whole blueprint found the weaker comparison but no public theorem with
the needed unit equation. No change record is necessary: no existing public signature,
definition or public import was changed, and no other module was adapted.


## Second reading by Q3

1. Compared each delivered file with the repository. The existing
   `PositiveRefinementData` structure, its fields, theorem signature and docstrings
   are byte-for-byte unchanged. The comparison module is new; the existing comparison
   module is untouched. All existing public imports are preserved. Verdict: pass.
2. Compiled both modules in import order with `lcompile.py --all`, without warnings.
   Scratch-copy `#print axioms` checks for `positive_refinement_data`,
   `extension_integer_section` and `constantSheaf_locallyConstant_unit_comparison`
   show only `propext`, `Classical.choice`, and `Quot.sound`. Neither module has a
   `sorry`, forbidden declaration mechanism, or hollow definition. Component maps
   are chosen from a fully proved construction, and local representatives are
   chosen from proved local surjectivity; no unproved existence supplies data.
   Verdict: pass.
3. No unproved statement is split off. Read the new comparison proof and the
   original private helpers it imports, including local surjectivity, pointwise
   unit injectivity, separation and gluing. The added conclusion is precisely the
   canonical-unit equation used in `hrestrict`; the old public theorem does not
   state it. Independent Loogle query `"LocallyConstant", "toSheafify"` returned
   no hits. LeanFinder search for canonical evaluation of constant-presheaf
   sheafification found condensed-site unit/counit APIs, not this open-site result.
   Repository searches found only the weaker public comparison. Checked empty
   opens, the zero coefficient group, unrelated universes, empty generator
   families, zero-only generators, and positive/negative integer fibres: the
   constructions and equations apply in all cases. Verdict: pass.
4. Read the finite-fibre construction, the extension/counit calculation, and sign
   normalization from the target downward. The proof reuses Mathlib finite-range
   and clopen-fibre results and the original proved comparison helpers. Public
   imports of the new module support its signature; its helper import is proof-only
   `import all`. No redundant direct import was found. The old direct comparison
   dependency is replaced but remains transitively needed; no module is globally
   pruned. Read `dag/units/sk-thm-curveestimate.json`: its realized statement stays
   `thm-sc-proper-cohomology`, with no realized steps altered. Verdict: pass.
5. Compared the assigned node diff: only `proof`, `proof_deps`, and `proof_origin`
   change, matching the Lean proof. The new node records its complete signature,
   source, searches, ancestry, creation and Lean fields; its dependency is the
   original comparison whose private helpers it uses. No change record is needed
   because no existing statement or definition changes. Verdict: pass.

Second reading changed only the report: explicitly recorded the replaced direct
proof dependency and this independent review. No Lean repair was necessary.
