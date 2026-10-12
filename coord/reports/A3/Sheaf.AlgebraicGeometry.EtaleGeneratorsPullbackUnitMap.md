## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.exists_etale_generators_pullback_unit_map`
to restriction naturality of an explicit pullback of generator sections. The existing
statement and docstring are unchanged. The proof constructs the direct-image sheaf map,
transposes it under the set-valued adjunction, proves its evaluation on unit sections,
and uses the scalar compatibility law.

Added three modules:
- `Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSections`: explicit construction
  `AlgebraicGeometry.Scheme.Modules.etaleGeneratorsPullbackSection`.
- `Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSectionsNatural`: the restriction law.
- `Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackMapUnitFormula`: the proved scalar law.

The two law modules are ordinary proof imports of the item. Each new module publicly
imports only what its signature or public definition uses. Removed the unused direct
Torsor import from the item and an unnecessary EtaleSheaves import from the construction.
No existing public imports, declarations, definitions, or file-level options change.

Change record: `coord/changes/EtaleGeneratorsPullbackUnitMap-interface.md`.

## Proved and sorry left

Original hole closed (1 of 1 in the item):
`AlgebraicGeometry.Scheme.Modules.exists_etale_generators_pullback_unit_map`
(node `lem-sc-etale-generators-pullback-unit-map`). Its proof still depends on the
new restriction theorem below, so this is a decomposition, not a sorry-free proof
of the original theorem.

New hole added (1):
`AlgebraicGeometry.Scheme.Modules.etaleGeneratorsPullbackSection_naturality`
(node `lem-sc-etale-generators-pullback-sections-natural`) in
`Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSectionsNatural`.
This is the only sorry in the delivered Lean source.

New proved theorem (no hole added):
`AlgebraicGeometry.Scheme.Modules.etale_generators_pullback_map_unit_formula`
(node `lem-sc-etale-generators-pullback-map-unit-formula`). The first worker left
this sorry; the second reader proved it using `pullback_map_smulHom`, the Gm
adjunction unit equation, and `smulHom_naturality_assoc`.

The explicit construction `AlgebraicGeometry.Scheme.Modules.etaleGeneratorsPullbackSection`
is compiled and has no sorry. Its locally chosen adjunction comes from the already
proved `nonempty_tensorPullbackAdjunction`, which has only the standard three axioms;
no data are chosen from an unproved existence theorem.

Baseline accounting: one original hole closed and one new hole added, net zero.
The scalar-law hole closed during second reading was only in the first-worker draft,
not in the baseline. No claim of whole-library progress or completed target is made.

## No longer needed

Removed direct import `WeilConjectures.CategoryTheory.Sites.Torsor` from the item.
It remains transitively available through EtaleIsoTorsor, and its node
`def-sc-gm-torsor` is still used; this is not pruning that node or module out of the
library. All four old proof dependencies are retained:
`def-pc-module-pullback`, `def-sc-gm-torsor`, `def-weil-pbc-etale-sheaves`,
and `def-weil-pbc-inverse-image`. No old proof-dependency node is unused.
No library module is claimed pruned.

Removed `Sheaf.AlgebraicGeometry.EtaleSheaves` from the new section-construction
module. Removed the first worker's duplicate public comparison helper
`generatorsTensorPullbackComparison` and its undelivered node; its one-line Mathlib
construction is local to the section definition. These are draft cleanup, not
baseline pruning.

## Where the brief, the DAG or earlier work was wrong

The first worker's modified item node omitted both lemmas actually used by its
proof. Its new construction-node statements were placeholders and its search
records did not describe the recorded search results. The second reading repaired
these records, the blueprint origins, the declaration signatures, and the
construction docstring's node tag.

The first report called the reduction proved without explicitly counting the two
new holes. After closing the scalar hole, the deliverable is a one-hole
decomposition. The restriction law is genuinely only the naturality step; it
neither asserts existence of the inverse-image sheaf map nor its equivariance.
The other law is proved and does not require restriction naturality.

## New nodes

`lem-sc-etale-generators-pullback-section` is a definition node for the explicit
composite of pullback isomorphisms. Its data are constructed without holes.

`lem-sc-etale-generators-pullback-sections-natural` is the sole split-off hole:
restriction along an etale arrow commutes with that specific section map. Its
complete natural-language proof is in its docstring and node.

`lem-sc-etale-generators-pullback-map-unit-formula` records the now-proved scalar
compatibility calculation for the same section map.

All three nodes remain below the original item and inherit its chapter, unit,
and blueprint ancestry. Their searches are genuine entries in `searches.jsonl`:
LeanSearch was unavailable (Internal Server Error); LeanFinder and source searches
found pullback/free-module coherence primitives, not this construction's laws.
Local source search found the scalar lemmas that closed the second hole.

## Second reading by A3

1. Compared the delivered item with the repository using diff, and checked its
   theorem signature as a byte-for-byte substring through the character before
   `:=`. It is identical, including both invertibility hypotheses and the full
   conclusion. No other existing Lean module is delivered. Verdict: unchanged
   existing interface, no target or definition weakened.

2. Compiled all four modules with `lcompile.py --all` in import order, with no
   errors or warnings. Searched all delivered source for forbidden declarations
   and sorry: there is exactly the named restriction theorem's whole-proof sorry,
   no sorry in a definition, and no forbidden declaration. A scratch copy compiled
   with `#print axioms`: the constructor, scalar theorem, and upstream
   `nonempty_tensorPullbackAdjunction` use only `propext`, `Classical.choice`, and
   `Quot.sound`; the restriction law and original existence theorem additionally
   use `sorryAx`. Verdict: kernel-checked reduction with one documented dependency.

3. Read both intermediate laws and the actual construction, including identity
   restrictions, empty schemes, and zero-ring sections. Pullback preserves
   isomorphisms even in these cases, the restriction identity follows from
   pseudofunctor composition coherence and the pullback-pasting square, and scalar
   compatibility needs no cancellation or nonempty generators. The laws are
   strictly separate parts of the original argument. Searched Mathlib through
   msearch with different words and searched lean/ for related pullback/scalar,
   torsor, and Hom comparison results. The scalar law was closed by existing
   upstream lemmas. The existing unit-normalized tensorSectionsPullbackComparison
   lives in an unrelated module with its own open evaluation law; its stronger
   normalization is unnecessary here. Removed the duplicate named comparison
   and kept only a local Mathlib left-adjoint comparison from a proved theorem.
   Verdict: one true, necessary, strictly smaller hole remains; no restatement.

4. Read the proof from the original theorem down through its helpers and retained
   its adjunction-based construction. All old DAG dependencies are accounted for
   in No longer needed. Proof-only imports are ordinary imports; the new modules'
   public imports are needed in signatures or public data. The unit
   `dag/units/sk-prop-ext-invariance.json` has empty realized lists and no node
   realizing a unit step was bypassed or removed. Verdict: the unit route is kept;
   no baseline module pruning claimed.

5. Checked each node against its declaration and proof. Replaced placeholder
   natural-language statements, made the two constructions a single definition
   node, corrected the blueprint ancestry, and recorded the actual three-step
   reduction and exact proof-dependency unions. The scalar node now describes
   the real proved argument, not an open tensor calculation. Verdict: DAG and
   Lean agree.

Second-reading changes: proved the scalar law; removed the duplicate comparison
helper/node and unused construction import; removed unnecessary item elaboration
options; restored exact signature whitespace; repaired source/docstring/node
records and the change record; rewrote hole accounting and pruning claims.
