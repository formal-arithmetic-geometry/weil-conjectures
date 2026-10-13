## What changed

Proved all eight original theorem holes in `lean/Sheaf/RingTheory/FormalGlueingData.lean`.
All existing public statements, universes, definitions, docstrings and imports are unchanged.
Added only fully proved private helpers for localized/base-changed endomorphisms,
scalar endomorphisms, fraction formulas and identity/composition functoriality.

The localized S-action is constructed by composing S's multiplication homomorphism
into R-linear endomorphisms with the ring homomorphism induced by localization.
Mathlib's `IsLocalizedModule.map_id`, `map_comp'` and the additivity of `map`
prove that this is a ring homomorphism; `Module.compHom` gives the module action.
`map_LocalizedModules` proves its required formula on every fraction.

For the swap, localizing endomorphisms preserves invertibility, so both sets of
powers act invertibly on the target. Two applications of `LocalizedModule.lift`
and `lift_unique` prove existence and uniqueness. For the comparison, base change
likewise preserves invertible scalar endomorphisms; one application of the same
universal property proves existence and uniqueness. Its S-linearity is proved
by localization extensionality, comparing the two R-linear composites with
scalar multiplication and checking equality on the original tensor module.
Localization of an S-linear map is S-linear by its fraction formula.

Identity and composition compatibilities use Mathlib functoriality and the
existing morphism compatibility equations. The category laws hold by componentwise
reduction and proof irrelevance. These are precisely the routes already described
in the original docstrings and the definition node's split report; no DAG route
or unit realization changes, so no node copy is needed.

Searches: LeanFinder for commuting scalar actions, iterated localization and tensor
localization found localization/base-change APIs; Loogle `IsLocalizedModule.map`
found `map_id`, `map_comp'`, `map_LocalizedModules`. The launcher grep search and
focused local rg searches found `LinearMap.baseChange_id`, `baseChange_comp`,
`LocalizedModule.lift`, `lift_comp`, `lift_unique` and `IsLocalizedModule.ext`.
The separate canonical-maps module imports this module and cannot be used here;
its needed basic properties are proved directly with Mathlib instead.

Validation: the entire delivered module compiles cleanly using the mandated
`lcompile.py`; no overlong lines and no remaining sorry. Direct `#print axioms`
checks on the delivered source show only `propext`, `Classical.choice`, and
`Quot.sound` for all eight theorems and for `localizedSModule`, `swap`, `compare`,
`idHom` and `compHom`. The proof covers arbitrary
commutative rings, zero or unit localization elements, the zero module, and the
empty chart family without additional hypotheses.

## Proved and sorry left

Closed eight original holes, all belonging to
`def-weil-pbc-formal-glueing-data` (the canonical-map clauses are also described by
`lem-weil-pbc-formal-glueing-canonical-maps`):

- `FormalGlueing.exists_localized_s_module`
- `FormalGlueing.exists_swap`
- `FormalGlueing.exists_compare`
- `FormalGlueing.compare_smul`
- `FormalGlueing.localMap_smul`
- `FormalGlueing.id_compat`
- `FormalGlueing.comp_compat`
- `FormalGlueing.category_laws`

No sorry remains in the item. No holes were added or split off. This is a proof,
not a decomposition. All new private helpers are fully proved.

## No longer needed

None. No imports were removed or added. All four original public imports supply
objects or operations appearing in the unchanged public declarations. There were
no planned proof-dependency imports to prune. No module is claimed globally pruned;
the canonical-maps module has additional inverse/isomorphism properties used elsewhere.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction was needed. The existing definition node
has empty `proof` and `proof_deps`; the eight implementation obligations and their
routes are documented in its split report and in the Lean theorem docstrings.
The cited Stacks TeX file is absent on this machine; the existing source references
were retained, and the official Stacks pages were read for the definition and
localization universal property: [Remark 05EL](https://stacks.math.columbia.edu/tag/05EL)
and [Lemma 07K0](https://stacks.math.columbia.edu/tag/07K0). No unsupported intermediate theorem was introduced.

## Second reading by J3

1. Interface: PASS. Read the full diff against the repository module and compared
   all 24 existing declaration records with `stage3_delivery.decl_table`.
   Every existing signature is byte-for-byte identical, and every existing
   non-theorem body (including structures, abbreviations and category instance)
   is identical. Only eight theorem proofs and 14 private implementation helpers
   were added. No change record or interface adaptation is required.
2. Proof: PASS. Independently compiled the delivered module with `lcompile.py`
   (7.5 seconds, no warnings). A scratch copy with `#print axioms` for all eight
   closed theorems and `localizedSModule`, `swap`, `compare`, `idHom`, `compHom`
   compiled in 7.0 seconds: each uses only `propext`, `Classical.choice`,
   `Quot.sound`. Scanned the source for sorry and forbidden declarations or
   kernel bypasses; none occurs. The module header, visibility and line lengths
   conform. The existing choice definitions now choose from proved theorems:
   the localized action is fixed on every fraction, and swap/compare are unique
   linear maps, so no arbitrary witness of an unproved existence is used.
3. Intermediate statements: PASS. No split-off statement or new sorry was added.
   Read every private helper: the endomorphism homomorphisms preserve products
   by localization/base-change functoriality; the scalar equalities identify
   their images, so transporting units is legitimate. The remaining helpers
   are fraction formulas or identity/composition facts. Reviewed zero and unit
   localization elements, zero modules, zero rings, and an empty chart family:
   no nonzero or nonempty premise is used. Independently searched with launcher
   Loogle `IsLocalizedModule.map, _ = _` and rg for scalar, algebraMap, map_smul,
   map_id and map_comp in Mathlib's localization API and for localEndHom,
   baseEndHom, localize_units, exists_swap and exists_compare in lean/. Results
   support the APIs already used; no missing shorter complete proof was found.
   The separate canonical-maps module imports this module and would create a
   cycle if used here.
4. Route and pruning: PASS. Read proofs from the eight holes downward. The
   action is genuinely constructed, the swap uses two lifts, the comparison
   uses one lift, scalar compatibility uses localization extensionality, and
   category laws reduce componentwise. These are direct Mathlib reductions;
   the private wrappers expose existing operations rather than duplicate open
   statements. The four public imports provide the localized module, restriction
   of scalars, away ring, and tensor/baseChange structures used by existing
   definitions and signatures; none is proof-only. No old proof dependency or
   module becomes unnecessary. Read `dag/units/sk-thm-p1.json`, including its
   `realized` steps: the item is below those steps and bypasses none of them.
5. DAG: PASS. Read the definition node and its canonical-maps pointer node.
   The definition node's empty proof/proof_deps and null proof_origin describe
   a definition, with its implementation obligations and their source route
   recorded in the split report. This delivery closes those existing obligations
   by the recorded route and introduces no new public mathematical statement.
   The pointer node's stronger inverse/isomorphism properties live in its own
   module and are not claimed proved by this delivery. No node update is needed.

Second reading changed only this report: added independent interface, proof,
axiom, intermediate-statement, pruning, unit-route and DAG checks. No Lean
repair was necessary. Verdict: deliver eight of eight holes closed, zero added.
