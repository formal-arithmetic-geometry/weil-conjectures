## What changed

Filled `AlgebraicGeometry.Etale.isIso_globalGerm_identity` in
`Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`, with the original signature,
visibility and both public imports preserved. The final module has three imports. An algebraically closed field is strictly
henselian: it is henselian as a field, and the proved separably closed fraction-field
lemma gives its separably closed residue field. Apply the existing
`Scheme.strictlyHenselianSections_geometricStalk_isIso` at its identity point.
Each component of `globalGerm` is the composite of the global-sections comparison
isomorphism and precisely that germ. Componentwise invertibility proves the theorem.

The coefficient universe is explicitly specialized to `u + 1`. The identity geometric
point is over the closed point because a field spectrum is a singleton. This works for
all fields in the original hypotheses, with no nonempty-sheaf or characteristic condition.
No definitions, existing statements or imported interfaces changed.

Updated the existing DAG node with the canonical-map refinement and its dependencies;
the original four steps for the clauses retained through the public import stay recorded.
The item is not a realized unit statement or unit proof step, so no unit route changes.

Validation: single-file compilation through `lcompile.py` succeeds without warnings.
`#print axioms AlgebraicGeometry.Etale.isIso_globalGerm_identity` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

Search: LeanFinder returned only structure-sheaf/Zariski stalk lemmas; Loogle did not
recognize `GrothendieckTopology.Point.toPresheafFiber`; the Mathlib grep found the
point/germ API but no algebraically closed-field global-germ isomorphism. Repository
search found the already-proved strictly henselian sections-to-stalk theorem and the
analogous componentwise argument in `StrictLocalGlobalGermIso`. The proof uses the
public sections-to-stalk theorem directly, without importing the latter module or
accessing any private helper. The actual three search invocations are in `searches.jsonl`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_globalGerm_identity`
(node `lem-weil-pbc-geometric-point-pullback-stalk`).
No `sorry` remains in the delivered module; no new holes or modules were added.
This is a proof, not a decomposition; the axiom check confirms the dependency proof
is also free of `sorryAx`.

## No longer needed

Removed six unused private proof-dependency imports present in the current repository:

- `Sheaf.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.Paper.InverseImageStalkGerm`
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`
- `WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

No whole module or node is withdrawn or claimed globally pruned. Both public imports
preserve the existing equivalence/module clauses and canonical-germ interface. The
private `StrictlyHenselianSectionsStalk` import is used directly.

The canonical refinement does not use these original proof dependencies directly:
`lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant`,
`def-weil-pbc-abelian-etale-sheaves`, `def-weil-pbc-etale-sheaves`,
`def-weil-sheaf-of-modules-category`, `def-weil-pbc-inverse-image`,
`def-weil-pbc-geometric-stalks`, `lem-weil-pbc-inverse-image-stalk-germ`,
`def-weil-geometric-point`, `lem-weil-pbc-constant-sheaf-sections-connected`, and
`def-weil-connected-scheme`. They remain in the node's original four steps because
its unchanged natural-language statement also includes the original full clauses,
which remain available through the public `GeometricPointPullbackStalk` import.
The fifth step records the proof of the specific canonical germ. Consequently no
original DAG dependency is removed and no global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The node's recorded four-step proof described the original equivalence and existence of
a pullback-stalk isomorphism, but did not identify the specific `globalGerm` map in the
current item's declaration. The module docstring already suggested the correct strictly
henselian specialization. Added that argument to the node without changing its statement
or removing the original clauses. No mathematical statement was disputed or changed.

## Second reading by C2

Independent second reader; opened the delivered Lean module, its repository version,
the node and its diff, the three imported modules, the strictly henselian terminology
and fraction-field lemmas, and `dag/units/sk-thm-properbasechange.json`.

1. **Existing declarations unchanged: pass.** The only existing declaration is
   `AlgebraicGeometry.Etale.isIso_globalGerm_identity`. Its signature, including
   `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` and the specific map
   `globalGerm (𝟙 (Spec (.of Ω)))`, is byte for byte unchanged. Its public visibility
   and both public imports are unchanged. Only its proof, a local elaboration option,
   and six private imports differ. No definitions or other modules changed; no change
   record is needed.
2. **Proof and axioms: pass.** Independently compiled the delivered file through
   `lcompile.py` with no errors or warnings. Compiled a scratch copy ending in
   `#print axioms AlgebraicGeometry.Etale.isIso_globalGerm_identity`; the result is
   exactly `propext`, `Classical.choice`, `Quot.sound`. Searched the delivered source
   for prohibited declarations and remaining holes: none. The argument obtains a
   separably closed residue field from the proved fraction-field lemma, constructs
   the strict henselian instance, and applies the sections-to-stalk theorem with
   `R = Ω`, the identity geometric point, and coefficient universe `u + 1`.
   The closed-point condition follows from the singleton spectrum. Unfolding
   `globalGerm` identifies its actual component with the comparison isomorphism
   followed by that germ; composition and componentwise invertibility finish.
3. **Split statements: pass, none.** No new declaration, node, or hole was added.
   There is no arbitrary witness choice or postponed data. The proof applies to all
   algebraically closed fields, all abelian sheaves in the specified universe,
   including the zero sheaf, and imposes no characteristic or torsion restriction.
4. **Route and pruning: pass, report corrected.** Independent `rg` searches for
   global-germ and presheaf-fiber invertibility in Mathlib, upstream and `lean/Sheaf`
   confirmed the direct proved sections-to-stalk route. The analogous strict-local
   global-germ helper is private, and the generic one-point-open theorem requires
   extra residue-field/open-object identifications, so neither shortens this proof.
   Both public imports preserve the established interface; the sole private import
   supplies the theorem used. The item's node is absent from the unit's `realized`
   statement and steps, and no unit route is bypassed. The previous report incorrectly
   said no imports were removed; the six removed private imports and all ten original
   dependencies unused directly by the canonical refinement are now listed above.
5. **DAG agreement: pass.** Only `proof`, `proof_deps`, and `proof_origin` differ in
   the existing node. Its statement, Lean record, and unit are unchanged. The fifth
   step correctly records the canonical-map proof and the three additional node
   dependencies. `proof_deps` is exactly the union of step uses. The four original
   steps remain explicitly scoped to the original full clauses retained through the
   public import; this delivery closes only the canonical-germ hole, not those clauses.

Second reading changed only this report: corrected the import/pruning account and
added the independent checks above. The Lean proof and node needed no repair.
