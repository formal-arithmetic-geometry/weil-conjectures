## What changed

Proved `AlgebraicGeometry.Scheme.Modules.scalar_unit_class_pullback` in
`Sheaf.AlgebraicGeometry.ScalarUnitClassPullback`, with its signature unchanged.
Added the proof-only import `Sheaf.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality`.
The four private helpers prove the augmentation cocycle formula, the degree-zero
unit-class comparison, the adjunction uniqueness formula, and the scalar-unit
coefficient pullback identity. The final proof applies injectivity of the scalar
cohomology-to-Ext comparison and coefficient naturality, then combines these identities
using preservation of degree-zero Ext classes and Yoneda composition.

The route is exactly the existing node's plan; its four proof dependencies are all used.
No public interface, definition, or target signature changed. Empty schemes require no
separate assumption: the section and morphism equalities apply to their zero modules.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.scalar_unit_class_pullback`
(node `lem-sc-scalar-unit-class-pullback`).
No holes added, no split-off statements, and no `sorry` remains in the delivered module.
The proof uses existing stated dependencies, including
`scalarCohomologyExtEquiv_map`, `exists_moduleExtEquiv`, and
`exists_scalarPullbackCoefficient`; their upstream holes are unchanged.

## No longer needed

None. Both original public imports are required by the statement, and the added
coefficient-naturality import is used by the proof. No planned dependency is bypassed,
and no node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The planned degree-zero and constant-sheaf
adjunction steps were not separately stated in the original dependencies; they are
now proved as private helpers rather than introduced as new obligations.

Searches ran through msearch (LeanFinder, Loogle, grep) and local rg searches of the
scheme-module library and Mathlib's injective-resolution, Ext, constant-sheaf, and
adjunction APIs. No existing complete unit-class pullback theorem was found.

The first dry run conservatively classified the section-local proof commands as an
interface change. Their scope and the unchanged downstream interface are documented in
`coord/changes/scalar-unit-class-pullback-local-proof-commands.md`. No adaptation is needed.


## Second reading by V2

1. **Unchanged interface: PASS.** Compared the sole delivered Lean module with the
   repository using `diff -u`. The existing theorem signature, docstring, visibility,
   and public imports are byte-for-byte unchanged. Additions are one plain proof-only
   import and a section containing four private proved helpers. The local options,
   opens, and instance attributes end before the public theorem. The existing change
   record documents the conservative interface classification; no definition changes
   or forced adaptations are present.
2. **Proof and compilation: PASS.** Compiled the complete sandbox through
   `lcompile.py --all`: no errors or warnings, approximately 30 seconds. Scanned the
   delivered source: no sorry, forbidden declarations, or hollow definitions.
   Compiled a scratch copy with `#print axioms` for all four helpers and the public
   theorem. `augmentation_cocycle` and `homEquiv_unique` use only `propext`,
   `Classical.choice`, and `Quot.sound`; the other three additionally use inherited
   `sorryAx`, as expected from open upstream dependencies. The reduction explicitly
   evaluates the resolution augmentation and the adjunction unit; it does not infer
   the result from an unrelated open statement. The coefficient comparison is pinned
   by its sectionwise adjoint formula, and moduleExtEquiv by its cocycle formula;
   these choices determine the objects used here, rather than arbitrary witnesses.
3. **Split statements and edge cases: PASS.** No split-off statements or new holes.
   Read each private helper and the specifications of exists_moduleExtEquiv,
   exists_scalarPullbackCoefficient, and exists_tensorPullbackAdjunction. The cocycle
   calculation handles degree zero and every other complex index explicitly. The
   adjunction calculation uses only preservation of one and linearity, so it applies
   also to empty schemes and to identity pullback without additional hypotheses.
   Independent msearch queries used Loogle (`CategoryTheory.InjectiveResolution.extMk`),
   LeanFinder (augmentation represents the identity Ext class), and grep
   (`extMk.*ι|ι.*extMk|homEquiv.*leftAdjointUniq`), supplemented by local rg searches.
   The relevant Mathlib results are already used; no complete duplicate was found.
4. **Route and pruning: PASS.** Read the statement imports, coefficient naturality,
   Mathlib's injective-resolution Ext API, and adjunction uniqueness API. No shorter
   existing replacement was found. Both public imports supply statement definitions;
   the additional import supplies the coefficient-naturality theorem used in the
   proof. All four old proof dependencies remain used; `## No longer needed` is
   complete. The item's unit is sk-prop-av-cube; its realized fields are unchanged
   and no unit-level argument is bypassed.
5. **DAG agreement: PASS.** Read lem-sc-scalar-unit-class-pullback, its four
   proof-dependency declarations, and dag/units/sk-prop-av-cube.json. The existing
   node already describes precisely this augmentation, constant-sheaf adjunction,
   and coefficient-naturality reduction, with the correct proof_deps and source
   origin. No new node or node-field repair is required.

Second reading changed only this report to record the independent checks and verdicts.
The Lean proof and change record required no repair. Closed one original named hole
(scalar_unit_class_pullback); added zero holes and split off zero statements.
