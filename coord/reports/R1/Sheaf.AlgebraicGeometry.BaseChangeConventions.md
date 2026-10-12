## What changed

Filled all four theorem proofs in
`lean/Sheaf/AlgebraicGeometry/BaseChangeConventions.lean`, without changing any signature,
definition, or import. No new module or node is needed.

- `AlgebraicGeometry.baseChange_morphism_projections`: unfold the map of `Over.pullback`
  and use the two universal-lift projection equations.
- `AlgebraicGeometry.baseChange_iterated`: apply `isPullback_baseChangeMap`, then use
  its canonical `isoPullback` and the two equations for its hom.
- `AlgebraicGeometry.baseChange_fiber`: use the inverse of
  `pullbackLeftPullbackSndIso`; its projection equations give precisely the fibre
  inclusion followed by the first projection and the residue-field projection.
- `AlgebraicGeometry.baseChange_section_characterization`: use the existing section's
  second projection equation and the lift's first projection equation; uniqueness
  follows from `pullback.hom_ext` applied to the two assumed equations.

These follow the existing declaration docstrings for node `def-pc-base-change`, whose
DAG proof and proof-dependency lists are empty because it is a definition bundle.
The unit `sk-def-av-jacobian` has no realized proof steps, and its route is unchanged.
Searches used the supplied LeanFinder and Loogle wrappers and direct searches of
Mathlib and both project roots. LeanFinder returned the pullback-pasting comparison
and its equations; Loogle returned `IsPullback.isoPullback` and its projection equations.
The resulting module compiled locally with no errors or warnings.

## Proved and sorry left

Proved all four original sorries, associated with `def-pc-base-change`:

- `AlgebraicGeometry.baseChange_morphism_projections`
- `AlgebraicGeometry.baseChange_iterated`
- `AlgebraicGeometry.baseChange_fiber`
- `AlgebraicGeometry.baseChange_section_characterization`

No sorry remains in the item's module, and no new sorry is introduced. The definitions
retain their existing dependency on `Scheme.Modules.tensorPullback`; this delivery
proves only the four comparison and characterization theorems.

## No longer needed

None. No imports were added or removed, and no planned proof nodes or modules are
bypassed. The four public imports remain needed by the existing definitions and
statements: scheme fibres, algebraic closures, base-change maps and sections, and
module tensor pullback.

## Where the brief, the DAG or earlier work was wrong

None. The four sorries are elementary consequences of existing universal-property
APIs, rather than requiring additional sheaf or algebraic-geometric theory. The
original statements and the unit's route are preserved.

## Second reading by R1

1. **Interface preservation: PASS.** Read the whole delivered module and its unified
   diff against the repository version. Only the four original theorem proof bodies
   changed. All existing signatures, definitions, docstrings and imports are byte
   for byte unchanged; no change record is required.
2. **Proof and trust: PASS.** Independently compiled the module with `lcompile.py`:
   no errors or warnings. A scratch copy with `#print axioms` for all six declarations
   confirms that each of the four proved theorems and `geometricFiberAt` uses only
   `propext`, `Classical.choice`, and `Quot.sound`. `moduleBaseChange` retains its
   pre-existing `sorryAx` dependency through the named open tensor-pullback theorems;
   its data is unchanged and is not hollow. No sorry or forbidden declaration occurs
   in the delivered module.
3. **Split statements: PASS (none).** No new declaration, split-off statement, module
   or node was added. Read the pullback-pasting inverse projection equations in
   Mathlib and the upstream definitions/proofs of `baseChangeMap`,
   `isPullback_baseChangeMap`, `sectionBaseChange`, and `sectionBaseChange_snd`.
   These are genuine universal-property reductions, not restatements. The arguments
   impose no nonemptiness or nondegeneracy assumptions, so empty schemes and identity
   base changes remain covered.
4. **Route and pruning: PASS.** Independent LeanFinder search with the description
   of a pullback of a second projection recovered the exact Mathlib inverse-pasting
   equation used here; direct repository and Mathlib searches confirm the existing
   APIs already used are the short route. The four public imports provide notions
   in public signatures or definition bodies (fibres, algebraic closures, the
   upstream base-change/section definitions, tensor module pullback). None is merely
   a proof import. No old proof dependency is bypassed: the node's list is empty.
   `sk-def-av-jacobian` has empty realized statement and step lists and is unchanged.
5. **DAG agreement: PASS.** Read `def-pc-base-change.json` and its unit record.
   This definition bundle already records all six declarations and has empty
   `proof`, `proof_deps`, and null `proof_origin`; the elementary comparison proofs
   implement its existing clauses using its recorded statement ingredients.
   No new or changed mathematical dependency or node record is needed.

Second reading changed only this report by adding the independent review. No repair
of the Lean proofs, imports, definitions, statements or nodes was necessary.
