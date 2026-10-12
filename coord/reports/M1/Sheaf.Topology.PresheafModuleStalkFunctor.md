## What changed

Filled the three proof holes in
`lean/Sheaf/Topology/PresheafModuleStalkFunctor.lean`, without changing any
signature, definition, docstring, or import.

`PresheafOfModules.stalkMap_linear` represents the scalar and vector as germs,
restricts both to the intersection of their neighborhoods, rewrites scalar
multiplication using `PresheafOfModules.germ_ringCat_smul`, and applies the
stalk-map germ formula and sectionwise linearity. This is the argument already
specified in the declaration's docstring. The source library's
`Scheme.Modules.stalkLinearMapMk` in
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` supplies the same
common-neighborhood proof pattern; no scheme hypothesis or import is used here.

`PresheafOfModules.stalkMap_id` and `PresheafOfModules.stalkMap_comp` use
extensionality and the identity/composition laws of the underlying presheaf
forgetful functor and abelian-group stalk functor.

Searches: LeanFinder through msearch returned tilde-sheaf special cases rather
than the arbitrary presheaf statement. Loogle through msearch confirmed
`PresheafOfModules.germ_ringCat_smul`. Ripgrep of Mathlib and both library roots
found the germ, restriction, and functoriality lemmas and the source proof
pattern above. The original public Mathlib import supplies every proof lemma.
Local single-file compilation passed without warnings in 2.3 seconds.

## Proved and sorry left

Proved all three original sorries:

- `PresheafOfModules.stalkMap_linear`.
- `PresheafOfModules.stalkMap_id`.
- `PresheafOfModules.stalkMap_comp`.

All belong to `def-weil-pbc-module-stalk`. No sorry remains in the module,
and none is added elsewhere. No intermediate statements were split off.

## No longer needed

None. No imports were removed. The original sole import,
`Mathlib.Algebra.Category.ModuleCat.Stalk`, is needed for the stalk module
structure and germ scalar-action formula. No DAG dependencies were bypassed;
the node already has no proof dependencies, and is not a realized statement
or proof step of its unit `sk-thm-reduction`. No additional Sheaf or
WeilConjectures module is needed for this proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The definition node has empty
`proof` and `proof_deps` fields; its module's existing theorem docstrings
contain the arguments, and those arguments now compile directly using
Mathlib. No change to the proof route or node record is needed.

## Second reading by M1

1. Compared the whole delivered module with the read-only repository using
   `diff -u`. Only the three original theorem proof bodies change. Every existing
   signature, definition body, docstring, and import is byte-for-byte unchanged;
   there are no additional delivered modules or change records. Verdict: pass.
2. Independently compiled the module with `lcompile.py`: clean, exit code 0
   (1.6 seconds). Scanned for sorry and forbidden declarations/options: none.
   Compiled a scratch copy with `#print axioms` for all seven declarations,
   including `moduleStalkFunctor`: every one uses only `propext`,
   `Classical.choice`, and `Quot.sound`. No hollow definition. Verdict: pass.
3. No statements were split off and no new declarations or nodes were added.
   The germ proof works for arbitrary ring presheaves, without a sheaf or
   commutativity assumption: the intersection contains x, restrictions put both
   representatives on it, and sectionwise linearity gives the claimed action.
   Zero scalars/vectors and the one-point case require no exceptional argument;
   an empty space has no x to instantiate. Verdict: pass.
4. Read Mathlib's ModuleCat/Stalk.lean and the upstream
   `Scheme.Modules.stalkLinearMapMk` proof; searched both library roots and
   independently searched Mathlib through msearch for stalk linearity and
   stalk-map germ formulas. The scheme and ringed-space results have narrower
   domains; no shorter existing presheaf-level linear map was found. The proof
   uses the existing Mathlib carrier, action, germ restriction, and stalk-map
   formulas directly. Identity and composition use the underlying functor laws.
   The sole public import is necessary for the definitions' module structure,
   so it is correctly public and cannot be pruned. The old proof_deps is empty,
   and the node is absent from every realized statement/step of
   dag/units/sk-thm-reduction.json. `No longer needed: None` is complete and
   the unit route is preserved. Verdict: pass.
5. Read def-weil-pbc-module-stalk in full. Its recorded seven declarations
   match this module. This is a Mathlib-backed definition node with empty
   proof/proof_deps and null proof_origin, rather than a theorem with a proof
   plan; the delivery introduces no DAG proof dependency or route change.
   Those fields remain appropriate. No relevant open change record was found.
   Verdict: pass.

Second reading changed only this report: added the independent review and
verification evidence. No Lean or DAG repair was needed.
