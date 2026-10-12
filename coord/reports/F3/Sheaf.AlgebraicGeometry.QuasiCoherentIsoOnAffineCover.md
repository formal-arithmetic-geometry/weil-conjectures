## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_bijective_on_affine_open_cover`
with a complete proof. The declaration's signature and existing docstring are unchanged.
Added the proof-only import `Mathlib.AlgebraicGeometry.Modules.Tilde`.

The local `affine_iso` argument turns the bijective global-sections map into an
isomorphism in `ModuleCat`, applies the tilde functor, and uses counit naturality
and the quasi-coherent counit isomorphisms to conclude. For each affine open,
`IsAffineOpen.fromSpec` supplies the chart, restriction preserves quasi-coherence,
and its top sections are the sections on that open. Restricting back along
`IsAffineOpen.isoSpec.hom`, `restrictFunctorComp` and `restrictFunctorCongr`
identify this restriction with restriction along the open inclusion.
`overFunctorEquiv`, reflection by `overEquiv`, and
`sheaf_module_isIso_iff_isIso_over_open_cover` then conclude.

These are precisely the four existing DAG steps. All seven existing proof-dependency
nodes remain used; their Mathlib realizations provide the chart, restriction,
affine adjunction and interpretation of open restriction. No node update is necessary.
The module compiled cleanly with `lcompile.py`.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_bijective_on_affine_open_cover`
(blueprint: `lem-weil-pbc-quasi-coherent-iso-on-affine-cover`).

No `sorry` remains in the item, and no new holes or declarations were added.
This is a proof, not a decomposition. All supporting affine results are proved
Mathlib declarations; the existing open-cover gluing theorem is also proved.
The argument works for empty indexing types (the cover equality then forces the
scheme to be empty), arbitrary affine opens, and zero modules, without extra hypotheses.

## No longer needed

None. No imports were removed and no planned nodes or modules were bypassed.
The public import `Sheaf.AlgebraicGeometry.Coherent` is retained as the original
statement interface; the existing proof import of the open-cover gluing theorem
is used in the proof. The new Mathlib import provides the affine adjunction and
quasi-coherent restriction instances.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. The existing DAG already records the
needed affine adjunction and restriction facts as Mathlib realizations, so no
additional intermediate statements are needed. The unit's realized statements
and steps are unchanged.

## Second reading by F3

1. **Interface — pass.** Compared the sandbox module against the repository with
   `diff -u`. The sole existing declaration, its signature and its docstring are
   byte-for-byte unchanged. The only changes are its proof and the plain,
   proof-only import `Mathlib.AlgebraicGeometry.Modules.Tilde`. No definitions,
   target statements, visibility or other modules changed.
2. **Proof — pass.** Independently compiled the delivered file with `lcompile.py`
   without errors or warnings. Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_bijective_on_affine_open_cover`:
   exactly `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   Read the whole proof: bijectivity gives an isomorphism of global-section
   modules; tilde and counit naturality give the affine isomorphism; restriction
   along the inverse chart and the two natural isomorphisms give the open
   restriction; the proved open-cover criterion reflects this to the global map.
   There is no `sorry`, forbidden declaration, or data chosen from an unproved
   existence theorem. The charts are Mathlib's constructed `fromSpec` maps.
3. **Split statements — pass, none.** No new declarations, nodes or holes were
   introduced. The local `affine_iso` is fully proved for arbitrary commutative
   rings and quasi-coherent modules. No nonemptiness, nonzero-ring, nonzero-module,
   finiteness or separation assumption is used, so empty covers/schemes and zero
   modules do not create an omitted case.
4. **Route and pruning — pass.** Read the Mathlib affine counit theorem and
   searched Mathlib's Modules/Tilde and the project's upstream and Sheaf modules
   for affine/quasi-coherent isomorphism criteria, restriction criteria and
   reflection. No direct replacement for this affine-cover theorem was found.
   The existing public Coherent import preserves the statement interface; the
   open-cover proof import and added Tilde proof import are used. There is no
   unused proof import to prune. Read `dag/units/sk-thm-p1.json`'s `realized`
   statement and steps: none is bypassed by this four-step implementation.
5. **DAG — pass.** Opened the item's node and the Lean/Mathlib records of all
   seven `proof_deps`. Its four steps match the proof: scheme/spectrum chart,
   restriction preserving quasi-coherence, tilde-Gamma counit naturality,
   transport back to the open restriction (`overFunctorEquiv`), and the
   open-cover isomorphism criterion. The coherent node records the
   quasi-coherence convention; the finite-type/presentation node's Mathlib
   interpretation records `M.over U` as open restriction. Thus the existing
   `proof`, `proof_deps` and `proof_origin` continue to describe this proof and
   need no update.

Second reading changed only this report to record the independent checks;
no Lean repair was necessary. One existing hole closed, zero holes added.
