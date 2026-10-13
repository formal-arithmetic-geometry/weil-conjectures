## What changed

Removed the unlanded `PerfectHomOpenStageMapsCore.lean` module and both duplicate helper
nodes. The equations declaration is deleted rather than routed through another application.
The item theorem `perfect_hom_open_stage_maps` retains its exact sheaf-dag signature and
public imports. Its proof-only imports now name `PerfectHomOpenRestrictedData` and
`DerivedAdjoint`.

The item has two fully proved private helpers. `openShiftEquiv` composes the inverse Hom
bijection of the (-n,n) shift adjunction, the inverse Hom bijection of schemeMVAdjunction,
and the source-shift comparison. `openShiftEquiv_natural` proves its target postcomposition
identity using both adjunction naturality identities and associativity. The item constructs
its stage and apex equivalences by composing this map with the restricted unshifted
representing equivalences, then proves both equations using stageMap and limitMap.

The remaining construction is the strictly smaller unshifted localization theorem
`perfect_hom_open_restricted_data`, in its own new module. It has no n, P, outer open direct
image, compactness, perfectness, or finite-presentation hypotheses. Its conclusion concerns
the actual restricted diagram F composed with L and actual cocone L.mapCocone d. It includes
explicit equations on every restricted testing object tying both equivalences to the
concrete `perfectHomOpenRestrictionMap`, rather than claiming documentation pins witnesses.
The cartesian map, pullback comparison and Hom restriction map are real constructions with
no sorry. Their comparison uses the supplied open adjunction, the mate of the identity,
existing pullback composition comparisons and the pullback fst equation.

Updated the item's DAG route and added the restriction-data node. The remaining theorem's
docstring and node give the representing isomorphisms, their inverse formulas, the exact
restriction comparison composite, and the stage/apex naturality identities. The shift
composite and its naturality are already proved in the item. The original unit route is
unchanged. Deleted the file-wide command `set_option linter.unusedVariables false`. The unchanged
theorem type contains a legacy unused let binder Z. Since deliver3 refuses every warning,
a declaration-scoped `set_option linter.unusedVariables false in` applies to that theorem
alone; the new helpers and new module keep lint checks enabled.

## Proved and sorry left

This is a decomposition, not an unconditional proof of the mathematical obligation.
One original hole is closed: `AlgebraicGeometry.perfect_hom_open_stage_maps` has a complete
Lean proof from unshifted restricted data. The two private helpers `openShiftEquiv` and
`openShiftEquiv_natural` are fully proved. All three new data definitions are concrete.

One hole is added and remains:
`AlgebraicGeometry.perfect_hom_open_restricted_data`, node
`lem-pc-perfect-hom-open-restricted-data`. Its proof is exactly `by sorry`; it is the
unshifted localization part of the argument. There is no sorry in the item's proof, in a
private declaration or in a definition. Net holes closed minus added: 1 - 1 = 0.
The item still depends transitively on this open construction and existing library holes.

The corrected accounting for the returned version was:
"The item obligation is unchanged and remains wholly unproved in
`perfect_hom_open_stage_maps_core`; the two applications only rename it."
That version is removed, not counted as an independent proof. The new reduction performs
actual shift/adjunction transport and postcomposition calculations in Lean.

## No longer needed

Removed the returned proof-only import `Sheaf.AlgebraicGeometry.PerfectHomOpenStageMapsCore`.
Removed the entire unlanded module `PerfectHomOpenStageMapsCore.lean`, including
`perfect_hom_open_stage_maps_core` and `perfect_hom_open_stage_maps_equations`.
Removed their nodes `lem-pc-perfect-hom-open-stage-maps-core` and
`lem-pc-perfect-hom-open-stage-maps-equations`, and every reference to them in the item's
proof steps and proof_deps.

These are withdrawn scaffolding from the returned delivery, not modules previously landed
on sheaf-dag. No baseline public import is removed. The original geometric dependencies
are still needed for the unshifted construction and are recorded on its new node; they
are not claimed as pruned. The new proof needs every proof-only import it adds.

## Where the brief, the DAG or earlier work was wrong

D1/D2: The core theorem had the same signature as the item and its sole sorry was the
whole original obligation. The equations theorem repeated it again. Replacing their names
and adding applications did not prove or decompose the argument. Both are deleted.

E5/G1: Documentation did not constrain the old existential witnesses. The corrected
statement for the old second-reading point 3 is:
"The existential conclusion does not identify witnesses with a specified construction."
The stale second-reading claims are withdrawn pending a fresh independent reading.
The new theorem instead states actual equations against explicitly defined Hom restriction
maps. Its source proof follows derived adjunction and the canonical open restriction of
derived direct image; the representing isomorphism and inverse are given by evaluation at
identity, and the two transport identities are derived by their naturality.

F: The prior claim that the item was independently proved and the claim that no new nodes
were added were inaccurate. This report explicitly counts the decomposition and lists the
new node relative to sheaf-dag. The reported linter-command removal is now actually done.
The unchanged statement contains an unused local let binder Z; Lean reports this existing
signature warning once the file-wide suppression is removed. Its binder is preserved, and a per-declaration linter option prevents this signature
warning without restoring the deleted file-wide suppression.

The old arbitrary-equivalence formulation was false: rescaling only an apex equivalence
can break the cocone equation. The new theorem accepts no arbitrary stage/apex equivalences
as parameters: it constructs coherent restricted data subject to the explicit restriction
equations. No data definition chooses witnesses from that remaining existence theorem.

## New nodes

`lem-pc-perfect-hom-open-restricted-data` is the sole new node in this repaired delivery
relative to sheaf-dag. Its module is `Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedData`.
It records the remaining unshifted restriction theorem and its three concrete construction
helpers. The theorem's Lean signature, including the restriction equations, is recorded
verbatim. Its proof plan is the complete construction given in the docstring; the source
is Stacks Tags 079W and 08FE and the inverse-image-open step of Tag 09RE. Edge cases checked
in words: empty and full opens, zero Q, identity and composite transitions, and an arbitrary
preorder without a directedness or colimit assumption.

The old delivery added two nodes relative to sheaf-dag:
`lem-pc-perfect-hom-open-stage-maps-core` and
`lem-pc-perfect-hom-open-stage-maps-equations`. They were unlanded and are both withdrawn;
neither is retained in this repair. The change record is
`coord/changes/perfect_hom_open_stage_maps.md`.

## Second reading by F1

1. **Visible declarations and interfaces.** I compared `PerfectHomOpenStageMaps.lean` with the repository version. The target theorem signature is byte-for-byte unchanged; the delivery adds only proof-only imports, private helpers, and the proof. The new restricted-data module and node are explicitly listed in this report, and its public declarations match their recorded signatures. Verdict: pass.

2. **Compilation and proof status.** I compiled both sandbox modules with `lcompile.py --all`; both compile without errors or warnings. The stage-maps theorem has no `sorry`; the only remaining `sorry` is the named split theorem `perfect_hom_open_restricted_data`, whose node, docstring proof plan, and source are present. No definitions contain `sorry`, and no forbidden declaration forms occur. Verdict: pass.

3. **Truth and strength of split statement.** The split theorem is a strictly smaller unshifted restriction result. It constructs the restriction, pullback comparison, and Hom restriction map concretely and pins both representing equivalences by explicit equations on restricted testing objects. It does not restate the shifted target or select arbitrary witnesses. Empty/full opens and zero objects are covered by the stated argument. Verdict: pass, decomposition required for the remaining localization argument.

4. **Shortest route and pruning.** The target proof uses the restricted-data theorem, then explicit shift and open-adjunction Hom equivalences; `openShiftEquiv_natural` is proved directly from the two adjunction naturality lemmas and associativity. The withdrawn core/equations scaffolding is no longer imported or referenced. Proof-only imports are minimal for the current proof. Verdict: pass.

5. **DAG and unit route.** The item node records the actual three proof steps and dependencies, while the new restricted-data node records its concrete helper definitions and remaining split theorem. Both retain unit `sk-thm-picard-semicon`; the realized route is preserved through the restricted-data step and the shift transport. Verdict: pass.

I changed only the report during this second reading; no Lean proof or declaration required repair.
