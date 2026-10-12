## What changed

Replaced the whole proof of
`AlgebraicGeometry.Scheme.exists_pointed_smooth_family_stage`, without changing its signature
or docstring. The module now imports two proof dependencies privately:
`Sheaf.AlgebraicGeometry.Morphisms.AffineLimitSmoothStage` and
`Sheaf.AlgebraicGeometry.Morphisms.PointedSectionStageDescent`.

The proof first descends the inverse of the integer, then its multiplicative equation, using
Mathlib's global-section continuity and eventual-zero lemmas. Restricting the diagram to
`Over` this unit stage ensures that every later stage still has the integer invertible.
Finite-presentation descent supplies a model. The new eventual-smoothness statement supplies
a later smooth model. The existing proved fixed-stage map-descent theorem descends the section
composed with the comparison. Pulling back the model and lifting the descended map together
with the identity constructs a section whose equation follows directly from the second
projection. No additional equality descent is required for that equation.

The existing smooth section-component theorem supplies an open with geometrically irreducible
fibres. The comparison maps each connected original fibre into the corresponding component:
its image is preconnected, contains the section point, and lies in the appropriate model
fibre. Both maps lift into this open. The restricted square is proved cartesian directly by
its universal property, using cancellation against the open immersion. The model is Noetherian,
so the restricted structural map is quasi-compact and quasi-separated. Its geometric
irreducibility gives geometric connectedness. Finally the index is read back in the original
category, and the integer unit is transported along the transition map.

All four private helpers have complete Lean proofs. The existing unit's limit-reduction route
is kept. Its `realized` record is empty and no unit or chapter file was changed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_pointed_smooth_family_stage`
(node `lem-sbc-pointed-smooth-family-stage`). There are no sorries left in the item's module.

Added one strictly smaller hole:
`AlgebraicGeometry.Scheme.exists_smooth_stage_of_affine_limit`
(node `lem-sbc-affine-limit-smooth-stage`), in the new module
`Sheaf.AlgebraicGeometry.Morphisms.AffineLimitSmoothStage`.
Its entire proof is `:= by sorry`. It only asserts eventual smoothness of an already given
finitely presented cartesian stage model. It does not descend a family, descend a section,
construct a section component, assert geometric connectedness, or descend an integer unit.
Those parts are proved in the original module. This is a decomposition: one upper hole closed,
one lower hole added, net zero holes. It is not a sorry-free proof of the entire theorem.

Both delivered modules compile without warnings using `lcompile.py`. The existing
`exists_map_at_refinement_of_affine_limit` theorem is used rather than duplicating its proof.

## No longer needed

No original import is removed, and no whole existing module is pruned: the source affine-limit
module supplies finite-presentation descent, and Slicing supplies the section component.

The original theorem no longer directly uses `thm-pd-spreading-out` or its separate morphism
equality-descent clause. Section descent uses the already proved
`lem-sbc-pointed-section-stage-descent`; the section equation is constructed by a pullback lift.
`thm-pd-spreading-out` remains in the *new eventual-smoothness node's* proof plan for descending
chart comparison isomorphisms, so it is not claimed globally unnecessary.
No other original proof dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The original plan cites Tag 0C0C without an applicable general scheme-level Lean declaration.
The nearby theorem `Scheme.NoetherianApproximation.exists_smooth_stage` is insufficient:
its approximation requires every stage to be of finite type over the integers, while this
item permits arbitrary Noetherian quasi-separated stages. For example a constant diagram at
the spectrum of a characteristic-zero field need not be of finite type over the integers.
No existing signature was changed and no other group's module was adapted.

The original plan's separate descent of the section identity can be shortened: descend the
map into the model over its base stage and pull the model back to the map's domain. The
identity is then the second pullback projection equation. This preserves the statement and
the unit route, and is reflected in the updated node.

Searches: LeanFinder found finite-type equality descent and local finite-presentation lemmas;
Loogle found smooth base-change and composition instances; repository and Mathlib grep found
no general eventual-smoothness theorem. LeanSearch returned Internal Server Error, recorded
as unavailable in the new node. Faithfully-flat smooth descent in Mathlib does not apply:
the limit projection need not be faithfully flat.

Checked the missing smoothness statement against Stacks Tag 0C0C
(https://stacks.math.columbia.edu/tag/0C0C) and its affine-local argument. The new node expands
that argument with the already stated smooth algebra descent and comparison-isomorphism
steps. Edge cases: a constant system admits the original smooth model by its cartesian
identification; an empty source is smooth at a sufficiently late stage by the same affine
argument with zero rings; no nonempty-source or finite-type-over-integers hypothesis is
inserted. The main proof also admits the empty base. Integer zero is not silently excluded:
it can be a unit only in the zero global-section ring, and the descent proof still works.
For integer one the same proof simply descends a unit already present at every stage.

## New nodes

`lem-sbc-affine-limit-smooth-stage` is the general eventual-smoothness step of Tag 0C0C, with
Noetherian qcqs stages and affine transition maps. Its source, complete proof in words,
three kinds of searches, Lean signature, and dependencies are recorded in
`dag/nodes/sec-smooth-base-change/lem-sbc-affine-limit-smooth-stage.json`.
Its single statement is in
`lean/Sheaf/AlgebraicGeometry/Morphisms/AffineLimitSmoothStage.lean`.

Updated only `proof`, `proof_deps`, and `proof_origin` of
`dag/nodes/sec-smooth-base-change/lem-sbc-pointed-smooth-family-stage.json`.
No definition or statement changed; no change record or forced adaptation is needed.

## Second reading by V3

1. **Interface preservation — pass.** Read both delivered Lean modules and compared the
   original module with the repository using `diff -u` and the declaration parser.
   `AlgebraicGeometry.Scheme.exists_pointed_smooth_family_stage` has its existing statement
   byte for byte unchanged; its existing docstring and four public imports also match.
   The two added imports are private proof imports. There are no changed definitions,
   removed declarations, forced adaptations, target edits, or unrecorded interface changes.

2. **Proof and axioms — pass as a decomposition.** Compiled both modules in import order
   through `lcompile.py --all`: clean, 3.1 and 4.9 seconds. Compiled scratch copies with
   `#print axioms` for all four private helpers, the original theorem, and the new theorem.
   The unit descent, component-image containment, and open-lift pullback helpers use only
   `propext`, `Classical.choice`, and `Quot.sound`. The pointed-model helper and original
   theorem additionally use `sorryAx`, as expected from eventual smoothness; the new
   smoothness theorem has the same permitted list plus `sorryAx`. The only direct sorry
   in the delivered sources is the entire proof of
   `AlgebraicGeometry.Scheme.exists_smooth_stage_of_affine_limit`, as reported above.
   No prohibited declaration, hollow definition, or arbitrary data chosen from an
   unproved mere-existence theorem is present. Existential elimination occurs inside
   theorem proofs, not in definitions of data.

3. **Split statement and source — pass.** Read Stacks Tag 0C0C (eventual smoothness)
   and Tag 0CAQ (smooth algebra descent). The new theorem fixes an already finitely
   presented cartesian model and asserts only that a later second projection is smooth.
   Its hypotheses supply qcqs base stages and affine transitions; no finite-type-over-Z,
   flatness, surjectivity, nonempty source, or nonempty base assumption is smuggled in.
   The docstring gives the finite affine-cover argument, smooth algebra descent,
   comparison-isomorphism and inverse-equation descent, and a common stage followed
   by locality. Checked constant diagrams (the identity refinement suffices), empty
   source and empty base (zero algebras and possibly empty covers), and the fact that
   an empty limit source with a nonempty original model needs an eventual refinement,
   rather than smoothness of that original model. The reduction is strictly smaller
   than the item: it does not provide a section, unit, or connected-fibre model.
   Independent LeanFinder query: "Smoothness of a finitely presented scheme morphism
   is detected at a finite stage of an inverse system with affine transitions";
   results were local smoothness and finite-presentation facts, no matching theorem.
   Loogle query `"Smooth", "IsLimit"` returned no hits. Launcher grep query
   `exists_smooth_stage|smooth.*[Ii]sLimit|[Ss]mooth.*[Cc]olimit` returned no hits;
   direct `rg` over `lean/Sheaf`, `lean/WeilConjectures`, and Mathlib additionally
   identified the specialized NoetherianApproximation theorem and flat descent.
   Read the specialized theorem: its finite-type-over-Z approximation is unavailable
   for the general diagram here. Neither candidate closes the split-off statement
   in a few minutes. The new node and full docstring correspond to its Lean signature.

4. **Route and pruning — pass.** Reviewed the proof from the original conclusion down.
   `exists_unit_stage` descends an inverse and the equation using the two Mathlib
   global-section lemmas. The restriction to `Over k` keeps this unit through all
   subsequent refinements. Finite-presentation descent and the split smoothness lemma
   give a smooth model. The already proved fixed-stage map-descent theorem gives the
   section map; two pullback lifts supply its section equation and compatibility
   without a separate equality-descent lemma. Read the slicing theorem and checked
   that its component-containment clause is exactly what the image helper uses:
   the continuous image of the original connected fibre contains the section point.
   The open-lift helper proves cartesianness by the universal property and monicity,
   not by assuming that restricting a model always preserves its pullback. Local
   finite type over a Noetherian base and quasi-compactness make the model Noetherian,
   so the open structural map is qcqs; its geometric irreducibility implies connectedness.
   Both private imports are used and no original import should be removed.
   `## No longer needed` names the sole removed direct dependency,
   `thm-pd-spreading-out`, while retaining it in the new smoothness proof plan.
   Read `dag/units/sk-prop-input-spreading.json`: its realized lists are empty, and
   its limit-reduction step remains the route of this proof. No unit route is bypassed.

5. **DAG and report — pass.** Compared the existing node JSON: only `proof`,
   `proof_deps`, and `proof_origin` differ. Its four steps follow the Lean reduction
   and their cited dependency union is exactly `proof_deps`. Read the declarations
   for fixed-stage map descent, finite-presentation descent, and section components,
   and the statements of global-section continuity, smooth-algebra descent, and
   spreading out: they provide the assertions assigned to them. The new node has
   its source, self-contained statement, declaration record, complete proof plan,
   dependency union, creation record, chapter/unit, blueprint origin, and recorded
   searches. Its Lean statement matches the new module. The report correctly counts
   one original hole closed and one smaller hole added: net zero, a decomposition.

**Second-reader changes.** Added this independent review and an explicit
`verdict: unavailable` to the new node's failed LeanSearch entry, whose recorded result
already said Internal Server Error. No Lean proof, signature, definition, import,
unit route, or dependency was changed. Removed the scratch axiom-check source copies.
