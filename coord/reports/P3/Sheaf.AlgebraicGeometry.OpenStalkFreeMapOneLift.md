## What changed

`Sheaf.AlgebraicGeometry.OpenStalkFreeMapOneLift` now proves
`AlgebraicGeometry.Scheme.exists_open_stalk_free_map_one_lift` with its original signature.
The proof reduces each coordinate to the unit-source case, intersects the finite
neighbourhoods, aligns comparisons with the existing restriction-transport theorem,
and sums coordinate projections. The private `restriction_lift_stalk` helper is
fully proved. Three proof-only imports are added: `OpenStalkUnitMapOneLift`,
`OpenStalkRestrictionTransport`, and the source-library free-sheaf coordinate API.
No definition, existing signature, visibility, or public import changes.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_open_stalk_free_map_one_lift` (one hole).
Added: `AlgebraicGeometry.Scheme.exists_open_stalk_unit_map_one_lift`
(node `lem-sc-open-stalk-unit-map-one-lift`, one hole), in its own new module.
This is a decomposition, net zero holes: the finite coordinate intersection,
comparison alignment, and linear combination are now proved in Lean; only the
single image-germ lifting case remains. The existing theorem
`exists_openStalk_restriction_transport` is used as stated; its existing hole is
not added or changed by this delivery. The item's module has no remaining sorry.

## No longer needed

No original imports removed. The general finite-free ringed-space lifting module
`Sheaf.AlgebraicGeometry.FiniteFreeLocalStalkMapLift` and node
`lem-weil-pbc-finite-free-local-stalk-map-lift` are no longer direct dependencies
of the item: only the new unit-source leaf needs the singleton case of that tool.
Similarly `lem-sc-open-module-stalk-restriction-comparison` and
`new-module-restriction-stalk-components` leave the item's direct proof dependency
list, replaced by `lem-sc-open-stalk-restriction-transport`; these still occur
beneath transport and the new unit-source leaf and are not globally pruned.
No whole modules are claimed pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

The original plan gave a general ringed-space germ-formula result but not the
slice/free-source and scalar-transport interfaces needed to apply it directly.
The stronger open-site local lifting statement already imports this item and
cannot be used here without a cycle. The new route proves the genuinely finite
part of the argument from a strictly smaller unit-source special case.
The unit record has no realized nodes affected by this change, so the unit's
statement and route are preserved. Rank zero works without selecting any
germs; rank one is precisely the new leaf; the zero target and zero map satisfy
that leaf by the zero section. No finiteness of the target is introduced.

## New nodes

`lem-sc-open-stalk-unit-map-one-lift` in
`dag/nodes/sec-abelian-varieties/lem-sc-open-stalk-unit-map-one-lift.json` states
only the unit-source case (no finite-rank parameter and no simultaneous lifts).
Its module is `Sheaf.AlgebraicGeometry.OpenStalkUnitMapOneLift`; the docstring
and node give the image-of-one section construction, scalar transport, and germ
comparison proof. Sources read: Stacks Tags 01CP and 00A0(3). Three recorded
search kinds and library/DAG/blueprint searches found no independent exact match.
No change record is needed because no existing statement or definition changes.

## Second reading by P3

1. Compared both delivered Lean files with the repository: the unit-source file is
   new; the original finite-free theorem signature is byte-for-byte identical.
   Its docstring, namespace, visibility, and both public imports are unchanged.
   The only additions in its interface region are three plain proof imports and
   elaboration options. No existing definition or statement changes, and no
   change record is required. Verdict: pass.
2. Both modules compile through lcompile.py without errors or warnings (18.3 s
   for the unit file, 28.8 s for the finite-free file). The only delivered sorry
   is the named public exists_open_stalk_unit_map_one_lift, with its complete
   image-of-one construction proof and blueprint node. No definitions are added;
   choices of neighbourhoods and lifts occur only inside a theorem proof, not in
   exported data. A scratch #print axioms check of both public theorems gives
   propext, Classical.choice, Quot.sound, and sorryAx, as expected from the open
   unit leaf and existing restriction-transport theorem. There are no prohibited
   declarations or attributes. The private helper is a proved cancellation and
   naturality calculation. Verdict: pass as a decomposition, not a closed proof.
3. Read Stacks 01CP (lemma-stalk-internal-hom), including its finitely presented
   surjectivity assertion, and 00A0(3) (lemma-restrict, also valid for modules).
   For the new leaf the unit stalk is the regular ambient stalk module because
   the open-immersion stalk-ring map is invertible. A linear map out of it is
   determined by its image of one; representing that single germ and multiplying
   by its section gives the lift. There is no finite-type or quasicoherent
   hypothesis on N. For zero N or zero t use the zero section; x in U rules out
   an empty U. The leaf covers one generator only, strictly part of the finite
   coordinate argument, and does not merely rename the original theorem.
   Independent searches used LeanFinder query "A germ of a module sheaf section
   is represented on a smaller open set and defines a morphism from the structure
   sheaf", Loogle query "unitHomEquiv", and grep query
   "exists_le_germ_eq|unitHomEquiv|sheafOfModulesEquivOverUnit". The results give
   germ representatives and the unit universal property, but no direct open-site
   ambient-linear lifting theorem. Also read the proved finite-free ringed-space
   lifting and finite-locally-free stalk lifting APIs: they need the slice and
   scalar comparison work left in this leaf; neither is a one-line application.
   Verdict: true, needed, and no quick closure found.
4. Read the main proof from its conclusion backward: sum_freeπ_ιFree collapses
   the explicitly constructed finite sum after naturality moves the projections;
   restriction_lift_stalk aligns the separately chosen comparisons using exactly
   the coherence law supplied by exists_openStalk_restriction_transport. No
   unsupported claim that arbitrary comparisons are canonical is made. All
   three added imports are used directly; the original public imports supply
   the unchanged signature. The old direct proof dependencies removed are
   lem-weil-pbc-finite-free-local-stalk-map-lift,
   lem-sc-open-module-stalk-restriction-comparison, and
   new-module-restriction-stalk-components, all listed above. They remain below
   the new leaf or transport, so no module is claimed globally pruned. For m=0,
   the index type is empty, V=U, and the sum is zero; for m=1 only one lift is
   needed. Inspected dag/units/sk-prop-av-cube.json: its realized arrays are empty,
   and no unit-level step is bypassed or changed. Verdict: pass.
5. Compared the existing node diff: only proof, proof_deps, and proof_origin
   change, and its three steps match coordinate lifting, comparison alignment,
   and the finite sum in Lean. The new node has the required source, searches,
   creation, blueprint, chapter/unit, and verbatim Lean signature fields; its
   proof_deps are the union of its two proof steps' uses. Its source proof and
   docstring describe a real section construction, with no choice-defined data
   object. Verdict: pass.

Second reading changed only this review report. No Lean or node repair was
needed. One upper hole is closed, one strictly smaller leaf is added, net zero;
no whole module is pruned.
