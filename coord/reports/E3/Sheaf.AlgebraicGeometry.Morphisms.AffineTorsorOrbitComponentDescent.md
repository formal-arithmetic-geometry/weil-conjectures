## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorOrbitComponentDescent`
with a complete proof assembling a family of descended components. The original
signature and docstring are unchanged. Added two proof-only imports, two new
statement modules, and their nodes; updated the item's proof, proof_deps and
proof_origin to match the Lean argument.

The first new theorem descends one labelled section to the puncture of its exact
stabilizer's invariant subalgebra, as an open immersion into the base change.
It supplies the structural-map and pulled-back-section equations and does not
assume a family of complete or distinct representatives. The second theorem
accepts such component maps and proves only coverage and disjointness of their
open images. Neither theorem asserts the item's coproduct isomorphism.

The assembly uses Mathlib's `nonempty_isColimit_cofanMk_of` and
`Cofan.nonempty_isColimit_iff_isIso_sigmaDesc`. It obtains an actual comparison
map with `Sigma.desc`, proves that it is an isomorphism, reverses it, proves
its projection equation by `Sigma.hom_ext`, and cancels its inverse. The maps
are selected inside a proof; no definition chooses data from an unproved
existence theorem. The restriction q in each new signature is an explicit
`Spec.map` of the invariant-subalgebra inclusion followed by `resLE`.

All three delivered modules compile cleanly through lcompile.py. No definitions,
existing interfaces, targets, or modules held by other groups were changed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.affine_torsor_orbit_component_descent`
(node `lem-sbc-affine-torsor-orbit-component-descent`). Its proof has no sorry.

Added two holes, each exactly `:= by sorry` in its own new module:

- `AlgebraicGeometry.Scheme.affine_torsor_single_stabilizer_component`
  (`lem-sbc-affine-torsor-single-stabilizer-component`, module
  `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSingleStabilizerComponent`).
- `AlgebraicGeometry.Scheme.affine_torsor_representative_component_cover`
  (`lem-sbc-affine-torsor-representative-component-cover`, module
  `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorRepresentativeComponentCover`).

This is a decomposition: one upper hole closed, two lower holes added, net -1.
The original module has zero direct holes, but the geometric descent argument
remains in the two statements. The existing `fixedPunctureLabel_laws` dependency
also remains unproved and is unchanged by this delivery.

Edge cases checked in the new statements: the single-component theorem has an
actual x : Fin d, so it makes no assertion for d = 0. For the family theorem,
d = 0 forces m = 0 by r : Fin m -> Fin d; the splitting and faithful cover force
the base change to be empty, so the empty supremum is top there. If m = 0 but
d > 0, completeness is impossible. For a trivial deck group, exact stabilizers
are trivial and the components are the individual split sections; distinctness
excludes repeated labels. For a transitive action, the family has one orbit and
the construction identifies that single component. No nonempty-family assumption
or invertibility of the group order was added.

## No longer needed

No existing imports, nodes, or modules were pruned. The action construction is
still used in the statements and in both remaining geometric obligations.
No product-spectrum or finite-product principal-open theorem is needed in this
module; none was imported originally, and none was added. The existing
`AffineTorsorEquivariantDescent` route cannot be imported here because it depends
on `AffineTorsorFixedPunctureDescentGeometric`, which depends on this item.

The unit `sk-prop-input-spreading` and its route are unchanged. Its realized
lists do not contain this item; the decomposition stays below the unit level.

## Where the brief, the DAG or earlier work was wrong

The original source record describes Stacks Tag 0EYG as a fixed-subalgebra
construction. Reading https://stacks.math.columbia.edu/tag/0EYG shows it is
Abhyankar's lemma for a regular divisor, with locally Noetherian and tame
ramification hypotheses. It is not the general invariant-subring quotient
result required here. Tag 03SF supplies the Galois-cover/permutation-set
classification used in the proof plan; the new nodes cite that source and
spell out the localization argument. The original docstring and source field
were preserved, with this citation issue reported rather than silently edited.

Library searches found finite-etale quotient and geometric-fibre APIs in
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisCategory`, but no
ready theorem combining the particular restricted inclusion, section equation,
and fixedPunctureDescentAction. LeanFinder returned related algebraic-etale and
invariant-ring results. LeanSearch returned Internal Server Error, recorded as
unavailable. The initial Loogle query rejected the unqualified identifier IsIso;
that is not treated as evidence of absence. The actual logged grep searches and
local source reading found Mathlib's disjoint-open-cover assembly theorem.
Blueprint searches for stabilizer and orbit did not find these two precise
statements. The ancestor tool reported no blueprint ancestor for this item;
the new nodes explicitly reference the parent's individual descent and coverage
steps in blueprint.from instead of inventing a blueprint ancestor.

## New nodes

`lem-sbc-affine-torsor-single-stabilizer-component` isolates descent of one
section and identification of its quotient with the explicit invariant-ring
puncture. Its docstring includes the torsor, connectedness, stabilizer quotient,
invariant-localization and compatibility arguments. This theorem is strictly
smaller than the item's family decomposition and needs no orbit completeness
or distinctness.

`lem-sbc-affine-torsor-representative-component-cover` isolates the two
open-image properties of an already supplied family of component maps. Its
proof sketch checks geometric fibres after faithful base change: each image
is the representative's orbit, completeness covers, and distinctness separates.
It does not construct maps or assert a coproduct isomorphism. The original
module supplies the Mathlib colimit argument and structural-map equation.

No change record is needed: existing signatures, definitions and public imports
are unchanged. No forced adaptations were made.

## Second reading by E3

1. **Interfaces and accidental changes.** Compared the delivered orbit module with the repository version. Existing declaration signatures, hypotheses, conclusions, and docstrings are byte-for-byte unchanged; the only edits there are two proof-only imports and the proof. The two additional modules contain only the explicitly split public statements and their documented holes.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`; compilation succeeds. The original target proof contains no `sorry`, and the only remaining holes are the two named split theorems listed above. No forbidden declarations or hollow definitions occur. The assembly proof uses the colimit and isomorphism lemmas directly, and its local choices are made inside the proof.

3. **Split statements.** Checked both new statements against their Lean signatures and edge cases. The single-component statement has an explicit `x : Fin d` and makes no false claim when `d = 0`; the family statement handles empty representatives and only asserts coverage/disjointness for supplied component maps. Both are strictly smaller than the target and do not restate its coproduct conclusion. Searches recorded in the node files found no existing declaration with either statement.

4. **Pruning and route.** The target proof uses both split statements and Mathlib's coproduct-cover route. No previous import or proof dependency became unused, and no unit-level route was bypassed; the unit and its realized route remain unchanged.

5. **DAG consistency.** The target and both new node files match the Lean declarations, proof dependencies, proof origins, source notes, and split status. The target node records the two new proof dependencies, while each split node records the imported split-label-laws dependency.

I changed only this report section after the initial review; no Lean source, node, or interface was altered.
