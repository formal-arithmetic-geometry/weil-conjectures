## What changed

Constructed `restrictedAffineSingleTransition` and `restrictedAffineSingleConeIso` explicitly
in `Sheaf.AlgebraicGeometry.RestrictedAffineSingleMaps`. No data is chosen from an unproved theorem.
Replaced the existence proof by substitution of the named concrete data, the explicit constructions,
three independent coherence obligations.

## Proved and sorry left

The sandbox main theorem `AlgebraicGeometry.Etale.exists_restricted_affine_single_coherence` has
no textual sorry and compiles from the named intermediate statements.
The generic coefficient-leg calculation compiles in scratchpad/Compatibility.lean.
Closed original hole (by reduction):
- `AlgebraicGeometry.Etale.exists_restricted_affine_single_coherence`
  (`lem-sbc-restricted-affine-single-coherence`).

Unconditionally proved original declarations: 0 of 1.
One original hole is reduced to three strictly simpler holes, so this is a decomposition, not
an unconditional proof or a net reduction in the number of holes.

New holes:
- `AlgebraicGeometry.Etale.restrictedAffineSingleConeIso_inv_leg`
  (`lem-sbc-restricted-affine-single-cone-leg`).
- `AlgebraicGeometry.Etale.restrictedAffineSingleTransition_laws`
  (`lem-sbc-restricted-affine-single-transition-laws`).
- `AlgebraicGeometry.Etale.restrictedAffineSingleConeIso_naturality`
  (`lem-sbc-restricted-affine-single-cone-naturality`).

## No longer needed

The original direct proof dependencies `def-weil-pbc-inverse-image` and
`lem-weil-pbc-inverse-image-composition` are replaced in the main node by the explicit-map
node and the three coherence obligations. They remain transitive dependencies of those
constructions and obligations; neither module is pruned from the target closure.
No original import is removed. The original inverse-image and coefficient construction nodes
remain needed through the explicit constructions and the three smaller obligations.
No limit, compactness, affine-transition, derived-cohomology, or colimit-preservation node is
added to this proof. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

Initially the shared last-green build lacked the prerequisite
`Sheaf.AlgebraicGeometry.RestrictedAffineCoefficientConstruction.olean`; it arrived during
the session and all five delivered modules compiled. No workaround by rebuilding shared
prerequisites was taken. The specialized coefficient-leg calculation caused costly unfolding;
its equation is separated as a named, strictly smaller obligation.

The new obligations retain the concrete canonical comparisons and the original coefficient
maps. They remain valid for an empty preorder (vacuous equations), a singleton (unit coherence),
and arbitrary cones, including cones that are not limits. The naturality obligation assumes
only the given transition equation; the transition-law obligation does not mention any cone.

## New nodes

`def-sbc-restricted-affine-single-maps`: the two explicit canonical maps, with no proof holes.
`lem-sbc-restricted-affine-single-transition-laws`: unit/composition laws for the fixed transitions.
`lem-sbc-restricted-affine-single-cone-naturality`: diagram equation for the fixed cone comparison.
`lem-sbc-restricted-affine-single-cone-leg`: the coefficient-leg equation alone,
without transitions or any coherence hypotheses.
Sources: [Stacks 09Z1](https://stacks.math.columbia.edu/tag/09Z1),
[Stacks 0EZM](https://stacks.math.columbia.edu/tag/0EZM), and
[Stacks 03CB](https://stacks.math.columbia.edu/tag/03CB).
LeanFinder, Loogle, and grep found composition components, but no assembled theorem;
LeanSearch returned an unavailable-service response. No change record is needed: existing
signatures and definitions are unchanged.

## Second reading by T4

1. Compared every delivered module with the repository. Only the main module existed;
   its theorem signature and original docstring are byte-for-byte unchanged. Its only
   edits are proof imports, local elaboration/linter options, and the proof body.
   The four new modules contain the reported explicit maps and obligations. No target,
   existing definition, or public import was changed; no change record is required.
2. All five modules compile locally in import order. No forbidden declaration or hollow
   definition occurs. The only textual holes are the three named public theorems listed
   above, each with its source, natural-language proof, and node. The existential witnesses
   are concrete maps, not choices from unproved existence. Explicit `#print axioms` checks on all six declarations show exactly propext,
   Classical.choice and Quot.sound for the two maps, and these three plus sorryAx for
   the three obligations and the reduced existence theorem. The delivery probe also
   passed. Thus sorryAx occurs only through the open obligations; this is a decomposition, not a completed proof.
3. Checked all three statements against the explicit definitions. Empty preorders make
   the laws vacuous; singleton/identity cases are the inverse-image unit laws. The leg
   equation is independent of transitions, the transition laws independent of cones,
   and naturality independent of a colimit. Zero sheaves and arbitrary nonlimiting cones
   introduce no obstruction. None restates the entire original existence theorem.
   Repeated LeanFinder, Loogle, and grep searches with different wording, and searched
   the library for raw restriction and single-complex comparisons. Existing coherence
   and single-functor lemmas supply components, not these assembled equations.
4. Read the proof from the existence theorem downward. Substitution eliminates only the
   data-identification hypotheses, then explicit transitions and cone comparisons reduce
   it to three distinct equations. Proof-only imports are plain imports; public imports
   in the new modules are needed in their signatures. The main node's removed direct
   dependencies are now listed above; no module is pruned. Checked the unit record:
   `sk-lem-failure-field` has empty statement/step realizations, and no unit-level route
   or statement is bypassed or changed by this below-unit categorical decomposition.
5. Checked each node's Lean declaration and normalized signature, proof steps, dependency
   union, provenance, source, creation and blueprint ancestry. They match the delivered
   proof and constructions. Checked the cited Stacks pages: 09Z1 supplies restriction
   to fibre products, 0EZM the complex coefficient system, and 03CB composition of
   inverse images. The obligations are the categorical elaboration of these sources.

Changed the report to name the original closed hole explicitly, record 0 of 1 original
holes unconditionally proved and three added holes, and enumerate the replaced direct
proof dependencies without claiming that their modules were pruned. Tried to close the
leg equation using the existing generic scratch calculation; both direct specialization
and a local generic calculation exceed the 60-second limit because of unfolding the
concrete dependent construction. Restored the original named obligation; no failing
trial, new helper declaration, or definition change is delivered.
