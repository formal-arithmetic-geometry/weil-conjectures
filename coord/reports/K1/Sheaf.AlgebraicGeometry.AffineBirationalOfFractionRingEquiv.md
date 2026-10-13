## What changed

Replaced the proof of `AlgebraicGeometry.birationalOver_of_fractionRing_equiv`, preserving
its signature and all existing public imports. Added two reusable, proved modules:
`Sheaf.AlgebraicGeometry.GenericInversePartialMapRestrictions` and
`Sheaf.AlgebraicGeometry.InversePartialMapRestrictions`. Both are proof dependencies;
the target imports the generic version privately, and the generic version imports the
composition version privately. No existing definitions, signatures, or visibility changed.

The proof identifies each affine section fraction ring with its generic-stalk function
field by Mathlib's localization algebra equivalence. It transports the compatibility
condition to the function fields, takes Spec, and proves compatibility over the affine
base by cancelling `S.toSpecΓ`. Mathlib's `PartialMap.ofFromSpecStalk` extends the two
inverse generic maps. The new generic restriction theorem proves dominance and proves
that both partial-map compositions are equivalent to the identities. The new composition
restriction theorem constructs smaller dense opens and mutually inverse restrictions.
Finally, the original theorem packages these restrictions into a partial isomorphism and
proves the base equation by the restriction factorization and `ofFromSpecStalk_comp`.

Sources read: Stacks Tags 0552 (Lemma 29.51.7), 0BAA (Lemma 29.50.12), and 01RR
(the rational-map definitions, generic determination, and composition discussion).
These were read on the Stacks website because the literature source checkout is absent
on this machine. Searches used Lean Finder, Loogle, grep, and LeanSearch; LeanSearch
returned HTTP 500 and is recorded as unavailable. Mathlib provides spreading out and
generic determination, but no complete inverse partial-map restriction theorem.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.birationalOver_of_fractionRing_equiv`
(node `lem-sbc-affine-birational-fraction-ring-equiv`). Added no holes.

Also proved:
- `AlgebraicGeometry.Scheme.PartialMap.exists_inverse_restrictions_of_generic_inverse`
  (node `lem-sbc-generic-inverse-partial-map-restrictions`);
- `AlgebraicGeometry.Scheme.PartialMap.exists_inverse_restrictions_of_comp_equiv_id`
  (node `lem-sbc-inverse-partial-map-restrictions`).

The three private helpers are fully proved. No declaration in the delivered modules
contains `sorry`. This is a proof, rather than a decomposition with remaining holes.

Edge cases checked in the argument: integral schemes are nonempty, including spectra
of fields; the dense open construction works for identity maps and already everywhere
defined inverse isomorphisms. Dominance supplies nonempty inverse images even when
structure maps to the base are not dominant. No integrality of the base is needed.
Both inverse identities are required; a one-sided inverse is not sufficient. Neither
new theorem assumes finite type or affineness, because its partial maps are already
supplied. Those hypotheses remain in the original theorem where spreading out and
the fraction-ring identification use them.

## No longer needed

No existing import, node, or module is pruned: the original node had no proof-dependency
imports or named proof dependencies. The generated common subalgebra and explicit
principal-localization denominator construction in the old proof plan are not needed;
their steps were never assigned nodes or modules. The source proof in Tag 0552 itself
uses spreading out a generic map, and this delivery follows that route using both inverse
maps. All imports in the delivery are used by statements or proofs.

## Where the brief, the DAG or earlier work was wrong

The node's two non-elementary proof steps had empty `uses`, and its `proof_deps` was
empty; there were no stated common-subalgebra or denominator lemmas to apply. This
was a gap in the plan, not a false statement. The updated node records the implemented
function-field and inverse-map proof. No unit statement or proof step is bypassed:
`dag/units/sk-prop-normal-form.json` has empty realization lists for the item, and the
affine fraction-field criterion remains available to the same caller.

## New nodes

`lem-sbc-generic-inverse-partial-map-restrictions`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-generic-inverse-partial-map-restrictions.json`,
records the proved generic inverse criterion for already supplied partial maps. Its Lean
module is `Sheaf.AlgebraicGeometry.GenericInversePartialMapRestrictions`. The proof
identifies the generic restrictions of the compositions, then uses Mathlib's generic
map determination theorem and the following restriction lemma.

`lem-sbc-inverse-partial-map-restrictions`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-inverse-partial-map-restrictions.json`, records
the proved restriction construction for dominant partial maps with identity composites.
Its Lean module is `Sheaf.AlgebraicGeometry.InversePartialMapRestrictions`. The proof
constructs the opens, verifies both image inclusions, lifts the maps, and cancels the
open inclusions to prove the inverse identities. No change records or forced adaptations
are needed. Blueprint searches for birationality, inverse rational maps, generic inverses,
and inverse dominant rational maps found no matching imported node.

## Second reading by K1

1. Compared the delivered existing module with the repository by diff: the theorem's
   signature and docstring are byte-for-byte unchanged. Only its proof and one private
   proof import changed. The other two modules are new; no existing definition,
   statement, visibility, or public import changed. Verdict: pass.
2. Read every proof, including the three private helpers. All three modules compile
   locally in import order, without errors or warnings. A scratch-copy axiom check of
   the original theorem and the generic inverse theorem reports only `propext`,
   `Classical.choice`, and `Quot.sound`; the latter includes the composition restriction
   theorem transitively. There are no sorries, forbidden declarations, or hollow
   definitions. The delivery tool additionally probes every declaration. Verdict: pass.
3. The two new theorems are proved, strictly intermediate results, not restatements of
   the original fraction-ring criterion. Checked the opens construction for identity
   maps, spectra of fields, and inverse maps on different dense domains: U and V are
   nonempty by dominance; f(U) lies in V by the identity on A, and g(V) lies in U by
   construction. Both inverse equations are used. Generic determination only shrinks
   the domain and requires no separatedness. Independent Lean Finder search for a
   rational map with a rational inverse, Loogle search for `PartialIso`, local Mathlib
   Birational source inspection, and repository searches found no existing theorem
   providing these inverse restrictions. Verdict: pass.
4. Read the argument from the original theorem downward. Mathlib supplies the fraction
   ring identification, spreading out, and generic determination; the new lemmas supply
   the remaining inverse restriction construction. Public imports provide signature
   notions, and the two new proof imports are private. The old proof_deps list is empty,
   so the pruning list is complete. Read sk-prop-normal-form's statement, steps, and
   empty realized lists; this change replaces only the lower affine criterion's route,
   preserving that criterion for its caller. Verdict: pass.
5. Compared the nodes with the declarations and proof bodies. Existing-node changes
   are confined to proof, proof_deps, and proof_origin. The function-field dependency
   is the matching Mathlib theorem; the two new node records include sources, searches,
   complete Lean signatures, creation records, and the same chapter/unit. Verdict: pass
   after removing an unused statement dependency from the new composition node.

Second reading changed only metadata: removed `def-sc-function-field` from the new
composition restriction node's stmt_deps, since its statement uses no function field.
No Lean repair was necessary; appended this independent review and its verification.
