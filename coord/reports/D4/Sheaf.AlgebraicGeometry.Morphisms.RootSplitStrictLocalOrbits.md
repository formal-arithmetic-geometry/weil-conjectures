## What changed

The signature of `AlgebraicGeometry.Scheme.root_split_strict_local_orbits` is unchanged.
Its complete Lean proof now combines descent to stabilizer fixed rings with the independent
calculation of those fixed rings. Two new modules carry these strictly smaller statements:
`Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootOrbitDescent` and
`Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootInvariants`.

`rootRotation` constructs polynomial evaluation at zeta times the root. Its relation proof is
complete. `rootFixedAlgebra` is the intersection of the actual equalizers of these rotations
with the identity. Neither construction chooses data from an existence theorem or contains
sorry. The fixed-ring calculation has no scheme or cover parameters and requires no regularity
or nonzerodivisor assumptions. The descent statement produces fixed rings and makes no claim
that they are intermediate root algebras.

The item's private, fully proved `root_fixed_puncture_iso` constructs the restriction of an
H-algebra equivalence to D(h), proves equality of its inverse-image open, and proves the equation
over Spec H using Spec.map_comp and algebra compatibility. The final proof transports n's unit
condition along iota, takes a product of the algebra equivalences, and composes its restricted
Spec isomorphism with the descent isomorphism. All old public imports and visibility remain
unchanged; the new import needed only by the proof is non-public.

## Proved and sorry left

Closed the item's one hole in `AlgebraicGeometry.Scheme.root_split_strict_local_orbits`
(node `lem-sbc-root-split-strict-local-orbits`) by decomposition. Its combining proof contains
no sorry. This is one upper hole closed and two lower holes added, not a completed axiom-free
proof; the net change in holes is +1 before any closure sharing is considered.

Every remaining sorry in the delivery is the complete body of one named public theorem:

- `AlgebraicGeometry.Scheme.strict_local_root_orbit_descent`, node
  `lem-sbc-strict-local-root-orbit-descent`: root torsor, base change, stabilizer descent, and
  localization of invariant rings.
- `AlgebraicGeometry.Scheme.strict_local_root_invariants`, node
  `lem-sbc-strict-local-root-invariants`: subgroup index and the invariant power-basis calculation.

The private puncture-isomorphism theorem and the polynomial-evaluation relation are fully
proved. No definitions contain sorry, and no axiom or forbidden declaration was introduced.

Edge cases checked mathematically: d=0 gives no stabilizers and the empty product/empty scheme;
n=1 has the trivial root group and degree-one charts; the full stabilizer has index 1 and its
fixed algebra is H; the trivial stabilizer has index n and fixes the whole root algebra.
The invariant-ring statement also allows h=0: the same monic basis calculation works for the
truncated polynomial ring. An invertible n is essential to the unit differences of residue roots.
The scheme restriction helper requires neither h nonzero nor a nonempty product, so it covers
the empty component case without an extra hypothesis.

## No longer needed

No existing import, node, or module was removed: the assigned node had no proof-dependency
imports and no proof dependencies. The existing public imports are all preserved.

The old plan's Eisenstein/intermediate-fraction-field/uniqueness-of-integral-closure calculation
is replaced by the invariant monic-basis calculation. No module implementing that unused route
was imported. This removes planned work rather than pruning an existing reachable module.

## Where the brief, the DAG or earlier work was wrong

The item's DAG advertised status split but had one non-elementary proof step and no proof
dependencies. There were therefore no supplied declaration signatures from which to realize
its plan directly. The two new nodes expose the geometric and algebraic parts separately, and
the original node now records the exact imports and explicit assembly that the Lean proof uses.

The blueprint-reference ancestry tool reports no ancestor because the earlier created.item
field names a Lean module, not a node. The existing item's explicit blueprint.from.node is
`sbc-thm-spreading-finite-etale-galois`, so both new records use that ancestor and extend the
existing via chain. Searches for root invariant, root orbit, 09EV, and 0EYG found no duplicate
blueprint node. The related tame-normalization node was read and is not this statement: it
requires a G-torsor and a supplied divisor and produces a normalization near its generic point.

The sources read were Stacks Tags 0EYG (strict local root extension and final intermediate-field
paragraphs) and 09EV (cyclic intermediate subextensions), at their official pages. The explicit
invariant-coefficient argument specializes the intermediate-root calculation and is marked as
written by an agent. LeanSearch returned Internal Server Error and is recorded as unavailable;
LeanFinder, Loogle, and Mathlib grep returned ingredients, including Kummer automorphisms over
fields, but no exact theorem over a strictly henselian local ring or the scheme descent result.

## New nodes

`lem-sbc-strict-local-root-orbit-descent` is in
`dag/nodes/sec-smooth-base-change/lem-sbc-strict-local-root-orbit-descent.json`, with module
`StrictLocalRootOrbitDescent`. It isolates descent to the explicitly constructed stabilizer
fixed subalgebras, including finite products, localization, and compatibility over H. It uses
the existing local root-regularity node in its proof plan and retains the trait-case unit route.

`lem-sbc-strict-local-root-invariants` is in
`dag/nodes/sec-smooth-base-change/lem-sbc-strict-local-root-invariants.json`, with module
`StrictLocalRootInvariants`. It isolates the subgroup-index and power-basis argument, independent
of every scheme, splitting, and cover. Its fixed ring and rotations are explicit constructions.
There are no signature changes, forced adaptations, or change records.


## Second reading by D4

1. Compared the delivered item with the repository using diff and checked the original
   theorem signature byte for byte: identical. Only its proof, proof explanation and a
   proof-only import changed, plus a proved private helper. The other two modules are new.
   No existing definition, target, public import or declaration visibility changed; no
   change record or forced adaptation is needed. Verdict: pass.

2. Compiled all three modules in import order with lcompile.py. In a scratch copy, printed
   the axioms of rootRotation, rootFixedAlgebra, both split theorems, the private restriction
   helper and root_split_strict_local_orbits. The two definitions and private helper use
   only propext, Classical.choice and Quot.sound. The combining theorem additionally uses
   sorryAx through the two declared split theorems. Exactly those two theorem bodies are
   sorry; there are no forbidden declarations or hollow definitions. Choosing equivalences
   inside the theorem proof merely eliminates their Nonempty conclusions; no public data
   definition chooses an arbitrary unproved witness. Verdict: pass as a decomposition,
   not an axiom-free proof of the original theorem.

3. Independently checked the invariant argument over a possibly nonreduced strictly
   henselian local ring: invertibility of n makes the residue roots simple, so Hensel
   lifting identifies the root group with the cyclic residue root group, and every
   nontrivial character difference used in coefficient comparison is a unit. This proves
   the claimed power-basis description even when h=0. Checked n=1, trivial and full
   stabilizers, and the empty-cover case d=0. The descent statement isolates the geometric
   quotient construction; it neither identifies fixed rings with root algebras nor merely
   renames the original conclusion. Both lower statements are true, strictly smaller
   parts and necessary in the assembly. Read the official Stacks pages
   https://stacks.math.columbia.edu/tag/0EYG and https://stacks.math.columbia.edu/tag/09EV.
   Repeated searches with different wording: LeanFinder for monic-quotient scaling
   invariants and finite covers classified by stabilizer fixed rings; Loogle for
   AdjoinRoot with Subalgebra; Mathlib and repository rg searches for fixed subalgebras,
   stabilizers and torsor descent. Found power-basis, Kummer field and abstract Galois
   category ingredients, but no theorem closing either split statement in a few minutes.
   Both complete natural-language proofs and matching nodes are present. Verdict: pass.

4. Read the assembly from its conclusion downward. The existing Spec.mapIso,
   Hom.preimageIso and isoOfEq operations directly implement restriction to D(h); the
   projection equation follows from algebra compatibility and Spec.map_comp. No shorter
   existing route was found. Old public imports support the preserved interface; new
   imports support fixed-algebra constructions and the dependent product algebra in the
   signatures. The item originally had no proof_deps, so No longer needed lists all
   removals (none). Read sk-prop-input-spreading and its realized record: the inherited
   empty realized arrays are unchanged. This below-unit decomposition preserves the
   trait-case standard tame-root-cover route. Verdict: pass.

5. Compared all three node lean.statement strings with the actual Lean signatures:
   exact. The only changed fields of the old node are proof, proof_deps and proof_origin.
   Its two dependencies are precisely the two split theorems used by the proof. The new
   nodes include source, full proof plans, searches, ancestry, creation metadata and Lean
   records. Found and repaired one mismatch: the descent node's regularity step names
   lem-sbc-root-algebra-regular-at-root, but its Lean module omitted the proof-dependency
   import. Added non-public import Sheaf.RingTheory.RootAlgebraRegularAtRoot, retaining
   that established local-regularity input without changing any statement. Verdict: pass
   after this repair.

Second reading changed only the missing proof-dependency import and this report. No further
holes were closed or added: the delivery still closes one original hole by decomposition
into two named lower holes, with no reachable module pruned.
