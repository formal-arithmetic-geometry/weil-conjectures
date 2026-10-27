## What changed

Repaired and proved `CategoryTheory.ringedNegativeKoszulSummand_D₂_term` in
`Sheaf.CategoryTheory.SignedKoszulSummandTermTransport`. Its left-hand rank-one scalar
now contains the earlier-index sign and the power `m + 1`, matching its unchanged
right-hand coefficient and the actual ordered negative Koszul factors.

The proof identifies rank-one multiplication with the recorded Hom scalar action,
proves that tensorLeft preserves that action using the naturality of the sheafification
unit and tensor comparison, transports the two integer degrees by equality induction,
and handles the total-tensor sign by integer parity. All helpers are private and proved.
There are no new public declarations or proof imports. Local instances and local
irreducibility keep the recursive Koszul definitions out of generic scalar calculations.

The same omitted factors occurred in the existing, still-unproved
`CategoryTheory.ringedNegativeKoszulBasis_d_succ` in the unclaimed module
`Sheaf.CategoryTheory.SignedKoszulSummandDifferential`; its scalar is corrected in this
packet. The signature and proof of `ringedNegativeKoszulSummand_D₂_succ` are preserved:
its existing assembly now combines the two correct formulas. Both changed declarations
have matching node records and statement-change citer audits.

Validation: `lcompile.py --all` compiled the item (42.6 s), the adapted parent (27.4 s),
and the unchanged direct importer `SignedKoszulTensorCoordinates` (35.2 s) against this
packet. The requested explanation of the local heartbeat setting has been added; the
60-second wall-time limit is unchanged. The unchanged importer copy was removed.

Change record: `coord/changes/P1-signed-koszul-summand-scalar.md`.

## Proved and sorry left

The item has one original hole and zero remaining holes. The corrected
`CategoryTheory.ringedNegativeKoszulSummand_D₂_term` is proved, with no split-off holes.
The original false equation is repaired, not claimed as a theorem of the old signature.

The delivery preserves the one existing hole
`CategoryTheory.ringedNegativeKoszulBasis_d_succ`
(node `lem-cbc-signed-koszul-basis-differential`) in the adapted parent module, now with
its mathematically correct signed-power statement. This is neither a new hole nor a
reduction of the item to that hole: the item's proof never imports or applies it.
Across the two delivered modules, textual holes change from two to one, with none added.

## No longer needed

None. No import, module, or dependency node is pruned, and no new node is introduced.
The proof uses only the existing signed model and the generic tensor, scalar-action,
sheafification, and equality-transport infrastructure it already imports. The unit route
is preserved. No further decomposition of the transport obligation is needed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old equations, repaired here): the old term-transport left side
used multiplication by `a i`, while its right side used the signed power `a i ^ (m + 1)`.
The old basis-differential right side also used the unsigned first power. On the site
with one object and only its identity, with only the maximal sieve covering, take
`O = A = Z`, the identity coefficient map, one factor `a_0 = 2`, `m = 1`, `I = {0}`,
`q = -1`, and `K = Z[0]`. The old term equation compares multiplication by 2 with
multiplication by 4; the old basis equation incorrectly gives 2 for a differential of 4.
With two selected indices, erasing the second additionally requires a minus sign.

The repaired formulas follow the actual definitions: each negative factor has
differential `ringedKoszulScalar a_i ^ (m + 1)`, and tensor ordering supplies one minus
sign per preceding selected factor (Stacks 0A0E and the existing node proof). No
hypothesis, definition, target, or full summand-differential statement is changed.
The only DAG citer of either repaired node is
`lem-cbc-signed-koszul-summand-differential`, and its use holds after the coordinated
repair. The only external Lean caller is in the adapted parent module. The direct
importer `Sheaf.CategoryTheory.SignedKoszulTensorCoordinates` uses its unchanged full
differential theorem. Negative coefficient degrees are handled by integer parity;
zero scalars, zero rings, and empty sites are not excluded. The empty-subset basis
formula still has an empty sum, and the term theorem retains its original membership
hypothesis.

## Forced adaptations

### Sheaf.CategoryTheory.SignedKoszulSummandDifferential
FORCED (held by M1). The tool's note "NOT FORCED" was wrong: compiled against the delivered item, the
original module fails at line 180 (`exact ringedNegativeKoszulSummand_D₂_term O ρ r a m K q I i hi hdeg hsrc`
in `ringedNegativeKoszulSummand_D₂_succ`): `(deterministic) timeout at whnf` (with a second report at line 70),
because after `rw [ringedNegativeKoszulBasis_d_succ]` the old basis lemma leaves the scalar `ρ (a i)` while
the repaired term theorem has `ρ ((-1) ^ #{j ∈ I | j < i} * a i ^ (m + 1))`. The only changed lines are the
scalar of the still-`sorry` statement `ringedNegativeKoszulBasis_d_succ` (old statement false, see above);
no proof, import or other signature of the module changed. (Correction by the reviewer.)

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
