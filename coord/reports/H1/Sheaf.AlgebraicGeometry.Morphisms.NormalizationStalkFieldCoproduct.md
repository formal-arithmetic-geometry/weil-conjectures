## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.normalization_stalk_field_coproduct`
in `Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkFieldCoproduct`.
Its signature, visibility, existing docstring, and imports are unchanged.

The private, proved helpers implement the existing node's three-step plan:
transport relative normalization through isomorphisms by its universal property;
apply the existing stalk base-change theorem with the identity base morphism;
identify affine normalization using its top affine chart; prove coordinatewise
integrality using the product of monic annihilating polynomials; and apply Spec
and the finite coproduct comparison. The final composite is checked over the
stalk spectrum, giving the required structural-map equation.

Mathlib's finite `sigmaSpec` isomorphism instance requires its index universe to
match the ring universe. A private helper reindexes `Fin n` through `ULift` and
transports the product ring by `RingEquiv.piCongrLeft`. This also covers `n = 0`.
The finite-product integrality argument works for commutative rings without any
nontriviality or domain assumption.

Searches used LeanFinder, Loogle, and local source searches. They found the
normalization universal property and binary coproduct comparison, but no direct
version of this theorem. The existing stalk base-change theorem is used, not
restated or reproved.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.normalization_stalk_field_coproduct`
(node `lem-sbc-normalization-stalk-field-coproduct`).

One of one original holes closed. No holes added or split off. No `sorry`
remains in any declaration of the delivered module. Every private helper has a
complete proof or a real explicit construction.

## No longer needed

None. Both public Mathlib imports are used by the unchanged statement.
The proof import `Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange`
and node `lem-sbc-normalization-stalk-base-change` are used. No planned node or
module was bypassed; the existing DAG proof and proof dependencies still match
the implemented argument.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The node already anticipates ULift
reindexing, which is needed for Mathlib's finite `sigmaSpec` isomorphism instance.
The unit's route and all target statements are unchanged.

## Second reading by H1

1. Compared the sole delivered Lean module with the repository version using
   `diff -u`. The existing theorem's signature, visibility, docstring and imports
   are byte-for-byte unchanged. The only changes are eight private helpers and
   the replacement proof. No definitions used by an existing public statement
   changed, no change record is needed, and no other module is delivered. Pass.
2. Compiled the delivered module through `lcompile.py`: exit 0, no errors or
   warnings (7.2 seconds). Compiled a scratch copy printing the axioms of the
   target and all eight helpers: every declaration uses only `propext`,
   `Classical.choice`, and `Quot.sound`; none uses `sorryAx`. There is no remaining
   `sorry`, forbidden declaration, or hollow definition. The two private ring
   equivalences construct their data explicitly, rather than selecting arbitrary
   witnesses of an unproved existence theorem. Pass.
3. No statements were split off and no holes were added. Read the private
   coordinatewise integrality proof: projections preserve integrality; the finite
   product of monic annihilating polynomials vanishes coordinatewise. For the
   empty index type this is the constant polynomial 1 in the zero tuple ring,
   so no nontriviality hypothesis is hidden. The algebra equivalence and ring
   transport have explicit inverse maps. The spectrum coproduct helper lifts
   `Fin n` to `ULift` and transports back, including `n = 0`. Pass.
4. Read Mathlib's normalization universal property, affine chart construction,
   and `sigmaSpec` finite-isomorphism instance, and searched Mathlib's integral
   closure sources, `lean/Sheaf`, and upstream `WeilConjectures` for product
   integrality and normalization comparison declarations. No public direct
   replacement or shorter complete route was found. An analogous isomorphism
   helper in `StalkNormalizationGenericComparison` is private and only treats a
   fixed base; importing that module would not expose it. The delivered proof
   uses the existing `Hom.isIso_normalizationPullback_stalk` with identity base
   morphism, not a copy of that theorem. Both public imports provide notions in
   the unchanged statement; the sole proof import supplies that base-change
   theorem. No old proof dependency is unused, so `No longer needed: None` is
   complete. Read `dag/units/sk-prop-input-spreading.json`: its statement and
   steps (in particular the trait normalization step) are retained; its existing
   `realized` lists are empty and this delivery neither alters them nor bypasses
   a realized node. Pass.
5. Read `lem-sbc-normalization-stalk-field-coproduct.json` and the imported
   base-change declaration. Its first step is implemented by the identity
   pullback comparisons and `exists_stalk_normalization_iso`; its second by
   normalization transport, the top affine chart and `integralClosurePiEquiv`;
   its third by the Spec ring equivalence and `sigmaSpec`, with the final
   structure-map equation proved by `hef`, `hep`, `hnA`, `hn`, and `hb`.
   The affine chart is the construction underlying `normalizationObjIso`.
   Thus the existing proof plan, sole proof dependency and source-based proof
   origin agree with the argument as written; there are no new nodes. Pass.

Second reading changed only this report: added the independent review and the
local compilation/axiom evidence. No Lean repair was necessary. One original
hole closed, zero added, zero split off, and no imports or modules pruned.
