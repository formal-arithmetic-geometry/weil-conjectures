## What changed

`Sheaf.Paper.NativeWeilTensorConstraintLifts` keeps all existing public signatures,
definitions and public imports. Its proof compares tensor slice adjunctions with a
normalized action-site model using `Adjunction.leftAdjointUniq`. Counit naturality
makes these slice comparisons natural in the second argument. The unit identity
and ordinary uncurrying identify the resulting forgotten comparison with the
caller's prescribed `τ`. Individual constraints are conjugated through this
bifunctor isomorphism, and strong monoidal functor composition supplies both
inducing-data records and their normalization equations.

Added `Sheaf.Paper.NativeHomRepresentativeUniqueness`: for the SAME fixed native
and ordinary representative data, projection equations identify the complex
comparison maps, their localized squares identify the derived Hom comparisons,
and K-injective replacement with naturality gives equality on every pair.
This does not assert uniqueness across different choices of representative data.

Added `Sheaf.Paper.NativeWeilRingedTensorModel` for the geometric construction in
steps 1 and 3 of the original plan. It has no supplied `T`, `a`, `ha`, `τ`, `hτ`,
`η` or `hη`: it produces an action-site closed model and its own normalized
comparisons before the formal comparison with arbitrary supplied tensor data.
The remaining statement includes the required unit, symmetry and uncurrying
normalizations; none is silently assumed in the formal proof.

The complete item proof compiled successfully on the project server in 10.9 s,
with no warnings. The fixed-representative uniqueness proof also compiled in an
earlier single-file check. Delivery preflight checks all three modules together.
A textual comparison confirms that the existing public structures, operations,
and target theorem signature remain identical to the shared source.

## Proved and sorry left

Original holes: one, `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_constraint_lifts`.
Its proof is replaced by a complete reduction to the geometric model theorem.
Original holes removed from the item: one (by decomposition).
New holes: one, `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_ringed_tensor_model`
(node `lem-sf-native-weil-ringed-tensor-model`). Thus this delivery is a
decomposition, with net zero holes closed, rather than a claim of a complete
geometric proof. No sorry remains in the item itself.

`AlgebraicGeometry.ProEtaleWeilSheaf.native_hom_representative_unique`
(node `lem-sf-native-hom-representative-uniqueness`) is proved without new holes.
All private helpers are proved. No definitions select data from the unproved
existence theorem; it is eliminated only inside a theorem proof.

## No longer needed

None. No existing public import is removed and no existing module is withdrawn.
The original action-resolution, ringed closed-monoidal, and ringed forgetful
descent dependencies remain necessary for the geometric model node. Their
role is now explicitly separated from the proved adjoint-uniqueness and raw
constraint-conjugation argument. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement correction is proposed. The original plan's general ringed-site
inputs do not directly state the specialized native closed model and its
normalization against the fixed representative data. That geometric bridge
remains explicit in the new node. The comparison of different tensor left
adjoints and the assembly of the faithful ULift model are formal steps proved
here, rather than another restatement of the original constraint-lifting goal.

## New nodes

`lem-sf-native-weil-ringed-tensor-model`: the native action-site specialization
of the original geometric steps 1 and 3, before supplying an arbitrary tensor.
It retains their three original proof dependencies and a complete proof in words.

`lem-sf-native-hom-representative-uniqueness`: the internal-Hom-only uniqueness
step for fixed representative models, proved using projections, localization
squares, K-injective representatives and naturality.

No change record is needed: no existing public interface was changed.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
