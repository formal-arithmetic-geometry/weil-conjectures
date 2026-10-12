## What changed

`ThickeningSystemPushforwardLifting.lean` now constructs coherent preimages of each
term through the existing closed-immersion coherent equivalence, using its inverse,
counit, and pushforward comparison. Annihilation by the module power is converted to
annihilation by the ideal-sheaf kernel using the existing identity-immersion case of
`Scheme.closedImmersion_idealPower_annihilation`. The proof lifts each conjugated
transition through fully faithful closed pushforward and takes its adjoint.

The new module `ThickeningSystemPushforwardTermwiseLift.lean` now states only
`AlgebraicGeometry.thickeningSystemPushforward_adjacent_isIso`: for one fixed adjacent
pair, with coherent terms, identifications, and a transition lift supplied, the adjoint
of that lift is invertible. This replaces the first worker's near-restatement asserting
the existence of an entire compatible coherent system. Its proof is still open.
The target uses this invertibility to construct the comparison isomorphisms and the
coherent thickening system, and verifies the adjacent pushforward equations explicitly.

`ThickeningSystemPushforwardAssembly.lean` now proves assembly with
`NatTrans.ofOpSequence`, verifies naturality of inverse components by cancellation,
and checks both inverse identities componentwise. All original public imports and
the existing target signature remain unchanged. New imports used only for proofs
are plain imports. No definition or existing statement changed; no change record is needed.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.thickeningSystemPushforward_lifting`
(node `lem-weil-pbc-thickening-system-pushforward-lifting`) by a genuine reduction:
construct terms and adjacent maps from existing library declarations, reduce only the
single adjacent invertibility step, then apply the proved categorical assembly.

The added declaration `AlgebraicGeometry.thickeningSystemPushforward_assemble`
(node `lem-weil-pbc-thickening-system-pushforward-lifting-assembly`) is proved without
`sorryAx`. The only added hole is
`AlgebraicGeometry.thickeningSystemPushforward_adjacent_isIso`
(node `lem-weil-pbc-thickening-system-pushforward-lifting-termwise`), whose whole proof
is `by sorry`, with source and complete mathematical proof in its docstring.

Relative to the repository: one original hole closed, one smaller hole added; net zero.
This is a decomposition, not a completed proof of the geometric lifting theorem.
Relative to the first worker's unpublished sandbox: closed the assembly hole and
replaced the full-system existence hole by a single adjacent invertibility obligation.
The old unpublished `thickeningSystemPushforward_termwise_lift` is removed.

All three modules compile without warnings. Scratch copies with `#print axioms` show
only `propext`, `Classical.choice`, and `Quot.sound` for assembly, and those axioms plus
`sorryAx` for the target and the adjacent obligation. No axioms, unsafe declarations,
opaque declarations, external implementations, or holes in definitions are introduced.

## No longer needed

Removed from the target's direct imports:
`Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`,
`Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`.
These proof dependencies now belong to the single adjacent obligation's module.
Removed the redundant direct imports
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`; the former is reached through
the existing annihilation lemma, while the Noetherian theorem is exposed by the
coherent-equivalence module. Removed redundant `public import CoherentThickeningSystem`
from both new modules, since `ThickeningSystemPushforward` already exposes it.

Of the old proof dependencies, `def-pc-module-pullback` is now a statement dependency
and is not needed as an independent proof step; the explicit adjunctions are inputs.
The unit-quotient and ideal-powers nodes are now dependencies of the adjacent obligation.
The ideal-times-affine-sections node is now reached through the existing inverse-image
annihilation lemma. The coherent-equivalence, fully-faithful, pushforward-functor and
Noetherian nodes are used directly. No old dependency module is removed from the import
closure, so no whole module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's termwise theorem already supplied a complete compatible coherent
system and differed from the target only by categorical packaging. That was too close
to restating the item and did not demonstrate the required geometric reduction.
The repaired proof carries out coherent preimage selection and full-faithful transition
lifting, and leaves only quotient invertibility for a single adjacent pair open.

The first worker also left categorical assembly open even though Mathlib's sequence
natural-transformation API closes it directly. The new assembly proof removes that hole.
The original target statement and the unit's realized route do not require correction.

## New nodes

`lem-weil-pbc-thickening-system-pushforward-lifting-termwise`, in
`lean/Sheaf/AlgebraicGeometry/ThickeningSystemPushforwardTermwiseLift.lean`, records
only invertibility of one lifted adjacent comparison. Its theorem receives both coherent
terms and the adjacent lift as inputs, and asserts no existence of a system.

`lem-weil-pbc-thickening-system-pushforward-lifting-assembly`, in
`lean/Sheaf/AlgebraicGeometry/ThickeningSystemPushforwardAssembly.lean`, records the
proved categorical assembly from given adjacent-compatible termwise isomorphisms.
Its status and proof record now reflect the proof as written.

## Second reading by U1

1. Compared each delivered module against the repository and checked the target's
signature byte for byte. The existing target signature and its public imports are
unchanged. The two new declarations have matching node records. No repository file
or module held by another group was edited, and no definition or existing declaration
was altered.

2. Compiled all three files through `lcompile.py --all`, without errors or warnings;
searched for forbidden constructs and all holes. The only hole is the named single
adjacent theorem above. Scratch `#print axioms` checks give exactly the allowed sets
recorded under `Proved and sorry left`. The coherent-system data are constructed from
terms and the explicit adjunction hom equivalence; `asIso` uses only the invertibility
proof. No definition chooses an arbitrary witness of an unproved existence theorem.
The equivalence inverse and counit determine preimages up to the isomorphism used here;
full faithfulness determines each lifted morphism uniquely.

3. Checked the adjacent statement mathematically, including n = 0 (the first positive
power), zero modules, empty schemes, and J = 0 or the unit ideal. It reduces locally to
M tensor A/J^(n+1) being the corresponding quotient and the induced adic transition
being invertible. Arbitrary supplied adjunctions change the comparison by an isomorphism,
so do not affect invertibility. The new statement is strictly a part of the argument:
terms and the lifted map are inputs, and its conclusion is only invertibility at one
level. Its docstring explains the quotient comparison, adjunction identity, and reflection
of isomorphisms. Searched with LeanFinder (closed immersion / pullback / quotient / adic
transition), Loogle (`NatTrans.ofOpSequence`), msearch grep (adjunction / IsIso), and local
rg on closed-immersion and upstream algebraic geometry modules. No duplicate adjacent
statement was found; the sequence API directly supplies assembly.
The source checks used [Stacks 087T](https://stacks.math.columbia.edu/tag/087T),
[088F](https://stacks.math.columbia.edu/tag/088F), and
[0880](https://stacks.math.columbia.edu/tag/0880).

4. Read `dag/units/sk-thm-p1.json` including `realized`; this lifting node is below the
unit's realized nodes and no unit step is bypassed. The target keeps the coherent
closed-immersion and fully-faithful route, constructs its own system, then uses the
proved assembly step. The removed direct imports and every old proof dependency are
accounted for under `No longer needed`; no closure pruning is claimed.

5. Checked the node statements, verbatim normalized Lean signatures, proof steps,
proof-dependency unions, source, origin, created/blueprint/lean fields, and searches.
The existing target node records the actual preimage, transition-lift, single-adjacent,
and assembly steps. The new adjacent node records only its supplied-data invertibility
obligation and planned quotient argument; assembly is marked proved and records its
sequence construction and inverse identities.

Second reading changed: proved assembly; replaced the near-restatement termwise hole
with the single adjacent invertibility hole; implemented the real termwise construction
and full-faithful transition reduction in the target; repaired docstring, nodes, searches,
imports, and report. No target or existing declaration signature changed.
