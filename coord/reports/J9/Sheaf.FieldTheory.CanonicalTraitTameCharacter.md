## What changed

Proved `IsDiscreteValuationRing.exists_canonical_tame_character` with its original
signature and public imports. Five new modules contain proved parts of the argument:
`FiniteCanonicalKummerCharacter`, `CanonicalTameCharacterData`,
`FiniteRadicalRestriction`, `TameRadicalKernel`, and `CanonicalTameCharacterStructure`.
All are under `Sheaf.FieldTheory`. The radical-kernel definition is the concrete
intersection of stabilizers; no object is chosen from an unproved existence theorem.

The construction uses Hensel roots of units, Eisenstein irreducibility and conjugates
for the finite canonical characters. Compactness of the absolute Galois group proves
surjectivity onto the root limit. The finite kernel argument uses the shorter direct
calculation in the strictly henselian normalization: if π=u w^(qn), extract b^n=u,
so β=b w^q is a tame radical. Radical-fixing automorphisms fix β. Their uniformizer
ratio has residue one; the finite-order telescoping argument forces the image to be
a p-group, or trivial in characteristic zero. The Krull neighborhood basis then
handles every finite continuous quotient. Coordinate fibers prove density and index.

The final proof imports are private. No existing consumer needs adaptation. All six
modules passed the remote import-order compile in `scratchpad/all-proved.log`, without
warnings, in 2.5--9.1 seconds per changed module. The final source-path compile in `scratchpad/all-source-fixed.log` passed all six
modules without warnings, in 2.2--8.2 seconds. The initial dry run caught an obsolete
Sheaf path for the strict-local roots theorem; both imports now point to its current
WeilConjectures source module. No delivery was pushed by that failed dry run.

## Proved and sorry left

Closed the one original hole, by declaration name:
`IsDiscreteValuationRing.exists_canonical_tame_character`.

Added zero holes. The following new theorems are all proved:
`IsDiscreteValuationRing.finite_canonical_kummer_character`,
`IsDiscreteValuationRing.canonical_tame_character_data`,
`IsDiscreteValuationRing.finite_radical_restriction_p_group`,
`IsDiscreteValuationRing.tame_radical_kernel_pro_p`, and
`IsDiscreteValuationRing.canonical_tame_character_structure`.
There is no `sorry` in any delivered Lean file, including the new definition
`IsDiscreteValuationRing.tameRadicalKernel`. Thus this closes 1 of 1 holes,
adds 0, and splits off 0 unfinished statements. This is a proof from existing named
library inputs, including the still-unproved connected integral henselian permanence
lemma; it is not a claim that all transitive library inputs have been proved.

## No longer needed

Removed these ten original proof imports from the item:

- `WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra`
- `WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity`
- `Sheaf.FieldTheory.FiniteDVRTameInertia`
- `Sheaf.FieldTheory.FiniteTameCharacterTower`
- `Sheaf.GroupTheory.InfiniteTameInverseLimit`
- `Sheaf.NumberTheory.DvrGaloisDegreeData`
- `Sheaf.RingTheory.DvrCharZeroTangentKernel`
- `WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`
- `WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct`
- `WeilConjectures.RingTheory.HenselianLocalRootLifting`

The strict-local root-count result remains used by the finite helpers, and the
algebraically-closed primitive-root result remains used by the structure helper.
The henselian product result remains a transitive input of connected integral
henselian permanence. These are not claimed pruned from the targets' import closure.

The direct normalization calculation removes the planned uses of
`lem-exc-dvr-galois-degree-data`, `lem-exc-finite-dvr-tame-inertia`,
`lem-exc-finite-tame-character-tower`, `lem-exc-infinite-tame-inverse-limit`, and
`lem-per-dvr-char-zero-tangent-kernel`, hence their modules above are unnecessary
for this proof route. No finite tower of normalized characters, cofinality comparison,
or separate characteristic-zero tangent theorem is required. The finite-order
congruence calculation is proved locally in `FiniteRadicalRestriction`.

The remaining old direct proof-dependency nodes are replaced as follows:
`lem-exc-kummer-binomial-splitting-field` and
`lem-sbc-dvr-uniformizer-root-algebra` are bypassed by Eisenstein/Gauss and the
normal-extension conjugate lemma; `lem-weil-pbc-normal-subextension-automorphism-extends`
is bypassed by compact directed intersections of finite-coordinate fibers;
`lem-pc-crt-ideal-quotient-product` is bypassed by finite inverse-system compactness,
which needs no surjectivity of primitive-root transition maps.
`lem-galois-inverse-limit-surjective`, `lem-exc-galois-krull-finite-limit`, and
`lem-sc-primitive-root` have no direct wrapper import: the corresponding Mathlib
finite-section, Krull-basis, and primitive-root APIs are used directly.
`lem-pc-kbar-pure-insep` has no separate import: Mathlib's purely inseparable
extension and uniqueness-of-embeddings instances suffice. The normalization finiteness,
normality and PID/Dedekind facts represented by
`lem-weil-pbc-integral-closure-finite-extension-normal`,
`lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`, and
`lem-weil-pbc-pid-noetherian-normal` use the existing Mathlib APIs directly.
`def-kun-separably-closed` and `def-sc-discrete-valuation-ring` remain mathematical
notions in the new helpers; their actual definitions are unchanged.
`lem-weil-pbc-henselian-local-root-lifting` has no direct import because
`HenselianLocalRing.TFAE` supplies the simple-root formulation.

The parent node now has exactly the construction and structure helper nodes as its
proof dependencies. All nine obsolete top-level `tool_uses` approvals were withdrawn:
`lem-weil-pbc-henselian-local-root-lifting`, `lem-sbc-strict-local-roots-of-unity`,
`lem-sbc-dvr-uniformizer-root-algebra`,
`lem-weil-pbc-finite-over-henselian-local-product`, `lem-exc-dvr-galois-degree-data`,
`lem-exc-finite-dvr-tame-inertia`, `lem-exc-finite-tame-character-tower`,
`lem-exc-infinite-tame-inverse-limit`, and
`lem-weil-pbc-normal-subextension-automorphism-extends`. Actual uses are now recorded
on the precise helper nodes; this withdrawal makes no new maintainer approval.

## Where the brief, the DAG or earlier work was wrong

The earlier interrupted sandbox had a two-hole decomposition and incomplete node
metadata. Both have been replaced: all helper theorems are proved and their node
statements and proof steps now describe the actual Lean argument. The brief and
original statement are sound. The planned finite tower and characteristic-zero
branches can be shortened by extracting the tame unit root in each normalization.
The blueprint unit's route and the item's mathematical statement are preserved.

The reference clock was reset by the dispatcher across resumptions; no clock file
was edited. This delivery introduces no unfinished split, so no elapsed-time
exception is needed. No delivery push preceded the final checks of this packet.

## New nodes

`lem-per-finite-canonical-kummer-character` records the proved finite continuous,
surjective character, with the formula for every uniformizer and every root.
Its edge case n=1 is included in the proof.

`lem-per-finite-radical-restriction` records the proved finite p-group restriction
image, including the trivial image in characteristic zero. It uses the existing
connected integral henselian permanence theorem and the strict-local roots theorem;
the residue-field, Hensel and telescoping glue is proved here.

`def-per-tame-radical-kernel` records the actual intersection of stabilizers.
`lem-per-tame-radical-kernel` records the proved finite continuous quotient statement
and triviality for p=1, with the quotient universe independent of the fields.

`lem-per-trait-tame-character-data` records the proved construction, compatible
radicals, surjectivity and simultaneous formula. It introduces no choice-based definition.

`lem-per-trait-tame-character-structure` records the proved kernel identification,
primitive-family existence, density and exact indices. It treats the order-one
coordinate and the trivial finite quotient without exceptions.

Every new node has its Lean statement verbatim, source, full proof steps, actual
proof dependencies, blueprint ancestry and logged Mathlib searches. No change record
is required: no existing statement, definition or public import was changed.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
