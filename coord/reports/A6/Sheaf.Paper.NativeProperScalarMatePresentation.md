## What changed

The statement of `native_proper_scalar_mate_presentation` is unchanged. Its proof now
constructs the ordinary module equivalences from a supplied coefficient-ring diagram,
uses a restriction/direct-image cube, and takes inverse mates. A private categorical
argument proves the arrow transport, and a fully proved auxiliary module supplies
the scalar-composition equation. In particular,
`mateEquiv_vcomp` transports the commuting cube, and `mateEquiv_hcomp` identifies the
condensed inverse mate with the specified integral-to-field-to-closure composite.
Neither geometric scalar mate is assumed invertible.

Two new modules isolate distinct parts of the existing plan:
`Sheaf.Paper.NativeScalarRingModel` contains the ordinary ring diagram, genuine
constructions of its module equivalences, and its existence theorem;
`Sheaf.Paper.NativeScalarRestrictionCube` contains the actual restriction squares and
their transport theorem, generic in the source and target coefficient systems.
The original public imports and all existing declaration signatures are preserved.
No existing module other than the assigned item is changed.

The auxiliary module `Sheaf.Paper.NativeScalarMateComposition` contains the fully proved
generic composition formula and canonical adjunction constructors. It adds no hole;
it isolates the categorical calculation after avoiding expensive unfolding of
concrete derived functors. Private projection equations and local reducibility of
canonical braiding and abelian-instance wrappers resolve the concrete conversions;
no public instance or shared definition is changed.

Validation: all four delivered Lean files compile under the normal per-file limit.
The final assigned-module compile completed cleanly in 51.5 seconds. Its theorem
signature matches the repository source verbatim. No diagnostic options or probe
modules remain in the packet.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.LocallyFiniteAdicCompactSupport.native_proper_scalar_mate_presentation`
by a complete combination proof from two strictly smaller statements. The item's
module has zero holes. This is a decomposition, not a claim of a complete axiom-free
proof: one hole closed and two added, for a packet net of minus one.

The two new holes are exactly:

- `WeilConjectures.LocallyFiniteAdicCompactSupport.exists_nativeScalarRingModel`,
  node `lem-sf-native-scalar-ring-model`. Its conclusion concerns only ordinary
  ring-sheaf isomorphisms, the scalar inclusion, and precomposition naturality.
- `WeilConjectures.LocallyFiniteAdicCompactSupport.nativeScalarRestrictionCube`,
  node `lem-sf-native-scalar-restriction-cube`. Given an ordinary ring diagram for
  arbitrary coefficient systems, it transports restriction and direct image.
  No scalar-extension functor or scalar mate appears in its conclusion.

Every definition is a construction with no hole. The ordinary equivalences are
constructed from ring-isomorphism restriction and the proved internal/section
module equivalence. No definition chooses an arbitrary unproved existence witness.
The two new theorem docstrings give their sources, complete proof plans, and
checks for identities, empty schemes, and arbitrary unbounded complexes.

## No longer needed

No original public import is removed. The direct proof dependency
`lem-sfb-pasted-mates-counit-normalization`
(`Sheaf.CategoryTheory.PastedMatesCounitNormalization`) is replaced by the explicit
proved calculations with Mathlib's `mateEquiv_hcomp`, `mateEquiv_vcomp`, and
whiskering formulas. No assertion is made that that module is globally unreachable;
it is not withdrawn.

The five ordinary coefficient-realization dependencies of the old proof remain
needed under `lem-sf-native-scalar-ring-model`. Internal module-operation transport
also remains needed for the new restriction cube. No unit statement or unit proof
step is bypassed. No upstream declaration is removed or weakened.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The ring-model plan explicitly cites the existing
`coefficientPresentations_exists` to obtain a presentation before applying `ha`.
The old plan combined the ordinary ring diagram,
derived restriction compatibility, and mate pasting into one hole. The delivered
proof establishes the categorical pasting and arrow transport while isolating the
two genuinely different remaining tasks. Existing finite constant-coefficient
realization cubes were inspected: their finiteness and constant-ring hypotheses
do not apply to these condensed coefficient rings.

An auxiliary DAG audit found a pre-existing two-node cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`. Neither node is changed in this
packet. None of the three new nodes has a dependency path back to the assigned item.

## New nodes

`lem-sf-native-scalar-ring-model` is the ordinary coefficient-identification part
of steps 1–3 of the assigned node. It records the completed/native ring isomorphisms,
the actual composite scalar inclusion, and the inverse-image-adjunct naturality.
Its Lean attachment includes the explicit module-equivalence constructions.

`lem-sf-native-scalar-restriction-cube` is the restriction/direct-image part of
steps 3–4, generalized to any supplied ordinary coefficient-ring diagram. Its
remaining proof is the identity-on-sections ordinary cube followed by exact
localization and canonical right-derived unit normalization. Both new nodes have
three kinds of Mathlib search, their inherited blueprint place, and full proofs
in words. The assigned node's proof and dependency records follow the Lean proof.

`lem-sf-native-scalar-derived-mate-composition`
(`Sheaf.Paper.NativeScalarMateComposition`) proves the canonical inverse-mate pasting
formula for any two flat condensed coefficient maps, using Mathlib `mateEquiv_hcomp`.
This third new node is fully proved and introduces no `sorry`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeProperScalarMatePresentation": "abe19421f0dbbd720289dab5fdcc82a672424c4b", "Sheaf.Paper.NativeScalarMateComposition": "f13aac1636f9f20ae8de4196831c3951d43c875c", "Sheaf.Paper.NativeScalarRestrictionCube": "a50c3abb31055a87a68dfe71096592026c206fec", "Sheaf.Paper.NativeScalarRingModel": "905692d974504f195819ff5454adcedb7018fd88"}, "results": {"Sheaf.Paper.NativeProperScalarMateBoundedBelowRestricted": {"hash": "926bfae07ee305a9bececeaee21fa1a6ef01af68", "status": "OK"}}, "seconds": 79, "time": "2026-10-28T13:28:47+0800", "transitive": 0, "version": 1}
```

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
