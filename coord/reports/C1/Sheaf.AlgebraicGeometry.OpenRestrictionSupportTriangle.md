## What changed

Proved `AlgebraicGeometry.openRestriction_support_triangle` with its original signature.
The proof derives the transported restriction/direct-image adjunction, uses the existing
quasi-coherent triangulated closure theorem to complete the unit, proves the restricted cone
is zero from the adjunction triangle identity, transports this to stalk vanishing, and uses
bounded-below/unbounded right-derived compatibility for the conditional boundedness clause.
Updated the theorem docstring and its node's proof route to describe the actual Lean argument.
All added imports are proof-only. No definitions, statements, public imports, or other modules
changed. Local single-file compilation succeeds without warnings.

The empty open gives a vacuous stalk clause; restriction to the entire scheme has invertible
unit and zero cone. The zero object and unbounded K are allowed throughout. Boundedness is
used only for the final implication. No arbitrary data is chosen from an unproved existence
statement: the cone is obtained from the proved triangulated-category completion theorem.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.openRestriction_support_triangle`
(node `lem-sc-open-restriction-support-triangle`). Proved 1 of 1 sorries in the item.
No sorries remain in the delivered module; no holes were added or split off.
Existing dependencies may still depend on sorries; this is a proof from the library's
stated results, not a claim that its entire transitive axiom closure is finished.

## No longer needed

Removed these seven direct proof imports:

- `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`
- `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension`
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`

The support proof no longer needs `lem-sc-derived-k-injective-restrict-open`,
`lem-sc-derived-open-restriction-adjunction-exact`, or
`lem-pc-restrict-derived-direct-image-open`: direct image, rather than restriction,
preserves K-injectives here, by the already-proved exact-left-adjoint criterion.
It also does not need `lem-sc-bounded-below-injective-resolution-existence` or
`lem-weil-pbc-bounded-below-injectives-kinjective` directly: the existing bounded-below
right-derived compatibility supplies the required boundedness.

The explicit kernel/cokernel/extension dependencies
`lem-weil-pbc-quasi-coherent-module-kernel`,
`lem-weil-pbc-quasi-coherent-module-cokernel-image`, and
`lem-pc-quasi-coherent-extension` are replaced in this node by the already-proved
`lem-pc-supported-qcoh-triangulated` specialized to the whole scheme.
They can still occur transitively through the retained direct-image preservation theorem
or the triangulated closure theorem; their removed direct imports do not claim those modules
have disappeared from every target's import closure. The ringed-space direct-image module
also remains in the public statement dependency through `DerivedOpenRestrictionMaps`.
Actual globally unreachable modules are determined by the maintainer's import-closure ledger.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The original DAG plan over-specified the
representative-level construction: existing derived-adjunction, full-faithfulness,
triangulated-property, homology-comparison, and stalk-isomorphism APIs suffice.
The original Step 2's abstract open-restriction/direct-image isomorphism alone does not
identify the restricted unit; this proof instead establishes invertibility of that specific
map using the counit and the left triangle identity. The unit's realized steps are empty,
so no fixed blueprint unit step is bypassed.

`src-right-derived-functor-plus-compatibility` is used as a tool from another unit because
it is the already-proved general comparison of the two derived functors used here.
Its bounded-below certificate and triangulated closure yield precisely the existential
bound requested; no stronger numerical bound is asserted.

Read the existing Lean signatures and the Stacks proof of the support triangle:
[Tag 0E4G](https://stacks.math.columbia.edu/tag/0E4G), proof of Lemma 48.4.3,
and [Tag 08D5](https://stacks.math.columbia.edu/tag/08D5).

## Second reading by C1

1. PASS — compared the sole delivered module with the repository using `diff` and
   checked the theorem signature byte for byte. Its hypotheses, conclusion, visibility,
   definitions, and public imports are unchanged. No change record or adaptation is needed.
2. PASS — compiled the module through `lcompile.py` without errors or warnings. There
   is no `sorry`, axiom, unsafe/opaque declaration, implementation override, or external
   code in the delivered module. A scratch-copy `#print axioms
   AlgebraicGeometry.openRestriction_support_triangle` reports exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`; the last comes from existing imported
   results, not a new hole. The proof constructs its adjunction from existing APIs and
   eliminates triangle-completion existence inside a theorem; it adds no witness-based
   definition or arbitrary data from an unproved existence statement.
3. PASS — no statement was split off and no new node was added. Independently checked
   the empty open, whole open, zero object, and unbounded-object cases. The conditional
   boundedness argument uses only an existing lower-bound certificate and does not assert
   that restriction preserves injectivity. No statement is weakened or merely renamed.
4. PASS — read the derived-adjunction, fully-faithful, plus-compatibility, restriction
   quasi-coherence, and supported-triangulated APIs. Searched Mathlib for zero third
   vertices, triangulated closure, and invertible counits, and searched both library roots
   for support triangles and restriction comparisons. The existing
   `derived_open_unit_restriction_isIso` is an over-site result with extra transport and
   extension-by-zero machinery; it gives no shorter route than the two adjunction lines
   here. Each added import supplies a used declaration or instance. Removal probes for
   Grp.Zero, Sheaves.Abelian, and GrothendieckCategory.EnoughInjectives each fail for the
   expected missing declaration or instance. All eight removed old `proof_deps` are
   accounted for above; seven direct imports are removed, without claiming global
   unreachability. Read `dag/units/sk-thm-picard-duality.json`: its realized statement and
   step arrays are empty, and the support-triangle reduction retains the unit's route.
5. PASS — compared both node JSON files. Only `proof`, `proof_deps`, and `proof_origin`
   change; the dependencies equal the union of the proof-step uses. Checked their Lean
   attachments or Mathlib matches against the declarations used. The narrative agrees
   with the restriction/direct-image transport, quasi-coherent cone, stalk vanishing,
   and bounded-below comparison actually written in Lean.

Second reading changed only this report: added the independent checks and their results.
The proof, imports, and node metadata needed no repair. Closed holes remain
`AlgebraicGeometry.openRestriction_support_triangle` (1); added holes and split-offs
remain none (0).
