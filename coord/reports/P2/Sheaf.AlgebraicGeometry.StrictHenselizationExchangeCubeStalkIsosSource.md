## What changed

Proved the unchanged signature of
`AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_stalkComparisons_source`
in `Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource` from one
strictly smaller geometric assertion. Added
`Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk`, which states invertibility
of homology of the base-change mate for only the cartesian square over Spec A, on its
residue closed-point stalk. It has no cube, B, g, g0, second total space, target exchange,
or comparison of pulled-back single complexes.

The source proof explicitly computes the residue square, transports the closed-stalk
map through derived inverse image using two natural isomorphisms and
`NatIso.isIso_map_iff`, and expands the fixed cube comparison into that map and images
of isomorphisms. Both private helpers are proved. All original signatures and public
imports are preserved. A declaration-local unused-variable linter setting preserves
the unchanged signature whose target-side data this source proof does not need.

Both modules compile together without warnings. The source texts were read online at
Stacks Tags 03Q9 and 03QO. Edge cases checked against the new statement's argument:
degree zero, zero sheaves, empty X, arbitrary chosen pullback models, and arbitrary
separably closed extensions of the residue field.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_stalkComparisons_source`
(node `lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos-source`).
No sorry remains in the assigned module.

Added one hole:
`AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_closedStalk`
(node `lem-weil-pbc-strict-local-base-change-closed-stalk`). Its whole proof is
`:= by sorry`. This is a decomposition: one upper hole closed and one lower hole added,
with no net reduction in holes. No other holes are added and no definitions or
statements are changed. These counts are against the session-start assigned module.
After its withdrawal, the live baseline has no upper hole to close, so reintroducing
the module alone does not establish live target-closure progress.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`.
- `Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`.
- `Sheaf.Paper.InverseImageStalkGerm`.
- `Sheaf.AlgebraicGeometry.GeometricPointFieldExtension`.

The sections/stalk and field-extension results remain dependencies of the new
geometric theorem. They are not globally pruned. The original proof node no longer
needs direct edges to `lem-weil-pbc-unrestricted-strict-henselization-stalk`,
`lem-weil-pbc-strictly-henselian-sections-stalk`,
`lem-weil-pbc-geometric-point-field-extension`, or
`lem-weil-pbc-inverse-image-stalk-germ`. Its new proof edges are the closed-stalk
intermediate, exact derived inverse image, and the fixed cube-comparison definition.

For this source argument the unrestricted comparison package
`Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk` and
`Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso`
(nodes `lem-weil-pbc-unrestricted-strict-henselization-stalk` and
`lem-weil-pbc-unrestricted-strict-henselization-stalk-comparison`) is bypassed in favour
of `lem-weil-pbc-strict-local-base-change-global-homology` and direct mate pasting.
This makes no claim that these modules are unreached from other targets.
The inverse-image germ formula is unnecessary for this source proof: naturality of
`upperStarCompSheafFiberIso` suffices. No UNIT statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The dependency declarations express the canonical strict-local comparison, but none
states its closed-stalk form for the arbitrary cartesian model in this signature.
The new intermediate makes exactly that remaining part explicit. Its full proof in
words specifies the chosen-model map and horizontal pasting factors.

`Etale.baseChange_eq_derivedBaseChangeMapPlus` and
`Etale.baseChange_app_eq_mateEquiv` in DerivedComparison carry monoidal and
functorial-flat-resolution assumptions unavailable for AddCommGrpCat. The new
proof plan instead compares the generic derived mate on complexes using
`Adjunction.derivedPlus_mateEquiv_app_fac`, the pullback-comparison component formula,
and `derivedBaseChangeMapPlus_ext`, without those assumptions.

The direct attempt at the remaining transport is saved only in
`scratchpad/closed-stalk-full.lean.txt` and
`scratchpad/closed-stalk-transport-attempt.lean.txt`. The sections-to-stalk,
global-section inverse-image, and horizontal-isomorphism helpers compiled. The
derived-mate identification and dependent chosen-model transport did not finish
within the local compile limit. These attempts are not delivered as partial proofs.

During work, the read-only checkout changed and the assigned source module and its
original node disappeared from the live baseline; its parent conjunction module
remains. The sandbox retains the original unchanged signature and compiling proof
against the available compiled snapshot. The node copy was recovered from the same
original read-only U2 snapshot, before that module disappeared there too. The first dry run treated the source module and node as new and required P2 creation
metadata plus a change record. The delivery now documents that reintroduction in
`coord/changes/strict-henselization-source-component-restoration.md`; its original
signature stays identical, and no parent or other group's module is modified. The
current baseline has no downstream module using this source declaration. The
second reader must assess that reachability change; the sandbox proof remains a
valid reduction of the originally assigned theorem.

## New nodes

`lem-weil-pbc-strict-local-base-change-closed-stalk`, module
`Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk`: one smaller geometric
statement about the sq0 mate on its closed stalk, with a full four-step source-based
proof and recorded searches. It inherits `sec-proper-base-change` and `sk-thm-p1`,
and serves clause 1 of `lemma-weil-pbc-p1-exchange-geometric-stalk` before the
closed-fibre comparison. The generic strict-local global-homology theorem is used as
a tool, retaining the unit's projective-line and curve calculation steps.

`lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos-source` is also a new node
relative to the current baseline because its original delivery was withdrawn during
this session. Its unchanged mathematical statement is reintroduced with the P2 proof
route and creation metadata. The associated change record is
`coord/changes/strict-henselization-source-component-restoration.md`.

## Second reading by P2

1. Interface: attempted the prescribed diff against the current checkout; the assigned
   module is absent, as reported by the first worker. Compared its entire declaration
   signature byte for byte with the restoration record: identical. Also checked the
   common hypotheses against the present parent conjunction theorem. No existing
   declaration or definition is modified. The withdrawn original file is unavailable,
   so an independent byte comparison with that file cannot be certified. The change
   record explicitly declares restoration; no downstream adaptation is included.
2. Kernel check: independently compiled both delivered modules in import order with
   lcompile.py, without errors or warnings. Scratch copies with #print axioms for both
   public theorems show only propext, Classical.choice, Quot.sound, and sorryAx. The
   sole written sorry is the named closed-stalk theorem listed above. Both private
   helpers are proved; there are no definitions, forbidden declarations, or arbitrary
   data selected from an unproved existence statement in this delivery.
3. Split statement: read the full docstring and matched it to Stacks 03Q9 and 03QO,
   and to the actual global-homology, sections/stalk, and field-extension declarations.
   It is true for qcqs f without torsion or properness. The chosen model is transported
   by a unique pullback isomorphism, and any residue-field point is over the closed
   point; field enlargement preserves the stalk. Degree zero, zero coefficients,
   empty X, identity chosen models, and transcendental separably closed point-field
   extensions introduce no extra requirement. The statement isolates the lower-square
   mate and omits the cube and further inverse image; the source proof performs the
   remaining transport, rather than simply renaming the target. Independent LeanFinder
   and Loogle searches with different terms, and rg searches of the project and the
   upstream derived-base-change files, found no matching theorem. The existing global
   result uses a generic derived mate and still needs mate identification and model
   transport. The saved unfinished transport attempts show that closing this remaining
   hole requires substantial further work; no partial proof is delivered.
4. Route/pruning: read the source proof from its conclusion downwards. The two NatIso
   transports and the expansion of exchangeCubeSourceComparison are direct and correct.
   Public imports support the unchanged signature; the new proof import supplies its
   only geometric input. Imports in the holed module retain the declarations of its
   documented proof plan. Checked sk-thm-p1.realized: no realized statement or step is
   replaced or skipped. The listed old direct proof dependencies are all accounted for
   under No longer needed. This is one closed upper hole and one added lower hole,
   not a net proof or a live target-closure reduction. The restored module is currently
   unreached; this delivery does not modify the parent merely to claim reachability.
5. DAG: checked both node records, their Lean declarations, proof steps, dependency
   unions, sources, creation metadata, and blueprint/unit links. The source node's
   three steps match the Lean residue calculation, exact inverse-image transport,
   and final functorial isomorphisms. The lower node matches its named sorry and full
   four-step proof plan. Corrected a leftover sentence in the newly restored source
   node that referred to two restriction maps; the statement has only the source map.

Changes by this reader: corrected that new-node prose and added this review. Lean
proofs, signatures, and imports were left as read. Verdict: valid documented
restoration and decomposition, with one remaining geometric theorem and no claimed
net target-closure progress.
