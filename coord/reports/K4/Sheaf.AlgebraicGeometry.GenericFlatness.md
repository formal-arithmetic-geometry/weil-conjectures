## What changed

Replaced the sorry in `AlgebraicGeometry.exists_nonempty_open_flat_restrict` with a
complete Lean reduction to generic flatness for a finite type algebra over an
arbitrary domain. The existing signature and all four public imports stay identical.
Added the proof-only import `Sheaf.AlgebraicGeometry.AffineGenericFlatness`.

The new affine-chart module proves
`AlgebraicGeometry.exists_nonzero_flat_restrict_basicOpen`: apply the algebraic
lemma to global sections, identify sections of a source basic open with its
localization, prove the composite to the affine base flat, then cancel the target
open immersion. Its import of `Sheaf.RingTheory.GenericFlatness` is proof-only.
The ring module has one named theorem and one sorry, with a full proof in words.

In the original module, two proved private helpers implement restriction to a
smaller open and finite-source-cover gluing over an affine base. Quasi-compactness
supplies a finite affine subcover. The generic point lies in each basic open, so
it lies in their finite intersection. A pullback cover and the canonical restriction
isomorphisms prove flatness on that intersection. An affine neighbourhood in the
original integral base and a final nested-restriction isomorphism complete the proof.
The updated DAG records precisely this route. All three delivered modules compile
cleanly together through lcompile.py.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_nonempty_open_flat_restrict`
(node `lem-sbc-generic-flatness`). No sorry remains in the original module.

Also proved the new affine bridge:
`AlgebraicGeometry.exists_nonzero_flat_restrict_basicOpen`
(node `lem-sbc-affine-chart-generic-flatness`). Its module has no sorry.
Both private helpers in the original module are proved.

Added exactly one hole:
`RingHom.exists_nonzero_flat_localizationAway`
(node `lem-sbc-finite-type-algebra-generic-flatness`,
`Sheaf.RingTheory.GenericFlatness`). This is the coordinate-algebra step of the
argument, not generic flatness for an arbitrary scheme morphism under another name.
The combination proves the affine bridge, finite-cover intersection, source gluing,
and passage back to the original non-affine base. This delivery is a decomposition:
one upper hole closed, one lower hole added, net zero holes. It does not claim a
sorry-free proof or count the imported algebraic hole as already proved.

Edge cases checked before stating the ring lemma: the zero target algebra is flat
with a = 1; the identity map has the same witness; for a quotient of the domain by
a nonzero ideal, inverting any nonzero element of the ideal makes the target zero,
even for a non-finitely-generated ideal. No injectivity of the ring map is assumed.
The geometric proof also handles the empty source: the finite intersection over
an empty cover is the whole affine base, and source locality is vacuous. Integral
bases are nonempty by definition. Non-Noetherian bases are retained throughout.

## No longer needed

None. No original import, node, or module was pruned. The original proof dependencies
remain used through the Mathlib definitions and locality criteria. The finite
intersection replaces the product calculation without changing the mathematical
route. No finite-presentation, coherent-module, or quasi-separatedness clause of
Tag 052A is imported or claimed.

## Where the brief, the DAG or earlier work was wrong

The original node's non-elementary algebraic step had no named proof dependency;
this delivery states precisely that missing step as the new ring theorem. The
existing upstream `Module.exists_flat_localizedModule_powers` assumes a Noetherian
base, so it cannot prove the current statement for arbitrary integral bases.

The actual searches are recorded in searches.jsonl: LeanSearch returned Internal
Server Error, recorded as unavailable; LeanFinder found localization and affine
flatness criteria, but no exact generic-flatness statement; Loogle returned no
matches for `Algebra.FiniteType, Module.Flat`; Mathlib grep found no generic-flatness
result applicable here. Source-library rg found the Noetherian result above.
Stacks Tags 051T, 051S and 052A were read directly from the Stacks website.

`tools/blueprint_refs.py ancestor lem-sbc-generic-flatness` returns None because the
existing created.item is a module name rather than a node ID. The original node
already explicitly records `sbc-lem-slicing` as its blueprint ancestor. Both new
nodes inherit that ancestor and the existing via chain, prepending this item.
The searches for generic flatness, generic freeness, 051T and 052A found no matching
imported blueprint node. The unit record sk-prop-normal-form has empty realized
lists; the slicing route through generic flatness is preserved, and no unit record
or target signature changed. No other held module was adapted.

## New nodes

`lem-sbc-finite-type-algebra-generic-flatness`, in sec-smooth-base-change, states
flatness of R → B → B[1/a] for finite type B over an arbitrary domain R, uniformly
for any localization model. Source: Stacks 051T, with the finite-presentation
descent of 051S and Noetherian generic freeness of 051R. The three search kinds
ran and are recorded honestly. The theorem is the only remaining hole.

`lem-sbc-affine-chart-generic-flatness`, in the same chapter and unit, states the
basic-open shrinking result for a single affine source chart over an affine
integral base. Source: the coordinate-chart step of Stacks 052A. Its proof from
the ring theorem and Mathlib's localization/flatness criteria is complete. Its
three searches also ran; LeanSearch was unavailable. No change record is needed:
existing statements, definitions, and public imports were not changed.

## Second reading by K4

1. **Visible declarations: PASS.** Compared the original module with the repository
   using diff. The existing theorem signature is byte-for-byte unchanged; its
   public imports and visibility are unchanged. The only additions to that module
   are a proof-only import, two proved private helpers, and the proof body. The
   revised docstring describes the finite-intersection implementation accurately.
   Both other modules and their public theorems are new. There are no definitions,
   interface changes, forced adaptations, or change records.
2. **Proof and axioms: PASS as a decomposition.** Independently compiled all three
   modules in import order with lcompile.py: no errors or warnings. Scanned every
   delivered Lean file: exactly one sorry, in the reported named ring theorem;
   no forbidden declarations or attributes, and no hollow definitions. Compiled
   temporary copies with #print axioms for all three public theorems and both
   private helpers. The restriction helper uses only propext, Classical.choice,
   and Quot.sound. The other four declarations additionally use sorryAx, from
   the single ring lemma. Thus this is one original hole closed and one lower
   hole added, net zero; it is not an axiom-clean proof of generic flatness.
3. **Split statements: PASS.** Read the ring lemma and its complete docstring proof
   against Stacks Tags [051T](https://stacks.math.columbia.edu/tag/051T) and
   [051S](https://stacks.math.columbia.edu/tag/051S). Checked the finite relation
   ideal over the fraction field, coefficient descent to a Noetherian subdomain,
   and injectivity of a free module into its fraction-field extension. Checked
   the zero algebra, identity map, noninjective quotient maps, empty scheme source,
   and empty finite cover. No Noetherian assumption is hidden. The affine bridge
   is proved, and the ring lemma is strictly the coordinate-algebra part of the
   global argument; it does not restate the original scheme theorem. Repeated
   LeanFinder searches with different wording for arbitrary-domain generic
   freeness and shrinking an affine morphism around the generic point; repeated
   Loogle with RingHom.FiniteType, RingHom.Flat; and searched Mathlib plus both
   repository roots by localization/free/flat terminology. No replacement was
   found. Read Module.exists_flat_localizedModule_powers: its Noetherian hypothesis
   prevents its direct use here. Closing the ring hole requires a substantial
   algebraic formalization, rather than a short application of an existing lemma.
4. **Route and pruning: PASS.** Read the proof from the top down and checked the
   affine chart, further restriction, finite intersection, source-local gluing,
   and final restriction isomorphism. Proof-only sibling imports are plain import;
   public imports supply the signatures. All old proof dependencies remain used,
   so the No longer needed list is complete. The sk-prop-normal-form unit record
   has empty realized lists and is unchanged; its slicing route through generic
   flatness is retained. The geometric argument matches the flatness portion of
   [Stacks 052A](https://stacks.math.columbia.edu/tag/052A).
5. **Nodes: PASS.** Compared the existing node with the repository: only proof,
   proof_deps, and proof_origin differ. Their steps match the actual Lean proof.
   Checked each new node's statement against its verbatim lean.statement and its
   module/declaration, source, searches, status, creation, blueprint ancestry,
   chapter, unit, and dependency union. The ring node names the only remaining
   sorry and the affine node records the proved bridge. No old dependency was
   silently dropped and no unit or target was edited.

Second reading changed only this report, recording the independent review and
explicit axiom results. The Lean proofs and DAG records required no repair.
