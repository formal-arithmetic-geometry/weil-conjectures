## What changed

The unchanged theorem `CategoryTheory.InternalActionSite.internalRestrictionModuleTensor`
now has a complete Lean assembly proof. It obtains the two normalized exact module
pullback cores and their section-pinned inflation identifications, enhances each
core with its canonical tensor structure, substitutes the core equalities, and
combines these with the two diagonal tensor results. The forgetful-exactness clauses
come directly from the existing proved `sheaf_action_grothendieck_inflation` theorem,
rather than becoming new obligations.

This is a decomposition of the tensor argument, with three strictly smaller public
statements in separate modules. The seven existing specification declarations move
verbatim to `InternalRestrictionModuleTensorData`; the original module publicly
re-exports them. Their signatures and bodies, including every normalization equation,
remain unchanged. The new data module contains no sorry and chooses no data.

A necessary definition repair adds `Presentation.inverse_morphisms`, naturality of
the inverse section equivalences in module maps. The existing `presentation`
construction proves it from the already proved inverse-map formulas of
`module_presheaf_equivalence`, using its object and morphism transport equalities.
No additional hypothesis is imposed on the site, groups, ring or group homomorphism.
The main theorem and every target keep their existing signatures. There are no
forced adaptations of claimed modules.

Validation: all six delivered Lean modules compile through `lcompile.py`. The
final item compiles in 6.1 seconds with diagnostic options removed and with the
usual heartbeat limit. The shared presentation repair compiles in 18–22 seconds;
the new argument modules compile in 2.5–5.6 seconds and the extracted data in
27.4 seconds. Direct importers of the repaired shared module are checked against
that version; unchanged copies are removed after their checks. The current
`PrimeToEllDerivedInvariantsReduction` importer exceeds the 60-second per-file
limit in both the repaired and baseline versions (66–68 seconds), so it is a
pre-existing slow consumer rather than a regression. Final compiler results and
the complete importer list are recorded in the change record.

## Proved and sorry left

Original holes closed: one, `CategoryTheory.InternalActionSite.internalRestrictionModuleTensor`
(node `lem-sfb-internal-restriction-module-tensor`), by a complete proof from the
three strict subarguments and existing forgetful exactness. This is a decomposition,
not a completed proof of the entire original mathematics: 0 of 1 original holes
are closed without newly split proof obligations; 1 of 1 has been reduced.

Holes added and remaining, exactly one per new module:

- `CategoryTheory.InternalActionSite.internalRestrictionModulePullback`
  (`lem-sfb-internal-restriction-module-pullback`): steps 1–3, the exact normalized
  scalar-extension cores and section-pinned inflation isomorphisms. It contains no
  tensor comparison, diagonal tensor or monoidal-coherence conclusion.
- `CategoryTheory.InternalActionSite.internalActionDiagonalTensor`
  (`lem-sfb-internal-action-diagonal-tensor`): step 4, diagonal action on the actual
  sheaf tensor under one presentation. It contains no geometric morphism,
  module-pullback adjunction, exactness or coherent tensor-pullback conclusion.
- `CategoryTheory.InternalActionSite.normalizedPrecompositionTensor`
  (`lem-sfb-normalized-precomposition-tensor`): steps 5–6 for an already supplied
  normalized exact core. It constructs only its tensor comparison and coherence;
  the core equality retains all previously supplied data. It has no action-site
  presentation or inflation-identification conclusion.

All three proofs are exactly `:= by sorry`. Each has its source, complete proof in
words, and matching node. There are no sorries in the item, the extracted data or
the repaired presentation module, and none inside definitions. No axiom is added.
The repair of the inverse naturality field is completely proved and adds zero holes.
Textual hole accounting for this packet: 1 closed, 3 added, net −2; this report
claims decomposition and a proved definition repair, not net sorry reduction.

## No longer needed

The old direct proof imports of ModulePullbackPushforwardAdjunction,
WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal and
Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorTrilinearUniversal move to the strict
subarguments that need them. They are retained as dependencies of those arguments;
no mathematical pruning is claimed for these modules. The original seven public
imports are retained by the extracted data module and publicly re-exported.

`lem-sfb-internal-action-sheaf-equivalence` and its module
`Sheaf.CategoryTheory.InternalActionSheafEquivalence` are not needed by this proof:
the hypotheses already supply both geometric morphisms and their inverse-image
identifications as literal precomposition, including maps. No set-action equivalence
has to be constructed. The module presentation alone supplies the module and
sheafification formulas. This removes that unused planned dependency without
changing any unit statement or proof step. The other old proof dependencies are
still needed in the respective new subarguments, with their node edges retained.
The parent's obsolete direct `tool_uses` entries are removed because these generic
tools now occur in the subarguments; none is silently abandoned there.

No module is withdrawn. In particular, zero current Lean importers of the item is
not treated as evidence that its unfinished DAG parents no longer need it. Actual
modules pruned from the library: none. All adopted WeilConjectures declarations,
signatures, public imports and proved bodies remain untouched.

## Where the brief, the DAG or earlier work was wrong

The old `Presentation` structure omitted naturality of `inverseSections` on module
morphisms, though the natural-language node describes a sectionwise inverse
functor. Its two inverse restriction/action fields do not imply that missing law.
On the one-object trivial-group site over ℤ, independently negating the inverse
section equivalence on ℤ but not on ℤ² preserves all old fields. The inclusion
ℤ → ℤ² then violates inverse-map naturality. In the assigned restriction equation
for θ = id, all the other maps are natural, so this object-dependent choice would
force an impossible natural comparison. The field repair rules out exactly this
unintended freedom, and the existing construction proves the required law.

The three stated proof dependencies supply general infrastructure, not the fully
normalized internal-action comparisons: the module adjunction does not specify
these inverse section maps, and the bilinear/trilinear universal properties do not
by themselves construct the action-site diagrams. The new lemmas isolate those
actual arguments. Their edge cases are unchanged: trivial groups, θ with a kernel,
zero coefficient rings and sites with empty covers are covered; no flatness,
nontriviality, enough-points or uniform-cover assumption is introduced.

The relevant current blueprint paragraph is read from `literature/blueprint/latest/`.
The detailed internal-action argument is agent-formulated infrastructure recorded
in the existing node; its mathematical sources are the existing Stacks 03D7,
03CY, 03DA and 03EK texts. The unit route is unchanged.

## New nodes

`def-sfb-internal-restriction-module-tensor-data` owns the seven extracted,
unchanged specification declarations. It asserts no existence and has no holes.

`lem-sfb-internal-restriction-module-pullback` isolates the non-tensor module
pullback and exactness argument, with both natural inflation comparisons pinned
on sections. It is a strict part of the original argument (steps 1–3).

`lem-sfb-internal-action-diagonal-tensor` isolates diagonal tensor sheafification
for a single action-site presentation (step 4).

`lem-sfb-normalized-precomposition-tensor` isolates the canonical tensor structure
and coherence on an existing normalized core (steps 5–6), independently of
internal-action presentations and of the inflation identifications.

Change records:
`coord/changes/G3-internal-presentation-inverse-naturality.md` and
`coord/changes/G3-internal-module-tensor-data-extraction.md`.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
