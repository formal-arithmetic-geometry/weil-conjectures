## What changed

Replaced the sorry in `Module.isOpen_setOf_flat_localizedModule` in
`Sheaf.RingTheory.OpenFlatLocus` with a complete Lean reduction following Stacks 00RC:
obtain a Noetherian model flat at the contracted prime, apply the existing
`Module.Flat.exists_notMem_forall_flat_localizedModule`, map its basic open to S,
and transfer pointwise flatness by the model's ring pushout and module base change.
The original signature, universes and public imports are unchanged.

Added `Sheaf.RingTheory.FlatLocalizedModuleBaseChange`. Its theorem
`Module.Flat.localizedModule_of_isPushout` is fully proved, without finiteness or
Noetherian hypotheses. A private proved helper uses the tensor-kernel criterion
for localized flatness: naturality and flatness of the localized target make a
kernel element vanish after localization, and the zero criterion supplies a
prime-avoiding denominator which kills it. Tensor symmetry, the localization
base-change instance and pushout cancellation provide the requisite localization map.

Added `Sheaf.RingTheory.FlatPointNoetherianModel` for precisely the unfinished
approximation and eventual-flat-stage steps (steps 1-2 of the original DAG).
It states an actual Noetherian model with a commuting ring pushout and an
S-linear module base-change equivalence, flat only at the contracted point.
It asserts no flat neighborhood or openness. Its docstring and node explain the
localization of the directed system and application of 00R6 in detail. The old
approximation imports remain here as proof dependencies for the next worker.
No definitions or existing intermediate statements were changed.

Updated `lem-weil-pbc-openness-of-flatness` to record the three-step proof written
in Lean. The unit `sk-thm-p1` and all of its realized nodes are unchanged; this
refines the same Noetherian-approximation route below the unit level.

## Proved and sorry left

Closed the item's one hole, `Module.isOpen_setOf_flat_localizedModule`
(node `lem-weil-pbc-openness-of-flatness`), by decomposition. Added exactly one
hole: `Module.exists_noetherian_model_flat_at_prime`
(node `lem-weil-pbc-flat-point-noetherian-model`), in its own module. Its proof is
exactly `:= by sorry`; the full natural-language proof and source are in its
docstring and node. The item's module itself contains no sorry.

Also fully proved `Module.Flat.localizedModule_of_isPushout`
(node `lem-weil-pbc-flat-localized-module-base-change`) and its private helper
`flat_at_prime_of_flat_localization`. This module contains no sorry. Thus one
original hole is closed and one lower hole is added: this is a decomposition,
not a claim of a net decrease or of sorry-free openness. No other holes are added.

All three delivery modules compile through `lcompile.py --all`. The lower
base-change proof handles arbitrary rings, modules and primes; it requires no
finite generation, excluded characteristic, nonzero-module assumption, or
Noetherianity. The zero-module and identity-pushout cases are covered. A zero
ring has no spectrum points, so it introduces no extra case. The model theorem
retains arbitrary independent input universes and places its witnesses in their
maximum universe. A scratch compile confirms that applying the existing 00R1
statement directly to R and S with different universes fails; its future proof
must use the universe transport explicitly described in the docstring.

## No longer needed

Removed these direct proof imports from `Sheaf.RingTheory.OpenFlatLocus`:
`Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`,
`Sheaf.RingTheory.ColimitEventuallyFlat`, and
`Sheaf.RingTheory.LimitModuleFinitePresentation`. All three are still imported
by the model-descent module. They are relocated, not globally pruned.

The item's direct proof dependencies are now the model-descent node, the existing
Noetherian-neighborhood node, the proved base-change node, and the affine-spectrum
node. The old approximation dependencies are recorded on the model node, and
the tensor/base-change dependencies on the proved transfer node. No old node or
module is asserted to be globally unnecessary; global pruning is **none**.
The explicit localization-exactness input of the former final step is unnecessary
for the new transfer proof, which uses the tensor-localization zero criterion
instead. Other routes may still need that node.

For completeness, every old node removed from the item's **direct** `proof_deps` is:
`lem-weil-pbc-limit-module-finite-presentation`, `def-weil-pbc-noetherian-ring`,
`lem-weil-pbc-finite-type-algebra-noetherian`,
`lem-weil-pbc-filtered-colimit-localization-at-prime`,
`lem-weil-pbc-colimit-eventually-flat`, `def-weil-directed-colimit-abelian-groups`,
`lem-weil-pbc-localization-tensor-product`, `lem-weil-pbc-localization-tensor-over-base`,
`lem-weil-pbc-flat-over-localization`, `lem-weil-pbc-flat-module-base-change`,
`def-weil-pbc-flat-ring-map`, and `lem-weil-pbc-localization-module-exact`.
The first nine remain on the approximation node; flat base change, tensor localization,
and the flatness criterion remain on the proved transfer node. Only the explicit
localization-exactness input disappears from this route.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the original statement or route was found. The
existing neighborhood theorem is over a Noetherian base; it cannot directly
prove the arbitrary-base statement. The main difficulty left is construction
of the localized approximation systems and transport of their colimit and
scalar structures into the interface of `RingTheory.exists_flat_stage`.

The advertised local file `literature/stacks-project/algebra.tex` is absent on
this machine. Read the corresponding primary source online instead:
[Stacks 00RC](https://stacks.math.columbia.edu/tag/00RC),
[00R1](https://stacks.math.columbia.edu/tag/00R1),
[00R6](https://stacks.math.columbia.edu/tag/00R6),
[00HI](https://stacks.math.columbia.edu/tag/00HI), and
[00HT](https://stacks.math.columbia.edu/tag/00HT).
LeanSearch returned Internal Server Error for both new-node searches; this is
recorded as unavailable, not as evidence of absence. LeanFinder, Loogle and
actual Mathlib grep results are recorded in the search log and nodes.

## New nodes

`lem-weil-pbc-flat-point-noetherian-model`, module
`Sheaf.RingTheory.FlatPointNoetherianModel`, is the remaining step: descend a
single flat localization to a Noetherian finite-type model, with actual scalar
pushout and module-base-change data. It is strictly a part of the original
argument: the Noetherian neighborhood theorem and flatness transfer still have
to be combined to establish openness. Its dependencies preserve the original
00R1/localization/00R6 approximation plan.

`lem-weil-pbc-flat-localized-module-base-change`, module
`Sheaf.RingTheory.FlatLocalizedModuleBaseChange`, is fully proved. It states the
pointwise base-change implication for arbitrary module pushouts. It contains no
openness, approximation, finite-presentation or Noetherian assertion. No change
record or forced adaptation is needed.

## Second reading by T3

1. **Unchanged interface: pass.** Read all three delivered modules and diffed
   `OpenFlatLocus.lean` against the repository. Only its three private proof imports
   and its proof body change; its signature, independent universes u/v/w, public
   imports and existing docstring are byte-for-byte unchanged. The other two modules
   are new. No definitions, target statements, or forced adaptations are delivered.
   Compared the existing node JSON: only `proof`, `proof_deps`, and `proof_origin`
   change. No arbitrary witness is chosen to define data: the existential model is
   eliminated inside a proposition proof, and there are no new definitions.

2. **Proof and axioms: pass with one declared lower hole.** Independently compiled
   all three files with `lcompile.py --all`, with no errors or warnings. Scratch
   copies with `#print axioms` show only `propext`, `Classical.choice`, `Quot.sound`
   for both the private tensor-kernel helper and
   `Module.Flat.localizedModule_of_isPushout`. The model theorem and openness theorem
   also have `sorryAx`, as expected from the one named approximation hole. Scanned
   the files: the model theorem is the sole `sorry`, exactly `:= by sorry`; no axiom,
   unsafe, opaque, extern, implemented_by, or hollow definition occurs.
   Read the helper's tensor induction: its commuting square sends the kernel
   element to zero in a flat module, and localization's zero criterion gives a
   denominator outside q. The public proof constructs this localization via
   tensor symmetry, restrict-scalars localization and the inverse of e. These
   constructions use proved Mathlib equivalences, not an unproved existence witness.

3. **Split statements: pass.** Read [Stacks 00RC](https://stacks.math.columbia.edu/tag/00RC),
   [00R1](https://stacks.math.columbia.edu/tag/00R1), and
   [00R6](https://stacks.math.columbia.edu/tag/00R6), and the actual Lean statements
   of `Algebra.limitModuleFinitePresentation` and `RingTheory.exists_flat_stage`.
   The model's finite-presentation assumptions are precisely 00R1's inputs.
   Its Noetherian A, finite-type B, finite N, canonical pushout and module equivalence
   come from one stage; 00R6 applied after localization supplies flatness at the
   contracted point. Localization transitions are local because primes contract;
   localizing transition base changes gives the additional localization in 00R6.
   Independent universes require lifting to max u v w, as the docstring records.
   The theorem supplies no open neighborhood, so it is strictly the approximation
   portion, not a renamed openness theorem. The transfer statement is fully proved
   and needs none of the approximation or finiteness assumptions.
   Checked zero modules (flat everywhere), identity pushouts (ordinary localization),
   and zero rings (no prime to instantiate q); none requires an omitted hypothesis.
   Both new nodes carry self-contained statements, source, docstring proof,
   blueprint provenance, recorded searches, matching Lean signatures and split metadata.
   Repeated searches with different wording: `msearch.py` LeanFinder query
   "Finitely presented module flat at one prime descends to a Noetherian approximation
   of the base ring" returned smoothness/flatness/localization lemmas, no model result;
   Loogle `Module.Flat, LocalizedModule, Algebra.IsPushout` returned zero hits.
   Also used msearch grep and direct rg on Mathlib, lean/Sheaf, lean/WeilConjectures
   and the source checkout. The existing
   `Module.exists_fg_flat_localization_tensor` concerns an algebra module already
   globally flat, not an arbitrary finitely presented module flat at one point;
   `Module.Flat.localization_of_isPushout` concerns ring localizations, not M.
   Neither closes the remaining model hole or replaces the general module transfer.

4. **Top-down route and pruning: pass after report repair.** The openness proof
   first obtains the point model, then uses the already proved Noetherian neighborhood
   theorem with exactly its required Noetherian, finite-type and finite-module
   instances, then transfers flatness and assembles a basic open neighborhood.
   Checked `Algebra.IsPushout` in Mathlib's `IsTensorProduct.lean`: this public import
   is needed by the signatures, not merely by cancellation in the proof. Public
   imports expose the remaining signature notions; Sheaf approximation imports and
   upstream tensor-kernel/neighborhood imports are private. No shorter exact theorem
   was found. Read `dag/units/sk-thm-p1.json`, including `realized`: these edits are
   below its realized statement and steps and keep the same approximation route.
   The original report did not explicitly enumerate all old direct proof nodes;
   added the complete list above and distinguished relocation from global pruning.

5. **DAG against Lean: pass.** The openness node's three steps are exactly the model
   elimination, Noetherian neighborhood and proved transfer/basic-open argument.
   Its `proof_deps` is the union of their citations. The model node preserves the
   old 00R1/localization/00R6 dependencies and its proof explains the remaining
   localization-colimit construction. The transfer node follows flat base change,
   pushout cancellation, tensor localization and the tensor-kernel criterion, with
   matching dependencies and document proof origin. No unit record is altered.

Second reading changed only this report: supplied the complete removed direct-node
list and this independent review. No Lean repair was needed. The remaining
approximation proof requires constructing compatible localized systems, not a
few-minute application of an existing exact statement; it remains explicitly open.
The delivery is one hole closed and one added, net zero, a decomposition.
