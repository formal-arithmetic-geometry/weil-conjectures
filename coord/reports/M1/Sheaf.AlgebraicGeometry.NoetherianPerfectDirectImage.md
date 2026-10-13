## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.noetherian_perfect_directImage` with a complete Lean proof of the
planned application of the existing Tag 08EV direct-image criterion. Its statement,
universes, visibility, and original docstring are unchanged. All six public imports
and both original proof imports remain; five proof-only imports were added.

The proof derives locally Noetherian X from locally finite type over S, derives
compact X from quasi-compact f and compact S, and assembles `IsNoetherian X`.
Finite presentation of every term of G supplies quasi-coherence and finite type;
the existing coherence equivalence supplies termwise coherence. The new bounded
coherent tensor lemma supplies the first two hypotheses of 08EV. A separate support
bound lemma puts all cohomology supports inside one proper closed Z. The main proof
then obtains closedness of each cohomology support from the existing finite-type
support lemma, and properness from the existing closed-subset properties theorem.
The third new lemma supplies relative finite Tor dimension. These are assembled
into the unchanged direct-image conclusion by applying the existing criterion.

The source proof was read at https://stacks.math.columbia.edu/tag/0DJQ, with the
supporting statements at Tags 01Y0, 08CI and 08CG. The referenced local Stacks files
are not populated in this read-only clone, so the official Stacks pages were read.
The new modules give the source references and expanded natural-language proofs.
The parent node copy now records the actual Lean route. No existing statement or
definition was changed, and no other held module required adaptation.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.noetherian_perfect_directImage`
(node `lem-pc-noetherian-perfect-direct-image`). There are no remaining `sorry`s
in the item module.

Added three explicitly named holes, exactly `:= by sorry`, in three separate modules:

- `AlgebraicGeometry.Scheme.perfect_tensor_bounded_coherent`,
  node `lem-pc-perfect-tensor-bounded-coherent`, module
  `Sheaf.AlgebraicGeometry.PerfectTensorBoundedCoherent`.
- `AlgebraicGeometry.Scheme.boundedComplex_tensor_proper_support_bound`,
  node `lem-pc-bounded-complex-tensor-proper-support-bound`, module
  `Sheaf.AlgebraicGeometry.BoundedComplexTensorProperSupportBound`.
- `AlgebraicGeometry.Scheme.perfect_tensor_hasFiniteTorDimensionOver`,
  node `lem-pc-perfect-tensor-finite-relative-tor`, module
  `Sheaf.AlgebraicGeometry.PerfectTensorFiniteRelativeTor`.

This is a decomposition: one upper hole closed and three lower holes added,
not a complete proof without `sorryAx`, and not positive net hole progress.
The already existing 08EV criterion remains a holed dependency and was not edited.
The coherence equivalence, finite-type support closedness and closed-subset
properness interfaces are used through their existing declarations.
No data-valued definition or axiom was added.

Edge cases checked mathematically: empty X, zero E or G, an empty or reversed
bounding interval for G, degree shifts, f not separated, and overlapping term
supports. The coherence lemma assumes Noetherian X to obtain global bounds,
not merely locally Noetherian X. The support-bound lemma does not require
cohomology to be coherent or bounded, and does not claim that the individual
supports are closed. Closedness is proved later in the main module. Properness
of the finite union descends from a proper surjective finite disjoint union
of reduced supports, so no separatedness hypothesis on f is silently added.
The Tor lemma requires compact X for uniform bounds but no locally finite-type,
Noetherian, coherent or proper-support assumption. Its proof in words includes
the passage from affine-section relative flatness to stalkwise flatness.

All four sandbox modules compile in import order using `lcompile.py --all`.
Import-direction checks permit both existing support modules to be imported.
The main proof has no partial holes or private holed helpers.

## No longer needed

None. No original import was removed. Every original proof dependency is still
used directly or through the new intermediate statements or the original
statement's definitions. In particular the coherence equivalence and 08EV
criterion remain necessary, and perfectness and proper support remain the
same definitions. No node or module is claimed to be pruned from the targets.

## Where the brief, the DAG or earlier work was wrong

The DAG's steps 1 and 3 contain substantial tensor calculations and local-to-global
arguments that are not supplied by the originally named declarations. Step 3 was
marked elementary although it includes existence of a relative K-flat representative
and uniform Tor bounds. It is now an explicitly sourced intermediate item.
The main proof does the existing Mathlib and coherence glue itself, rather than
moving the whole theorem into another holed declaration.

The original finite-presentation and quasi-compactness hypotheses also imply
that X itself is Noetherian. This gives a finite perfect-model cover of all X,
so the bounded-coherence and Tor lemmas can use compact X rather than deriving
compactness only of the proper support. This retains the 0DJQ/08EV route and
changes nothing at unit level. The unit's `realized` fields are empty, and the
unit's own statement and steps were not edited or bypassed.

The new support-bound statement is broader than the original support verification:
E is arbitrary. It only bounds the nonzero-stalk loci. The main Lean proof explicitly
uses coherent cohomology, support closedness and properness for closed subsets to
recover the exact hypothesis required by 08EV. This avoids duplicating the
coherence verification inside a second holed lemma.

The two proper-support theorems from the proper-base-change chapter are used as
generic support tools; the existing declarations were inspected. The new support
node also cites generic separatedness and universal-closedness descent for its
finite-union argument. No replacement route through another unit is proposed.

LeanFinder and Loogle found only unrelated perfect pairings/groups, generic derived
t-structure facts, or module flatness/Tor facts. LeanSearch returned Internal Server
Error for the targeted searches, recorded as unavailable. Grep of Mathlib's algebraic
geometry and derived-category directories found no matching declarations. Searches
of both library roots and the complete DAG found no duplicate of the three new
statements. Existing `perfect_derivedTensor` concerns two perfect factors, and is
not applicable to G, whose terms need not be perfect over O_X.

## New nodes

`lem-pc-perfect-tensor-bounded-coherent`: on Noetherian X, a perfect tensor with a
bounded termwise coherent complex has bounded coherent cohomology. It has neither
a base morphism nor any relative-flatness/proper-support hypothesis. This isolates
step 1 of the original argument; it asserts no direct-image property.

`lem-pc-bounded-complex-tensor-proper-support-bound`: a bounded complex with proper
termwise supports bounds the support of its tensor with any derived object by one
proper closed subset. It neither assumes nor concludes coherence or cohomology
boundedness. This isolates the finite-union and support-containment argument.

`lem-pc-perfect-tensor-finite-relative-tor`: a perfect tensor with a bounded relatively
flat complex on compact X has finite Tor dimension over the inverse-image structure
sheaf. It asserts no coherence, support or direct-image property. This isolates
step 3 and explicitly keeps the uniform-bound issue.

Each new node inherits the parent's chapter and unit, points through the parent
node to blueprint ancestor `lem-pc-rf-perfect-base-change`, records the searches,
and gives the exact Lean signature and a complete proof in words. No change record
is needed because every existing signature and definition is preserved.

## Second reading by M1

1. **Interface preservation: PASS.** Diffed the existing module against the repository
   and compared the theorem signature byte for byte. Universes, binders, hypotheses,
   conclusion, visibility and original docstring are unchanged. The only existing-node
   changes are `proof`, `proof_deps` and `proof_origin`. Three modules and nodes are new;
   no definition, target or other existing declaration changes.
2. **Kernel and holes: PASS as a decomposition.** Independently compiled all four
   modules in import order with `lcompile.py --all`. Also compiled a scratch copy with
   `#print axioms` for the parent and all three intermediate declarations: only
   `propext`, `Classical.choice`, `Quot.sound` and `sorryAx` occur. The parent has no
   direct hole; each new hole is exactly the entire proof of a named public theorem.
   No forbidden declaration or data-valued definition is added. The dependency on
   `sorryAx` remains and this is not a completed axiom-clean proof.
3. **Split statements: PASS.** Read each complete signature, docstring and node, and
   the definitions of perfectness, relative flatness, proper support and relative Tor
   dimension. Tested empty source, zero factors, reversed intervals, shifts, overlapping
   supports and a nonseparated ambient morphism. Each lemma is strictly one part of
   the original argument, with independent hypotheses, rather than a renamed direct
   image theorem. Verified finite-union properness by the proper surjective finite
   disjoint union and Stacks [09MQ (4)](https://stacks.math.columbia.edu/tag/09MQ)
   and [03GN](https://stacks.math.columbia.edu/tag/03GN). The local tensor argument
   agrees with [0DJQ](https://stacks.math.columbia.edu/tag/0DJQ).
   Repeated searches using "preserves bounded coherent cohomology", "intersection of
   supports", "finite union of proper closed subschemes", and `CochainComplex.IsKFlat`
   through LeanFinder, Loogle and grep. No matching theorem was found. Read the nearby
   `perfect_hasFiniteTorDimensionOver`: it assumes finite Tor dimension of f, which
   is unavailable here. The perfect-pseudo-coherent/local-Tor result concerns O_X,
   not the inverse-image O_S. None closes these three lemmas in a few minutes.
4. **Route and pruning: PASS.** The parent constructs Noetherian X using Mathlib,
   converts finite presentation to coherence, uses the three tensor lemmas, constructs
   closed cohomology supports using the existing support-closedness theorem, inherits
   properness by its closed-subset theorem, and applies the original 08EV criterion.
   All added imports are proof-only in the parent; new public imports supply their
   signatures and the specified derived tensor instance. Every original import and
   proof dependency remains used. No pruning is claimed. The unit record and blueprint
   route are unchanged (`realized.statement` and its step lists are empty).
5. **Node agreement: PASS after repair.** Checked exact new Lean signatures, existence
   of every cited dependency, and equality of each `proof_deps` with the union of its
   steps' `uses`. The parent node now records the explicit use of HasSupportProperOver's
   definition when assembling the support witness. This restores the original proper-
   support definition dependency that was missing from its updated `proof_deps`.
   Corrected the support-subset projection description to "the third conjunct".

Second reading changed only the parent node's proof text/dependency bookkeeping and
this report. No Lean proof or statement required repair. One original hole is closed
and three lower holes are added: a decomposition with net hole count -2, pruned none.
